-- Frozen-dependency gate (2026-10-19). The meaning of a frozen statement depends
-- not only on its own file but on every definition it unfolds to. This script
-- computes, from the environment, the dependency closure of EVERY frozen
-- statement (each `…Statement` definition outside the proof and audit modules):
-- the types of all constants reached and the bodies of definitions (theorems are
-- skipped: by proof irrelevance a proof cannot change what a statement means).
-- It prints the Shiftsym modules in that closure and fails unless each of them is
-- fingerprinted in ../frozen_statements.sha256 (whose bytes ../check_frozen.py
-- checks). Run from research/formal/shiftsym:  lake env lean ../frozen_deps.lean
import Shiftsym
import Shiftsym.AuditPaper
open Lean Meta Elab Command

#eval show CoreM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Option Name :=
    (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!
  let isProj (m : Name) : Bool := m.getRoot == `Shiftsym
  let isProofOrAudit (m : Name) : Bool :=
    m.components.any (fun x => x == `Proofs) ||
      (m.components.getLast?.map (fun x => x.toString.startsWith "Audit")).getD false
  -- roots: every frozen statement
  let mut roots : Array Name := #[]
  for (c, ci) in env.constants.toList do
    let .str _ s := c | continue
    unless s.endsWith "Statement" do continue
    unless ci matches .defnInfo _ do continue
    let some m := modOf c | continue
    unless isProj m && !isProofOrAudit m do continue
    roots := roots.push c
  -- closure over types and definition bodies, restricted to Shiftsym modules
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut mods : Std.HashMap Name Nat := {}
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some m := modOf c | continue
    unless isProj m do continue
    let some ci := env.find? c | continue
    if ci matches .thmInfo _ then continue
    mods := mods.insert m (mods.getD m 0 + 1)
    let mut es : Array Expr := #[ci.type]
    match ci with
    | .defnInfo d => es := es.push d.value
    | .opaqueInfo o => es := es.push o.value
    | .inductInfo i => todo := todo ++ i.ctors.toArray
    | .ctorInfo k => todo := todo.push k.induct
    | .recInfo r => todo := todo ++ r.all.toArray
    | _ => pure ()
    for e in es do
      todo := todo ++ e.getUsedConstants
  -- compare with the fingerprinted files
  let txt ← IO.FS.readFile "../frozen_statements.sha256"
  let recorded : List String := (txt.splitOn "\n").filterMap fun l =>
    if l.startsWith "#" then none else
      match (l.splitOn " ").filter (· ≠ "") with
      | [_, p] => some p
      | _ => none
  let mut missing : Array String := #[]
  let modList := (mods.toList.map (fun (m, k) => (m.toString, k))).toArray.qsort (·.1 < ·.1)
  for (m, k) in modList do
    let path := "/".intercalate (m.splitOn ".") ++ ".lean"
    let ok := recorded.contains path
    IO.println s!"FROZEN DEPS: {if ok then "ok        " else "UNRECORDED"} {path} ({k} constants)"
    unless ok do missing := missing.push path
  IO.println s!"FROZEN DEPS: {roots.size} frozen statements, {seen.size} constants visited, {modList.size} Shiftsym modules in the closure, {missing.size} unrecorded"
  unless missing.isEmpty do throwError "Frozen-dependency gate failed: not fingerprinted: {missing.toList}"
