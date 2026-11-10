/-
Correspondence-audit exporter: re-elaborates one Lean file of the `shiftsym`
development and dumps, as JSON, what the editor's infoview would show:

* every term node of the info trees (source range, elaborated type, the
  elaborated term itself, and the constant it names, if any);
* every tactic node (source range, goals before and after);
* the declarations the file defines (name + source range);
* for every referenced constant: its module, source range, signature and
  docstring (so the audit UI can show definitions without a Lean server).

Read-only: nothing is written into the Lean development.

Usage (from `research/formal/shiftsym/`):
  lake env lean --run ../correspondence_audit/tools/ExportInfo.lean <file.lean> <out.json>
-/
import Lean

open Lean Elab Meta

namespace AuditExport

def clip (s : String) (n : Nat := 3000) : String :=
  if s.length ≤ n then s else (s.take n).toString ++ " …[truncated]"

/-- Codepoint line/column (1-based line, 0-based column) of a position. -/
def posJson (fm : FileMap) (p : String.Pos.Raw) : Json × Json :=
  let q := fm.toPosition p
  (toJson q.line, toJson q.column)

structure Acc where
  nodes : Array Json := #[]
  consts : Std.HashSet Name := {}

def rangeFields (fm : FileMap) (stx : Syntax) : Option (List (String × Json)) := do
  let s ← stx.getPos? (canonicalOnly := true)
  let e ← stx.getTailPos? (canonicalOnly := true)
  let (sl, sc) := posJson fm s
  let (el, ec) := posJson fm e
  return [("sl", sl), ("sc", sc), ("el", el), ("ec", ec)]

partial def visit (fm : FileMap) (ctx? : Option ContextInfo) (t : InfoTree) (acc : Acc) :
    IO Acc := do
  match t with
  | .context pctx t => visit fm (pctx.mergeIntoOuter? ctx?) t acc
  | .hole _ => return acc
  | .node info children =>
    let mut acc := acc
    if let some ctx := ctx? then
      match info with
      | .ofTermInfo ti =>
        if let some rf := rangeFields fm ti.stx then
          let (ty, ex) ← (ti.runMetaM ctx do
              let e ← instantiateMVars ti.expr
              let ty ← instantiateMVars (← inferType e)
              return (toString (← ppExpr ty), toString (← ppExpr e)))
            |>.toBaseIO
            |>.map fun
              | .ok r => r
              | .error _ => ("?", "?")
          let c := ti.expr.getAppFn.constName?
          let mut fields := rf ++ [("k", toJson "t"), ("ty", toJson (clip ty)),
            ("ex", toJson (clip ex 600)), ("sk", toJson ti.stx.getKind.toString)]
          if let some c := c then
            fields := fields ++ [("c", toJson (privateToUserName c).toString)]
            acc := { acc with consts := acc.consts.insert c }
          acc := { acc with nodes := acc.nodes.push (Json.mkObj fields) }
      | .ofTacticInfo ti =>
        let k := ti.stx.getKind
        let skip := k == nullKind || k == ``Lean.Parser.Tactic.tacticSeq ||
          k == ``Lean.Parser.Tactic.tacticSeq1Indented || k == ``Lean.Parser.Term.byTactic ||
          k == ``Lean.Parser.Tactic.tacticSeqBracketed
        if !skip then
          if let some rf := rangeFields fm ti.stx then
            let pp (mctx : MetavarContext) (gs : List MVarId) : IO String := do
              let r ← ({ ctx with mctx := mctx }.runMetaM {} do
                  let ms ← gs.mapM fun g => do return toString (← Meta.ppGoal g)
                  return if ms.isEmpty then "no goals" else "\n\n".intercalate ms)
                |>.toBaseIO
              return match r with | .ok s => s | .error _ => "?"
            let gb ← pp ti.mctxBefore ti.goalsBefore
            let ga ← pp ti.mctxAfter ti.goalsAfter
            acc := { acc with nodes := acc.nodes.push (Json.mkObj (rf ++ [("k", toJson "tac"),
              ("sk", toJson k.toString), ("gb", toJson (clip gb 6000)),
              ("ga", toJson (clip ga 6000))])) }
      | _ => pure ()
    let ctx' := info.updateContext? ctx?
    for c in children do
      acc ← visit fm ctx' c acc
    return acc

def rangeJson (r : DeclarationRange) : Json :=
  Json.mkObj [("sl", toJson r.pos.line), ("sc", toJson r.pos.column),
    ("el", toJson r.endPos.line), ("ec", toJson r.endPos.column)]

end AuditExport

open AuditExport in
unsafe def main (args : List String) : IO UInt32 := do
  let [file, out] := args | do IO.eprintln "usage: ExportInfo <file.lean> <out.json>"; return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let opts := Options.empty |>.setBool `Elab.async false
  let (env, messages) ← processHeader header opts messages inputCtx (trustLevel := 1024) (mainModule := `AuditMain)
  let cmdState := { Command.mkState env messages opts with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState cmdState
  let env := s.commandState.env
  let fm := inputCtx.fileMap
  let mut errs : Array String := #[]
  for m in s.commandState.messages.toList do
    if m.severity == .error then errs := errs.push (← m.toString)
  let mut acc : Acc := {}
  for t in s.commandState.infoState.trees.toArray do
    acc ← visit fm none t acc
  -- declarations defined by this file
  let mut decls : Array Json := #[]
  for (n, _) in env.constants.map₂.toList do
    -- private helpers are shown under their user-facing name; auxiliary
    -- declarations (`_proof_1`, `match_1`, equation lemmas, …) are skipped
    let un := privateToUserName n
    if un.isInternal then continue
    if let .str _ s := un then
      if s.startsWith "match_" || s.startsWith "eq_" || s == "eq_def" || s == "proof_1" then continue
    if let some r ← (findDeclarationRanges? n : CoreM _).run' { fileName := file, fileMap := fm }
        { env } |>.toBaseIO |>.map (fun | .ok r => r | .error _ => none) then
      decls := decls.push (Json.mkObj [("name", toJson un.toString),
        ("private", toJson (isPrivateName n)), ("range", rangeJson r.range)])
  -- referenced constants
  let mut consts : Array Json := #[]
  for n in acc.consts.toList do
    let r ← (do
        let mod? := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
        let rng ← findDeclarationRanges? n
        let doc ← findDocString? env n
        let sig ← Meta.MetaM.run' do
          let ci ← getConstInfo n
          return toString (← ppExpr ci.type)
        return Json.mkObj ([("name", toJson (privateToUserName n).toString), ("type", toJson (clip sig 2000))] ++
          (match mod? with | some m => [("module", toJson m.toString)] | none => [("module", toJson "<this file>")]) ++
          (match rng with | some r => [("range", rangeJson r.range)] | none => []) ++
          (match doc with | some d => [("doc", toJson (clip d 4000))] | none => [])) : CoreM Json)
      |>.run' { fileName := file, fileMap := fm } { env } |>.toBaseIO
    if let .ok j := r then consts := consts.push j
  let j := Json.mkObj [("file", toJson file), ("errors", toJson errs),
    ("nodes", Json.arr acc.nodes), ("decls", Json.arr decls), ("consts", Json.arr consts)]
  IO.FS.writeFile out j.compress
  IO.println s!"{file}: {acc.nodes.size} nodes, {decls.size} decls, {consts.size} consts, {errs.size} errors"
  return 0
