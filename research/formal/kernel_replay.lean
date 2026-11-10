-- Kernel replay (Phase H): re-sends every theorem and safe definition of every
-- Shiftsym.* module to the Lean kernel under a fresh name. Run from
-- research/formal/shiftsym:  lake env lean ../kernel_replay.lean   (prints "errors=0"; since
-- 2026-10-19 it also fails, with a nonzero exit status, on any kernel error or any
-- axiom declared in a Shiftsym module, so the exit status alone is a usable gate).
import Shiftsym
import Shiftsym.AuditPaper
open Lean Meta Elab Command
/- Re-send every theorem and definition of every `Shiftsym.*` module to the kernel
   under a fresh name (catches anything admitted without kernel checking upstream). -/
#eval show CoreM Unit from do
  let env ← getEnv
  let kenv := env.toKernelEnv
  let mut nThm := 0
  let mut nDef := 0
  let mut nMods := 0
  let mut other : Array String := #[]
  let mut errs : Array String := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless m.toString.startsWith "Shiftsym" do continue
    nMods := nMods + 1
    let md := env.header.moduleData[i]!
    for c in md.constants do
      match c with
      | .thmInfo t =>
        let d := Declaration.thmDecl { t with name := t.name ++ `__rk, all := [t.name ++ `__rk] }
        match kenv.addDeclCore 0 0 d none with
        | .ok _ => nThm := nThm + 1
        | .error _ => errs := errs.push s!"thm {t.name}"
      | .defnInfo dv =>
        if dv.safety != .safe then
          other := other.push s!"nonsafe def {dv.name}"
        else
          let d := Declaration.defnDecl { dv with name := dv.name ++ `__rk, all := [dv.name ++ `__rk] }
          match kenv.addDeclCore 0 0 d none with
          | .ok _ => nDef := nDef + 1
          | .error _ => errs := errs.push s!"def {dv.name}"
      | .axiomInfo a => other := other.push s!"AXIOM {a.name}"
      | .opaqueInfo o => other := other.push s!"OPAQUE {o.name}"
      | _ => pure ()
  IO.println s!"KERNEL REPLAY: modules={nMods} theorems ok={nThm} defs ok={nDef} errors={errs.size} {errs.toList.take 40}"
  IO.println s!"KERNEL REPLAY: other={other.toList}"
  unless errs.isEmpty do throwError "Kernel replay failed: {errs.toList}"
  let axs := other.filter (·.startsWith "AXIOM")
  unless axs.isEmpty do throwError "Kernel replay: axioms declared in Shiftsym modules: {axs.toList}"
