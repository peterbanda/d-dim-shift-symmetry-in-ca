/- Phase H audit module (part of the default build). -/
import Shiftsym.Paper.Proofs.P01_Model
import Shiftsym.Paper.Proofs.P02_LatticeLemmas
import Shiftsym.Paper.Proofs.P03_MobiusCoefficients
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Formula
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Lattice
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Mobius
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Second
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Words
import Shiftsym.Paper.Proofs.P05_KActive
import Shiftsym.Paper.Proofs.P05_KActive_B2019
import Shiftsym.Paper.Proofs.P05_KActive_Fix
import Shiftsym.Paper.Proofs.P05_KActive_Rank
import Shiftsym.Paper.Proofs.P06_BoundsProbability
import Shiftsym.Paper.Proofs.P06_BoundsProbability_Count
import Shiftsym.Paper.Proofs.P06_BoundsProbability_Gauss
import Shiftsym.Paper.Proofs.P06_BoundsProbability_Real
import Shiftsym.Paper.Proofs.P07_Dynamics
import Shiftsym.Paper.Proofs.P07_Dynamics_Caption
import Shiftsym.Paper.Proofs.P07_Dynamics_SymmetryBreaking
import Shiftsym.Paper.Proofs.P08_Detection
import Shiftsym.Paper.Proofs.P08_Detection_Algo
import Shiftsym.Paper.Proofs.P08_Detection_Reads
import Shiftsym.Paper.Proofs.P13_AbelianGroups
import Shiftsym.Paper.Proofs.P13_AbelianGroups_Mono
import Shiftsym.Paper.Proofs.P13_AbelianGroups_Torsion
import Shiftsym.Paper.Proofs.P08_Detection_Smooth
import Shiftsym.Paper.Proofs.P09_CrossoverLaws
import Shiftsym.Paper.Proofs.P09_CrossoverLaws_Bounds
import Shiftsym.Paper.Proofs.P09_CrossoverLaws_Window20
import Shiftsym.Paper.Proofs.P10_AppendixLemmas
import Shiftsym.Paper.Proofs.P10_AppendixLemmas_Analytic
import Shiftsym.Paper.Proofs.P10_AppendixLemmas_Basic
import Shiftsym.Paper.Proofs.P10_AppendixLemmas_Core
import Shiftsym.Paper.Proofs.P10_AppendixLemmas_Torus
import Shiftsym.Paper.Proofs.P11_Numerics
import Shiftsym.Paper.Proofs.P11_Numerics_Bounds
import Shiftsym.Paper.Proofs.P11_Numerics_Dc
import Shiftsym.Paper.Proofs.P11_Numerics_Deepens
import Shiftsym.Paper.Proofs.P11_Numerics_Meas
import Shiftsym.Paper.Proofs.P11_Numerics_Real
import Shiftsym.Paper.Proofs.P12_Necklaces

/-!
Phase H audit (2026-10-16): every frozen statement of the paper-wide
formalization (`Shiftsym/Paper/S??_*.lean`, namespaces `ShiftSym.P01` …
`ShiftSym.P12`; group 12 = the necklace sentence of Remark 4.5, added 2026-10-18;
the group-09 supplement `S09_CrossoverLaws_Window20` = the window constant 20 of
Proposition 10.2, added 2026-10-22; the group-07 supplement
`S07_Dynamics_SymmetryBreaking` = the symmetry-breaking clause of Corollary 8.2,
added 2026-10-27; the group-08 supplement `S08_Detection_Reads` = Remark 9.4 (read
complexity) and the paragraph after it, added 2026-11-06; group 13 = Section 4.5 (finite abelian groups),
added 2026-11-06 in paper v10, with the supplement `S13_AbelianGroups_Torsion` = the setting sentence
"G[p] is an F_p-vector space of dimension d_p", added 2026-11-08) is matched with its proof. The check below is
discovered from the environment, not from a hand-written list: for EVERY
constant `ShiftSym.Pxx.<X>Statement` declared in module
`Shiftsym.Paper.Sxx_*`, it requires a theorem `ShiftSym.Pxx.<X>_proved`
declared in a module `Shiftsym.Paper.Proofs.Pxx_*` whose type is literally
`∀ params, <X>Statement params` (with the statement instantiated at exactly
the theorem's own universe parameters), and whose axioms are among
`propext`, `Classical.choice`, `Quot.sound`. Any violation is an error, so
`lake build` fails.
-/

open Lean Meta Elab Command

namespace ShiftSym.AuditPaper

def allowedAx : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def modOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

/-- Returns (number of statements checked, list of failures). -/
def auditGroup (gid : String) : MetaM (Nat × List String) := do
  let env ← getEnv
  let ns : Name := (`ShiftSym).str s!"P{gid}"
  let sPre := s!"Shiftsym.Paper.S{gid}_"
  let pPre := s!"Shiftsym.Paper.Proofs.P{gid}_"
  let mut n := 0
  let mut fails : List String := []
  for (c, ci) in env.constants.toList do
    unless c.getPrefix == ns do continue
    let .str _ s := c | continue
    unless s.endsWith "Statement" do continue
    let some m := modOf env c | continue
    unless m.toString.startsWith sPre do continue
    unless ci matches .defnInfo _ do continue
    n := n + 1
    let base := s.dropRight "Statement".length
    let prf := ns.str (base ++ "_proved")
    match env.find? prf with
    | none => fails := s!"missing {prf}" :: fails
    | some pci =>
      unless pci matches .thmInfo _ do fails := s!"{prf} is not a theorem" :: fails
      match modOf env prf with
      | some pm => unless pm.toString.startsWith pPre do fails := s!"{prf} declared in {pm}" :: fails
      | none => fails := s!"{prf} has no module" :: fails
      let shapeOk ← forallTelescope pci.type fun xs body => do
        let lvlOk := match body.getAppFn with
          | .const _ ls => ls == pci.levelParams.map Level.param && ls.length == ci.levelParams.length
          | _ => false
        return body.getAppFn.constName? == some c && body.getAppArgs.toList == xs.toList && lvlOk
      unless shapeOk do fails := s!"{prf} type is not ∀ params, {c} params" :: fails
      let axs ← collectAxioms prf
      let bad := axs.toList.filter fun a => !(allowedAx.contains a)
      unless bad.isEmpty do fails := s!"{prf} uses axioms {bad}" :: fails
  return (n, fails)

end ShiftSym.AuditPaper

open ShiftSym.AuditPaper in
#eval show MetaM Unit from do
  let groups := ["01", "02", "03", "04", "05", "06", "07", "08", "09", "10", "11", "12", "13"]
  let mut total := 0
  let mut allFails : List String := []
  for g in groups do
    let (n, fs) ← auditGroup g
    IO.println s!"Phase H audit: group {g}: {n} frozen statements, {fs.length} failures"
    if n == 0 then allFails := s!"group {g}: no statements found" :: allFails
    total := total + n
    allFails := fs ++ allFails
  IO.println s!"Phase H audit: {total} frozen paper statements checked"
  unless allFails.isEmpty do throwError s!"Phase H audit FAILED: {allFails}"

-- Human-readable axiom sets of the per-group conjunctions (each conjoins its group's statements).
