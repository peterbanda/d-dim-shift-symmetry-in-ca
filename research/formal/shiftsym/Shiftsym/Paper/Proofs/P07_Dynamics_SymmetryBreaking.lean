/-
Phase H, group 07 (Dynamics), SUPPLEMENT of 2026-10-27 — PROOFS of the frozen
statements in `Shiftsym/Paper/S07_Dynamics_SymmetryBreaking.lean` (the
symmetry-breaking clause of Corollary 8.2), written after those statements
passed their fidelity reviews.

The clause is Theorem 8.1 in stabilizer form (`irrevStab_proved`), iterated
along the trajectory. The facts at the end (not paper claims) record that the
new hypothesis is satisfiable with nonempty acceptable-output sets, and that it
is strictly weaker than `RequiresLeavingS`, so `insolvSymBreakStatement`
strictly extends `insolvGeneralStatement`.
-/
import Shiftsym.Paper.S07_Dynamics_SymmetryBreaking
import Shiftsym.Paper.Proofs.P07_Dynamics

namespace ShiftSym.P07

/-- Stabilizers only grow along the trajectory of a translation-equivariant map
(Theorem 8.1, stabilizer form, iterated). -/
theorem stab_le_stab_iterate {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ)
    {Φ : Config n d (Fin σ) → Config n d (Fin σ)} (hΦ : Equivariant Φ)
    (x : Config n d (Fin σ)) : ∀ k : ℕ, stab x ≤ stab (Φ^[k] x) := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (irrevStab_proved n d σ hn hd hσ Φ hΦ _)

theorem insolvSymBreak_proved : insolvSymBreakStatement := by
  intro n d σ hn hd hσ _ T ⟨x, hx, hbr⟩ Φ hΦ hsol
  obtain ⟨k, hk⟩ := hsol x hx
  exact hbr _ hk (stab_le_stab_iterate hn hd hσ hΦ x k)

theorem insolvFull_proved : insolvFullStatement := ⟨insolv_proved, insolvSymBreak_proved⟩

/-! ## The new hypothesis against `RequiresLeavingS` (not paper claims) -/

/-- Every task that requires leaving `S` requires symmetry breaking: a
nonzero translation fixes the symmetric input but no asymmetric output. -/
theorem requiresSymmetryBreaking_of_requiresLeavingS {n d σ : ℕ} {T : Task n d σ}
    (h : RequiresLeavingS T) : RequiresSymmetryBreaking T := by
  obtain ⟨x, hx, ⟨v, hv0, hv⟩, hacc⟩ := h
  exact ⟨x, hx, fun y hy hle => hacc hy ⟨v, hv0, hle hv⟩⟩

/-- On `Z_4` over two states: the constant input `0000` must become the period-2
pattern `0101`. -/
def stripeTask : Task 4 1 2 where
  admissible := {fun _ => 0}
  accept := fun _ => {fun u => if (u 0).val % 2 = 0 then 0 else 1}

/-- The stripe task requires symmetry breaking, has a nonempty acceptable-output
set, and does not require leaving `S` (the target `0101` is shift-symmetric). -/
theorem stripeTask_requiresSymmetryBreaking_not_requiresLeavingS :
    RequiresSymmetryBreaking stripeTask ∧
      (stripeTask.accept (fun _ => 0)).Nonempty ∧ ¬ RequiresLeavingS stripeTask := by
  have hfix : shift (fun _ => (2 : ZMod 4))
      (fun u : Lat 4 1 => if (u 0).val % 2 = 0 then (0 : Fin 2) else 1) =
      (fun u : Lat 4 1 => if (u 0).val % 2 = 0 then (0 : Fin 2) else 1) := by
    funext u; revert u; decide
  refine ⟨⟨fun _ => 0, rfl, fun y hy hle => ?_⟩, ⟨_, rfl⟩, fun ⟨x, hx, _, hacc⟩ => ?_⟩
  · have hy' : y = fun u : Lat 4 1 => if (u 0).val % 2 = 0 then (0 : Fin 2) else 1 := hy
    subst hy'
    have h1 : (fun _ => (1 : ZMod 4)) ∈ stab (fun _ : Lat 4 1 => (0 : Fin 2)) := rfl
    have := congrFun (hle h1) 0
    revert this; decide
  · have hx' : x = fun _ => 0 := hx
    subst hx'
    exact hacc rfl ⟨fun _ => 2, by decide, hfix⟩

end ShiftSym.P07
