/-
Paper group-13 supplement (Section 4.5, the setting sentence "an $\FF_p$-vector space" and
"$d_p=\dim_{\FF_p}G[p]$") — proof of the frozen statement in
`Shiftsym/Paper/S13_AbelianGroups_Torsion.lean`, written after its three fidelity reviews (Run 046).

The structure is mathlib's `AddCommGroup.zmodModule` (scalar action `c • g = c.val • g` by
definition); the dimension follows from `|V| = p ^ dim V` for a finite `ZMod p`-space
(`Module.card_eq_pow_finrank`) and the proved `pRankPowStatement` (`|G[p]| = p ^ pRank G p`).
-/
import Shiftsym.Paper.Proofs.P13_AbelianGroups_Core
import Shiftsym.Paper.S13_AbelianGroups_Torsion

namespace ShiftSym.P13

/-- Every element of `G[p]` is killed by `p`, inside the subgroup. -/
private theorem nsmul_pTorsion (G : Type*) [AddCommGroup G] (p : ℕ) (x : pTorsion G p) :
    p • x = 0 :=
  Subtype.ext x.2

theorem pTorsionVectorSpace_proved (G : Type*) [AddCommGroup G] [Finite G] (p : ℕ) :
    pTorsionVectorSpaceStatement G p := by
  intro hp
  refine ⟨AddCommGroup.zmodModule (nsmul_pTorsion G p), ?_, ?_⟩
  · intro c g
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
    rfl
  · have : Fact p.Prime := ⟨hp⟩
    let _ : Module (ZMod p) (pTorsion G p) := AddCommGroup.zmodModule (nsmul_pTorsion G p)
    have := Fintype.ofFinite (pTorsion G p)
    have hcard : Nat.card (pTorsion G p) = p ^ Module.finrank (ZMod p) (pTorsion G p) := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
    have hsub : Nat.card (pTorsion G p) = Nat.card {g : G // p • g = 0} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
    exact Nat.pow_right_injective hp.two_le
      (hcard.symm.trans (hsub.trans (pRankPow_proved G p hp)))

end ShiftSym.P13
