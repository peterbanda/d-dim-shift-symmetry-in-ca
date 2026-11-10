/-
The fixed-count lemma (paper Lemma 3.2(i), claim C002/C005 interface):
configurations fixed by a subgroup `H` are exactly the labelings of the
coset space, hence there are `|A| ^ [G : H]` of them.
-/
import Shiftsym.Definitions

namespace ShiftSym

variable {n d : ℕ} {A : Type*}

/-- A configuration fixed by `H` induces a well-defined map on the coset
space, and this is a bijection `fixedBy A H ≃ ((Lat n d ⧸ H) → A)`. -/
def fixedByEquiv (H : AddSubgroup (Lat n d)) :
    fixedBy A H ≃ ((Lat n d ⧸ H) → A) where
  toFun s := Quotient.lift (s : Config n d A) (by
    intro u v huv
    have hmem : -u + v ∈ H := QuotientAddGroup.leftRel_apply.mp huv
    have h1 : (s : Config n d A) (u + (-u + v)) = (s : Config n d A) u :=
      congrFun (s.2 _ hmem) u
    have h2 : u + (-u + v) = v := by
      rw [← add_assoc, add_neg_cancel, zero_add]
    rw [h2] at h1
    exact h1.symm)
  invFun f := ⟨fun u => f (QuotientAddGroup.mk u), by
    intro h hh
    funext u
    simp only [shift_apply]
    have hq : (QuotientAddGroup.mk (u + h) : Lat n d ⧸ H)
        = QuotientAddGroup.mk u := by
      rw [QuotientAddGroup.eq]
      have : -(u + h) + u = -h := by
        rw [neg_add_rev, add_assoc, neg_add_cancel, add_zero]
      rw [this]
      exact H.neg_mem hh
    rw [hq]⟩
  left_inv s := Subtype.ext (funext fun _ => rfl)
  right_inv f := funext fun q => Quotient.inductionOn q fun _ => rfl

/-- **Fixed-count lemma, index form**: `|Fix(H)| = |A| ^ [G : H]`. -/
theorem card_fixedBy [Finite A] [NeZero n] (H : AddSubgroup (Lat n d)) :
    Nat.card (fixedBy A H) = Nat.card A ^ H.index := by
  rw [Nat.card_congr (fixedByEquiv H), Nat.card_fun,
    AddSubgroup.index_eq_card]

/-- The translation group has `n ^ d` elements. -/
theorem card_lat [NeZero n] : Nat.card (Lat n d) = n ^ d := by
  simp

/-- **Fixed-count lemma, division form** (paper's `σ^(N/|H|)`). -/
theorem card_fixedBy_div [Finite A] [NeZero n] (H : AddSubgroup (Lat n d)) :
    Nat.card (fixedBy A H) = Nat.card A ^ (n ^ d / Nat.card H) := by
  have hmul : H.index * Nat.card H = Nat.card (Lat n d) :=
    H.index_mul_card
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hidx : n ^ d / Nat.card H = H.index := by
    rw [← card_lat (n := n) (d := d), ← hmul,
      Nat.mul_div_cancel _ hpos]
  rw [card_fixedBy, hidx]

end ShiftSym
