/-
Cyclic-subgroup count (paper Lemma 3.3, line count; Phase C item 3b,
completing claim C005's counting component):

the subgroups of order `p` of `(Z/nZ)^d` number `(p^d - 1)/(p - 1)
= [d 1]_p`. Proof: fiber the `p^d - 1` order-`p` elements
(machine-checked in Torsion.lean) over the subgroup they generate; each
fiber is the set of `p - 1` nonzero elements of that subgroup.
-/
import Shiftsym.Lemmas.Torsion
import Shiftsym.Statement

namespace ShiftSym

variable {n d p : ℕ}

/-- In a finite type with zero, the nonzero elements number one less. -/
private theorem card_ne_zero_subtype (G : Type*) [Zero G] [Finite G] :
    Nat.card {w : G // w ≠ 0} = Nat.card G - 1 := by
  classical
  haveI := Fintype.ofFinite G
  simp only [ne_eq]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]

section Fiber

/-- A nonzero element of a subgroup of prime cardinality `p` has order
exactly `p`. -/
theorem addOrderOf_eq_of_mem_card_prime (hpp : p.Prime)
    {C : AddSubgroup (Lat n d)}
    (hC : Nat.card C = p) {w : Lat n d} (hw : w ∈ C) (hw0 : w ≠ 0) :
    addOrderOf w = p := by
  have hdvd : addOrderOf w ∣ p := by
    have h1 := AddSubgroup.addOrderOf_dvd_natCard C hw
    rwa [hC] at h1
  rcases hpp.eq_one_or_self_of_dvd _ hdvd with h1 | h
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hw0
  · exact h

/-- A nonzero element of a subgroup of prime cardinality generates it. -/
theorem zmultiples_eq_of_mem_card_prime (hpp : p.Prime)
    [Finite (Lat n d)] {C : AddSubgroup (Lat n d)}
    (hC : Nat.card C = p) {w : Lat n d} (hw : w ∈ C) (hw0 : w ≠ 0) :
    AddSubgroup.zmultiples w = C := by
  apply AddSubgroup.eq_of_le_of_card_ge
  · exact AddSubgroup.zmultiples_le.mpr hw
  · rw [Nat.card_zmultiples, hC,
      addOrderOf_eq_of_mem_card_prime hpp hC hw hw0]

/-- Map an order-`p` element to the (cardinality-`p`) subgroup it
generates. -/
def genMap (v : {v : Lat n d // addOrderOf v = p}) :
    {C : AddSubgroup (Lat n d) // Nat.card C = p} :=
  ⟨AddSubgroup.zmultiples v.1, by rw [Nat.card_zmultiples]; exact v.2⟩

/-- The fiber of `genMap` over `C` is the set of nonzero elements
of `C`. -/
def fiberEquiv (hpp : p.Prime) [Finite (Lat n d)]
    (C : {C : AddSubgroup (Lat n d) // Nat.card C = p}) :
    {v : {v : Lat n d // addOrderOf v = p} // genMap v = C}
      ≃ {w : C.1 // w ≠ 0} where
  toFun x := ⟨⟨x.1.1, by
      have h : AddSubgroup.zmultiples x.1.1 = C.1 :=
        congrArg Subtype.val x.2
      exact h ▸ AddSubgroup.mem_zmultiples x.1.1⟩, by
      intro h0
      have hx0 : x.1.1 = 0 := congrArg Subtype.val h0
      have hord := x.1.2
      rw [hx0, addOrderOf_zero] at hord
      exact hpp.one_lt.ne hord⟩
  invFun w := ⟨⟨w.1.1, addOrderOf_eq_of_mem_card_prime hpp C.2 w.1.2
      (fun h => w.2 (Subtype.ext h))⟩,
    Subtype.ext (zmultiples_eq_of_mem_card_prime hpp C.2 w.1.2
      (fun h => w.2 (Subtype.ext h)))⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv w := Subtype.ext (Subtype.ext rfl)

end Fiber

/-- **Line count** (paper Lemma 3.3, subgroup form): for prime `p ∣ n`,
the subgroups of `(Z/nZ)^d` of cardinality `p` number
`[d 1]_p = (p^d - 1)/(p - 1)`. -/
theorem card_orderP_subgroups [NeZero n] (hpp : p.Prime) (hp : p ∣ n) :
    Nat.card {C : AddSubgroup (Lat n d) // Nat.card C = p}
      = gaussBinom p d 1 := by
  classical
  haveI : NeZero p := ⟨hpp.pos.ne'⟩
  haveI : Fintype {C : AddSubgroup (Lat n d) // Nat.card C = p} :=
    Fintype.ofFinite _
  -- fiber the order-p elements over the subgroup they generate
  have h1 : Nat.card {v : Lat n d // addOrderOf v = p}
      = ∑ C : {C : AddSubgroup (Lat n d) // Nat.card C = p},
          Nat.card {v : {v : Lat n d // addOrderOf v = p} // genMap v = C} :=
    (Nat.card_congr (Equiv.sigmaFiberEquiv (genMap (p := p))).symm).trans
      Nat.card_sigma
  have hfib : ∀ C : {C : AddSubgroup (Lat n d) // Nat.card C = p},
      Nat.card {v : {v : Lat n d // addOrderOf v = p} // genMap v = C}
        = p - 1 := by
    intro C
    rw [Nat.card_congr (fiberEquiv hpp C), card_ne_zero_subtype, C.2]
  rw [card_addOrderOf_eq_prime hpp hp] at h1
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] at h1
  -- p^d - 1 = X * (p - 1) and (p - 1) * [d 1]_p = p^d - 1 force equality
  have hgeom := sub_one_mul_gaussBinom hpp.one_le d
  have hpos : 0 < p - 1 := by have := hpp.one_lt; omega
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← h1, ← hgeom, Nat.mul_comm]

end ShiftSym
