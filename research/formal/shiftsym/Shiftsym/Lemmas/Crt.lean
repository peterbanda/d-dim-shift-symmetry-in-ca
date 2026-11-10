/-
CRT splitting (paper Lemma 3.5 infrastructure; Phase B item 4):
the translation group `(Z/nZ)^d` decomposes as the product of its primary
parts `(Z/p^{α_p}Z)^d` over the distinct primes `p ∣ n`.
-/
import Shiftsym.Definitions

namespace ShiftSym

variable {n d : ℕ}

open Finset in
/-- The product of the maximal prime powers of `n` recovers `n`. -/
theorem prod_primePow_eq (hn : n ≠ 0) :
    ∏ p : n.primeFactors, (p : ℕ) ^ n.factorization p = n := by
  rw [Finset.prod_coe_sort n.primeFactors (fun q => q ^ n.factorization q),
    ← Nat.support_factorization]
  exact Nat.factorization_prod_pow_eq_self hn

open Function in
/-- Distinct maximal prime powers of `n` are pairwise coprime. -/
theorem primePow_pairwise_coprime :
    Pairwise (Nat.Coprime on
      fun p : n.primeFactors => (p : ℕ) ^ n.factorization p) := by
  intro i j hij
  have hi : (i : ℕ).Prime := Nat.prime_of_mem_primeFactors i.2
  have hj : (j : ℕ).Prime := Nat.prime_of_mem_primeFactors j.2
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hi hj).mpr hne)

/-- CRT for `ZMod n`, indexed by the prime factors of `n`. -/
noncomputable def zmodPrimarySplit (hn : n ≠ 0) :
    ZMod n ≃+ ∀ p : n.primeFactors, ZMod ((p : ℕ) ^ n.factorization p) :=
  ((ZMod.ringEquivCongr (prod_primePow_eq hn).symm).trans
    (ZMod.prodEquivPi _ primePow_pairwise_coprime)).toAddEquiv

/-- **Primary decomposition of the translation group** (paper Lemma 3.5
infrastructure): `(Z/nZ)^d` is additively the product over `p ∣ n` of
`(Z/p^{α_p}Z)^d`. -/
noncomputable def latPrimarySplit (hn : n ≠ 0) :
    Lat n d ≃+ ∀ p : n.primeFactors, Lat ((p : ℕ) ^ n.factorization p) d :=
  (AddEquiv.piCongrRight fun _ : Fin d => zmodPrimarySplit hn).trans
    { toFun := fun f p i => f i p
      invFun := fun g i p => g p i
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

/-- Cardinality sanity: the split preserves the `n^d` count. -/
theorem card_latPrimarySplit (hn : n ≠ 0) :
    Nat.card (∀ p : n.primeFactors, Lat ((p : ℕ) ^ n.factorization p) d)
      = n ^ d := by
  haveI : NeZero n := ⟨hn⟩
  rw [← Nat.card_congr (latPrimarySplit (d := d) hn).toEquiv]
  simp [Nat.card_pi, Nat.card_zmod]

end ShiftSym
