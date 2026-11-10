/-
Phase H, group 04 — proofs, part 2: the case `d = 1` of Remark 4.5(ii)
(Moreau–Witt complement; non-primitive words).
-/
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Formula

open Finset

namespace ShiftSym.P04

open ShiftSym

/-! ### `rad n` is squarefree and its divisors carry `coeffOf 1 h = -μ(h)` -/

theorem factorization_rad_le_one (n p : ℕ) : (rad n).factorization p ≤ 1 := by
  have h : rad n = phi n (fun _ => 1) := by rw [← rad_pow_eq_phi, pow_one]
  by_cases hp : p ∈ n.primeFactors
  · obtain ⟨i, rfl⟩ := exists_primeSeq_eq hp
    rw [h, factorization_phi_apply]
  · rw [h, factorization_phi_apply_of_notMem n _ hp]; exact zero_le_one

theorem squarefree_rad (n : ℕ) : Squarefree (rad n) :=
  Nat.squarefree_of_factorization_le_one rad_ne_zero (factorization_rad_le_one n)

theorem rdCoeff_one_one (p : ℕ) : rdCoeff p 1 1 = 1 := by
  simp [rdCoeff, gaussBinom]

theorem coeffOf_one_of_squarefree {h : ℕ} (hsq : Squarefree h) :
    coeffOf 1 h = -ArithmeticFunction.moebius h := by
  have hh0 : h ≠ 0 := hsq.ne_zero
  unfold coeffOf
  have hprod : ∏ p ∈ h.primeFactors, (rdCoeff p (h.factorization p) 1 : ℤ) = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    have hle := (Nat.squarefree_iff_factorization_le_one hh0).mp hsq p
    have hpos : 0 < h.factorization p := by
      rw [← Nat.support_factorization] at hp
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have h1 : h.factorization p = 1 := by omega
    rw [h1, rdCoeff_one_one, Nat.cast_one]
  rw [hprod, mul_one, ArithmeticFunction.moebius_apply_of_squarefree hsq,
    ArithmeticFunction.cardFactors_eq_sum_factorization, bigOmega, pow_add, pow_one]
  ring

theorem sum_moebius_divisors_eq_rad (n : ℕ) (hn : n ≠ 0) (f : ℕ → ℤ) :
    ∑ m ∈ n.divisors, ArithmeticFunction.moebius m * f m
      = ∑ m ∈ (rad n).divisors, ArithmeticFunction.moebius m * f m := by
  have hsub : (rad n).divisors ⊆ n.divisors :=
    Nat.divisors_subset_of_dvd hn (Nat.prod_primeFactors_dvd n)
  symm
  refine Finset.sum_subset hsub fun m hm hmr => ?_
  have hnsq : ¬ Squarefree m := by
    intro hsq
    apply hmr
    rw [Nat.mem_divisors] at hm ⊢
    refine ⟨?_, rad_ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hsq, rad]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono hm.1 hm.2)
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq, zero_mul]

/-- Remark 4.5(ii), `d = 1`, formula level, in divisor form. -/
theorem enumerationRHS_one_eq (n σ : ℕ) (hn : n ≠ 0) :
    enumerationRHS n 1 σ = moreauWittComplement n σ := by
  unfold enumerationRHS moreauWittComplement
  rw [sum_moebius_divisors_eq_rad n hn (fun m => (σ : ℤ) ^ (n / m)), pow_one, pow_one]
  have h1 : (1 : ℕ) ∈ (rad n).divisors := Nat.one_mem_divisors.mpr rad_ne_zero
  rw [← Finset.add_sum_erase _ _ h1]
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul, Nat.div_one]
  rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hdvd : h ∣ rad n := Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase hh)
  rw [coeffOf_one_of_squarefree ((squarefree_rad n).squarefree_of_dvd hdvd)]
  ring

theorem mainFormulaRHS_one_eq (n σ : ℕ) (hn : n ≠ 0) :
    mainFormulaRHS n 1 σ = moreauWittComplement n σ := by
  rw [mainFormulaRHS_eq_enumerationRHS, enumerationRHS_one_eq n σ hn]

theorem moreauWittComplement_one (σ : ℕ) : moreauWittComplement 1 σ = 0 := by
  simp [moreauWittComplement]

theorem numSS_d_one {n σ : ℕ} (hn : 1 ≤ n) (hσ : 1 ≤ σ) :
    (numSS n 1 σ : ℤ) = moreauWittComplement n σ := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    rw [numSS_one, moreauWittComplement_one, Nat.cast_zero]
  · rw [numSS_eq_mainFormulaRHS h le_rfl hσ, mainFormulaRHS_one_eq n σ (by omega)]

/-! ### Non-primitive words ↔ shift-symmetric cyclic configurations -/

section Words

variable {n σ : ℕ} [NeZero n]

/-- `Fin n → ZMod n`, `i ↦ (i : ZMod n)`. -/
def toZ (i : Fin n) : ZMod n := ((i : ℕ) : ZMod n)

/-- `ZMod n → Fin n`, `x ↦ x.val`. -/
def ofZ (x : ZMod n) : Fin n := ⟨x.val, ZMod.val_lt x⟩

theorem ofZ_toZ (i : Fin n) : ofZ (toZ i) = i := by
  ext
  simp only [ofZ, toZ, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt i.2

theorem toZ_ofZ (x : ZMod n) : toZ (ofZ x) = x := by
  simp [ofZ, toZ, ZMod.natCast_zmod_val]

/-- Words of length `n` ≃ configurations on `Z_n = (ZMod n)^1`. -/
def wordEquiv : (Fin n → Fin σ) ≃ Config n 1 (Fin σ) where
  toFun w := fun u => w (ofZ (u 0))
  invFun s := fun i => s (fun _ => toZ i)
  left_inv w := by
    funext i
    simp [ofZ_toZ]
  right_inv s := by
    funext u
    simp only [toZ_ofZ]
    congr 1
    funext j
    rw [Subsingleton.elim j 0]

theorem lat1_eq (u : Lat n 1) : u = fun _ => u 0 := by
  funext j; rw [Subsingleton.elim j 0]

theorem isNonPrimitive_iff (w : Fin n → Fin σ) :
    IsNonPrimitive w ↔ IsShiftSymmetric (wordEquiv w) := by
  constructor
  · rintro ⟨t, htn, htlt, H⟩
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact absurd (Nat.eq_zero_of_zero_dvd htn) (NeZero.ne n)
      · exact h
    refine ⟨fun _ => (t : ZMod n), ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp only [Pi.zero_apply] at h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact absurd (Nat.le_of_dvd htpos h0) (by omega)
    · funext u
      simp only [shift_apply, wordEquiv, Equiv.coe_fn_mk, Pi.add_apply]
      apply H
      simp only [ofZ]
      rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt htlt,
        Nat.mod_mod_of_dvd _ htn, Nat.add_mod_right]
  · rintro ⟨v, hv, hfix⟩
    set x := v 0 with hx
    have hx0 : x ≠ 0 := by
      intro h
      apply hv
      rw [lat1_eq v, ← hx, h]
      rfl
    set a := x.val with ha
    have hapos : 0 < a := by
      rw [ha]; exact Nat.pos_of_ne_zero ((ZMod.val_ne_zero x).mpr hx0)
    have halt : a < n := ZMod.val_lt x
    set t := Nat.gcd a n with ht
    have htn : t ∣ n := Nat.gcd_dvd_right a n
    have htle : t ≤ a := Nat.gcd_le_left n hapos
    have htpos : 0 < t := Nat.gcd_pos_of_pos_left n hapos
    refine ⟨t, htn, by omega, ?_⟩
    -- the translation by `t` fixes the configuration
    have hT : (fun _ => (t : ZMod n) : Lat n 1) ∈ stab (wordEquiv w) := by
      have hvmem : v ∈ stab (wordEquiv w) := hfix
      have hzs : (Nat.gcdA a n) • v ∈ stab (wordEquiv w) :=
        AddSubgroup.zsmul_mem _ hvmem _
      convert hzs using 1
      funext j
      rw [Subsingleton.elim j 0]
      simp only [Pi.smul_apply, zsmul_eq_mul]
      have hb := Nat.gcd_eq_gcd_ab a n
      have hcast : ((t : ℤ) : ZMod n) = (((a : ℤ) * Nat.gcdA a n + (n : ℤ) * Nat.gcdB a n : ℤ)
          : ZMod n) := by rw [ht, hb]
      push_cast at hcast
      rw [ZMod.natCast_self, zero_mul, add_zero, ha, ZMod.natCast_zmod_val] at hcast
      rw [hcast, ← hx, mul_comm]
    have hmT : ∀ m : ℕ, shift (m • (fun _ => (t : ZMod n) : Lat n 1)) (wordEquiv w)
        = wordEquiv w := fun m => AddSubgroup.nsmul_mem _ hT m
    intro i j hij
    have hdvd : t ∣ j + n - i := by
      apply Nat.dvd_of_mod_eq_zero
      apply Nat.sub_mod_eq_zero_of_mod_eq
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd htn, add_zero, Nat.mod_mod, hij]
    set m := (j + n - i) / t with hm
    have hmt : m * t = j + n - i := Nat.div_mul_cancel hdvd
    have key := congrFun (hmT m) (fun _ => toZ i)
    simp only [shift_apply, wordEquiv, Equiv.coe_fn_mk, Pi.add_apply] at key
    rw [ofZ_toZ] at key
    rw [← key]
    congr 1
    have hz : toZ i + (m • (fun _ => (t : ZMod n)) : Lat n 1) 0 = toZ j := by
      rw [Pi.smul_apply, nsmul_eq_mul]
      unfold toZ
      rw [← Nat.cast_mul, ← Nat.cast_add, hmt]
      have hi : (i : ℕ) ≤ j + n := by have := i.2; omega
      rw [Nat.add_sub_cancel' hi, Nat.cast_add, ZMod.natCast_self, add_zero]
    rw [hz, ofZ_toZ]

theorem card_nonPrimitive :
    Nat.card {w : Fin n → Fin σ // IsNonPrimitive w} = numSS n 1 σ := by
  unfold numSS
  exact Nat.card_congr (wordEquiv.subtypeEquiv fun w => isNonPrimitive_iff w)

end Words

theorem card_nonPrimitive_eq {n σ : ℕ} (hn : 1 ≤ n) (hσ : 1 ≤ σ) :
    (Nat.card {w : Fin n → Fin σ // IsNonPrimitive w} : ℤ) = moreauWittComplement n σ := by
  haveI : NeZero n := ⟨by omega⟩
  rw [card_nonPrimitive, numSS_d_one hn hσ]

end ShiftSym.P04
