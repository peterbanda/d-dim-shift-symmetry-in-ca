/-
Phase H, group 07 — helper module: the numerical claims of the Figure 2
caption (`fig:pattern-flip`, paper L725–736), from the certified
enumeration / lower-bound theorems, the union bound over prime-order
subgroups and explicit fixed sets.
-/
import Shiftsym.Paper.S07_Dynamics
import Shiftsym.Lemmas.LowerBound

open scoped Classical

namespace ShiftSym.P07

open ShiftSym

/-! ## Counting tools -/

theorem numSS_eq_card (n d σ : ℕ) [NeZero n] :
    numSS n d σ
      = (Finset.univ.filter (fun s : Config n d (Fin σ) => IsShiftSymmetric s)).card :=
  natCard_shiftSymmetric_eq_filterCard σ

/-- At a prime the count is the lower envelope (Theorem 6.1, equality case). -/
theorem numSS_prime_eq {p d σ : ℕ} (hp : p.Prime) (hd : 1 ≤ d) (hσ : 2 ≤ σ) :
    (numSS p d σ : ℤ) = lowerEnvelope p d σ :=
  ((lowerBound_proved p d σ hp.two_le hd hσ).2.mpr hp).symm

theorem lowerEnvelope_two (q σ : ℕ) :
    lowerEnvelope q 2 σ = ((q : ℤ) + 1) * (σ : ℤ) ^ q - (q : ℤ) * σ := by
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [lowerEnvelope, hI, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [rdCoeff, gaussBinom]
  ring

/-- One order-2 fixed set: `σ^{m^d/2} ≤ |S|` for even `m`. -/
theorem numSS_even_ge {m : ℕ} (d σ : ℕ) (hm : 2 ≤ m) (hm2 : 2 ∣ m) (hd : 1 ≤ d) :
    σ ^ (m ^ d / 2) ≤ numSS m d σ := by
  have : NeZero m := ⟨by omega⟩
  rw [numSS_eq_card]
  exact card_SS_ge_fix σ Nat.prime_two hm2 hd


/-- Union bound over the prime-order subgroups, each fixed set having at
most `σ^{N/2}` elements. -/
theorem numSS_le_union (n d σ : ℕ) [NeZero n] (hσ : 1 ≤ σ) :
    numSS n d σ ≤ (primeOrderSubs n d).card * σ ^ (n ^ d / 2) := by
  rw [numSS_eq_card]
  have hunion : Finset.univ.filter (fun s : Config n d (Fin σ) => IsShiftSymmetric s)
      = (primeOrderSubs n d).biUnion (fun C => fixedByF σ C) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isShiftSymmetric_iff_mem_biUnion σ s
  rw [hunion]
  refine Finset.card_biUnion_le.trans ?_
  rw [← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun C hC => ?_
  rw [card_fixedByF]
  exact Nat.pow_le_pow_right hσ
    (Nat.div_le_div_left (mem_primeOrderSubs.mp hC).two_le (by norm_num))

/-- The prime-order subgroups number `sopf_d(n)`. -/
theorem card_primeOrderSubs (n d : ℕ) [NeZero n] :
    (primeOrderSubs n d).card = sopfD n d := by
  have hset : primeOrderSubs n d = n.primeFactors.biUnion
      (fun p => Finset.univ.filter (fun C : AddSubgroup (Lat n d) => Nat.card C = p)) := by
    ext C
    simp only [mem_primeOrderSubs, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, Nat.mem_primeFactors]
    constructor
    · intro hC
      refine ⟨Nat.card C, ⟨hC, ?_, NeZero.ne n⟩, rfl⟩
      have h1 : Nat.card C ∣ Nat.card (Lat n d) := AddSubgroup.card_addSubgroup_dvd_card C
      rw [card_lat] at h1
      exact hC.dvd_of_dvd_pow h1
    · rintro ⟨p, ⟨hp, -, -⟩, hC⟩
      rw [hC]; exact hp
  rw [hset, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    rw [← card_orderP_subgroups (d := d) hpp hpn, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  · intro p _ q _ hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro C hCp hCq
    simp only [Finset.mem_filter] at hCp hCq
    exact hpq (hCp.2.symm.trans hCq.2)


set_option maxRecDepth 8000 in
/-- Two order-2 fixed sets on `Z_6^2`: `2^19 − 2^12 ≤ |S_{6^2}|`. -/
theorem numSS_six_two_ge : 2 ^ 19 - 2 ^ 12 ≤ numSS 6 2 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a : Lat 6 2 := ![3, 0] with ha
  set b : Lat 6 2 := ![0, 3] with hb
  set A : AddSubgroup (Lat 6 2) := AddSubgroup.zmultiples a with hA
  set B : AddSubgroup (Lat 6 2) := AddSubgroup.zmultiples b with hB
  have ha0 : a ≠ 0 := by rw [ha]; decide
  have hb0 : b ≠ 0 := by rw [hb]; decide
  have hcA : Nat.card A = 2 := by
    rw [hA, Nat.card_zmultiples]
    exact addOrderOf_eq_prime (by rw [ha]; decide) ha0
  have hcB : Nat.card B = 2 := by
    rw [hB, Nat.card_zmultiples]
    exact addOrderOf_eq_prime (by rw [hb]; decide) hb0
  have hdist : ∀ i j : Fin 3, (![0, ![3, 0], ![0, 3]] : Fin 3 → Lat 6 2) i
      = (![0, ![3, 0], ![0, 3]] : Fin 3 → Lat 6 2) j → i = j := by decide
  have h3 : 3 ≤ Nat.card (A ⊔ B : AddSubgroup (Lat 6 2)) := by
    have hmem : ∀ i : Fin 3, (![0, a, b] i) ∈ A ⊔ B := by
      intro i
      fin_cases i
      · exact zero_mem _
      · exact (le_sup_left : A ≤ A ⊔ B) (AddSubgroup.mem_zmultiples a)
      · exact (le_sup_right : B ≤ A ⊔ B) (AddSubgroup.mem_zmultiples b)
    have hinj : Function.Injective
        (fun i : Fin 3 => (⟨![0, a, b] i, hmem i⟩ : (A ⊔ B : AddSubgroup (Lat 6 2)))) := by
      intro i j hij
      have h := congrArg Subtype.val hij
      simp only at h
      exact hdist i j h
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  set X := fixedByF 2 A
  set Y := fixedByF 2 B
  have hX : X.card = 2 ^ 18 := by rw [card_fixedByF, hcA]; norm_num
  have hY : Y.card = 2 ^ 18 := by rw [card_fixedByF, hcB]; norm_num
  have hXY : X ∩ Y = fixedByF 2 (A ⊔ B) := by
    ext s
    simp only [Finset.mem_inter, mem_fixedByF, sup_le_iff, X, Y]
  have hI : (X ∩ Y).card ≤ 2 ^ 12 := by
    rw [hXY, card_fixedByF]
    exact Nat.pow_le_pow_right (by norm_num)
      (Nat.div_le_div_left h3 (by norm_num))
  have hU := Finset.card_union_add_card_inter X Y
  have hsub : X ∪ Y ⊆
      Finset.univ.filter (fun s : Config 6 2 (Fin 2) => IsShiftSymmetric s) := by
    intro s hs
    simp only [Finset.mem_union, mem_fixedByF, X, Y] at hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hs with hs | hs
    · exact ⟨a, ha0, hs (AddSubgroup.mem_zmultiples a)⟩
    · exact ⟨b, hb0, hs (AddSubgroup.mem_zmultiples b)⟩
  have hle := Finset.card_le_card hsub
  rw [numSS_eq_card]
  omega

/-! ## Comparing probabilities -/

theorem probUnif_lt_of {n d m e σ a b : ℕ} (hσ : 0 < σ)
    (ha : numSS n d σ ≤ a) (hb : b ≤ numSS m e σ)
    (h : a * σ ^ (m ^ e) < b * σ ^ (n ^ d)) :
    probUnif n d σ < probUnif m e σ := by
  unfold probUnif
  have hσ' : (0 : ℝ) < σ := by exact_mod_cast hσ
  have h1 : (0 : ℝ) < (σ : ℝ) ^ (n ^ d) := pow_pos hσ' _
  have h2 : (0 : ℝ) < (σ : ℝ) ^ (m ^ e) := pow_pos hσ' _
  rw [div_lt_div_iff₀ h1 h2]
  have key : numSS n d σ * σ ^ (m ^ e) < numSS m e σ * σ ^ (n ^ d) :=
    calc numSS n d σ * σ ^ (m ^ e) ≤ a * σ ^ (m ^ e) := Nat.mul_le_mul_right _ ha
      _ < b * σ ^ (n ^ d) := h
      _ ≤ numSS m e σ * σ ^ (n ^ d) := Nat.mul_le_mul_right _ hb
  exact_mod_cast key

/-- Upper bound at a prime, `d = 2`, `σ = 2`: `|S_{p^2}| ≤ (p+1)·2^p`. -/
theorem numSS_prime_two_le {p : ℕ} (hp : p.Prime) : numSS p 2 2 ≤ (p + 1) * 2 ^ p := by
  have h := numSS_prime_eq hp (by norm_num : 1 ≤ 2) (le_refl 2)
  rw [lowerEnvelope_two] at h
  have : ((numSS p 2 2 : ℕ) : ℤ) ≤ (((p + 1) * 2 ^ p : ℕ) : ℤ) := by
    rw [h]; push_cast
    have : (0 : ℤ) ≤ (p : ℤ) * 2 := by positivity
    linarith
  exact_mod_cast this

/-- A dip against an even neighbour `m`, given a lower bound `b ≤ |S_{m^2}|`. -/
theorem dip_of {p m b : ℕ} (hp : p.Prime) (hb : b ≤ numSS m 2 2)
    (h : (p + 1) * 2 ^ p * 2 ^ (m ^ 2) < b * 2 ^ (p ^ 2)) :
    probUnif p 2 2 < probUnif m 2 2 :=
  probUnif_lt_of (by norm_num) (numSS_prime_two_le hp) hb h


/-! ## The caption claims -/

set_option exponentiation.threshold 2000 in
theorem captionDipsD2_proved : captionDipsD2Statement := by
  intro p hp h5 h40
  interval_cases p
  all_goals first
    | (exfalso; revert hp; norm_num; done)
    | exact ⟨dip_of hp (numSS_even_ge 2 2 (by norm_num) (by norm_num) (by norm_num))
          (by decide),
        dip_of hp (numSS_even_ge 2 2 (by norm_num) (by norm_num) (by norm_num))
          (by decide)⟩
    | exact ⟨dip_of hp (numSS_even_ge 2 2 (by norm_num) (by norm_num) (by norm_num))
          (by decide),
        dip_of hp numSS_six_two_ge (by decide)⟩

theorem captionBoundary_proved : captionBoundaryStatement := by
  have h3 : numSS 3 2 2 = 26 := by
    have h := numSS_prime_eq Nat.prime_three (by norm_num : 1 ≤ 2) (le_refl 2)
    rw [lowerEnvelope_two] at h
    norm_num at h
    exact_mod_cast h
  have h4 : numSS 4 2 2 ≤ 3 * 2 ^ 8 := by
    have h := numSS_le_union 4 2 2 (by norm_num)
    rw [card_primeOrderSubs] at h
    have hs : sopfD 4 2 = 3 := by
      rw [sopfD, show (4 : ℕ) = 2 ^ 2 by norm_num,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
      decide
    calc numSS 4 2 2 ≤ sopfD 4 2 * 2 ^ (4 ^ 2 / 2) := h
      _ = 3 * 2 ^ 8 := by rw [hs]; norm_num
  exact probUnif_lt_of (by norm_num) h4 h3.ge (by norm_num)

theorem captionD3_proved : captionD3Statement := by
  have h5 : numSS 5 3 2 = 1040182682 := by
    have h := numSS_prime_eq (by norm_num : Nat.Prime 5) (by norm_num : 1 ≤ 3) (le_refl 2)
    have hl : lowerEnvelope 5 3 2 = 1040182682 := by decide
    rw [hl] at h
    exact_mod_cast h
  have h6 : numSS 6 3 2 ≤ 20 * 2 ^ 108 := by
    have h := numSS_le_union 6 3 2 (by norm_num)
    rw [card_primeOrderSubs] at h
    have hs : sopfD 6 3 = 20 := by
      have hpf : Nat.primeFactors 6 = {2, 3} := by
        rw [show (6 : ℕ) = 2 * 3 by norm_num,
          Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
        decide
      rw [sopfD, hpf]
      decide
    calc numSS 6 3 2 ≤ sopfD 6 3 * 2 ^ (6 ^ 3 / 2) := h
      _ = 20 * 2 ^ 108 := by rw [hs]; norm_num
  exact probUnif_lt_of (by norm_num) h6 h5.ge (by norm_num)

theorem captionD3NotMin_proved : captionD3NotMinStatement := by
  rintro ⟨-, h⟩
  exact absurd h (not_le.mpr captionD3_proved)

theorem caption_proved : captionStatement :=
  ⟨captionDipsD2_proved, captionBoundary_proved, captionD3_proved,
    captionD3NotMin_proved⟩

end ShiftSym.P07
