/-
Phase H, group 06 (BoundsProbability), proof helper 3: real-number estimates.

* `card_primeFactors_le_logb` — `ω(n) ≤ log₂ n` (from `2^{ω(n)} ≤ rad n ≤ n`);
* `unionRHS_le_closed` — the right side of Theorem 6.3(i) is at most
  `(2^d - 1 + 2 log₂ n) σ^{N/2}` (paper proof of 6.3(ii), every odd-prime term
  bounded by `2σ^{N/2}` after squaring, which keeps all arithmetic in `ℕ`);
* `unionRHS_le_rateRHS` — the right side of 6.3(i) is at most
  `2 log₂(n) n^{d-1} σ^{N/p₁}`;
* the prefactor comparisons of the paragraph after Theorem 6.3;
* the decay-rate algebra of Corollary 7.1, stated for an abstract count `S`.
-/
import Shiftsym.Paper.S06_BoundsProbability
import Shiftsym.Lemmas.Ineq

namespace ShiftSym.P06

open ShiftSym

/-! ### `ω(n) ≤ log₂ n` -/

theorem two_pow_card_primeFactors_le {n : ℕ} (hn : n ≠ 0) : 2 ^ n.primeFactors.card ≤ n := by
  calc 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

theorem card_primeFactors_le_logb {n : ℕ} (hn : n ≠ 0) :
    (n.primeFactors.card : ℝ) ≤ Real.logb 2 n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos, Real.rpow_natCast]
  exact_mod_cast two_pow_card_primeFactors_le hn

theorem logb_two_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ Real.logb 2 n :=
  Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)

theorem one_le_logb_two {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Real.logb 2 n := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast (by omega : 0 < n))]
  simp only [Real.rpow_one]
  exact_mod_cast hn

theorem two_le_logb_two {n : ℕ} (hn : 4 ≤ n) : 2 ≤ Real.logb 2 n := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast (by omega : 0 < n))]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num
  exact_mod_cast hn

/-- `2 log₂ n ≤ n` for `n ≥ 4`. -/
theorem two_logb_le {n : ℕ} (hn : 4 ≤ n) : 2 * Real.logb 2 n ≤ n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 : 2 * Real.logb 2 n = Real.logb 2 ((n : ℝ) ^ 2) := by
    rw [Real.logb_pow]; push_cast; ring
  have h2 : (n : ℝ) = Real.logb 2 ((2 : ℝ) ^ n) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  rw [h1]
  conv_rhs => rw [h2]
  rw [Real.logb_le_logb (by norm_num) (by positivity) (by positivity)]
  exact_mod_cast sq_le_two_pow hn

/-- `log₂ n ≤ n` for `n ≥ 1`. -/
theorem logb_le_self {n : ℕ} (hn : 1 ≤ n) : Real.logb 2 n ≤ n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2 : (n : ℝ) = Real.logb 2 ((2 : ℝ) ^ n) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  conv_rhs => rw [h2]
  rw [Real.logb_le_logb (by norm_num) hnpos (by positivity)]
  exact_mod_cast (Nat.lt_two_pow_self).le

/-! ### Real powers of `σ` with exponents `N/p` -/

theorem rpow_div_natCast {σ N p : ℕ} (hp : p ∣ N) (hp0 : 0 < p) :
    (σ : ℝ) ^ ((N : ℝ) / (p : ℝ)) = ((σ ^ (N / p) : ℕ) : ℝ) := by
  rw [← Nat.cast_div hp (by exact_mod_cast hp0.ne'), Real.rpow_natCast]
  push_cast
  rfl

theorem rpow_half_sq {σ N : ℕ} :
    ((σ : ℝ) ^ ((N : ℝ) / 2)) ^ 2 = (σ : ℝ) ^ N := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [show (N : ℝ) / 2 * ((2 : ℕ) : ℝ) = (N : ℝ) by push_cast; ring, Real.rpow_natCast]

theorem rpow_half_pos {σ N : ℕ} (hσ : 1 ≤ σ) : 0 < (σ : ℝ) ^ ((N : ℝ) / 2) :=
  Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < σ)) _

/-! ### Theorem 6.3(ii): the closed-form estimate of the union bound -/

theorem gaussBinom_two_d_one (d : ℕ) : gaussBinom 2 d 1 = 2 ^ d - 1 := by
  have := sub_one_mul_gaussBinom (q := 2) (by norm_num) d
  simpa using this

/-- The natural-number core of the odd-prime estimate:
`([d 1]_p σ^{N/p})^2 ≤ 4 σ^N` for an odd prime `p ∣ n`. -/
theorem odd_term_sq_le {n d σ p : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ)
    (pp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n) :
    (gaussBinom p d 1 * σ ^ (n ^ d / p)) ^ 2 ≤ 4 * σ ^ (n ^ d) := by
  have hp3 : 3 ≤ p := by have := pp.two_le; omega
  have hpN : p ∣ n ^ d := hpn.trans (dvd_pow_self n (by omega))
  set m := n ^ d / p with hm
  have hNm : n ^ d = p * m := (Nat.mul_div_cancel' hpN).symm
  have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
  -- `m ≥ p^{d-1}`
  have hmge : p ^ (d - 1) ≤ m := by
    have h1 : p ^ d ≤ n ^ d := Nat.pow_le_pow_left hpn' d
    have h2 : p ^ d = p * p ^ (d - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hd]
    rw [hNm, h2] at h1
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  -- reduce to `[d 1]_p^2 ≤ 4 · 2^m`
  have hkey : gaussBinom p d 1 ^ 2 ≤ 4 * 2 ^ m := by
    rcases Nat.lt_or_ge d 2 with hd1 | hd2
    · have : d = 1 := by omega
      subst this
      have : gaussBinom p 1 1 = 1 := rfl
      rw [this]
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    · set y := p ^ (d - 1) with hy
      have hy3 : 3 ≤ y := le_trans hp3 (by
        calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega))
      have hG : gaussBinom p d 1 ≤ 2 * y := gaussBinom_d_one_le (by omega) d
      rcases Nat.lt_or_ge y 4 with hy4 | hy4
      · -- `y = 3`: `p = 3`, `d = 2`
        have hy3' : y = 3 := by omega
        have hp3' : p = 3 := by
          by_contra hne
          have : 4 ≤ p := by omega
          have : 4 ≤ y := le_trans this (by
            calc p = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega))
          omega
        have hd2' : d = 2 := by
          by_contra hne
          have : p ^ 2 ≤ y := Nat.pow_le_pow_right (by omega) (by omega)
          rw [hp3'] at this
          omega
        subst hp3' hd2'
        have hg : gaussBinom 3 2 1 = 4 := rfl
        rw [hg]
        have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · calc gaussBinom p d 1 ^ 2 ≤ (2 * y) ^ 2 := Nat.pow_le_pow_left hG 2
          _ = 4 * y ^ 2 := by ring
          _ ≤ 4 * 2 ^ y := Nat.mul_le_mul_left 4 (sq_le_two_pow hy4)
          _ ≤ 4 * 2 ^ m := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by norm_num) hmge)
  have hσm : 2 ^ m ≤ σ ^ ((p - 2) * m) := by
    calc 2 ^ m ≤ 2 ^ ((p - 2) * m) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left m (by omega))
      _ ≤ σ ^ ((p - 2) * m) := Nat.pow_le_pow_left hσ _
  have hpm : p * m = 2 * m + (p - 2) * m := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' (by omega : 2 ≤ p)]
  calc (gaussBinom p d 1 * σ ^ m) ^ 2 = gaussBinom p d 1 ^ 2 * σ ^ (2 * m) := by ring
    _ ≤ (4 * 2 ^ m) * σ ^ (2 * m) := Nat.mul_le_mul_right _ hkey
    _ ≤ (4 * σ ^ ((p - 2) * m)) * σ ^ (2 * m) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hσm)
    _ = 4 * σ ^ (n ^ d) := by rw [hNm, hpm, pow_add]; ring

/-- One term of the union bound, against `σ^{N/2}`. -/
theorem term_le_half {n d σ p : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ)
    (hp : p ∈ n.primeFactors) :
    ((gaussBinom p d 1 * σ ^ (n ^ d / p) : ℕ) : ℝ)
      ≤ ((if p = 2 then (2 : ℝ) ^ d - 1 else 0) + 2) * (σ : ℝ) ^ (((n ^ d : ℕ) : ℝ) / 2) := by
  have pp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hX := rpow_half_pos (σ := σ) (N := n ^ d) (by omega)
  by_cases hp2 : p = 2
  · subst hp2
    rw [if_pos rfl]
    have h2N : 2 ∣ n ^ d := hpn.trans (dvd_pow_self n (by omega))
    rw [show (((n ^ d : ℕ) : ℝ) / 2) = (((n ^ d : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) by norm_num,
      rpow_div_natCast h2N (by norm_num), gaussBinom_two_d_one]
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    push_cast [Nat.cast_sub h1]
    have : (0 : ℝ) ≤ ((σ ^ (n ^ d / 2) : ℕ) : ℝ) := by positivity
    push_cast at this
    nlinarith
  · rw [if_neg hp2, zero_add]
    have hsq := odd_term_sq_le hn hd hσ pp hp2 hpn
    have hsqR : ((gaussBinom p d 1 * σ ^ (n ^ d / p) : ℕ) : ℝ) ^ 2
        ≤ (2 * (σ : ℝ) ^ (((n ^ d : ℕ) : ℝ) / 2)) ^ 2 := by
      rw [mul_pow, rpow_half_sq]
      exact_mod_cast hsq
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsqR

theorem unionRHS_le_closed {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ) :
    (unionRHS n d σ : ℝ) ≤ closedPrefactor n d * (σ : ℝ) ^ (((n ^ d : ℕ) : ℝ) / 2) := by
  set X := (σ : ℝ) ^ (((n ^ d : ℕ) : ℝ) / 2) with hXdef
  have hX : 0 < X := rpow_half_pos (by omega)
  rw [unionRHS, Nat.cast_sum]
  calc ∑ p ∈ n.primeFactors, ((gaussBinom p d 1 * σ ^ (n ^ d / p) : ℕ) : ℝ)
      ≤ ∑ p ∈ n.primeFactors, ((if p = 2 then (2 : ℝ) ^ d - 1 else 0) + 2) * X :=
        Finset.sum_le_sum fun p hp => term_le_half hn hd hσ hp
    _ = ((if 2 ∈ n.primeFactors then (2 : ℝ) ^ d - 1 else 0)
          + 2 * (n.primeFactors.card : ℝ)) * X := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ closedPrefactor n d * X := by
        apply mul_le_mul_of_nonneg_right _ hX.le
        rw [closedPrefactor]
        have h1 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
        have h2 := card_primeFactors_le_logb (n := n) (by omega)
        split_ifs <;> linarith

/-! ### The comparison paragraph -/

theorem unionRHS_le_rateRHS {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ) :
    (unionRHS n d σ : ℝ) ≤ rateRHS n d σ := by
  have hmf : 0 < n.minFac := Nat.minFac_pos n
  have hmfN : n.minFac ∣ n ^ d := (Nat.minFac_dvd n).trans (dvd_pow_self n (by omega))
  rw [rateRHS, rpow_div_natCast hmfN hmf]
  have hterm : ∀ p ∈ n.primeFactors,
      gaussBinom p d 1 * σ ^ (n ^ d / p) ≤ 2 * n ^ (d - 1) * σ ^ (n ^ d / n.minFac) := by
    intro p hp
    have pp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    apply Nat.mul_le_mul
    · calc gaussBinom p d 1 ≤ 2 * p ^ (d - 1) := gaussBinom_d_one_le pp.two_le d
        _ ≤ 2 * n ^ (d - 1) :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.le_of_dvd (by omega) hpn) _)
    · apply Nat.pow_le_pow_right (by omega)
      exact Nat.div_le_div_left (Nat.minFac_le_of_dvd pp.two_le hpn) hmf
  rw [unionRHS]
  have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [smul_eq_mul] at hsum
  have hsumR : ((∑ p ∈ n.primeFactors, gaussBinom p d 1 * σ ^ (n ^ d / p) : ℕ) : ℝ)
      ≤ (n.primeFactors.card : ℝ) * (2 * (n : ℝ) ^ (d - 1) * ((σ ^ (n ^ d / n.minFac) : ℕ) : ℝ)) := by
    exact_mod_cast hsum
  have hcard := card_primeFactors_le_logb (n := n) (by omega)
  have hpos : (0 : ℝ) ≤ 2 * (n : ℝ) ^ (d - 1) * ((σ ^ (n ^ d / n.minFac) : ℕ) : ℝ) := by
    positivity
  calc _ ≤ _ := hsumR
    _ ≤ Real.logb 2 n * (2 * (n : ℝ) ^ (d - 1) * ((σ ^ (n ^ d / n.minFac) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard hpos
    _ = _ := by ring

theorem sq_lt_two_pow_pred {n : ℕ} (hn : 7 ≤ n) : n ^ 2 < 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have e1 : 2 ^ (m + 1 - 1) = 2 * 2 ^ (m - 1) := by
      rw [show m + 1 - 1 = (m - 1) + 1 by omega, pow_succ]; ring
    rw [e1]
    have : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by nlinarith
    omega

/-- The exact integer form of the sharpening inequality. -/
theorem cg_sharpen_nat {n d : ℕ} (h : (7 ≤ n ∧ 1 ≤ d) ∨ (5 ≤ n ∧ 2 ≤ d)) :
    n ^ (2 * n ^ (d - 1)) < 2 ^ (n ^ d - 1) := by
  by_cases h7 : 7 ≤ n
  · have hd : 1 ≤ d := by rcases h with h | h <;> omega
    set x := n ^ (d - 1) with hx
    have hx1 : 1 ≤ x := Nat.one_le_pow _ _ (by omega)
    have hnd : n ^ d = n * x := by rw [hx, ← pow_succ', Nat.sub_add_cancel hd]
    calc n ^ (2 * x) = (n ^ 2) ^ x := by rw [pow_mul]
      _ < (2 ^ (n - 1)) ^ x := Nat.pow_lt_pow_left (sq_lt_two_pow_pred h7) (by omega)
      _ = 2 ^ ((n - 1) * x) := by rw [← pow_mul]
      _ ≤ 2 ^ (n ^ d - 1) := by
          apply Nat.pow_le_pow_right (by norm_num)
          rw [hnd, Nat.sub_mul, one_mul]
          omega
  · have h56 : n = 5 ∨ n = 6 := by rcases h with h | h <;> omega
    have hd : 2 ≤ d := by rcases h with h | h <;> omega
    set x := n ^ (d - 2) with hx
    have hx1 : 1 ≤ x := Nat.one_le_pow _ _ (by omega)
    have hnd1 : n ^ (d - 1) = n * x := by
      rw [hx, ← pow_succ', show d - 2 + 1 = d - 1 by omega]
    have hnd : n ^ d = n ^ 2 * x := by
      rw [hx, ← pow_add, show 2 + (d - 2) = d by omega]
    have hbase : n ^ (2 * n) < 2 ^ (n ^ 2 - 1) := by
      rcases h56 with rfl | rfl <;> norm_num
    calc n ^ (2 * n ^ (d - 1)) = (n ^ (2 * n)) ^ x := by rw [hnd1, ← pow_mul]; ring_nf
      _ < (2 ^ (n ^ 2 - 1)) ^ x := Nat.pow_lt_pow_left hbase (by omega)
      _ = 2 ^ ((n ^ 2 - 1) * x) := by rw [← pow_mul]
      _ ≤ 2 ^ (n ^ d - 1) := by
          apply Nat.pow_le_pow_right (by norm_num)
          rw [hnd, Nat.sub_mul, one_mul]
          omega

theorem cg_sharpen {n d : ℕ} (h : (7 ≤ n ∧ 1 ≤ d) ∨ (5 ≤ n ∧ 2 ≤ d)) :
    2 * Real.logb 2 n * (n : ℝ) ^ (d - 1) < (n : ℝ) ^ d - 1 := by
  have hn : 5 ≤ n := by rcases h with h | h <;> omega
  have hd : 1 ≤ d := by rcases h with h | h <;> omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN1 : 1 ≤ n ^ d := Nat.one_le_pow _ _ (by omega)
  have hL : 2 * Real.logb 2 n * (n : ℝ) ^ (d - 1)
      = Real.logb 2 (((n ^ (2 * n ^ (d - 1)) : ℕ) : ℝ)) := by
    push_cast
    rw [Real.logb_pow]
    push_cast
    ring
  have hR : (n : ℝ) ^ d - 1 = Real.logb 2 (((2 ^ (n ^ d - 1)) : ℕ) : ℝ) := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    push_cast [Nat.cast_sub hN1]
    ring
  rw [hL, hR, Real.logb_lt_logb_iff (by norm_num) (by positivity) (by positivity)]
  exact_mod_cast cg_sharpen_nat h

theorem even_improve {n d : ℕ} (he : Even n) (hn : 4 ≤ n) (hd : 2 ≤ d) :
    n.minFac = 2
      ∧ closedPrefactor n d < 2 * Real.logb 2 n * (n : ℝ) ^ (d - 1)
      ∧ closedPrefactor n d < (n : ℝ) ^ d - 1 := by
  have hL2 := two_le_logb_two hn
  have hLn := two_logb_le hn
  set L := Real.logb 2 n
  set a : ℝ := (2 : ℝ) ^ d with ha
  set b : ℝ := (n : ℝ) ^ (d - 1) with hb
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have ha4 : (4 : ℝ) ≤ a := by
    rw [ha]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have hab : a ^ 2 ≤ 4 * b := by
    have h1 : a ^ 2 = 4 * (4 : ℝ) ^ (d - 1) := by
      rw [ha, ← pow_mul, show d * 2 = 2 + 2 * (d - 1) by omega, pow_add, pow_mul]
      norm_num
    rw [h1, hb]
    have : (4 : ℝ) ^ (d - 1) ≤ (n : ℝ) ^ (d - 1) := pow_le_pow_left₀ (by norm_num) hn4 _
    linarith
  have hb1 : (1 : ℝ) ≤ b := one_le_pow₀ (by linarith)
  have hnd : (n : ℝ) ^ d = n * b := by
    rw [hb, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ d)]
  refine ⟨Nat.minFac_eq_two_iff n |>.mpr (even_iff_two_dvd.mp he), ?_, ?_⟩
  · rw [closedPrefactor]
    nlinarith
  · rw [closedPrefactor, hnd]
    nlinarith

theorem odd_exponent {n d : ℕ} (hn : 2 ≤ n) (_hd : 1 ≤ d) (ho : Odd n) :
    (∀ p ∈ n.primeFactors,
        ((n ^ d : ℕ) : ℝ) / (p : ℝ) ≤ ((n ^ d : ℕ) : ℝ) / (n.minFac : ℝ))
      ∧ ((n ^ d : ℕ) : ℝ) / (n.minFac : ℝ) ≤ ((n ^ d : ℕ) : ℝ) / 3
      ∧ ((n ^ d : ℕ) : ℝ) / 3 < ((n ^ d : ℕ) : ℝ) / 2 := by
  have hN : (0 : ℝ) < ((n ^ d : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  have hmf : 0 < n.minFac := Nat.minFac_pos n
  have hmf3 : 3 ≤ n.minFac := by
    have h2 : n.minFac ≠ 2 := by
      intro h
      have := (Nat.minFac_eq_two_iff n).mp h
      exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr this)
    have := (Nat.minFac_prime (by omega : n ≠ 1)).two_le
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have pp := Nat.prime_of_mem_primeFactors hp
    apply div_le_div_of_nonneg_left hN.le (by exact_mod_cast hmf)
    exact_mod_cast Nat.minFac_le_of_dvd pp.two_le (Nat.dvd_of_mem_primeFactors hp)
  · apply div_le_div_of_nonneg_left hN.le (by norm_num)
    exact_mod_cast hmf3
  · exact div_lt_div_of_pos_left hN (by norm_num) (by norm_num)

theorem e22_sharpen {n σ : ℕ} (hn : 4 ≤ n) (hσ : 2 ≤ σ) :
    closedPrefactor n 2 * (σ : ℝ) ^ (((n ^ 2 : ℕ) : ℝ) / 2)
      < 6 * Real.logb 2 n * (σ : ℝ) ^ (((n ^ 2 : ℕ) : ℝ) / 2) := by
  have hX := rpow_half_pos (σ := σ) (N := n ^ 2) (by omega)
  apply mul_lt_mul_of_pos_right _ hX
  rw [closedPrefactor]
  have := two_le_logb_two hn
  norm_num
  linarith

theorem closed_le_e22 {n σ : ℕ} (hn : 2 ≤ n) (hσ : 2 ≤ σ) :
    closedPrefactor n 2 * (σ : ℝ) ^ (((n ^ 2 : ℕ) : ℝ) / 2)
      ≤ 6 * Real.logb 2 n * (σ : ℝ) ^ (((n ^ 2 : ℕ) : ℝ) / 2) := by
  have hX := rpow_half_pos (σ := σ) (N := n ^ 2) (by omega)
  apply mul_le_mul_of_nonneg_right _ hX.le
  rw [closedPrefactor]
  have := one_le_logb_two hn
  norm_num
  linarith

/-! ### Corollary 7.1: decay-rate algebra -/

theorem closedPrefactor_pos {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) : 0 < closedPrefactor n d := by
  rw [closedPrefactor]
  have h1 : (2 : ℝ) ≤ 2 ^ d := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have := one_le_logb_two hn
  linarith

theorem one_le_closedPrefactor {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) : 1 ≤ closedPrefactor n d := by
  rw [closedPrefactor]
  have h1 : (2 : ℝ) ≤ 2 ^ d := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have := one_le_logb_two hn
  linarith

theorem closedPrefactor_le_three_N {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    closedPrefactor n d ≤ 3 * ((n ^ d : ℕ) : ℝ) := by
  rw [closedPrefactor]
  push_cast
  have h1 : (2 : ℝ) ^ d ≤ (n : ℝ) ^ d := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hn) d
  have h2 := logb_le_self (n := n) (by omega)
  have h3 : (n : ℝ) ≤ (n : ℝ) ^ d := by
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ (n : ℝ) ^ d := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ n)) hd
  linarith

/-- For a positive count `S`, `log_σ(1/(S/σ^N)) / N = 1 - log_σ S / N`. -/
theorem rate_eq {S N σ : ℕ} (hS : 0 < S) (hN : 0 < N) (hσ : 2 ≤ σ) :
    Real.logb σ (1 / ((S : ℝ) / (σ : ℝ) ^ N)) / (N : ℝ)
      = 1 - Real.logb σ S / (N : ℝ) := by
  have hσ1 : (1 : ℝ) < σ := by exact_mod_cast hσ
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [one_div_div, Real.logb_div (by positivity) hSpos.ne', Real.logb_pow,
    Real.logb_self_eq_one hσ1]
  field_simp

end ShiftSym.P06
