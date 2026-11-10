/-
Group 11 (Numerics), proof helpers, part 2: the real-number layer.
Positivity of `P^unif`, comparisons of `P^unif` as comparisons of naturals,
the sign / order of `inversionLogRatio`, logarithm bounds from integer power
certificates, and the interpolation algebra.
-/
import Shiftsym.Paper.Proofs.P11_Numerics_Bounds

open Real

namespace ShiftSym.P11

open ShiftSym

theorem numSS_pos {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    0 < numSS n d σ := by
  have hq := Nat.minFac_prime (show n ≠ 1 by omega)
  have h := numSS_ge_fix (σ := σ) hn hd hq (Nat.minFac_dvd n)
  exact lt_of_lt_of_le (pow_pos (by omega) _) h

theorem probUnif_pos {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    0 < probUnif n d σ := by
  unfold probUnif
  have h1 : (0 : ℝ) < numSS n d σ := by exact_mod_cast numSS_pos hn hd hσ
  have h2 : (0 : ℝ) < (σ : ℝ) ^ (n ^ d) := pow_pos (by exact_mod_cast hσ) _
  exact div_pos h1 h2

theorem probUnif_lt_iff {a b d σ : ℕ} (hσ : 1 ≤ σ) :
    probUnif a d σ < probUnif b d σ ↔
      numSS a d σ * σ ^ (b ^ d) < numSS b d σ * σ ^ (a ^ d) := by
  unfold probUnif
  have h0 : (0 : ℝ) < σ := by exact_mod_cast hσ
  rw [div_lt_div_iff₀ (pow_pos h0 _) (pow_pos h0 _)]
  norm_cast

theorem probUnif_le_iff {a b d σ : ℕ} (hσ : 1 ≤ σ) :
    probUnif a d σ ≤ probUnif b d σ ↔
      numSS a d σ * σ ^ (b ^ d) ≤ numSS b d σ * σ ^ (a ^ d) := by
  unfold probUnif
  have h0 : (0 : ℝ) < σ := by exact_mod_cast hσ
  rw [div_le_div_iff₀ (pow_pos h0 _) (pow_pos h0 _)]
  norm_cast

/-! ### `inversionLogRatio` -/

theorem ilr_eq {σ p d : ℕ} (hp : 2 ≤ p) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    inversionLogRatio σ p d
      = (log (probUnif (p + 1) d σ) - log (probUnif p d σ)) / log 10 := by
  unfold inversionLogRatio Real.logb
  rw [log_div (probUnif_pos (by omega) hd hσ).ne' (probUnif_pos hp hd hσ).ne']

theorem ilr_neg_iff {σ p d : ℕ} (hp : 2 ≤ p) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    inversionLogRatio σ p d < 0 ↔ probUnif (p + 1) d σ < probUnif p d σ := by
  unfold inversionLogRatio
  have hc := probUnif_pos (n := p + 1) (by omega) hd hσ
  have hpp := probUnif_pos hp hd hσ
  rw [Real.logb_neg_iff (by norm_num) (div_pos hc hpp), div_lt_one hpp]

theorem ilr_nonneg_iff {σ p d : ℕ} (hp : 2 ≤ p) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    0 ≤ inversionLogRatio σ p d ↔ probUnif p d σ ≤ probUnif (p + 1) d σ := by
  rw [← not_lt, ilr_neg_iff hp hd hσ, not_lt]

theorem ilr_lt_iff {σ p d d' : ℕ} (hp : 2 ≤ p) (hd : 1 ≤ d) (hd' : 1 ≤ d') (hσ : 1 ≤ σ) :
    inversionLogRatio σ p d' < inversionLogRatio σ p d ↔
      probUnif (p + 1) d' σ / probUnif p d' σ < probUnif (p + 1) d σ / probUnif p d σ := by
  unfold inversionLogRatio
  exact Real.logb_lt_logb_iff (by norm_num)
    (div_pos (probUnif_pos (by omega) hd' hσ) (probUnif_pos hp hd' hσ))
    (div_pos (probUnif_pos (by omega) hd hσ) (probUnif_pos hp hd hσ))

/-! ### Logarithm bounds from integer certificates (units of `log 2`) -/

theorem log_nat_lb {S e m u v : ℕ} (hS : m * 2 ^ e ≤ S) (hv : 0 < v) (hc : 2 ^ u ≤ m ^ v) :
    ((e : ℝ) + u / v) * log 2 ≤ log S := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [zero_pow hv.ne'] at hc
      have := Nat.one_le_two_pow (n := u)
      omega
    · exact h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have h1 : (u : ℝ) * log 2 ≤ v * log m := by
    rw [← log_pow, ← log_pow]
    apply log_le_log (by positivity)
    exact_mod_cast hc
  have h2 : log ((m : ℝ) * 2 ^ e) ≤ log S := by
    apply log_le_log (by positivity)
    exact_mod_cast hS
  rw [log_mul hm'.ne' (by positivity), log_pow] at h2
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have h3 : (u : ℝ) / v * log 2 ≤ log m := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hv']
    linarith
  nlinarith

theorem log_nat_ub {S e M u v : ℕ} (hS : S ≤ M * 2 ^ e) (hS0 : 0 < S) (hv : 0 < v)
    (hc : M ^ v ≤ 2 ^ u) : log S ≤ ((e : ℝ) + u / v) * log 2 := by
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hS; omega
    · exact h
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : (v : ℝ) * log M ≤ u * log 2 := by
    rw [← log_pow, ← log_pow]
    apply log_le_log (by positivity)
    exact_mod_cast hc
  have h2 : log (S : ℝ) ≤ log ((M : ℝ) * 2 ^ e) := by
    apply log_le_log (by exact_mod_cast hS0)
    exact_mod_cast hS
  rw [log_mul hM'.ne' (by positivity), log_pow] at h2
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have h3 : log M ≤ (u : ℝ) / v * log 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hv']
    linarith
  nlinarith

theorem log_probUnif_two {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    log (probUnif n d 2) = log (numSS n d 2) - ((n ^ d : ℕ) : ℝ) * log 2 := by
  unfold probUnif
  have h1 : (0 : ℝ) < numSS n d 2 := by exact_mod_cast numSS_pos hn hd (by norm_num)
  rw [log_div h1.ne' (by positivity), log_pow]
  push_cast
  ring

theorem logP_lb {n d e m u v : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hS : m * 2 ^ e ≤ numSS n d 2) (hv : 0 < v) (hc : 2 ^ u ≤ m ^ v) :
    ((e : ℝ) + u / v - ((n ^ d : ℕ) : ℝ)) * log 2 ≤ log (probUnif n d 2) := by
  rw [log_probUnif_two hn hd]
  have := log_nat_lb hS hv hc
  linarith

theorem logP_ub {n d e M u v : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hS : numSS n d 2 ≤ M * 2 ^ e) (hv : 0 < v) (hc : M ^ v ≤ 2 ^ u) :
    log (probUnif n d 2) ≤ ((e : ℝ) + u / v - ((n ^ d : ℕ) : ℝ)) * log 2 := by
  rw [log_probUnif_two hn hd]
  have := log_nat_ub hS (numSS_pos hn hd (by norm_num)) hv hc
  linarith

/-! ### `log₁₀` bounds of ratios of naturals -/

theorem logb10_ten_zpow (a : ℤ) : Real.logb 10 ((10 : ℝ) ^ a) = a := by
  rw [Real.logb, Real.log_zpow, mul_div_assoc,
    div_self (ne_of_gt (log_pos (by norm_num : (1 : ℝ) < 10))), mul_one]

theorem logb10_ge_of {x : ℝ} (hx : 0 < x) {k : ℕ} (hk : 0 < k) {a : ℤ}
    (h : (10 : ℝ) ^ a ≤ x ^ k) : (a : ℝ) / k ≤ Real.logb 10 x := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : Real.logb 10 ((10 : ℝ) ^ a) ≤ Real.logb 10 (x ^ k) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) h
  rw [logb10_ten_zpow, Real.logb_pow] at h1
  rw [div_le_iff₀ hk']
  linarith

theorem logb10_le_of {x : ℝ} (hx : 0 < x) {k : ℕ} (hk : 0 < k) {a : ℤ}
    (h : x ^ k ≤ (10 : ℝ) ^ a) : Real.logb 10 x ≤ (a : ℝ) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : Real.logb 10 (x ^ k) ≤ Real.logb 10 ((10 : ℝ) ^ a) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) h
  rw [logb10_ten_zpow, Real.logb_pow] at h1
  rw [le_div_iff₀ hk']
  linarith

/-- `(10^a ≤ (A/B)^k)` from a natural-number certificate, `a ≥ 0`. -/
theorem ten_pow_le_ratio {A B k a : ℕ} (hB : 0 < B) (h : 10 ^ a * B ^ k ≤ A ^ k) :
    (10 : ℝ) ^ (a : ℤ) ≤ ((A : ℝ) / B) ^ k := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  rw [zpow_natCast, div_pow, le_div_iff₀ (pow_pos hB' _)]
  exact_mod_cast h

/-- `(10^{-a} ≤ (A/B)^k)` from a natural-number certificate. -/
theorem ten_zpow_neg_le_ratio {A B k a : ℕ} (hB : 0 < B) (h : B ^ k ≤ A ^ k * 10 ^ a) :
    (10 : ℝ) ^ (-(a : ℤ)) ≤ ((A : ℝ) / B) ^ k := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have h' : ((B : ℝ)) ^ k ≤ (A : ℝ) ^ k * 10 ^ a := by exact_mod_cast h
  have h10 : (0 : ℝ) < 10 ^ a := by positivity
  rw [zpow_neg, zpow_natCast, div_pow, inv_eq_one_div, div_le_div_iff₀ h10 (pow_pos hB' _)]
  linarith

/-- `((A/B)^k ≤ 10^a)` from a natural-number certificate, `a ≥ 0`. -/
theorem ratio_le_ten_pow {A B k a : ℕ} (hB : 0 < B) (h : A ^ k ≤ 10 ^ a * B ^ k) :
    ((A : ℝ) / B) ^ k ≤ (10 : ℝ) ^ (a : ℤ) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  rw [zpow_natCast, div_pow, div_le_iff₀ (pow_pos hB' _)]
  exact_mod_cast h

/-- `((A/B)^k ≤ 10^{-a})` from a natural-number certificate. -/
theorem ratio_le_ten_zpow_neg {A B k a : ℕ} (hB : 0 < B) (h : A ^ k * 10 ^ a ≤ B ^ k) :
    ((A : ℝ) / B) ^ k ≤ (10 : ℝ) ^ (-(a : ℤ)) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have h' : (A : ℝ) ^ k * 10 ^ a ≤ (B : ℝ) ^ k := by exact_mod_cast h
  have h10 : (0 : ℝ) < 10 ^ a := by positivity
  rw [zpow_neg, zpow_natCast, div_pow, inv_eq_one_div, div_le_div_iff₀ (pow_pos hB' _) h10]
  linarith

/-! ### Interpolation algebra -/

theorem interp_of_signs (f : ℕ → ℝ) (d₀ : ℕ) (hd₀ : 1 ≤ d₀)
    (hpos : ∀ d : ℕ, 1 ≤ d → d ≤ d₀ → 0 ≤ f d) (hneg : f (d₀ + 1) < 0) :
    IsInterpolatedSignChange f ((d₀ : ℝ) + f d₀ / (f d₀ - f (d₀ + 1))) :=
  ⟨d₀, hd₀, hpos, hneg, rfl⟩

/-- Bounds for `a / (a + b)` from bounds of `a, b` in units of `t > 0`. -/
theorem frac_bounds {a b t a1 a2 b1 b2 : ℝ} (ht : 0 < t) (ha1 : a1 * t ≤ a) (ha2 : a ≤ a2 * t)
    (hb1 : b1 * t ≤ b) (hb2 : b ≤ b2 * t) (h0 : 0 ≤ a1) (hb1p : 0 < b1) :
    a1 / (a1 + b2) ≤ a / (a + b) ∧ a / (a + b) ≤ a2 / (a2 + b1) := by
  have ha : 0 ≤ a := le_trans (mul_nonneg h0 ht.le) ha1
  have hb : 0 < b := lt_of_lt_of_le (mul_pos hb1p ht) hb1
  have hb2p : 0 < b2 := by
    by_contra h
    push Not at h
    have : b2 * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h ht.le
    linarith
  have ha2p : 0 ≤ a2 := by
    by_contra h
    push Not at h
    have : a2 * t < 0 := mul_neg_of_neg_of_pos h ht
    linarith
  constructor
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hb2 h0, mul_le_mul_of_nonneg_right ha1 hb2p.le]
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hb1 ha2p, mul_le_mul_of_nonneg_right ha2 hb1p.le]

/-- Scale invariance of the chord zero: `(g/L) d₀ / ((g/L) d₀ − (g/L)(d₀+1)) = g d₀ /(g d₀ − g (d₀+1))`. -/
theorem chord_scale (A B L : ℝ) (hL : L ≠ 0) : (A / L) / (A / L - B / L) = A / (A - B) := by
  by_cases h : A - B = 0
  · have : A / L - B / L = 0 := by rw [← sub_div, h, zero_div]
    rw [h, this, div_zero, div_zero]
  · field_simp

end ShiftSym.P11
