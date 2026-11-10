/-
Group 11 (Numerics), proof helpers, part 3: the predicted inversion
dimension `d_c(p) = ln(2 − 2/p)/ln(1 + 1/p)` — the tabulated values and the
asymptotics `d_c(p) = p ln 2 + (ln 2/2 − 1) + O(1/p)`.
-/
import Shiftsym.Paper.S11_Numerics

open Real

namespace ShiftSym.P11

open ShiftSym

/-- `a/b ≤ log X / log Y` from `Y^a ≤ X^b` (for `Y > 1`, `X > 0`). -/
theorem le_log_div_log {X Y : ℝ} (hX : 0 < X) (hY : 1 < Y) {a b : ℕ} (hb : 0 < b)
    (h : Y ^ a ≤ X ^ b) : (a : ℝ) / b ≤ log X / log Y := by
  have hlY : 0 < log Y := log_pos hY
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : (a : ℝ) * log Y ≤ b * log X := by
    rw [← log_pow, ← log_pow]
    exact log_le_log (pow_pos (by linarith) _) h
  rw [div_le_div_iff₀ hb' hlY]
  linarith

/-- `log X / log Y ≤ a/b` from `X^b ≤ Y^a` (for `Y > 1`, `X > 0`). -/
theorem log_div_log_le {X Y : ℝ} (hX : 0 < X) (hY : 1 < Y) {a b : ℕ} (hb : 0 < b)
    (h : X ^ b ≤ Y ^ a) : log X / log Y ≤ (a : ℝ) / b := by
  have hlY : 0 < log Y := log_pos hY
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : (b : ℝ) * log X ≤ a * log Y := by
    rw [← log_pow, ← log_pow]
    exact log_le_log (pow_pos hX _) h
  rw [div_le_div_iff₀ hlY hb']
  linarith

theorem dc_three : dc 3 = 1 := by
  unfold dc
  have h : (2 : ℝ) - 2 / ((3 : ℕ) : ℝ) = 1 + 1 / ((3 : ℕ) : ℝ) := by norm_num
  rw [h, div_self]
  exact ne_of_gt (log_pos (by norm_num))

/-- Rational powers comparison from a natural-number certificate. -/
theorem ratpow_le {A B C D a b : ℕ} (hB : 0 < B) (hD : 0 < D) (h : C ^ a * B ^ b ≤ A ^ b * D ^ a) :
    ((C : ℝ) / D) ^ a ≤ ((A : ℝ) / B) ^ b := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_pow, div_pow, div_le_div_iff₀ (pow_pos hD' _) (pow_pos hB' _)]
  exact_mod_cast h

theorem dc_eq_nat {p : ℕ} (hp : 1 ≤ p) :
    dc p = log (((2 * p - 2 : ℕ) : ℝ) / p) / log (((p + 1 : ℕ) : ℝ) / p) := by
  unfold dc
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  congr 2
  · rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
  · push_cast
    field_simp

theorem dc_ge_of {p a b : ℕ} (hp : 2 ≤ p) (hb : 0 < b)
    (h : (p + 1) ^ a * p ^ b ≤ (2 * p - 2) ^ b * p ^ a) : (a : ℝ) / b ≤ dc p := by
  rw [dc_eq_nat (by omega)]
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  apply le_log_div_log _ _ hb (ratpow_le (by omega) (by omega) h)
  · apply div_pos _ hp'
    exact_mod_cast (show 0 < 2 * p - 2 by omega)
  · rw [one_lt_div hp']
    exact_mod_cast (show p < p + 1 by omega)

theorem dc_le_of {p a b : ℕ} (hp : 2 ≤ p) (hb : 0 < b)
    (h : (2 * p - 2) ^ b * p ^ a ≤ (p + 1) ^ a * p ^ b) : dc p ≤ (a : ℝ) / b := by
  rw [dc_eq_nat (by omega)]
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  apply log_div_log_le _ _ hb (ratpow_le (by omega) (by omega) h)
  · apply div_pos _ hp'
    exact_mod_cast (show 0 < 2 * p - 2 by omega)
  · rw [one_lt_div hp']
    exact_mod_cast (show p < p + 1 by omega)

theorem dc5_bounds : (103 : ℝ) / 40 ≤ dc 5 ∧ dc 5 ≤ (517 : ℝ) / 200 := by
  have h1 : ((5 : ℕ) + 1) ^ 103 * (5 : ℕ) ^ 40 ≤ (2 * (5 : ℕ) - 2) ^ 40 * (5 : ℕ) ^ 103 := by
    decide +kernel
  have h2 : (2 * (5 : ℕ) - 2) ^ 200 * (5 : ℕ) ^ 517 ≤ ((5 : ℕ) + 1) ^ 517 * (5 : ℕ) ^ 200 := by
    decide +kernel
  have e1 := dc_ge_of (p := 5) (a := 103) (b := 40) (by norm_num) (by norm_num) h1
  have e2 := dc_le_of (p := 5) (a := 517) (b := 200) (by norm_num) (by norm_num) h2
  push_cast at e1 e2
  exact ⟨e1, e2⟩

theorem dc7_bounds : (807 : ℝ) / 200 ≤ dc 7 ∧ dc 7 ≤ (809 : ℝ) / 200 := by
  have h1 : ((7 : ℕ) + 1) ^ 807 * (7 : ℕ) ^ 200 ≤ (2 * (7 : ℕ) - 2) ^ 200 * (7 : ℕ) ^ 807 := by
    decide +kernel
  have h2 : (2 * (7 : ℕ) - 2) ^ 200 * (7 : ℕ) ^ 809 ≤ ((7 : ℕ) + 1) ^ 809 * (7 : ℕ) ^ 200 := by
    decide +kernel
  have e1 := dc_ge_of (p := 7) (a := 807) (b := 200) (by norm_num) (by norm_num) h1
  have e2 := dc_le_of (p := 7) (a := 809) (b := 200) (by norm_num) (by norm_num) h2
  push_cast at e1 e2
  exact ⟨e1, e2⟩

theorem dc11_bounds : (1373 : ℝ) / 200 ≤ dc 11 ∧ dc 11 ≤ (55 : ℝ) / 8 := by
  have h1 : ((11 : ℕ) + 1) ^ 1373 * (11 : ℕ) ^ 200 ≤ (2 * (11 : ℕ) - 2) ^ 200 * (11 : ℕ) ^ 1373 := by
    decide +kernel
  have h2 : (2 * (11 : ℕ) - 2) ^ 8 * (11 : ℕ) ^ 55 ≤ ((11 : ℕ) + 1) ^ 55 * (11 : ℕ) ^ 8 := by
    decide +kernel
  have e1 := dc_ge_of (p := 11) (a := 1373) (b := 200) (by norm_num) (by norm_num) h1
  have e2 := dc_le_of (p := 11) (a := 55) (b := 8) (by norm_num) (by norm_num) h2
  push_cast at e1 e2
  exact ⟨e1, e2⟩

theorem dc13_bounds : (1653 : ℝ) / 200 ≤ dc 13 ∧ dc 13 ≤ (331 : ℝ) / 40 := by
  have h1 : ((13 : ℕ) + 1) ^ 1653 * (13 : ℕ) ^ 200 ≤ (2 * (13 : ℕ) - 2) ^ 200 * (13 : ℕ) ^ 1653 := by
    decide +kernel
  have h2 : (2 * (13 : ℕ) - 2) ^ 40 * (13 : ℕ) ^ 331 ≤ ((13 : ℕ) + 1) ^ 331 * (13 : ℕ) ^ 40 := by
    decide +kernel
  have e1 := dc_ge_of (p := 13) (a := 1653) (b := 200) (by norm_num) (by norm_num) h1
  have e2 := dc_le_of (p := 13) (a := 331) (b := 40) (by norm_num) (by norm_num) h2
  push_cast at e1 e2
  exact ⟨e1, e2⟩

/-! ### Asymptotics -/

/-- Second-order expansion of `log (1 + x)`. -/
theorem log_one_add_approx {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 3) :
    |log (1 + x) - (x - x ^ 2 / 2)| ≤ 3 / 2 * x ^ 3 := by
  have habs : |(-x)| < 1 := by rw [abs_neg, abs_of_pos hx0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_pos hx0,
    sub_neg_eq_add] at h
  have e1 : (0 : ℝ) + (-x) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + (-x) ^ (1 + 1) / ((1 : ℕ) + 1 : ℝ)
      = -x + x ^ 2 / 2 := by norm_num
  have e2 : log (1 + x) - (x - x ^ 2 / 2)
      = (0 : ℝ) + (-x) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + (-x) ^ (1 + 1) / ((1 : ℕ) + 1 : ℝ)
        + log (1 + x) := by rw [e1]; ring
  rw [e2]
  refine le_trans h ?_
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ x ^ 3 := by positivity
  nlinarith

/-- First-order expansion of `log (1 - x)`. -/
theorem log_one_sub_approx {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 3) :
    |log (1 - x) + x| ≤ 3 / 2 * x ^ 2 := by
  have habs : |x| < 1 := by rw [abs_of_pos hx0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_pos hx0] at h
  have e2 : log (1 - x) + x = (0 : ℝ) + x ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + log (1 - x) := by
    norm_num; ring
  rw [e2]
  refine le_trans h ?_
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ x ^ 2 := by positivity
  nlinarith

/-- `|d_c(p) − p ln 2 − (ln 2/2 − 1)| ≤ 6/p` for every natural `p ≥ 3`. -/
theorem dc_offset_bound {p : ℕ} (hp : 3 ≤ p) :
    |dc p - ((p : ℝ) * log 2 + (log 2 / 2 - 1))| ≤ 6 / p := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  set x : ℝ := 1 / (p : ℝ) with hxdef
  have hx0 : 0 < x := by positivity
  have hx3 : x ≤ 1 / 3 := by
    rw [hxdef, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hpx : (p : ℝ) = 1 / x := by rw [hxdef, one_div_one_div]
  have hL := log_one_add_approx hx0 hx3
  have hM := log_one_sub_approx hx0 hx3
  set L := log (1 + x) with hLdef
  set M := log (1 - x) with hMdef
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hx2 : 0 < x ^ 2 := by positivity
  have hx3' : 0 < x ^ 3 := by positivity
  have hLlo : 2 / 3 * x ≤ L := by
    have := (abs_le.mp hL).1
    nlinarith
  have hLpos : 0 < L := by linarith
  have hdc : dc p = (log 2 + M) / L := by
    unfold dc
    have : (2 : ℝ) - 2 / (p : ℝ) = 2 * (1 - x) := by rw [hxdef]; ring
    rw [this, log_mul (by norm_num) (by linarith), ← hxdef]
  have h6 : (6 : ℝ) / p = 6 * x := by rw [hpx]; field_simp
  rw [hdc, h6, hpx]
  have key : (log 2 + M) / L - (1 / x * log 2 + (log 2 / 2 - 1))
      = (log 2 * (2 * x - 2 * L - x * L) + 2 * x * (M + L)) / (2 * x * L) := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * x * L),
    div_le_iff₀ (by positivity)]
  have hA : |2 * x - 2 * L - x * L| ≤ 4 * x ^ 3 := by
    rw [abs_le] at hL ⊢
    constructor <;> nlinarith
  have hB : |M + L| ≤ 5 / 2 * x ^ 2 := by
    rw [abs_le] at hL hM ⊢
    constructor <;> nlinarith
  have hN : |log 2 * (2 * x - 2 * L - x * L) + 2 * x * (M + L)| ≤ 8 * x ^ 3 := by
    have hl2pos : 0 < log 2 := log_pos (by norm_num)
    calc |log 2 * (2 * x - 2 * L - x * L) + 2 * x * (M + L)|
        ≤ |log 2 * (2 * x - 2 * L - x * L)| + |2 * x * (M + L)| := abs_add_le _ _
      _ = log 2 * |2 * x - 2 * L - x * L| + 2 * x * |M + L| := by
          rw [abs_mul, abs_mul, abs_of_pos hl2pos, abs_of_pos (by positivity : (0:ℝ) < 2 * x)]
      _ ≤ log 2 * (4 * x ^ 3) + 2 * x * (5 / 2 * x ^ 2) := by
          gcongr
      _ ≤ 8 * x ^ 3 := by nlinarith
  calc |log 2 * (2 * x - 2 * L - x * L) + 2 * x * (M + L)| ≤ 8 * x ^ 3 := hN
    _ ≤ 6 * x * (2 * x * L) := by nlinarith

theorem abs_log2_offset : |log 2 / 2 - 1| ≤ 1 := by
  have h1 := Real.log_two_lt_d9
  have h2 := Real.log_two_gt_d9
  rw [abs_le]; constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- `|d_c(p) − p ln 2| ≤ 3` for `p ≥ 3`. -/
theorem dc_offset_le_three {p : ℕ} (hp : 3 ≤ p) : |dc p - (p : ℝ) * log 2| ≤ 3 := by
  have h := dc_offset_bound hp
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h6 : (6 : ℝ) / p ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hc := abs_log2_offset
  calc |dc p - (p : ℝ) * log 2|
      = |(dc p - ((p : ℝ) * log 2 + (log 2 / 2 - 1))) + (log 2 / 2 - 1)| := by ring_nf
    _ ≤ |dc p - ((p : ℝ) * log 2 + (log 2 / 2 - 1))| + |log 2 / 2 - 1| := abs_add_le _ _
    _ ≤ 3 := by linarith

theorem dc_linear_asymptote : IsLinearAsymptotePrimes dc (log 2) (log 2 / 2 - 1) := by
  intro ε hε
  refine ⟨max 3 (⌈6 / ε⌉₊), fun p _ hP => ?_⟩
  have hp3 : 3 ≤ p := le_trans (le_max_left _ _) hP
  have hpc : ⌈6 / ε⌉₊ ≤ p := le_trans (le_max_right _ _) hP
  have hp' : (6 / ε : ℝ) ≤ p := le_trans (Nat.le_ceil _) (by exact_mod_cast hpc)
  have hppos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have h := dc_offset_bound hp3
  have h6 : (6 : ℝ) / p ≤ ε := by
    rw [div_le_iff₀ hppos]
    rw [div_le_iff₀ hε] at hp'
    linarith
  calc |dc p - (log 2 * (p : ℝ) + (log 2 / 2 - 1))|
      = |dc p - ((p : ℝ) * log 2 + (log 2 / 2 - 1))| := by ring_nf
    _ ≤ ε := le_trans h h6

theorem dc_not_asymptote_zero : ¬ IsLinearAsymptotePrimes dc (log 2) 0 := by
  intro h
  obtain ⟨P₀, hP⟩ := h (1 / 10) (by norm_num)
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (max P₀ 100)
  have h1 := hP p hp2 (le_trans (le_max_left _ _) hp1)
  have hp100 : 100 ≤ p := le_trans (le_max_right _ _) hp1
  have hp' : (100 : ℝ) ≤ p := by exact_mod_cast hp100
  have h2 := dc_offset_bound (show 3 ≤ p by omega)
  have h6 : (6 : ℝ) / p ≤ 6 / 100 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp'
  have hl1 := Real.log_two_lt_d9
  have hl2 := Real.log_two_gt_d9
  rw [abs_le] at h1 h2
  norm_num at hl1 hl2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  nlinarith

theorem dc_slope (ε : ℝ) (hε : 0 < ε) : ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p →
    |dc p / (p : ℝ) - log 2| ≤ ε := by
  refine ⟨max 3 (⌈3 / ε⌉₊), fun p _ hP => ?_⟩
  have hp3 : 3 ≤ p := le_trans (le_max_left _ _) hP
  have hpc : ⌈3 / ε⌉₊ ≤ p := le_trans (le_max_right _ _) hP
  have hp' : (3 / ε : ℝ) ≤ p := le_trans (Nat.le_ceil _) (by exact_mod_cast hpc)
  have hppos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have h := dc_offset_le_three hp3
  have e : dc p / (p : ℝ) - log 2 = (dc p - (p : ℝ) * log 2) / p := by
    field_simp
  rw [e, abs_div, abs_of_pos hppos, div_le_iff₀ hppos]
  rw [div_le_iff₀ hε] at hp'
  linarith

end ShiftSym.P11
