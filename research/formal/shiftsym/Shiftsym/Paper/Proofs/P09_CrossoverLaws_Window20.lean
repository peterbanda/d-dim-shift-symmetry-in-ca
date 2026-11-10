/-
Phase H, group 09 (CrossoverLaws), SUPPLEMENT of 2026-10-22 — PROOFS of the
frozen statements in `Shiftsym/Paper/S09_CrossoverLaws_Window20.lean` (the
explicit window constant 20 of Proposition 10.2), written after those
statements passed their fidelity reviews.

The window bounds are the helper theorems `window_i` / `window_ii` of
`P09_CrossoverLaws`; the probability form adds the proved parts (i), (ii).
The non-vacuity facts at the end bracket `d_c` with the certificate lemmas of
`P11_Numerics_Dc`.
-/
import Shiftsym.Paper.S09_CrossoverLaws_Window20
import Shiftsym.Paper.Proofs.P09_CrossoverLaws
import Shiftsym.Paper.Proofs.P11_Numerics_Dc

namespace ShiftSym.P09

theorem inversionExplicitWindow20_proved : inversionExplicitWindow20Statement := by
  intro p σ d _hp hp3 hσ hd
  exact ⟨fun h => window_i hp3 hσ hd h, fun h => window_ii hp3 hσ h⟩

theorem inversionWindow20_proved : inversionWindow20Statement := by
  intro p σ d hp hp3 hσ hd
  exact ⟨fun h => inversionComposite_proved p σ d hp hp3 hσ hd (window_i hp3 hσ hd h),
    fun h => inversionPrime_proved p σ d hp hp3 hσ hd (window_ii hp3 hσ h)⟩

theorem inversionLaw20_proved : inversionLaw20Statement :=
  ⟨inversionLaw_proved, inversionExplicitWindow20_proved, inversionWindow20_proved⟩

/-! ## Non-vacuity of the two branches of the window (not paper claims) -/

/-- Group 11 keeps its own copy `P11.dc` of `d_c` (same formula); it is
literally `dc`, so its certificate lemmas apply here. -/
theorem p11_dc_eq (p : ℕ) : P11.dc p = dc p := rfl

/-- `24 ≤ d_c(37) < 25` (numerically `d_c(37) ≈ 24.964`). -/
theorem dc37_bounds : (24 : ℝ) ≤ dc 37 ∧ dc 37 < 25 := by
  have h1 : ((37 : ℕ) + 1) ^ 24 * (37 : ℕ) ^ 1 ≤ (2 * (37 : ℕ) - 2) ^ 1 * (37 : ℕ) ^ 24 := by
    decide +kernel
  have h2 : (2 * (37 : ℕ) - 2) ^ 100 * (37 : ℕ) ^ 2497 ≤ ((37 : ℕ) + 1) ^ 2497 * (37 : ℕ) ^ 100 := by
    decide +kernel
  have e1 := P11.dc_ge_of (p := 37) (a := 24) (b := 1) (by norm_num) (by norm_num) h1
  have e2 := P11.dc_le_of (p := 37) (a := 2497) (b := 100) (by norm_num) (by norm_num) h2
  rw [p11_dc_eq] at e1 e2
  push_cast at e1 e2
  constructor <;> linarith

/-- `d_c(31) < 21` (numerically `d_c(31) ≈ 20.7995`). -/
theorem dc31_lt : dc 31 < 21 := by
  have h : (2 * (31 : ℕ) - 2) ^ 100 * (31 : ℕ) ^ 2081 ≤ ((31 : ℕ) + 1) ^ 2081 * (31 : ℕ) ^ 100 := by
    decide +kernel
  have e := P11.dc_le_of (p := 31) (a := 2081) (b := 100) (by norm_num) (by norm_num) h
  rw [p11_dc_eq] at e
  push_cast at e
  linarith

/-- Both branches of the window are reached: the lower one at `p = 37` for
exactly `d ∈ {1, …, 4}`, the upper one at `p = 3` from `d = 21` on
(`d_c(3) = 1`). -/
theorem inversionWindow20_nonvacuous :
    (Nat.Prime 37 ∧ ((1 : ℕ) : ℝ) ≤ dc 37 - 20 ∧ ((4 : ℕ) : ℝ) ≤ dc 37 - 20 ∧
        ¬ (((5 : ℕ) : ℝ) ≤ dc 37 - 20)) ∧
      (Nat.Prime 3 ∧ dc 3 + 20 ≤ ((21 : ℕ) : ℝ)) := by
  obtain ⟨h24, h25⟩ := dc37_bounds
  refine ⟨⟨by norm_num, ?_, ?_, ?_⟩, ⟨by norm_num, ?_⟩⟩
  · push_cast; linarith
  · push_cast; linarith
  · intro h; push_cast at h; linarith
  · rw [← p11_dc_eq, P11.dc_three]; norm_num

/-- The lower branch is empty for every prime `p ≤ 31`: there `d_c(p) < 21`,
so no `d ≥ 1` satisfies `d ≤ d_c(p) − 20`. -/
theorem inversionWindow20_lower_empty {p d : ℕ} (hp : p.Prime) (hp31 : p ≤ 31) (hd : 1 ≤ d) :
    ¬ ((d : ℝ) ≤ dc p - 20) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdc : dc p < 21 := by
    rcases Nat.lt_or_ge p 30 with h | h
    · obtain ⟨-, -, hle⟩ := dc_bounds hp.two_le
      have hP : (p : ℝ) + 1 ≤ 30 := by exact_mod_cast (show p + 1 ≤ 30 by omega)
      have hl0 : (0 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hmul := mul_le_mul_of_nonneg_right hP hl0
      have hl := Real.log_two_lt_d9
      linarith
    · have hp' : p = 31 := by
        interval_cases p
        · exact absurd hp (by norm_num)
        · rfl
      subst hp'
      exact dc31_lt
  intro h
  linarith

end ShiftSym.P09
