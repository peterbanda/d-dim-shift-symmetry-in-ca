/-
Group 11 (Numerics): proofs of every frozen statement of
`Shiftsym/Paper/S11_Numerics.lean` (Observation 7.3, Remark 10.3 with the
Figure 3 caption, Observation 10.4, Observation 10.5, and the PAPER-ISSUE
evidence / extension Props).

Method. `|S|` is never evaluated by brute force: exact values come from
the certified closed form (`enumeration_proved`, specialised to `rad n = p`,
`rad n = p q` and primes, then evaluated by `decide +kernel` on
GMP-accelerated natural-number arithmetic); all other comparisons use one
fixed set (lower) and the union bound over prime-order subgroups (upper).
Logarithms are bounded through integer power certificates. No
`native_decide`; options used: `maxRecDepth` (for the kernel evaluations).
Helper modules: `P11_Numerics_Bounds`, `_Real`, `_Dc`, `_Deepens`, `_Meas`.
-/
import Shiftsym.Paper.Proofs.P11_Numerics_Meas
import Shiftsym.Paper.Proofs.P11_Numerics_Dc

open Real

namespace ShiftSym.P11

open ShiftSym

/-! ## Generic tools -/

/-- `P^unif_{a^d} < P^unif_{b^d}` (σ = 2) from the union bound for `a` and one
fixed set (order `q`) for `b`, given a natural-number certificate. -/
theorem probUnif_lt_of_bounds {a b d : ℕ} {s : Finset ℕ} {q : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hd : 1 ≤ d) (hs : a.primeFactors = s) (hq : q.Prime) (hqb : q ∣ b)
    (h : (∑ r ∈ s, gaussBinom r d 1 * 2 ^ (a ^ d / r)) * 2 ^ (b ^ d)
      < 2 ^ (b ^ d / q) * 2 ^ (a ^ d)) :
    probUnif a d 2 < probUnif b d 2 := by
  rw [probUnif_lt_iff (by norm_num)]
  have hU := numSS_le_union (n := a) (d := d) (σ := 2) ha
  rw [hs] at hU
  have hL := numSS_ge_fix (σ := 2) hb hd hq hqb
  calc numSS a d 2 * 2 ^ (b ^ d)
      ≤ (∑ r ∈ s, gaussBinom r d 1 * 2 ^ (a ^ d / r)) * 2 ^ (b ^ d) :=
        Nat.mul_le_mul_right _ hU
    _ < 2 ^ (b ^ d / q) * 2 ^ (a ^ d) := h
    _ ≤ numSS b d 2 * 2 ^ (a ^ d) := Nat.mul_le_mul_right _ hL

/-- Once negative, the log-ratio stays negative (Observation 10.5(c)). -/
theorem neg_forever {σ p d₀ : ℕ} (hσ : 2 ≤ σ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (h : inversionLogRatio σ p (d₀ + 1) < 0) :
    ∀ d : ℕ, d₀ < d → inversionLogRatio σ p d < 0 := by
  intro d hd
  induction d, (hd : d₀ + 1 ≤ d) using Nat.le_induction with
  | base => exact h
  | succ k hk ih => exact lt_trans (inversionDeepens_thm σ hσ p hp hp3 k (by omega) ih) ih

/-- The chord zero in terms of `g(d) = log P_{(p+1)^d} − log P_{p^d}`. -/
theorem chord_eq {p d₀ : ℕ} (hp : 2 ≤ p) (hd₀ : 1 ≤ d₀) :
    inversionLogRatio 2 p d₀ / (inversionLogRatio 2 p d₀ - inversionLogRatio 2 p (d₀ + 1))
      = (log (probUnif (p + 1) d₀ 2) - log (probUnif p d₀ 2)) /
        ((log (probUnif (p + 1) d₀ 2) - log (probUnif p d₀ 2))
          + -(log (probUnif (p + 1) (d₀ + 1) 2) - log (probUnif p (d₀ + 1) 2))) := by
  rw [ilr_eq hp hd₀ (by norm_num), ilr_eq hp (by omega) (by norm_num), ← sub_eq_add_neg]
  exact chord_scale _ _ _ (ne_of_gt (log_pos (by norm_num)))

/-- The interpolated sign change of `d ↦ log₁₀[P_{(p+1)^d}/P_{p^d}]` (σ = 2), with
bounds, from the signs and from bounds of `g(d₀)`, `−g(d₀+1)` in units of `log 2`. -/
theorem interp_bounds_of {p d₀ : ℕ} (hp : 2 ≤ p) (hd₀ : 1 ≤ d₀) {a1 a2 b1 b2 : ℝ}
    (h0 : 0 ≤ a1) (hb1 : 0 < b1)
    (hpos : ∀ d : ℕ, 1 ≤ d → d ≤ d₀ → 0 ≤ inversionLogRatio 2 p d)
    (hneg : inversionLogRatio 2 p (d₀ + 1) < 0)
    (ha1 : a1 * log 2 ≤ log (probUnif (p + 1) d₀ 2) - log (probUnif p d₀ 2))
    (ha2 : log (probUnif (p + 1) d₀ 2) - log (probUnif p d₀ 2) ≤ a2 * log 2)
    (hb1' : b1 * log 2 ≤ -(log (probUnif (p + 1) (d₀ + 1) 2) - log (probUnif p (d₀ + 1) 2)))
    (hb2 : -(log (probUnif (p + 1) (d₀ + 1) 2) - log (probUnif p (d₀ + 1) 2)) ≤ b2 * log 2) :
    ∃ x : ℝ, IsInterpolatedSignChange (inversionLogRatio 2 p) x ∧
      (d₀ : ℝ) + a1 / (a1 + b2) ≤ x ∧ x ≤ (d₀ : ℝ) + a2 / (a2 + b1) := by
  refine ⟨_, interp_of_signs _ d₀ hd₀ hpos hneg, ?_⟩
  rw [chord_eq hp hd₀]
  have hf := frac_bounds (log_pos (by norm_num : (1 : ℝ) < 2)) ha1 ha2 hb1' hb2 h0 hb1
  constructor <;> linarith [hf.1, hf.2]

/-- `log₁₀ (A/B)` bounds from natural-number certificates (negative exponents). -/
theorem logb_ratio_neg {A B k a1 a2 : ℕ} (hA : 0 < A) (hB : 0 < B) (hk : 0 < k)
    (h1 : B ^ k ≤ A ^ k * 10 ^ a1) (h2 : A ^ k * 10 ^ a2 ≤ B ^ k) :
    -(a1 : ℝ) / k ≤ Real.logb 10 ((A : ℝ) / B) ∧ Real.logb 10 ((A : ℝ) / B) ≤ -(a2 : ℝ) / k := by
  have hx : (0 : ℝ) < (A : ℝ) / B := div_pos (by exact_mod_cast hA) (by exact_mod_cast hB)
  have e1 := logb10_ge_of hx hk (ten_zpow_neg_le_ratio hB h1)
  have e2 := logb10_le_of hx hk (ratio_le_ten_zpow_neg hB h2)
  push_cast at e1 e2
  exact ⟨e1, e2⟩

/-- `log₁₀ (A/B)` bounds from natural-number certificates (positive exponents). -/
theorem logb_ratio_pos {A B k a1 a2 : ℕ} (hA : 0 < A) (hB : 0 < B) (hk : 0 < k)
    (h1 : 10 ^ a1 * B ^ k ≤ A ^ k) (h2 : A ^ k ≤ 10 ^ a2 * B ^ k) :
    (a1 : ℝ) / k ≤ Real.logb 10 ((A : ℝ) / B) ∧ Real.logb 10 ((A : ℝ) / B) ≤ (a2 : ℝ) / k := by
  have hx : (0 : ℝ) < (A : ℝ) / B := div_pos (by exact_mod_cast hA) (by exact_mod_cast hB)
  have e1 := logb10_ge_of hx hk (ten_pow_le_ratio hB h1)
  have e2 := logb10_le_of hx hk (ratio_le_ten_pow hB h2)
  push_cast at e1 e2
  exact ⟨e1, e2⟩

/-! ## Observation 7.3 (`obs:extrema`) -/

theorem numSS_3_2 : numSS 3 2 2 = 26 :=
  numSS_prime_val Nat.prime_three (by norm_num) (by norm_num) 26 (by decide)

theorem numSS_4_2 : numSS 4 2 2 = 736 := by
  have h := numSS_int 4 2 2 (by norm_num) (by norm_num) (by norm_num)
  rw [enumerationRHS_primePow Nat.prime_two
    (by simp [rad, Nat.primeFactors, Nat.primeFactorsList_ofNat])] at h
  have e : (∑ r ∈ Finset.Icc 1 2, (-1 : ℤ) ^ (r + 1) * (rdCoeff 2 r 2 : ℤ) *
      (((2 ^ (4 ^ 2 / 2 ^ r)) : ℕ) : ℤ)) = 736 := by decide +kernel
  rw [e] at h
  exact_mod_cast h

theorem p5_lt_p6_d2 : probUnif 5 2 2 < probUnif 6 2 2 := by
  rw [probUnif_lt_iff (by norm_num), numSS_5_2, numSS_6_2]
  norm_num

set_option maxRecDepth 100000

theorem extremaD2_proved : extremaD2Statement := by
  unfold extremaD2Statement ExtremalPattern
  refine ⟨?_, ?_⟩
  · intro n hp h5 h40
    interval_cases n
    · exact ⟨(probUnif_lt_of_bounds (a := 5) (b := 4) (d := 2) (s := {5}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        p5_lt_p6_d2⟩
    · exact absurd hp (by norm_num)
    · exact ⟨(probUnif_lt_of_bounds (a := 7) (b := 6) (d := 2) (s := {7}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 7) (b := 8) (d := 2) (s := {7}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨(probUnif_lt_of_bounds (a := 11) (b := 10) (d := 2) (s := {11}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 11) (b := 12) (d := 2) (s := {11}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd hp (by norm_num)
    · exact ⟨(probUnif_lt_of_bounds (a := 13) (b := 12) (d := 2) (s := {13}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 13) (b := 14) (d := 2) (s := {13}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨(probUnif_lt_of_bounds (a := 17) (b := 16) (d := 2) (s := {17}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 17) (b := 18) (d := 2) (s := {17}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd hp (by norm_num)
    · exact ⟨(probUnif_lt_of_bounds (a := 19) (b := 18) (d := 2) (s := {19}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 19) (b := 20) (d := 2) (s := {19}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨(probUnif_lt_of_bounds (a := 23) (b := 22) (d := 2) (s := {23}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 23) (b := 24) (d := 2) (s := {23}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨(probUnif_lt_of_bounds (a := 29) (b := 28) (d := 2) (s := {29}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 29) (b := 30) (d := 2) (s := {29}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd hp (by norm_num)
    · exact ⟨(probUnif_lt_of_bounds (a := 31) (b := 30) (d := 2) (s := {31}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 31) (b := 32) (d := 2) (s := {31}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact ⟨(probUnif_lt_of_bounds (a := 37) (b := 36) (d := 2) (s := {37}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 37) (b := 38) (d := 2) (s := {37}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
  · intro n he h4 h40
    interval_cases n
    · exact absurd he (by decide)
    · exact ⟨p5_lt_p6_d2,
        (probUnif_lt_of_bounds (a := 7) (b := 6) (d := 2) (s := {7}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 7) (b := 8) (d := 2) (s := {7}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 9) (b := 8) (d := 2) (s := {3}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 9) (b := 10) (d := 2) (s := {3}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 11) (b := 10) (d := 2) (s := {11}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 11) (b := 12) (d := 2) (s := {11}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 13) (b := 12) (d := 2) (s := {13}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 13) (b := 14) (d := 2) (s := {13}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 15) (b := 14) (d := 2) (s := {3, 5}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 15) (b := 16) (d := 2) (s := {3, 5}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 17) (b := 16) (d := 2) (s := {17}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 17) (b := 18) (d := 2) (s := {17}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 19) (b := 18) (d := 2) (s := {19}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 19) (b := 20) (d := 2) (s := {19}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 21) (b := 20) (d := 2) (s := {3, 7}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 21) (b := 22) (d := 2) (s := {3, 7}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 23) (b := 22) (d := 2) (s := {23}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 23) (b := 24) (d := 2) (s := {23}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 25) (b := 24) (d := 2) (s := {5}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 25) (b := 26) (d := 2) (s := {5}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 27) (b := 26) (d := 2) (s := {3}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 27) (b := 28) (d := 2) (s := {3}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 29) (b := 28) (d := 2) (s := {29}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 29) (b := 30) (d := 2) (s := {29}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 31) (b := 30) (d := 2) (s := {31}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 31) (b := 32) (d := 2) (s := {31}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 33) (b := 32) (d := 2) (s := {3, 11}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 33) (b := 34) (d := 2) (s := {3, 11}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 35) (b := 34) (d := 2) (s := {5, 7}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 35) (b := 36) (d := 2) (s := {5, 7}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 37) (b := 36) (d := 2) (s := {37}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 37) (b := 38) (d := 2) (s := {37}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 39) (b := 38) (d := 2) (s := {3, 13}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩
    · exact absurd he (by decide)
    · exact ⟨(probUnif_lt_of_bounds (a := 39) (b := 40) (d := 2) (s := {3, 13}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)),
        (probUnif_lt_of_bounds (a := 41) (b := 40) (d := 2) (s := {41}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel))⟩

theorem extremaBoundary_proved : extremaBoundaryStatement := by
  have hP3 : probUnif 3 2 2 = (26 : ℝ) / 2 ^ 9 := by
    unfold probUnif; rw [numSS_3_2]; norm_num
  have hP4 : probUnif 4 2 2 = (736 : ℝ) / 2 ^ 16 := by
    unfold probUnif; rw [numSS_4_2]; norm_num
  have hlt : (736 : ℝ) / 2 ^ 16 < 26 / 2 ^ 9 := by norm_num
  refine ⟨numSS_3_2, numSS_4_2, hP3, hP4, hlt, ?_, ?_⟩
  · intro h
    have h2 : probUnif 3 2 2 < probUnif 4 2 2 := h.2
    rw [hP3, hP4] at h2
    linarith
  · intro h
    have h2 : probUnif 3 2 2 ≤ probUnif 4 2 2 := h.2
    rw [hP3, hP4] at h2
    linarith

theorem probUnif_5_3 : probUnif 5 3 2 = ((1040182682 : ℕ) : ℝ) / ((2 ^ 125 : ℕ) : ℝ) := by
  unfold probUnif; rw [numSS_5_3]; norm_num

theorem probUnif_6_3 : probUnif 6 3 2
    = ((2271629875670377599551565394859176 : ℕ) : ℝ) / ((2 ^ 216 : ℕ) : ℝ) := by
  unfold probUnif; rw [numSS_6_3]; norm_num

theorem logP53_bounds : -(5723 : ℝ) / 200 ≤ Real.logb 10 (probUnif 5 3 2) ∧
    Real.logb 10 (probUnif 5 3 2) ≤ -(5721 : ℝ) / 200 := by
  rw [probUnif_5_3]
  have := logb_ratio_neg (A := 1040182682) (B := 2 ^ 125) (k := 200) (a1 := 5723) (a2 := 5721)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
  push_cast at this ⊢
  exact this

theorem logP63_bounds : -(6335 : ℝ) / 200 ≤ Real.logb 10 (probUnif 6 3 2) ∧
    Real.logb 10 (probUnif 6 3 2) ≤ -(6333 : ℝ) / 200 := by
  rw [probUnif_6_3]
  have := logb_ratio_neg (A := 2271629875670377599551565394859176) (B := 2 ^ 216) (k := 200)
    (a1 := 6335) (a2 := 6333)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
  push_cast at this ⊢
  exact this

theorem extremaD3Values_proved : extremaD3ValuesStatement := by
  obtain ⟨h1, h2⟩ := logP53_bounds
  obtain ⟨h3, h4⟩ := logP63_bounds
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> norm_num <;> linarith
  · rw [abs_le]; constructor <;> norm_num <;> linarith
  · linarith

theorem p6_lt_p5_d3 : probUnif 6 3 2 < probUnif 5 3 2 :=
  probUnif_lt_of_bounds (a := 6) (b := 5) (d := 3) (s := {2, 3}) (q := 5) (by norm_num)
    (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat])
    (by norm_num) (by norm_num) (by decide +kernel)

theorem extremaD3Fail_proved : extremaD3FailStatement := by
  have h := p6_lt_p5_d3
  refine ⟨⟨fun h' => ?_, fun h' => ?_⟩, ⟨fun h' => ?_, fun h' => ?_⟩⟩
  · have : probUnif 5 3 2 < probUnif 6 3 2 := h'.2
    exact lt_asymm h this
  · have : probUnif 5 3 2 ≤ probUnif 6 3 2 := h'.2
    exact absurd h (not_lt.mpr this)
  · have : probUnif 5 3 2 < probUnif 6 3 2 := h'.1
    exact lt_asymm h this
  · have : probUnif 5 3 2 ≤ probUnif 6 3 2 := h'.1
    exact absurd h (not_lt.mpr this)

theorem p10_lt_p9_d3 : probUnif 10 3 2 < probUnif 9 3 2 :=
  probUnif_lt_of_bounds (a := 10) (b := 9) (d := 3) (s := {2, 5}) (q := 3) (by norm_num)
    (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat])
    (by norm_num) (by norm_num) (by decide +kernel)

theorem extremaN10_proved : extremaN10Statement := by
  have h := p10_lt_p9_d3
  refine ⟨fun h' => ?_, fun h' => ?_⟩
  · have : probUnif 9 3 2 < probUnif 10 3 2 := h'.1
    exact lt_asymm h this
  · have : probUnif 9 3 2 ≤ probUnif 10 3 2 := h'.1
    exact absurd h (not_lt.mpr this)

theorem p6_lt_p5_d4 : probUnif 6 4 2 < probUnif 5 4 2 :=
  probUnif_lt_of_bounds (a := 6) (b := 5) (d := 4) (s := {2, 3}) (q := 5) (by norm_num)
    (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat])
    (by norm_num) (by norm_num) (by decide +kernel)

theorem p10_lt_p9_d4 : probUnif 10 4 2 < probUnif 9 4 2 :=
  probUnif_lt_of_bounds (a := 10) (b := 9) (d := 4) (s := {2, 5}) (q := 3) (by norm_num)
    (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat])
    (by norm_num) (by norm_num) (by decide +kernel)

theorem extremaD4_proved : extremaD4Statement := by
  have h := p6_lt_p5_d4
  have h' := p10_lt_p9_d4
  refine ⟨⟨fun g => ?_, fun g => ?_⟩, ⟨fun g => ?_, fun g => ?_⟩, ⟨fun g => ?_, fun g => ?_⟩⟩
  · exact lt_asymm h (g.2 : probUnif 5 4 2 < probUnif 6 4 2)
  · exact absurd h (not_lt.mpr (g.2 : probUnif 5 4 2 ≤ probUnif 6 4 2))
  · exact lt_asymm h (g.1 : probUnif 5 4 2 < probUnif 6 4 2)
  · exact absurd h (not_lt.mpr (g.1 : probUnif 5 4 2 ≤ probUnif 6 4 2))
  · exact lt_asymm h' (g.1 : probUnif 9 4 2 < probUnif 10 4 2)
  · exact absurd h' (not_lt.mpr (g.1 : probUnif 9 4 2 ≤ probUnif 10 4 2))

/-- `P(6^d) < P(5^d)` for every `d ≥ 3` (σ = 2). -/
theorem p6_lt_p5_all {d : ℕ} (hd : 3 ≤ d) : probUnif 6 d 2 < probUnif 5 d 2 := by
  have h := neg_forever (σ := 2) (p := 5) (d₀ := 2) le_rfl (by norm_num) (by norm_num)
    meas_5.2.1 d (by omega)
  exact (ilr_neg_iff (by norm_num) (by omega) (by norm_num)).mp h

theorem extremaBreaks_proved : extremaBreaksStatement := by
  intro d hd
  have h := p6_lt_p5_all hd
  refine ⟨fun g => ?_, fun g => ?_⟩
  · exact lt_asymm h ((g.1 5 (by norm_num) le_rfl (by norm_num)).2 :
      probUnif 5 d 2 < probUnif 6 d 2)
  · exact absurd h (not_lt.mpr ((g.1 5 (by norm_num) le_rfl (by norm_num)).2 :
      probUnif 5 d 2 ≤ probUnif 6 d 2))

theorem obsExtrema_proved : obsExtremaStatement :=
  ⟨extremaD2_proved, extremaBoundary_proved, extremaD3Values_proved, extremaD3Fail_proved,
    extremaN10_proved, extremaD4_proved, extremaBreaks_proved⟩

/-! ## Remark 10.3 (`rem:dc-measured`) and the Figure 3 caption -/

theorem dcRow_proved : dcRowStatement := by
  have h5 := dc5_bounds
  have h7 := dc7_bounds
  have h11 := dc11_bounds
  have h13 := dc13_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [dc_three]; norm_num
  all_goals
    rw [abs_le]
    constructor <;> norm_num <;>
      linarith [h5.1, h5.2, h7.1, h7.2, h11.1, h11.2, h13.1, h13.2]

/-! ### The boundary case `p = 3` (exact for every alphabet) -/

theorem numSS_3_1 (σ : ℕ) (_hσ : 1 ≤ σ) : numSS 3 1 σ = σ := by
  have h1 := numSS_prime_le (σ := σ) Nat.prime_three (le_refl 1)
  have h2 := numSS_prime_ge (σ := σ) Nat.prime_three (le_refl 1)
  simp only [gaussBinom_one_one, Nat.sub_self, pow_zero, pow_one, one_mul] at h1 h2
  omega

theorem numSS_4_1 (σ : ℕ) (hσ : 1 ≤ σ) : numSS 4 1 σ = σ ^ 2 := by
  have h1 := numSS_four_le 1 σ hσ
  have h2 := numSS_four_ge 1 σ le_rfl
  simp only [gaussBinom_one_one, pow_one, one_mul] at h1 h2
  norm_num at h1 h2
  exact le_antisymm h1 h2

theorem probUnif_3_1 (σ : ℕ) (hσ : 2 ≤ σ) : probUnif 3 1 σ = ((σ : ℝ) ^ 2)⁻¹ := by
  unfold probUnif
  rw [numSS_3_1 σ (by omega)]
  have hs : (σ : ℝ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by omega)
  field_simp
  norm_num

theorem probUnif_4_1 (σ : ℕ) (hσ : 2 ≤ σ) : probUnif 4 1 σ = ((σ : ℝ) ^ 2)⁻¹ := by
  unfold probUnif
  rw [numSS_4_1 σ (by omega)]
  have hs : (σ : ℝ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by omega)
  push_cast
  field_simp

theorem ilr3_one (σ : ℕ) (hσ : 2 ≤ σ) : inversionLogRatio σ 3 1 = 0 := by
  unfold inversionLogRatio
  rw [show (3 + 1 : ℕ) = 4 from rfl, probUnif_3_1 σ hσ, probUnif_4_1 σ hσ, div_self]
  · exact Real.logb_one
  · have hs : (0 : ℝ) < σ := by exact_mod_cast (show 0 < σ by omega)
    positivity

theorem ilr3_two_neg (σ : ℕ) (hσ : 2 ≤ σ) : inversionLogRatio σ 3 2 < 0 := by
  rw [ilr_neg_iff (by norm_num) (by norm_num) (by omega), probUnif_lt_iff (by omega)]
  have hU := numSS_four_le 2 σ (by omega)
  have hL := numSS_prime_ge (σ := σ) Nat.prime_three (by norm_num : 1 ≤ 2)
  norm_num [gaussBinom] at hU hL
  have hσ2 : 3 < σ ^ 2 := by nlinarith
  have hpos : 0 < σ ^ 17 := pow_pos (by omega) _
  calc numSS (3 + 1) 2 σ * σ ^ (3 ^ 2) ≤ 3 * σ ^ 8 * σ ^ (3 ^ 2) := Nat.mul_le_mul_right _ hU
    _ = 3 * σ ^ 17 := by ring
    _ < σ ^ 2 * σ ^ 17 := Nat.mul_lt_mul_of_pos_right hσ2 hpos
    _ = σ ^ 3 * σ ^ 16 := by ring
    _ ≤ numSS 3 2 σ * σ ^ ((3 + 1) ^ 2) := by norm_num; exact Nat.mul_le_mul_right _ hL

theorem interp3 (σ : ℕ) (hσ : 2 ≤ σ) : IsInterpolatedSignChange (inversionLogRatio σ 3) 1 := by
  refine ⟨1, le_rfl, ?_, ilr3_two_neg σ hσ, ?_⟩
  · intro d h1 h2
    obtain rfl : d = 1 := by omega
    rw [ilr3_one σ hσ]
  · rw [ilr3_one σ hσ]
    norm_num

theorem boundaryCase_proved : boundaryCaseStatement :=
  ⟨fun σ hσ => ⟨numSS_3_1 σ hσ, numSS_4_1 σ hσ⟩,
    fun σ hσ => ⟨probUnif_3_1 σ hσ, probUnif_4_1 σ hσ, ilr3_one σ hσ⟩, dc_three,
    fun σ hσ => interp3 σ hσ⟩

/-! ### The measured inversion points -/

theorem xb5 : ∃ x : ℝ, IsInterpolatedSignChange (inversionLogRatio 2 5) x ∧
    (2098 : ℝ) / 1000 ≤ x ∧ x ≤ (20982 : ℝ) / 10000 := by
  obtain ⟨hpos, hneg, ha1, ha2, hb1, hb2⟩ := meas_5
  obtain ⟨x, hx, hlo, hhi⟩ := interp_bounds_of (p := 5) (d₀ := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hpos hneg ha1 ha2 hb1 hb2
  refine ⟨x, hx, ?_, ?_⟩ <;> norm_num at hlo hhi ⊢ <;> linarith

theorem xb7 : ∃ x : ℝ, IsInterpolatedSignChange (inversionLogRatio 2 7) x ∧
    (40005 : ℝ) / 10000 ≤ x ∧ x ≤ (400302 : ℝ) / 100000 := by
  obtain ⟨hpos, hneg, ha1, ha2, hb1, hb2⟩ := meas_7
  obtain ⟨x, hx, hlo, hhi⟩ := interp_bounds_of (p := 7) (d₀ := 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hpos hneg ha1 ha2 hb1 hb2
  refine ⟨x, hx, ?_, ?_⟩ <;> norm_num at hlo hhi ⊢ <;> linarith

theorem xb11 : ∃ x : ℝ, IsInterpolatedSignChange (inversionLogRatio 2 11) x ∧
    (636971 : ℝ) / 100000 ≤ x ∧ x ≤ (6369736 : ℝ) / 1000000 := by
  obtain ⟨hpos, hneg, ha1, ha2, hb1, hb2⟩ := meas_11
  obtain ⟨x, hx, hlo, hhi⟩ := interp_bounds_of (p := 11) (d₀ := 6) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hpos hneg ha1 ha2 hb1 hb2
  refine ⟨x, hx, ?_, ?_⟩ <;> norm_num at hlo hhi ⊢ <;> linarith

theorem xb13 : ∃ x : ℝ, IsInterpolatedSignChange (inversionLogRatio 2 13) x ∧
    (8027095 : ℝ) / 1000000 ≤ x ∧ x ≤ (802709503 : ℝ) / 100000000 := by
  obtain ⟨hpos, hneg, ha1, ha2, hb1, hb2⟩ := meas_13
  obtain ⟨x, hx, hlo, hhi⟩ := interp_bounds_of (p := 13) (d₀ := 8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hpos hneg ha1 ha2 hb1 hb2
  refine ⟨x, hx, ?_, ?_⟩ <;> norm_num at hlo hhi ⊢ <;> linarith

theorem measuredRow_proved : measuredRowStatement := by
  refine ⟨⟨1, interp3 2 le_rfl, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx, h1, h2⟩ := xb5
    exact ⟨x, hx, by rw [abs_le]; constructor <;> norm_num <;> linarith⟩
  · obtain ⟨x, hx, h1, h2⟩ := xb7
    exact ⟨x, hx, by rw [abs_le]; constructor <;> norm_num <;> linarith⟩
  · obtain ⟨x, hx, h1, h2⟩ := xb11
    exact ⟨x, hx, by rw [abs_le]; constructor <;> norm_num <;> linarith⟩
  · obtain ⟨x, hx, h1, h2⟩ := xb13
    exact ⟨x, hx, by rw [abs_le]; constructor <;> norm_num <;> linarith⟩

theorem measuredAtOrBelow_proved : measuredAtOrBelowStatement := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, interp3 2 le_rfl, by rw [dc_three]⟩
  · obtain ⟨x, hx, h1, h2⟩ := xb5
    exact ⟨x, hx, by linarith [dc5_bounds.1]⟩
  · obtain ⟨x, hx, h1, h2⟩ := xb7
    exact ⟨x, hx, by linarith [dc7_bounds.1]⟩
  · obtain ⟨x, hx, h1, h2⟩ := xb11
    exact ⟨x, hx, by linarith [dc11_bounds.1]⟩
  · obtain ⟨x, hx, h1, h2⟩ := xb13
    exact ⟨x, hx, by linarith [dc13_bounds.1]⟩

/-! ### The bare exponent `φ` (no coefficients) -/

theorem yb3 : IsInterpolatedSignChange (phiInv 3) 1 := by
  refine ⟨1, le_rfl, ?_, ?_, ?_⟩
  · intro d h1 h2
    obtain rfl : d = 1 := by omega
    norm_num [phiInv]
  · norm_num [phiInv]
  · norm_num [phiInv]

theorem yb5 : IsInterpolatedSignChange (phiInv 5) (11 / 5) := by
  refine ⟨2, by norm_num, ?_, ?_, ?_⟩
  · intro d h1 h2
    interval_cases d <;> norm_num [phiInv]
  · norm_num [phiInv]
  · norm_num [phiInv]

theorem yb7 : IsInterpolatedSignChange (phiInv 7) (3981 / 994) := by
  refine ⟨4, by norm_num, ?_, ?_, ?_⟩
  · intro d h1 h2
    interval_cases d <;> norm_num [phiInv]
  · norm_num [phiInv]
  · norm_num [phiInv]

theorem yb11 : IsInterpolatedSignChange (phiInv 11) (6 + 117518 / 317812) := by
  refine ⟨6, by norm_num, ?_, ?_, ?_⟩
  · intro d h1 h2
    interval_cases d <;> norm_num [phiInv]
  · norm_num [phiInv]
  · norm_num [phiInv]

theorem yb13 : IsInterpolatedSignChange (phiInv 13) (8 + 15087676 / 556842416) := by
  refine ⟨8, by norm_num, ?_, ?_, ?_⟩
  · intro d h1 h2
    interval_cases d <;> norm_num [phiInv]
  · norm_num [phiInv]
  · norm_num [phiInv]

theorem coefficientsFavorPrime_proved : coefficientsFavorPrimeStatement := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 1, interp3 2 le_rfl, yb3, le_rfl, fun h => absurd h (by norm_num)⟩
  · obtain ⟨x, hx, h1, h2⟩ := xb5
    have hlt : x < 11 / 5 := by linarith
    exact ⟨x, _, hx, yb5, hlt.le, fun _ => hlt⟩
  · obtain ⟨x, hx, h1, h2⟩ := xb7
    have hlt : x < 3981 / 994 := by linarith
    exact ⟨x, _, hx, yb7, hlt.le, fun _ => hlt⟩
  · obtain ⟨x, hx, h1, h2⟩ := xb11
    have hlt : x < 6 + 117518 / 317812 := by linarith
    exact ⟨x, _, hx, yb11, hlt.le, fun _ => hlt⟩
  · obtain ⟨x, hx, h1, h2⟩ := xb13
    have hlt : x < 8 + 15087676 / 556842416 := by linarith
    exact ⟨x, _, hx, yb13, hlt.le, fun _ => hlt⟩

/-! ### Figure 3 caption -/

theorem fig15SignFlip_proved : fig15SignFlipStatement := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · refine ⟨1, le_rfl, ?_, neg_forever le_rfl Nat.prime_three le_rfl (ilr3_two_neg 2 le_rfl)⟩
    intro d h1 h2
    obtain rfl : d = 1 := by omega
    rw [ilr3_one 2 le_rfl]
  · exact ⟨2, by norm_num, meas_5.1, neg_forever le_rfl (by norm_num) (by norm_num) meas_5.2.1⟩
  · exact ⟨4, by norm_num, meas_7.1, neg_forever le_rfl (by norm_num) (by norm_num) meas_7.2.1⟩
  · exact ⟨6, by norm_num, meas_11.1,
      neg_forever le_rfl (by norm_num) (by norm_num) meas_11.2.1⟩
  · exact ⟨8, by norm_num, meas_13.1,
      neg_forever le_rfl (by norm_num) (by norm_num) meas_13.2.1⟩

theorem figInversionAsymptote_proved : figInversionAsymptoteStatement :=
  ⟨fun ε hε => dc_slope ε hε, ⟨3, 3, fun _ _ h3 => dc_offset_le_three h3⟩⟩

theorem remDcMeasured_proved : remDcMeasuredStatement :=
  ⟨dcRow_proved, measuredRow_proved, measuredAtOrBelow_proved, coefficientsFavorPrime_proved,
    boundaryCase_proved, fig15SignFlip_proved, figInversionAsymptote_proved⟩

theorem dcOffsetLimit_proved : dcOffsetLimitStatement :=
  ⟨dc_linear_asymptote, dc_not_asymptote_zero⟩

theorem floor_eq_of {r : ℝ} {z : ℤ} (h1 : (z : ℝ) ≤ r) (h2 : r < z + 1) : ⌊r⌋ = z :=
  Int.floor_eq_iff.mpr ⟨h1, h2⟩

theorem measuredGapCause_proved : measuredGapCauseStatement := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · obtain ⟨x, hx, h1, h2⟩ := xb5
    obtain ⟨d1, d2⟩ := dc5_bounds
    have fdc : ⌊dc 5⌋ = 2 := floor_eq_of (by push_cast; linarith) (by push_cast; linarith)
    refine ⟨x, _, hx, yb5, ?_, ?_, ?_, ?_, fun h => absurd h (by norm_num)⟩
    · rw [fdc]; exact floor_eq_of (by push_cast; linarith) (by push_cast; linarith)
    · rw [fdc]; exact floor_eq_of (by norm_num) (by norm_num)
    · linarith
    · linarith
  · obtain ⟨x, hx, h1, h2⟩ := xb7
    obtain ⟨d1, d2⟩ := dc7_bounds
    have fdc : ⌊dc 7⌋ = 4 := floor_eq_of (by push_cast; linarith) (by push_cast; linarith)
    refine ⟨x, _, hx, yb7, ?_, ?_, ?_, ?_, fun h => absurd h (by norm_num)⟩
    · rw [fdc]; exact floor_eq_of (by push_cast; linarith) (by push_cast; linarith)
    · rw [fdc]; exact floor_eq_of (by norm_num) (by norm_num)
    · linarith
    · linarith
  · obtain ⟨x, hx, h1, h2⟩ := xb11
    obtain ⟨d1, d2⟩ := dc11_bounds
    have fdc : ⌊dc 11⌋ = 6 := floor_eq_of (by push_cast; linarith) (by push_cast; linarith)
    refine ⟨x, _, hx, yb11, ?_, ?_, ?_, ?_, fun _ => by linarith⟩
    · rw [fdc]; exact floor_eq_of (by push_cast; linarith) (by push_cast; linarith)
    · rw [fdc]; exact floor_eq_of (by norm_num) (by norm_num)
    · linarith
    · linarith
  · obtain ⟨x, hx, h1, h2⟩ := xb13
    obtain ⟨d1, d2⟩ := dc13_bounds
    have fdc : ⌊dc 13⌋ = 8 := floor_eq_of (by push_cast; linarith) (by push_cast; linarith)
    refine ⟨x, _, hx, yb13, ?_, ?_, ?_, ?_, fun _ => by linarith⟩
    · rw [fdc]; exact floor_eq_of (by push_cast; linarith) (by push_cast; linarith)
    · rw [fdc]; exact floor_eq_of (by norm_num) (by norm_num)
    · linarith
    · linarith

/-! ## Observation 10.4 (`obs:dstar`) -/

theorem primeTerm_two (p d σ : ℕ) :
    primeTerm p d σ 2 = -((p : ℝ) * gaussBinom p d 2 * (σ : ℝ) ^ (p ^ (d - 2))) := by
  simp [primeTerm]
  ring

theorem primeTerm_one (p d σ : ℕ) :
    primeTerm p d σ 1 = (gaussBinom p d 1 : ℝ) * (σ : ℝ) ^ (p ^ (d - 1)) := by
  simp [primeTerm]

theorem t2t1_formula {p d σ : ℕ} (hp : p.Prime) (hd : 2 ≤ d) (hσ : 2 ≤ σ) :
    t2t1 p d σ = (p : ℝ) * (gaussBinom p d 2 : ℝ) / (gaussBinom p d 1 : ℝ) *
      (σ : ℝ) ^ (-((p ^ (d - 2) * (p - 1) : ℕ) : ℤ)) := by
  have hG : (0 : ℝ) < gaussBinom p d 1 := by
    exact_mod_cast gaussBinom_one_pos hp.two_le (by omega)
  have hs : (0 : ℝ) < σ := by exact_mod_cast (show 0 < σ by omega)
  have hexp : p ^ (d - 1) = p ^ (d - 2) + p ^ (d - 2) * (p - 1) := by
    have h1 : p ^ (d - 1) = p ^ (d - 2) * p := by rw [← pow_succ]; congr 1; omega
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    rw [h1]; simp only [Nat.add_sub_cancel]; ring
  unfold t2t1
  rw [primeTerm_two, primeTerm_one, neg_div, abs_neg, abs_of_nonneg (by positivity), hexp,
    pow_add, zpow_neg, zpow_natCast]
  field_simp

theorem t2t1Formula_proved : t2t1FormulaStatement :=
  fun _ _ _ hp hd hσ => t2t1_formula hp hd hσ

theorem gaussBinom_two_two (q : ℕ) : gaussBinom q 2 2 = 1 := by simp [gaussBinom]

theorem gaussBinom_one_two (q : ℕ) : gaussBinom q 1 2 = 0 := by simp [gaussBinom]

/-- `|T₂/T₁|` at `d = 2`, `σ = 2`: `p/(p+1) · 2^{-(p-1)}`, bounded by `2^{-(p-1)}`. -/
theorem t2t1_d2_le {p : ℕ} (hp : p.Prime) : t2t1 p 2 2 ≤ ((2 : ℝ) ^ (p - 1))⁻¹ := by
  rw [t2t1_formula hp le_rfl le_rfl, gaussBinom_two_two, gaussBinom_two_one]
  simp only [Nat.sub_self, pow_zero, one_mul, zpow_neg, zpow_natCast, Nat.cast_one, mul_one]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h1 : (p : ℝ) / ((p + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; push_cast; linarith
  have h2 : (0 : ℝ) < ((2 : ℝ) ^ (p - 1))⁻¹ := by positivity
  push_cast at h1 ⊢
  nlinarith

theorem t2t1_d2_lt_of {p : ℕ} (hp : p.Prime) {θ : ℝ} {k : ℕ} (hk : k ≤ p - 1)
    (hθ : ((2 : ℝ) ^ k)⁻¹ < θ) : t2t1 p 2 2 < θ := by
  refine lt_of_le_of_lt (t2t1_d2_le hp) (lt_of_le_of_lt ?_ hθ)
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) hk

theorem isLeast_two {p : ℕ} {θ : ℝ} (h : t2t1 p 2 2 < θ) : IsLeast (dStarSet p θ 2) 2 :=
  ⟨⟨le_rfl, h⟩, fun _ hd => hd.1⟩

theorem not_unclamped {p : ℕ} {θ : ℝ} (h : t2t1 p 2 2 < θ) : p ∉ unclampedPrimes θ := by
  rintro ⟨-, -, D, hD, h2⟩
  have := hD.unique (isLeast_two h)
  omega

/-- `IsLeast` of `dStarSet` at an explicit `D > 2`, from the values below `D`. -/
theorem isLeast_of {p D : ℕ} {θ : ℝ} (hD : 2 ≤ D) (hlt : t2t1 p D 2 < θ)
    (hge : ∀ d : ℕ, 2 ≤ d → d < D → θ ≤ t2t1 p d 2) : IsLeast (dStarSet p θ 2) D := by
  refine ⟨⟨hD, hlt⟩, fun d hd => ?_⟩
  by_contra h
  push Not at h
  exact absurd hd.2 (not_lt.mpr (hge d hd.1 h))

theorem tv22 : t2t1 2 2 2 = 1 / 3 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
theorem tv23 : t2t1 2 3 2 = 1 / 2 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
theorem tv24 : t2t1 2 4 2 = 7 / 24 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
theorem tv25 : t2t1 2 5 2 = 5 / 128 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
theorem tv26 : t2t1 2 6 2 = 31 / 98304 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
theorem tv32 : t2t1 3 2 2 = 3 / 16 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
theorem tv33 : t2t1 3 3 2 = 3 / 64 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
theorem tv34 : t2t1 3 4 2 < 1 / 100 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
theorem tv52 : t2t1 5 2 2 = 5 / 96 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
theorem tv53 : t2t1 5 3 2 < 1 / 100 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
theorem tv72 : t2t1 7 2 2 = 7 / 512 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
theorem tv73 : t2t1 7 3 2 < 1 / 100 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]

theorem dstarAllPrimes_proved : dstarAllPrimesStatement := by
  intro p hp
  by_cases h2 : p = 2
  · subst h2
    refine ⟨5, isLeast_of (by norm_num) (by rw [tv25]; norm_num) ?_, by norm_num⟩
    intro d hd1 hd2
    interval_cases d
    · rw [tv22]; norm_num
    · rw [tv23]; norm_num
    · rw [tv24]; norm_num
  by_cases h3 : p = 3
  · subst h3
    refine ⟨3, isLeast_of (by norm_num) (by rw [tv33]; norm_num) ?_, by norm_num⟩
    intro d hd1 hd2
    interval_cases d
    rw [tv32]; norm_num
  by_cases h5 : p = 5
  · subst h5
    refine ⟨3, isLeast_of (by norm_num) (by linarith [tv53]) ?_, by norm_num⟩
    intro d hd1 hd2
    interval_cases d
    rw [tv52]; norm_num
  have hp7 : 7 ≤ p := by
    have := hp.two_le
    by_contra h
    push Not at h
    interval_cases p <;> simp_all <;> exact absurd hp (by norm_num)
  refine ⟨2, isLeast_two (t2t1_d2_lt_of hp (k := 6) (by omega) (by norm_num)), ?_⟩
  constructor
  · intro h; omega
  · rintro (h | h | h) <;> omega

theorem primes_le_499 : ((Finset.Iic 499).filter Nat.Prime).card = 95 := by decide +kernel

theorem dstarClaim_proved : dstarClaimStatement :=
  ⟨primes_le_499, fun p hp _ => dstarAllPrimes_proved p hp⟩

theorem unclamped_005 : unclampedPrimes 0.05 = {2, 3, 5} := by
  ext p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hp
    have hpp : p.Prime := hp.1
    by_contra h
    push Not at h
    obtain ⟨h2, h3, h5⟩ := h
    have hp7 : 7 ≤ p := by
      have := hpp.two_le
      by_contra h'
      push Not at h'
      interval_cases p <;> simp_all <;> exact absurd hpp (by norm_num)
    exact not_unclamped (t2t1_d2_lt_of hpp (k := 6) (by omega) (by norm_num)) hp
  · rintro (rfl | rfl | rfl)
    · obtain ⟨D, hD, h⟩ := dstarAllPrimes_proved 2 Nat.prime_two
      exact ⟨Nat.prime_two, by norm_num, D, hD, h.mpr (Or.inl rfl)⟩
    · obtain ⟨D, hD, h⟩ := dstarAllPrimes_proved 3 Nat.prime_three
      exact ⟨Nat.prime_three, by norm_num, D, hD, h.mpr (Or.inr (Or.inl rfl))⟩
    · obtain ⟨D, hD, h⟩ := dstarAllPrimes_proved 5 (by norm_num)
      exact ⟨by norm_num, by norm_num, D, hD, h.mpr (Or.inr (Or.inr rfl))⟩

theorem unclamped_001 : unclampedPrimes 0.01 = {2, 3, 5, 7} := by
  ext p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hp
    have hpp : p.Prime := hp.1
    by_contra h
    push Not at h
    obtain ⟨h2, h3, h5, h7⟩ := h
    have hp11 : 11 ≤ p := by
      have := hpp.two_le
      by_contra h'
      push Not at h'
      interval_cases p <;> simp_all <;> exact absurd hpp (by norm_num)
    exact not_unclamped (t2t1_d2_lt_of hpp (k := 10) (by omega) (by norm_num)) hp
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨Nat.prime_two, by norm_num, 6, isLeast_of (by norm_num) (by rw [tv26]; norm_num) ?_,
        by norm_num⟩
      intro d hd1 hd2
      interval_cases d
      · rw [tv22]; norm_num
      · rw [tv23]; norm_num
      · rw [tv24]; norm_num
      · rw [tv25]; norm_num
    · refine ⟨Nat.prime_three, by norm_num, 4, isLeast_of (by norm_num) (by linarith [tv34]) ?_,
        by norm_num⟩
      intro d hd1 hd2
      interval_cases d
      · rw [tv32]; norm_num
      · rw [tv33]; norm_num
    · refine ⟨by norm_num, by norm_num, 3, isLeast_of (by norm_num) (by linarith [tv53]) ?_,
        by norm_num⟩
      intro d hd1 hd2
      interval_cases d
      rw [tv52]; norm_num
    · refine ⟨by norm_num, by norm_num, 3, isLeast_of (by norm_num) (by linarith [tv73]) ?_,
        by norm_num⟩
      intro d hd1 hd2
      interval_cases d
      rw [tv72]; norm_num

theorem unclamped_01 : unclampedPrimes 0.1 = {2, 3} := by
  ext p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hp
    have hpp : p.Prime := hp.1
    by_contra h
    push Not at h
    obtain ⟨h2, h3⟩ := h
    by_cases h5 : p = 5
    · subst h5
      exact not_unclamped (by rw [tv52]; norm_num) hp
    have hp7 : 7 ≤ p := by
      have := hpp.two_le
      by_contra h'
      push Not at h'
      interval_cases p <;> simp_all <;> exact absurd hpp (by norm_num)
    exact not_unclamped (t2t1_d2_lt_of hpp (k := 6) (by omega) (by norm_num)) hp
  · rintro (rfl | rfl)
    · refine ⟨Nat.prime_two, by norm_num, 5, isLeast_of (by norm_num) (by rw [tv25]; norm_num) ?_,
        by norm_num⟩
      intro d hd1 hd2
      interval_cases d
      · rw [tv22]; norm_num
      · rw [tv23]; norm_num
      · rw [tv24]; norm_num
    · refine ⟨Nat.prime_three, by norm_num, 3, isLeast_of (by norm_num) (by rw [tv33]; norm_num) ?_,
        by norm_num⟩
      intro d hd1 hd2
      interval_cases d
      rw [tv32]; norm_num

theorem dstarUnclampedByTheta_proved : dstarUnclampedByThetaStatement :=
  ⟨unclamped_001, unclamped_005, unclamped_01⟩

theorem dstarUnclamped_proved : dstarUnclampedStatement := by
  unfold dstarUnclampedStatement
  rw [unclamped_005]
  rw [Set.ncard_eq_toFinset_card']
  decide

theorem obsDstar_proved : obsDstarStatement :=
  ⟨t2t1Formula_proved, dstarClaim_proved, dstarUnclamped_proved⟩

theorem dstarLiteralDegenerate_proved : dstarLiteralDegenerateStatement := by
  intro p σ _ _ θ hθ
  refine ⟨⟨le_rfl, ?_⟩, fun d hd => hd.1⟩
  have : t2t1 p 1 σ = 0 := by
    unfold t2t1
    rw [primeTerm_two, gaussBinom_one_two]
    simp
  rw [this]
  exact hθ

/-! ### Observation 10.5(b), scope (PAPER-ISSUE evidence) -/

theorem inversionD3Scope_proved : inversionD3ScopeStatement := by
  intro p c hp h3 h23 hc2 hcnp hadj
  interval_cases p
  · rcases hadj with rfl | hc
    · exact iff_of_true (probUnif_lt_of_bounds (a := 4) (b := 3) (d := 3) (s := {2}) (q := 3) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)) (by norm_num)
    · obtain rfl : c = 2 := by omega
      exact absurd hcnp (by norm_num)
  · exact absurd hp (by norm_num)
  · rcases hadj with rfl | hc
    · exact iff_of_true (probUnif_lt_of_bounds (a := 6) (b := 5) (d := 3) (s := {2, 3}) (q := 5) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)) (by norm_num)
    · obtain rfl : c = 4 := by omega
      exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 5) (b := 4) (d := 3) (s := {5}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)
  · exact absurd hp (by norm_num)
  · rcases hadj with rfl | hc
    · exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 7) (b := 8) (d := 3) (s := {7}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)
    · obtain rfl : c = 6 := by omega
      exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 7) (b := 6) (d := 3) (s := {7}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · rcases hadj with rfl | hc
    · exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 11) (b := 12) (d := 3) (s := {11}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)
    · obtain rfl : c = 10 := by omega
      exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 11) (b := 10) (d := 3) (s := {11}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)
  · exact absurd hp (by norm_num)
  · rcases hadj with rfl | hc
    · exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 13) (b := 14) (d := 3) (s := {13}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)
    · obtain rfl : c = 12 := by omega
      exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 13) (b := 12) (d := 3) (s := {13}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · rcases hadj with rfl | hc
    · exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 17) (b := 18) (d := 3) (s := {17}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)
    · obtain rfl : c = 16 := by omega
      exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 17) (b := 16) (d := 3) (s := {17}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)
  · exact absurd hp (by norm_num)
  · rcases hadj with rfl | hc
    · exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 19) (b := 20) (d := 3) (s := {19}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)
    · obtain rfl : c = 18 := by omega
      exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 19) (b := 18) (d := 3) (s := {19}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · rcases hadj with rfl | hc
    · exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 23) (b := 24) (d := 3) (s := {23}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)
    · obtain rfl : c = 22 := by omega
      exact iff_of_false (not_lt.mpr (probUnif_lt_of_bounds (a := 23) (b := 22) (d := 3) (s := {23}) (q := 2) (by norm_num) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by norm_num) (by decide +kernel)).le) (by norm_num)

/-! ## Observation 10.5 (`obs:inversion`) -/

theorem key_ineq {σ p h e : ℕ} (hσ : 2 ≤ σ) (hlt : p + 1 < σ ^ e) (hexp : p + h + e ≤ p * p) :
    (p + 1) * σ ^ p * σ ^ (2 * h) < σ ^ h * σ ^ (p * p) := by
  have hpos : 0 < σ ^ (p + h) * σ ^ h := by positivity
  calc (p + 1) * σ ^ p * σ ^ (2 * h) = (p + 1) * (σ ^ (p + h) * σ ^ h) := by
        rw [two_mul, pow_add, pow_add]; ring
    _ < σ ^ e * (σ ^ (p + h) * σ ^ h) := Nat.mul_lt_mul_of_pos_right hlt hpos
    _ = σ ^ (p + h + e) * σ ^ h := by rw [pow_add (a := σ) (p + h) e]; ring
    _ ≤ σ ^ (p * p) * σ ^ h := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hexp)
    _ = σ ^ h * σ ^ (p * p) := Nat.mul_comm _ _

theorem compositeAdvantageD2_proved : compositeAdvantageD2Statement := by
  intro σ hσ p c hp hc2 hcnp hadj hex
  have hσ1 : 1 ≤ σ := by omega
  -- the prime is at least 5
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    push Not at hlt
    interval_cases p
    · rcases hadj with rfl | h
      · exact hcnp Nat.prime_three
      · omega
    · rcases hadj with rfl | h
      · exact hex ⟨rfl, rfl⟩
      · obtain rfl : c = 2 := by omega
        exact hcnp Nat.prime_two
    · exact absurd hp (by norm_num)
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hcev : 2 ∣ c := by
    obtain ⟨k, hk⟩ := hodd
    rcases hadj with h | h
    · exact ⟨k + 1, by omega⟩
    · exact ⟨k, by omega⟩
  have hcle : c ≤ p + 1 := by omega
  obtain ⟨h, hh⟩ : ∃ h, c ^ 2 = 2 * h := ⟨c ^ 2 / 2, by
    have : 2 ∣ c ^ 2 := dvd_pow hcev (by norm_num)
    omega⟩
  have hhalf : c ^ 2 / 2 = h := by omega
  rw [probUnif_lt_iff hσ1]
  have hU : numSS p 2 σ ≤ (p + 1) * σ ^ p := by
    have := numSS_prime_le (σ := σ) hp (by norm_num : 1 ≤ 2)
    rwa [gaussBinom_two_one, Nat.add_one_sub_one, pow_one] at this
  have hL : σ ^ h ≤ numSS c 2 σ := by
    have := numSS_ge_fix (σ := σ) hc2 (by norm_num : 1 ≤ 2) Nat.prime_two hcev
    rwa [hhalf] at this
  have hp2 : p ^ 2 = p * p := by ring
  -- main estimate, by cases
  have main : (p + 1) * σ ^ p * σ ^ (2 * h) < σ ^ h * σ ^ (p * p) ∨
      (p = 5 ∧ c = 6 ∧ σ = 2) := by
    by_cases hp7 : 7 ≤ p
    · left
      apply key_ineq (e := p + 3) hσ
      · calc p + 1 < 2 ^ (p + 3) := by
              have := Nat.lt_two_pow_self (n := p + 3); omega
          _ ≤ σ ^ (p + 3) := Nat.pow_le_pow_left hσ _
      · have hc2' : c ^ 2 ≤ (p + 1) ^ 2 := Nat.pow_le_pow_left hcle 2
        nlinarith
    · have hp5' : p = 5 := by
        have : p ≤ 6 := by omega
        interval_cases p
        · rfl
        · exact absurd hp (by norm_num)
      subst hp5'
      have hc46 : c = 4 ∨ c = 6 := by omega
      rcases hc46 with rfl | rfl
      · left
        have hh8 : h = 8 := by norm_num at hh; omega
        subst hh8
        apply key_ineq (e := 12) hσ _ (by norm_num)
        calc 5 + 1 < 2 ^ 12 := by norm_num
          _ ≤ σ ^ 12 := Nat.pow_le_pow_left hσ _
      · have hh18 : h = 18 := by norm_num at hh; omega
        subst hh18
        by_cases hσ2 : σ = 2
        · right; exact ⟨rfl, rfl, hσ2⟩
        · left
          apply key_ineq (e := 2) hσ _ (by norm_num)
          have : 3 ≤ σ := by omega
          nlinarith
  rcases main with hm | ⟨rfl, rfl, rfl⟩
  · calc numSS p 2 σ * σ ^ (c ^ 2) ≤ (p + 1) * σ ^ p * σ ^ (c ^ 2) := Nat.mul_le_mul_right _ hU
      _ = (p + 1) * σ ^ p * σ ^ (2 * h) := by rw [hh]
      _ < σ ^ h * σ ^ (p * p) := hm
      _ ≤ numSS c 2 σ * σ ^ (p ^ 2) := by rw [hp2]; exact Nat.mul_le_mul_right _ hL
  · exact (probUnif_lt_iff (by norm_num)).mp p5_lt_p6_d2

theorem compositeNearestPrimeFail_proved : compositeNearestPrimeFailStatement :=
  ⟨probUnif_lt_of_bounds (a := 9) (b := 7) (d := 2) (s := {3}) (q := 7) (by norm_num)
      (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat])
      (by norm_num) (by norm_num) (by decide +kernel),
    probUnif_lt_of_bounds (a := 10) (b := 7) (d := 2) (s := {2, 5}) (q := 7) (by norm_num)
      (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat])
      (by norm_num) (by norm_num) (by decide +kernel),
    probUnif_lt_of_bounds (a := 35) (b := 31) (d := 2) (s := {5, 7}) (q := 31) (by norm_num)
      (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat])
      (by norm_num) (by norm_num) (by decide +kernel)⟩

theorem inversionD3_proved : inversionD3Statement := p6_lt_p5_d3

theorem inversionDeepens_proved : inversionDeepensStatement :=
  fun σ hσ p hp hp3 d hd hneg => inversionDeepens_thm σ hσ p hp hp3 d hd hneg

theorem inversionDeepens56_proved : inversionDeepens56Statement := by
  have hneg := neg_forever (σ := 2) (p := 5) (d₀ := 2) le_rfl (by norm_num) (by norm_num)
    meas_5.2.1
  refine ⟨fun d hd => hneg d (by omega), fun d hd => ?_⟩
  rcases Nat.eq_or_lt_of_le hd with rfl | h
  · exact lt_of_lt_of_le (hneg 3 (by norm_num)) (meas_5.1 2 (by norm_num) le_rfl)
  · exact inversionDeepens_thm 2 le_rfl 5 (by norm_num) (by norm_num) d (by omega)
      (hneg d (by omega))

theorem ilr52_eq : inversionLogRatio 2 5 2 = Real.logb 10 ((801064 : ℕ) / (372736 : ℕ)) := by
  unfold inversionLogRatio probUnif
  rw [show (5 + 1 : ℕ) = 6 from rfl, numSS_6_2, numSS_5_2]
  norm_num

theorem ilr55_eq : inversionLogRatio 2 5 5
    = Real.logb 10 ((numSS 6 5 2 : ℝ) / ((numSS 5 5 2 * 2 ^ 4651 : ℕ) : ℝ)) := by
  unfold inversionLogRatio probUnif
  rw [show (5 + 1 : ℕ) = 6 from rfl]
  congr 1
  have e6 : (6 : ℕ) ^ 5 = 4651 + 5 ^ 5 := by norm_num
  rw [e6, pow_add]
  push_cast
  have h5 : (0 : ℝ) < numSS 5 5 2 := by exact_mod_cast numSS_pos (by norm_num) (by norm_num) (by norm_num)
  field_simp

set_option maxRecDepth 100000 in
theorem cert55 : (numSS 5 5 2 * 2 ^ 4651) ^ 20 ≤ numSS 6 5 2 ^ 20 * 10 ^ 8385 ∧
    numSS 6 5 2 ^ 20 * 10 ^ 8383 ≤ (numSS 5 5 2 * 2 ^ 4651) ^ 20 := by
  have h6 := numSS_six_int 5 2 (by norm_num) (by norm_num)
  have h5 := numSS_prime_int (p := 5) (d := 5) (σ := 2) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · have : ((numSS 5 5 2 : ℤ) * 2 ^ 4651) ^ 20 ≤ (numSS 6 5 2 : ℤ) ^ 20 * 10 ^ 8385 := by
      rw [h6, h5]; decide +kernel
    exact_mod_cast this
  · have : (numSS 6 5 2 : ℤ) ^ 20 * 10 ^ 8383 ≤ ((numSS 5 5 2 : ℤ) * 2 ^ 4651) ^ 20 := by
      rw [h6, h5]; decide +kernel
    exact_mod_cast this

theorem inversionExample_proved : inversionExampleStatement := by
  have hA := logb_ratio_pos (A := 801064) (B := 372736) (k := 200) (a1 := 65) (a2 := 67)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
  have hB := logb_ratio_neg (A := numSS 6 5 2) (B := numSS 5 5 2 * 2 ^ 4651) (k := 20)
    (a1 := 8385) (a2 := 8383) (numSS_pos (by norm_num) (by norm_num) (by norm_num))
    (by have := numSS_pos (n := 5) (d := 5) (σ := 2) (by norm_num) (by norm_num) (by norm_num)
        positivity) (by norm_num) cert55.1 cert55.2
  unfold inversionExampleStatement
  rw [ilr52_eq, ilr55_eq]
  refine ⟨?_, ?_⟩
  · rw [abs_le]; constructor <;> norm_num at hA ⊢ <;> linarith [hA.1, hA.2]
  · generalize Real.logb 10 ((numSS 6 5 2 : ℝ) / ((numSS 5 5 2 * 2 ^ 4651 : ℕ) : ℝ)) = L at hB ⊢
    rw [abs_le]; constructor <;> norm_num at hB ⊢ <;> linarith [hB.1, hB.2]

theorem obsInversion_proved : obsInversionStatement :=
  ⟨compositeAdvantageD2_proved, inversionD3_proved, inversionDeepens_proved,
    inversionDeepens56_proved, inversionExample_proved⟩

/-! ## The whole group -/

theorem group11_proved : group11Statement :=
  ⟨obsExtrema_proved, remDcMeasured_proved, obsDstar_proved, obsInversion_proved⟩

end ShiftSym.P11
