/-
Group 11 (Numerics), proof helpers, part 5: the measured inversion points
of Remark 10.3 (`σ = 2`, `p ∈ {5, 7, 11, 13}`; `p = 3` is exact and lives in
the main file). For each prime we prove the signs of
`d ↦ log₁₀[P_{(p+1)^d}/P_{p^d}]` on `1 ≤ d ≤ d₀ + 1` and two-sided bounds of
`g(d) = log P_{(p+1)^d} − log P_{p^d}` at `d₀, d₀ + 1` in units of `log 2`.
Sources: one fixed set / the union bound / the first two terms of
Corollary 4.4 (large lattices) and exact values (`p = 5`); all numerical
certificates are integer inequalities checked by `decide +kernel`.
(The certificate parameters were produced by
scratchpad/research/formal_ext/scratch/p11/gen_meas.py.)
-/
import Shiftsym.Paper.Proofs.P11_Numerics_Deepens

open Real

namespace ShiftSym.P11

open ShiftSym

theorem numSS_prime_ge2 {p d k : ℕ} (hp : p.Prime) (hd : 2 ≤ d)
    (hK : (∑ r ∈ Finset.Icc 2 d, rdCoeff p r d) ≤ 2 ^ k) (hk : p ^ (d - 2) + k ≤ p ^ (d - 1)) :
    (gaussBinom p d 1 - 1) * 2 ^ (p ^ (d - 1)) ≤ numSS p d 2 := by
  have h1 := numSS_prime_int (p := p) (d := d) (σ := 2) hp (by omega) (by norm_num)
  have h2 := lowerEnvelope_ge p d 2 hp.one_lt.le hd (by norm_num)
  have hG : 1 ≤ gaussBinom p d 1 := gaussBinom_one_pos hp.two_le (by omega)
  have hrd : rdCoeff p 1 d = gaussBinom p d 1 := by simp [rdCoeff]
  have h3n : (∑ r ∈ Finset.Icc 2 d, rdCoeff p r d) * 2 ^ (p ^ (d - 2)) ≤ 2 ^ (p ^ (d - 1)) := by
    calc _ ≤ 2 ^ k * 2 ^ (p ^ (d - 2)) := Nat.mul_le_mul_right _ hK
      _ = 2 ^ (p ^ (d - 2) + k) := by rw [← pow_add, add_comm]
      _ ≤ 2 ^ (p ^ (d - 1)) := Nat.pow_le_pow_right (by norm_num) hk
  have h3 : ((∑ r ∈ Finset.Icc 2 d, rdCoeff p r d : ℕ) : ℤ) * (2 : ℤ) ^ (p ^ (d - 2))
      ≤ (2 : ℤ) ^ (p ^ (d - 1)) := by exact_mod_cast h3n
  push_cast at h3
  rw [hrd] at h2
  have h4 : ((gaussBinom p d 1 - 1 : ℕ) : ℤ) * 2 ^ (p ^ (d - 1)) ≤ (numSS p d 2 : ℤ) := by
    rw [Nat.cast_sub hG, h1]
    push_cast
    push_cast at h2
    linarith
  exact_mod_cast h4

theorem lp_prime_ub {p d u v : ℕ} (hp : p.Prime) (hd : 1 ≤ d) (hv : 0 < v)
    (hc : gaussBinom p d 1 ^ v ≤ 2 ^ u) :
    log (probUnif p d 2) ≤ (((p ^ (d - 1) : ℕ) : ℝ) + u / v - ((p ^ d : ℕ) : ℝ)) * log 2 :=
  logP_ub hp.two_le hd (numSS_prime_le hp hd) hv hc

theorem lp_prime_lb_fix {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d) :
    (((p ^ (d - 1) : ℕ) : ℝ) + ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - ((p ^ d : ℕ) : ℝ)) * log 2
      ≤ log (probUnif p d 2) :=
  logP_lb (m := 1) hp.two_le hd (by rw [one_mul]; exact numSS_prime_ge (σ := 2) hp hd) one_pos
    (by norm_num)

theorem lp_prime_lb2 {p d k u v : ℕ} (hp : p.Prime) (hd : 2 ≤ d)
    (hK : (∑ r ∈ Finset.Icc 2 d, rdCoeff p r d) ≤ 2 ^ k) (hk : p ^ (d - 2) + k ≤ p ^ (d - 1))
    (hv : 0 < v) (hc : 2 ^ u ≤ (gaussBinom p d 1 - 1) ^ v) :
    (((p ^ (d - 1) : ℕ) : ℝ) + u / v - ((p ^ d : ℕ) : ℝ)) * log 2 ≤ log (probUnif p d 2) :=
  logP_lb hp.two_le (by omega) (numSS_prime_ge2 hp hd hK hk) hv hc

theorem lc_lb {c d : ℕ} (hc : 2 ≤ c) (hd : 1 ≤ d) (h2 : 2 ∣ c) :
    (((c ^ d / 2 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) - ((c ^ d : ℕ) : ℝ)) * log 2
      ≤ log (probUnif c d 2) :=
  logP_lb (m := 1) hc hd (by rw [one_mul]; exact numSS_ge_fix (σ := 2) hc hd Nat.prime_two h2) one_pos
    (by norm_num)

theorem lc_ub1 {c d u v : ℕ} (hc : 2 ≤ c) (hd : 1 ≤ d) (hpf : c.primeFactors = {2})
    (hv : 0 < v) (hcert : gaussBinom 2 d 1 ^ v ≤ 2 ^ u) :
    log (probUnif c d 2) ≤ (((c ^ d / 2 : ℕ) : ℝ) + u / v - ((c ^ d : ℕ) : ℝ)) * log 2 := by
  have h := numSS_le_union (n := c) (d := d) (σ := 2) hc
  rw [hpf, Finset.sum_singleton] at h
  exact logP_ub hc hd h hv hcert

theorem lc_ub2 {c d q k u v : ℕ} (hc : 2 ≤ c) (hd : 1 ≤ d) (hpf : c.primeFactors = {2, q})
    (hq : q ≠ 2) (hk : gaussBinom q d 1 ≤ 2 ^ k) (hexp : c ^ d / q + k ≤ c ^ d / 2)
    (hv : 0 < v) (hcert : (gaussBinom 2 d 1 + 1) ^ v ≤ 2 ^ u) :
    log (probUnif c d 2) ≤ (((c ^ d / 2 : ℕ) : ℝ) + u / v - ((c ^ d : ℕ) : ℝ)) * log 2 := by
  have h := numSS_le_union (n := c) (d := d) (σ := 2) hc
  rw [hpf, Finset.sum_pair (Ne.symm hq)] at h
  have h2 : gaussBinom q d 1 * 2 ^ (c ^ d / q) ≤ 2 ^ (c ^ d / 2) :=
    calc _ ≤ 2 ^ k * 2 ^ (c ^ d / q) := Nat.mul_le_mul_right _ hk
      _ = 2 ^ (c ^ d / q + k) := by rw [← pow_add, add_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hexp
  have h3 : numSS c d 2 ≤ (gaussBinom 2 d 1 + 1) * 2 ^ (c ^ d / 2) := by
    rw [add_mul, one_mul]; omega
  exact logP_ub hc hd h3 hv hcert

theorem lexact_lb {n d S u v : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hS : numSS n d 2 = S)
    (hv : 0 < v) (hc : 2 ^ u ≤ S ^ v) :
    (((0 : ℕ) : ℝ) + u / v - ((n ^ d : ℕ) : ℝ)) * log 2 ≤ log (probUnif n d 2) :=
  logP_lb hn hd (by rw [hS]; simp) hv hc

theorem lexact_ub {n d S u v : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hS : numSS n d 2 = S)
    (hv : 0 < v) (hc : S ^ v ≤ 2 ^ u) :
    log (probUnif n d 2) ≤ (((0 : ℕ) : ℝ) + u / v - ((n ^ d : ℕ) : ℝ)) * log 2 :=
  logP_ub hn hd (by rw [hS]; simp) hv hc

/-! ### Exact values for `n = 6` and primes -/

theorem rad_six : rad 6 = 2 * 3 := by simp [rad, Nat.primeFactors, Nat.primeFactorsList_ofNat]

theorem numSS_six_int (d σ : ℕ) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    (numSS 6 d σ : ℤ) = (∑ a ∈ Finset.range (d + 1), ∑ b ∈ Finset.range (d + 1),
          (-1 : ℤ) ^ (1 + a + b) * (rdCoeff 2 a d : ℤ) * (rdCoeff 3 b d : ℤ) *
            (((σ ^ (6 ^ d / (2 ^ a * 3 ^ b))) : ℕ) : ℤ))
        + (((σ ^ (6 ^ d)) : ℕ) : ℤ) := by
  rw [numSS_int 6 d σ (by norm_num) hd hσ,
    enumerationRHS_twoPrime Nat.prime_two Nat.prime_three (by norm_num) rad_six]

theorem numSS_6_2 : numSS 6 2 2 = 801064 := by
  have h := numSS_six_int 2 2 (by norm_num) (by norm_num)
  have e : (∑ a ∈ Finset.range (2 + 1), ∑ b ∈ Finset.range (2 + 1),
          (-1 : ℤ) ^ (1 + a + b) * (rdCoeff 2 a 2 : ℤ) * (rdCoeff 3 b 2 : ℤ) *
            (((2 ^ (6 ^ 2 / (2 ^ a * 3 ^ b))) : ℕ) : ℤ))
        + (((2 ^ (6 ^ 2)) : ℕ) : ℤ) = 801064 := by decide +kernel
  rw [e] at h
  exact_mod_cast h

theorem numSS_6_3 : numSS 6 3 2 = 2271629875670377599551565394859176 := by
  have h := numSS_six_int 3 2 (by norm_num) (by norm_num)
  have e : (∑ a ∈ Finset.range (3 + 1), ∑ b ∈ Finset.range (3 + 1),
          (-1 : ℤ) ^ (1 + a + b) * (rdCoeff 2 a 3 : ℤ) * (rdCoeff 3 b 3 : ℤ) *
            (((2 ^ (6 ^ 3 / (2 ^ a * 3 ^ b))) : ℕ) : ℤ))
        + (((2 ^ (6 ^ 3)) : ℕ) : ℤ) = 2271629875670377599551565394859176 := by decide +kernel
  rw [e] at h
  exact_mod_cast h

theorem numSS_5_2 : numSS 5 2 2 = 182 :=
  numSS_prime_val (by norm_num) (by norm_num) (by norm_num) 182 (by decide)

theorem numSS_5_3 : numSS 5 3 2 = 1040182682 :=
  numSS_prime_val (by norm_num) (by norm_num) (by norm_num) 1040182682 (by decide)

theorem ilr_nonneg_of_G {p d : ℕ} (hp : 2 ≤ p) (hd : 1 ≤ d)
    (h : 0 ≤ log (probUnif (p + 1) d 2) - log (probUnif p d 2)) :
    0 ≤ inversionLogRatio 2 p d := by
  rw [ilr_eq hp hd (by norm_num)]
  exact div_nonneg h (log_pos (by norm_num)).le

theorem ilr_neg_of_G {p d : ℕ} (hp : 2 ≤ p) (hd : 1 ≤ d)
    (h : log (probUnif (p + 1) d 2) - log (probUnif p d 2) < 0) :
    inversionLogRatio 2 p d < 0 := by
  rw [ilr_eq hp hd (by norm_num)]
  exact div_neg_of_neg_of_pos h (log_pos (by norm_num))

theorem meas_5 :
    (∀ d : ℕ, 1 ≤ d → d ≤ 2 → 0 ≤ inversionLogRatio 2 5 d) ∧
    inversionLogRatio 2 5 (2 + 1) < 0 ∧
    ((2207 : ℝ) / 2000) * log 2 ≤ (log (probUnif 6 2 2) - log (probUnif 5 2 2)) ∧
    (log (probUnif 6 2 2) - log (probUnif 5 2 2)) ≤ ((2209 : ℝ) / 2000) * log 2 ∧
    ((20293 : ℝ) / 2000) * log 2 ≤ -(log (probUnif 6 3 2) - log (probUnif 5 3 2)) ∧
    -(log (probUnif 6 3 2) - log (probUnif 5 3 2)) ≤ ((4059 : ℝ) / 400) * log 2 := by
  have t0 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have clb1 := lc_lb (c := 6) (d := 1) (by norm_num) (by norm_num) (by norm_num)
  have pub1 := lp_prime_ub (p := 5) (d := 1) (u := 0) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb2 := lexact_lb (n := 6) (d := 2) (S := 801064) (u := 39223) (v := 2000) (by norm_num) (by norm_num) numSS_6_2 (by norm_num) (by decide +kernel)
  have cub2 := lexact_ub (n := 6) (d := 2) (S := 801064) (u := 39224) (v := 2000) (by norm_num) (by norm_num) numSS_6_2 (by norm_num) (by decide +kernel)
  have plb2 := lexact_lb (n := 5) (d := 2) (S := 182) (u := 15015) (v := 2000) (by norm_num) (by norm_num) numSS_5_2 (by norm_num) (by decide +kernel)
  have pub2 := lexact_ub (n := 5) (d := 2) (S := 182) (u := 15016) (v := 2000) (by norm_num) (by norm_num) numSS_5_2 (by norm_num) (by decide +kernel)
  have clb3 := lexact_lb (n := 6) (d := 3) (S := 2271629875670377599551565394859176) (u := 221614) (v := 2000) (by norm_num) (by norm_num) numSS_6_3 (by norm_num) (by decide +kernel)
  have cub3 := lexact_ub (n := 6) (d := 3) (S := 2271629875670377599551565394859176) (u := 221615) (v := 2000) (by norm_num) (by norm_num) numSS_6_3 (by norm_num) (by decide +kernel)
  have plb3 := lexact_lb (n := 5) (d := 3) (S := 1040182682) (u := 59908) (v := 2000) (by norm_num) (by norm_num) numSS_5_3 (by norm_num) (by decide +kernel)
  have pub3 := lexact_ub (n := 5) (d := 3) (S := 1040182682) (u := 59909) (v := 2000) (by norm_num) (by norm_num) numSS_5_3 (by norm_num) (by decide +kernel)
  norm_num at clb1 pub1 clb2 cub2 plb2 pub2 clb3 cub3 plb3 pub3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd1 hd2
    interval_cases d
    · have h : 0 ≤ (log (probUnif 6 1 2) - log (probUnif 5 1 2)) := by linarith
      exact ilr_nonneg_of_G (p := 5) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 6 2 2) - log (probUnif 5 2 2)) := by linarith
      exact ilr_nonneg_of_G (p := 5) (by norm_num) (by norm_num) h
  · have h : (log (probUnif 6 3 2) - log (probUnif 5 3 2)) < 0 := by linarith
    exact ilr_neg_of_G (p := 5) (by norm_num) (by norm_num) h
  · linarith
  · linarith
  · linarith
  · linarith

theorem meas_7 :
    (∀ d : ℕ, 1 ≤ d → d ≤ 4 → 0 ≤ inversionLogRatio 2 7 d) ∧
    inversionLogRatio 2 7 (4 + 1) < 0 ∧
    (1 : ℝ) * log 2 ≤ (log (probUnif 8 4 2) - log (probUnif 7 4 2)) ∧
    (log (probUnif 8 4 2) - log (probUnif 7 4 2)) ≤ (6 : ℝ) * log 2 ∧
    (1984 : ℝ) * log 2 ≤ -(log (probUnif 8 5 2) - log (probUnif 7 5 2)) ∧
    -(log (probUnif 8 5 2) - log (probUnif 7 5 2)) ≤ (1990 : ℝ) * log 2 := by
  have t0 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have clb1 := lc_lb (c := 8) (d := 1) (by norm_num) (by norm_num) (by norm_num)
  have pub1 := lp_prime_ub (p := 7) (d := 1) (u := 0) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb2 := lc_lb (c := 8) (d := 2) (by norm_num) (by norm_num) (by norm_num)
  have pub2 := lp_prime_ub (p := 7) (d := 2) (u := 3) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb3 := lc_lb (c := 8) (d := 3) (by norm_num) (by norm_num) (by norm_num)
  have pub3 := lp_prime_ub (p := 7) (d := 3) (u := 6) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb4 := lc_lb (c := 8) (d := 4) (by norm_num) (by norm_num) (by norm_num)
  have cub4 := lc_ub1 (c := 8) (d := 4) (u := 4) (v := 1) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by decide +kernel)
  have plb4 := lp_prime_lb2 (p := 7) (d := 4) (k := 19) (u := 8) (v := 1) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  have pub4 := lp_prime_ub (p := 7) (d := 4) (u := 9) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb5 := lc_lb (c := 8) (d := 5) (by norm_num) (by norm_num) (by norm_num)
  have cub5 := lc_ub1 (c := 8) (d := 5) (u := 5) (v := 1) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by decide +kernel)
  have plb5 := lp_prime_lb2 (p := 7) (d := 5) (k := 30) (u := 11) (v := 1) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  have pub5 := lp_prime_ub (p := 7) (d := 5) (u := 12) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at clb1 pub1 clb2 pub2 clb3 pub3 clb4 cub4 plb4 pub4 clb5 cub5 plb5 pub5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd1 hd2
    interval_cases d
    · have h : 0 ≤ (log (probUnif 8 1 2) - log (probUnif 7 1 2)) := by linarith
      exact ilr_nonneg_of_G (p := 7) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 8 2 2) - log (probUnif 7 2 2)) := by linarith
      exact ilr_nonneg_of_G (p := 7) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 8 3 2) - log (probUnif 7 3 2)) := by linarith
      exact ilr_nonneg_of_G (p := 7) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 8 4 2) - log (probUnif 7 4 2)) := by linarith
      exact ilr_nonneg_of_G (p := 7) (by norm_num) (by norm_num) h
  · have h : (log (probUnif 8 5 2) - log (probUnif 7 5 2)) < 0 := by linarith
    exact ilr_neg_of_G (p := 7) (by norm_num) (by norm_num) h
  · linarith
  · linarith
  · linarith
  · linarith

theorem meas_11 :
    (∀ d : ℕ, 1 ≤ d → d ≤ 6 → 0 ≤ inversionLogRatio 2 11 d) ∧
    inversionLogRatio 2 11 (6 + 1) < 0 ∧
    (117500 : ℝ) * log 2 ≤ (log (probUnif 12 6 2) - log (probUnif 11 6 2)) ∧
    (log (probUnif 12 6 2) - log (probUnif 11 6 2)) ≤ (117507 : ℝ) * log 2 ∧
    (200307 : ℝ) * log 2 ≤ -(log (probUnif 12 7 2) - log (probUnif 11 7 2)) ∧
    -(log (probUnif 12 7 2) - log (probUnif 11 7 2)) ≤ (200315 : ℝ) * log 2 := by
  have t0 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have clb1 := lc_lb (c := 12) (d := 1) (by norm_num) (by norm_num) (by norm_num)
  have pub1 := lp_prime_ub (p := 11) (d := 1) (u := 0) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb2 := lc_lb (c := 12) (d := 2) (by norm_num) (by norm_num) (by norm_num)
  have pub2 := lp_prime_ub (p := 11) (d := 2) (u := 4) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb3 := lc_lb (c := 12) (d := 3) (by norm_num) (by norm_num) (by norm_num)
  have pub3 := lp_prime_ub (p := 11) (d := 3) (u := 8) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb4 := lc_lb (c := 12) (d := 4) (by norm_num) (by norm_num) (by norm_num)
  have pub4 := lp_prime_ub (p := 11) (d := 4) (u := 11) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb5 := lc_lb (c := 12) (d := 5) (by norm_num) (by norm_num) (by norm_num)
  have pub5 := lp_prime_ub (p := 11) (d := 5) (u := 14) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb6 := lc_lb (c := 12) (d := 6) (by norm_num) (by norm_num) (by norm_num)
  have cub6 := lc_ub2 (c := 12) (d := 6) (q := 3) (k := 9) (u := 6) (v := 1) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  have plb6 := lp_prime_lb2 (p := 11) (d := 6) (k := 54) (u := 17) (v := 1) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  have pub6 := lp_prime_ub (p := 11) (d := 6) (u := 18) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb7 := lc_lb (c := 12) (d := 7) (by norm_num) (by norm_num) (by norm_num)
  have cub7 := lc_ub2 (c := 12) (d := 7) (q := 3) (k := 11) (u := 7) (v := 1) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  have plb7 := lp_prime_lb2 (p := 11) (d := 7) (k := 74) (u := 20) (v := 1) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  have pub7 := lp_prime_ub (p := 11) (d := 7) (u := 21) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at clb1 pub1 clb2 pub2 clb3 pub3 clb4 pub4 clb5 pub5 clb6 cub6 plb6 pub6 clb7 cub7 plb7 pub7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd1 hd2
    interval_cases d
    · have h : 0 ≤ (log (probUnif 12 1 2) - log (probUnif 11 1 2)) := by linarith
      exact ilr_nonneg_of_G (p := 11) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 12 2 2) - log (probUnif 11 2 2)) := by linarith
      exact ilr_nonneg_of_G (p := 11) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 12 3 2) - log (probUnif 11 3 2)) := by linarith
      exact ilr_nonneg_of_G (p := 11) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 12 4 2) - log (probUnif 11 4 2)) := by linarith
      exact ilr_nonneg_of_G (p := 11) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 12 5 2) - log (probUnif 11 5 2)) := by linarith
      exact ilr_nonneg_of_G (p := 11) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 12 6 2) - log (probUnif 11 6 2)) := by linarith
      exact ilr_nonneg_of_G (p := 11) (by norm_num) (by norm_num) h
  · have h : (log (probUnif 12 7 2) - log (probUnif 11 7 2)) < 0 := by linarith
    exact ilr_neg_of_G (p := 11) (by norm_num) (by norm_num) h
  · linarith
  · linarith
  · linarith
  · linarith

theorem meas_13 :
    (∀ d : ℕ, 1 ≤ d → d ≤ 8 → 0 ≤ inversionLogRatio 2 13 d) ∧
    inversionLogRatio 2 13 (8 + 1) < 0 ∧
    (15087649 : ℝ) * log 2 ≤ (log (probUnif 14 8 2) - log (probUnif 13 8 2)) ∧
    (log (probUnif 14 8 2) - log (probUnif 13 8 2)) ≤ (15087658 : ℝ) * log 2 ∧
    (541754760 : ℝ) * log 2 ≤ -(log (probUnif 14 9 2) - log (probUnif 13 9 2)) ∧
    -(log (probUnif 14 9 2) - log (probUnif 13 9 2)) ≤ (541754770 : ℝ) * log 2 := by
  have t0 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have clb1 := lc_lb (c := 14) (d := 1) (by norm_num) (by norm_num) (by norm_num)
  have pub1 := lp_prime_ub (p := 13) (d := 1) (u := 0) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb2 := lc_lb (c := 14) (d := 2) (by norm_num) (by norm_num) (by norm_num)
  have pub2 := lp_prime_ub (p := 13) (d := 2) (u := 4) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb3 := lc_lb (c := 14) (d := 3) (by norm_num) (by norm_num) (by norm_num)
  have pub3 := lp_prime_ub (p := 13) (d := 3) (u := 8) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb4 := lc_lb (c := 14) (d := 4) (by norm_num) (by norm_num) (by norm_num)
  have pub4 := lp_prime_ub (p := 13) (d := 4) (u := 12) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb5 := lc_lb (c := 14) (d := 5) (by norm_num) (by norm_num) (by norm_num)
  have pub5 := lp_prime_ub (p := 13) (d := 5) (u := 15) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb6 := lc_lb (c := 14) (d := 6) (by norm_num) (by norm_num) (by norm_num)
  have pub6 := lp_prime_ub (p := 13) (d := 6) (u := 19) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb7 := lc_lb (c := 14) (d := 7) (by norm_num) (by norm_num) (by norm_num)
  have pub7 := lp_prime_ub (p := 13) (d := 7) (u := 23) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb8 := lc_lb (c := 14) (d := 8) (by norm_num) (by norm_num) (by norm_num)
  have cub8 := lc_ub2 (c := 14) (d := 8) (q := 7) (k := 20) (u := 8) (v := 1) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  have plb8 := lp_prime_lb2 (p := 13) (d := 8) (k := 105) (u := 26) (v := 1) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  have pub8 := lp_prime_ub (p := 13) (d := 8) (u := 27) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  have clb9 := lc_lb (c := 14) (d := 9) (by norm_num) (by norm_num) (by norm_num)
  have cub9 := lc_ub2 (c := 14) (d := 9) (q := 7) (k := 23) (u := 9) (v := 1) (by norm_num) (by norm_num) (by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  have plb9 := lp_prime_lb2 (p := 13) (d := 9) (k := 135) (u := 29) (v := 1) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by decide +kernel)
  have pub9 := lp_prime_ub (p := 13) (d := 9) (u := 30) (v := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  norm_num at clb1 pub1 clb2 pub2 clb3 pub3 clb4 pub4 clb5 pub5 clb6 pub6 clb7 pub7 clb8 cub8 plb8 pub8 clb9 cub9 plb9 pub9
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd1 hd2
    interval_cases d
    · have h : 0 ≤ (log (probUnif 14 1 2) - log (probUnif 13 1 2)) := by linarith
      exact ilr_nonneg_of_G (p := 13) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 14 2 2) - log (probUnif 13 2 2)) := by linarith
      exact ilr_nonneg_of_G (p := 13) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 14 3 2) - log (probUnif 13 3 2)) := by linarith
      exact ilr_nonneg_of_G (p := 13) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 14 4 2) - log (probUnif 13 4 2)) := by linarith
      exact ilr_nonneg_of_G (p := 13) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 14 5 2) - log (probUnif 13 5 2)) := by linarith
      exact ilr_nonneg_of_G (p := 13) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 14 6 2) - log (probUnif 13 6 2)) := by linarith
      exact ilr_nonneg_of_G (p := 13) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 14 7 2) - log (probUnif 13 7 2)) := by linarith
      exact ilr_nonneg_of_G (p := 13) (by norm_num) (by norm_num) h
    · have h : 0 ≤ (log (probUnif 14 8 2) - log (probUnif 13 8 2)) := by linarith
      exact ilr_nonneg_of_G (p := 13) (by norm_num) (by norm_num) h
  · have h : (log (probUnif 14 9 2) - log (probUnif 13 9 2)) < 0 := by linarith
    exact ilr_neg_of_G (p := 13) (by norm_num) (by norm_num) h
  · linarith
  · linarith
  · linarith
  · linarith

end ShiftSym.P11
