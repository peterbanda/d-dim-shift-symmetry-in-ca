/-
Phase H, group 09 (CrossoverLaws) — PROOFS of the frozen statements in
`Shiftsym/Paper/S09_CrossoverLaws.lean` (paper §10, Propositions 10.1 and 10.2).

The combinatorial two-sided bound lives in the helper module
`P09_CrossoverLaws_Bounds`; everything here is real analysis on top of it.
-/
import Shiftsym.Paper.Proofs.P09_CrossoverLaws_Bounds

namespace ShiftSym.P09

open ShiftSym Filter
open scoped Topology

/-! ## Proposition 10.1: the two-sided bound and the prefactor chain -/

theorem rateLower_proved : rateLowerStatement := by
  intro n d σ hn hd _hσ
  exact numSS_ge_pow hn hd

theorem rateUpper_proved : rateUpperStatement := by
  intro n d σ hn _hd hσ
  exact numSS_le_real hn (by omega)

theorem rateBounds_proved : rateBoundsStatement :=
  ⟨rateLower_proved, rateUpper_proved⟩

theorem rateProofPrefactor_proved : rateProofPrefactorStatement := by
  intro n d hn _hd
  exact ⟨fun p hp => div_le_div_p1 hp, sopfD_le_sum n d, sum_le_omega d hn,
    omega_term_le d hn⟩

/-! ## Real-valued consequences -/

section Real

variable {n d σ : ℕ}

theorem p1_pos_real (n : ℕ) : (0 : ℝ) < (p1 n : ℝ) := by
  exact_mod_cast Nat.minFac_pos n

theorem p1_two_le (hn : 2 ≤ n) : 2 ≤ p1 n :=
  (Nat.minFac_prime (by omega)).two_le

/-- The exponent `N/p_1`, cast to `ℝ`, is the real quotient. -/
theorem cast_E (hd : 1 ≤ d) :
    ((n ^ d / p1 n : ℕ) : ℝ) = (n : ℝ) ^ d / (p1 n : ℝ) := by
  rw [Nat.cast_div (p1_dvd_pow n d hd) (p1_pos_real n).ne']
  push_cast
  ring

theorem numSS_pos (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ) :
    (0 : ℝ) < (numSS n d σ : ℝ) := by
  have h := numSS_ge_pow (σ := σ) hn hd
  have h1 : 1 ≤ σ ^ (n ^ d / p1 n) := Nat.one_le_pow _ _ (by omega)
  exact_mod_cast (show 0 < numSS n d σ by omega)

theorem logb_probUnif (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ) :
    Real.logb (σ : ℝ) (probUnif n d σ) = Real.logb (σ : ℝ) (numSS n d σ) - (n : ℝ) ^ d := by
  have hσ1 : (1 : ℝ) < σ := by exact_mod_cast (show 1 < σ by omega)
  have hσ0 : (0 : ℝ) < σ := by linarith
  unfold probUnif
  rw [Real.logb_div (numSS_pos hn hd hσ).ne' (pow_pos hσ0 _).ne', Real.logb_pow,
    Real.logb_self_eq_one hσ1]
  push_cast
  ring

/-- `N/p_1 ≤ log_σ |S|` (lower bound in log form). -/
theorem logb_numSS_ge (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ) :
    (n : ℝ) ^ d / (p1 n : ℝ) ≤ Real.logb (σ : ℝ) (numSS n d σ) := by
  have hσ1 : (1 : ℝ) < σ := by exact_mod_cast (show 1 < σ by omega)
  have hσ0 : (0 : ℝ) < σ := by linarith
  have h := numSS_ge_pow (σ := σ) hn hd
  have h' : (σ : ℝ) ^ (n ^ d / p1 n) ≤ (numSS n d σ : ℝ) := by exact_mod_cast h
  have := (Real.logb_le_logb hσ1 (pow_pos hσ0 _) (numSS_pos hn hd hσ)).mpr h'
  rwa [Real.logb_pow, Real.logb_self_eq_one hσ1, mul_one, cast_E hd] at this

/-- The upper prefactor `2 log₂(n) n^{d−1}` is positive. -/
theorem prefactor_pos (hn : 2 ≤ n) (d : ℕ) :
    (0 : ℝ) < 2 * Real.logb 2 (n : ℝ) * (n : ℝ) ^ (d - 1) := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have h2 : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) h1
  positivity

/-- `log_σ |S| ≤ log_σ(2 log₂(n) n^{d−1}) + N/p_1` (upper bound in log form). -/
theorem logb_numSS_le (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ) :
    Real.logb (σ : ℝ) (numSS n d σ) ≤
      Real.logb (σ : ℝ) (2 * Real.logb 2 (n : ℝ) * (n : ℝ) ^ (d - 1)) +
        (n : ℝ) ^ d / (p1 n : ℝ) := by
  have hσ1 : (1 : ℝ) < σ := by exact_mod_cast (show 1 < σ by omega)
  have hσ0 : (0 : ℝ) < σ := by linarith
  have h := numSS_le_real (d := d) (σ := σ) hn (by omega)
  have hK := prefactor_pos hn d
  have := (Real.logb_le_logb hσ1 (numSS_pos hn hd hσ) (by positivity)).mpr h
  rwa [Real.logb_mul hK.ne' (pow_pos hσ0 _).ne', Real.logb_pow,
    Real.logb_self_eq_one hσ1, mul_one, cast_E hd] at this

/-- The gap `(1 − 1/p_1) − c(n,d) = (log_σ|S| − N/p_1)/N`. -/
theorem gap_eq (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ) :
    (1 - 1 / (p1 n : ℝ)) - decayRate n d σ =
      (Real.logb (σ : ℝ) (numSS n d σ) - (n : ℝ) ^ d / (p1 n : ℝ)) / (n : ℝ) ^ d := by
  have hN : (0 : ℝ) < (n : ℝ) ^ d := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hp := p1_pos_real n
  unfold decayRate
  rw [logb_probUnif hn hd hσ]
  field_simp
  ring

end Real

/-! ## Proposition 10.1: decay-rate sandwich and limits -/

theorem rateGap_proved : rateGapStatement := by
  intro n d σ hn hd hσ
  have hN : (0 : ℝ) < (n : ℝ) ^ d := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  rw [gap_eq hn hd hσ]
  constructor
  · apply div_nonneg _ hN.le
    linarith [logb_numSS_ge hn hd hσ]
  · apply div_le_div_of_nonneg_right _ hN.le
    have h := logb_numSS_le hn hd hσ
    have e : 2 * (n : ℝ) ^ (d - 1) * Real.logb 2 (n : ℝ) =
        2 * Real.logb 2 (n : ℝ) * (n : ℝ) ^ (d - 1) := by ring
    rw [e]
    linarith

theorem rateGapBoundTendsto_proved : rateGapBoundTendstoStatement := by
  intro n σ hn hσ
  have h1n : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) h1n
  set A : ℝ := Real.logb (σ : ℝ) 2 + Real.logb (σ : ℝ) (Real.logb 2 (n : ℝ)) -
    Real.logb (σ : ℝ) n with hA
  set B : ℝ := Real.logb (σ : ℝ) n with hB
  have hinv : Tendsto (fun d : ℕ => ((n : ℝ) ^ d)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt h1n)
  have hlin : Tendsto (fun d : ℕ => (d : ℝ) / (n : ℝ) ^ d) atTop (𝓝 0) := by
    have := tendsto_pow_const_div_const_pow_of_one_lt 1 h1n
    simpa using this
  have hlim : Tendsto (fun d : ℕ => A * ((n : ℝ) ^ d)⁻¹ + B * ((d : ℝ) / (n : ℝ) ^ d))
      atTop (𝓝 0) := by
    have := (hinv.const_mul A).add (hlin.const_mul B)
    simpa using this
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  have hpow : (0 : ℝ) < (n : ℝ) ^ (d - 1) := by positivity
  rw [Real.logb_mul (by positivity) hL.ne', Real.logb_mul (by norm_num) hpow.ne',
    Real.logb_pow, Nat.cast_sub hd]
  have hN : (n : ℝ) ^ d ≠ 0 := by positivity
  field_simp
  ring

/-- The gap tends to `0`. -/
theorem tendsto_gap {n σ : ℕ} (hn : 2 ≤ n) (hσ : 2 ≤ σ) :
    Tendsto (fun d : ℕ => (1 - 1 / (p1 n : ℝ)) - decayRate n d σ) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (rateGapBoundTendsto_proved n σ hn hσ)
  · filter_upwards [eventually_ge_atTop 1] with d hd
    exact (rateGap_proved n d σ hn hd hσ).1
  · filter_upwards [eventually_ge_atTop 1] with d hd
    exact (rateGap_proved n d σ hn hd hσ).2

theorem rateLimit_proved : rateLimitStatement := by
  intro n σ hn hσ
  have h := (tendsto_const_nhds (x := (1 - 1 / (p1 n : ℝ)))).sub (tendsto_gap hn hσ)
  simp only [sub_sub_cancel, sub_zero] at h
  exact h

theorem rateUniversality_proved : rateUniversalityStatement := by
  intro n m σ hn hm hσ hnm
  refine ⟨1 - 1 / (p1 n : ℝ), rateLimit_proved n σ hn hσ, ?_⟩
  rw [hnm]
  exact rateLimit_proved m σ hm hσ

theorem rateEvenClass_proved : rateEvenClassStatement := by
  intro n σ hn hev hσ
  have h := rateLimit_proved n σ hn hσ
  have h2 : p1 n = 2 := Nat.minFac_eq_two_iff n |>.mpr (even_iff_two_dvd.mp hev)
  rw [h2] at h
  norm_num at h ⊢
  exact h

theorem ratePrimeClass_proved : ratePrimeClassStatement := by
  intro p σ hp hσ
  have h := rateLimit_proved p σ hp.two_le hσ
  rwa [show p1 p = p from hp.minFac_eq] at h

theorem rateExtremalClass_proved : rateExtremalClassStatement := by
  intro n hn
  have h2 : (2 : ℝ) ≤ (p1 n : ℝ) := by exact_mod_cast p1_two_le hn
  have hp0 : (0 : ℝ) < (p1 n : ℝ) := by linarith
  constructor
  · have : 1 / (p1 n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    linarith
  · constructor
    · intro h
      have h' : (p1 n : ℝ) = 2 := by
        field_simp at h
        linarith
      have h'' : p1 n = 2 := by exact_mod_cast h'
      exact even_iff_two_dvd.mpr ((Nat.minFac_eq_two_iff n).mp h'')
    · intro hev
      have h'' : p1 n = 2 := (Nat.minFac_eq_two_iff n).mpr (even_iff_two_dvd.mp hev)
      rw [h'']
      norm_num

theorem rateFloor_proved : rateFloorStatement := by
  intro n σ hn hσ ε hε
  have h := rateLimit_proved n σ hn hσ
  have hext := (rateExtremalClass_proved n hn).1
  have hev := (h.eventually (eventually_gt_nhds (show 1 - 1 / (p1 n : ℝ) - ε <
    1 - 1 / (p1 n : ℝ) by linarith)))
  obtain ⟨D, hD⟩ := eventually_atTop.mp hev
  exact ⟨D, fun d hd => by linarith [hD d hd]⟩

theorem rateLaw_proved : rateLawStatement :=
  ⟨rateBounds_proved, rateGap_proved, rateGapBoundTendsto_proved, rateLimit_proved,
    rateUniversality_proved, rateEvenClass_proved, ratePrimeClass_proved,
    rateExtremalClass_proved, rateFloor_proved⟩

/-! ## Proposition 10.2: the log-ratio sandwich and parts (i), (ii) -/

section Inversion

variable {p σ d : ℕ}

theorem probUnif_pos {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ) :
    0 < probUnif n d σ := by
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast (show 0 < σ by omega)
  unfold probUnif
  exact div_pos (numSS_pos hn hd hσ) (pow_pos hσ0 _)

theorem p1_succ_of_odd_prime (hp : p.Prime) (hp3 : 3 ≤ p) : p1 (p + 1) = 2 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hev : Even (p + 1) := hodd.add_one
  exact (Nat.minFac_eq_two_iff (p + 1)).mpr (even_iff_two_dvd.mp hev)

/-- `log_σ P_{(p+1)^d} − log_σ P_{p^d}` is sandwiched by `φ(d) ∓ (log terms)`. -/
theorem logRatio_bounds (hp : p.Prime) (hp3 : 3 ≤ p) (hσ : 2 ≤ σ) (hd : 1 ≤ d) :
    phi p (d : ℝ) - Real.logb (σ : ℝ) (2 * Real.logb 2 (p : ℝ) * (p : ℝ) ^ (d - 1)) ≤
        Real.logb (σ : ℝ) (probUnif (p + 1) d σ) - Real.logb (σ : ℝ) (probUnif p d σ) ∧
      Real.logb (σ : ℝ) (probUnif (p + 1) d σ) - Real.logb (σ : ℝ) (probUnif p d σ) ≤
        phi p (d : ℝ) +
          Real.logb (σ : ℝ) (2 * Real.logb 2 ((p : ℝ) + 1) * ((p : ℝ) + 1) ^ (d - 1)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ p + 1 := by omega
  rw [logb_probUnif hq2 hd hσ, logb_probUnif hp2 hd hσ]
  have a1 := logb_numSS_ge hq2 hd hσ
  have a2 := logb_numSS_le hq2 hd hσ
  have b1 := logb_numSS_ge hp2 hd hσ
  have b2 := logb_numSS_le hp2 hd hσ
  rw [p1_succ_of_odd_prime hp hp3] at a1 a2
  rw [show p1 p = p from hp.minFac_eq] at b1 b2
  push_cast at a1 a2 ⊢
  rw [phi_natCast]
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have e : (p : ℝ) ^ d / (p : ℝ) = (1 / (p : ℝ)) * (p : ℝ) ^ d := by
    field_simp
  rw [e] at b1 b2
  constructor
  · nlinarith
  · nlinarith

theorem inversionProofLogRatio_proved : inversionProofLogRatioStatement := by
  intro p σ d hp hp3 hσ hd
  have h1 : 2 ≤ p + 1 := by have := hp.two_le; omega
  rw [Real.logb_div (probUnif_pos h1 hd hσ).ne' (probUnif_pos hp.two_le hd hσ).ne']
  exact logRatio_bounds hp hp3 hσ hd

theorem inversionComposite_proved : inversionCompositeStatement := by
  intro p σ d hp hp3 hσ hd hyp
  have h1 : 2 ≤ p + 1 := by have := hp.two_le; omega
  have hσ1 : (1 : ℝ) < σ := by exact_mod_cast (show 1 < σ by omega)
  have hb := (logRatio_bounds hp hp3 hσ hd).1
  have hlt : Real.logb (σ : ℝ) (probUnif p d σ) < Real.logb (σ : ℝ) (probUnif (p + 1) d σ) := by
    linarith
  exact (Real.logb_lt_logb_iff hσ1 (probUnif_pos hp.two_le hd hσ)
    (probUnif_pos h1 hd hσ)).mp hlt

theorem inversionPrime_proved : inversionPrimeStatement := by
  intro p σ d hp hp3 hσ hd hyp
  have h1 : 2 ≤ p + 1 := by have := hp.two_le; omega
  have hσ1 : (1 : ℝ) < σ := by exact_mod_cast (show 1 < σ by omega)
  have hb := (logRatio_bounds hp hp3 hσ hd).2
  have hlt : Real.logb (σ : ℝ) (probUnif (p + 1) d σ) < Real.logb (σ : ℝ) (probUnif p d σ) := by
    linarith
  exact (Real.logb_lt_logb_iff hσ1 (probUnif_pos h1 hd hσ)
    (probUnif_pos hp.two_le hd hσ)).mp hlt

end Inversion

/-! ## Proposition 10.2: the sign pattern of `φ` and `d_c(p) = p ln 2 + O(1)` -/

section Phi

variable {p : ℕ}

/-- `φ(x) = p^x · ((1 − 1/p) − ½ (1 + 1/p)^x)`. -/
theorem phi_eq_mul (hp : 1 ≤ p) (x : ℝ) :
    phi p x = (p : ℝ) ^ x * ((1 - 1 / (p : ℝ)) - (1 / 2) * (1 + 1 / (p : ℝ)) ^ x) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  have hsplit : (p : ℝ) + 1 = (p : ℝ) * (1 + 1 / (p : ℝ)) := by field_simp
  unfold phi
  rw [hsplit, Real.mul_rpow hP.le (by positivity)]
  ring

/-- `(1 + 1/p)^{d_c(p)} = 2 − 2/p`. -/
theorem q_rpow_dc (hp : 2 ≤ p) : (1 + 1 / (p : ℝ)) ^ dc p = 2 - 2 / (p : ℝ) := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : (1 : ℝ) < 1 + 1 / (p : ℝ) := by
    have : (0 : ℝ) < 1 / (p : ℝ) := by positivity
    linarith
  have hlq : 0 < Real.log (1 + 1 / (p : ℝ)) := Real.log_pos hq
  have h2 : (0 : ℝ) < 2 - 2 / (p : ℝ) := by
    have : 2 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  rw [Real.rpow_def_of_pos (by linarith), dc, mul_div_cancel₀ _ hlq.ne', Real.exp_log h2]

/-- `φ(x) = ½ p^x ((1 + 1/p)^{d_c} − (1 + 1/p)^x)`. -/
theorem phi_eq_half (hp : 2 ≤ p) (x : ℝ) :
    phi p x = (1 / 2) * (p : ℝ) ^ x *
      ((1 + 1 / (p : ℝ)) ^ dc p - (1 + 1 / (p : ℝ)) ^ x) := by
  rw [phi_eq_mul (by omega), q_rpow_dc hp]
  ring

theorem phiSign_proved : phiSignStatement := by
  intro p hp hp3
  have hp2 : 2 ≤ p := hp.two_le
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq : (1 : ℝ) < 1 + 1 / (p : ℝ) := by
    have : (0 : ℝ) < 1 / (p : ℝ) := by positivity
    linarith
  have hpos : ∀ x : ℝ, 0 < (1 / 2 : ℝ) * (p : ℝ) ^ x := fun x => by
    have := Real.rpow_pos_of_pos hP x
    positivity
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [phi_eq_half hp2]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h0 | h0
      · exact absurd h0 (hpos x).ne'
      · have h1 : (1 + 1 / (p : ℝ)) ^ x = (1 + 1 / (p : ℝ)) ^ dc p := by linarith
        rcases lt_trichotomy x (dc p) with hlt | heq | hgt
        · have := Real.rpow_lt_rpow_of_exponent_lt hq hlt
          linarith
        · exact heq
        · have := Real.rpow_lt_rpow_of_exponent_lt hq hgt
          linarith
    · intro h
      rw [h, sub_self, mul_zero]
  · rw [phi_eq_half hp2]
    apply mul_pos (hpos x)
    have := Real.rpow_lt_rpow_of_exponent_lt hq hx
    linarith
  · rw [phi_eq_half hp2]
    apply mul_neg_of_pos_of_neg (hpos x)
    have := Real.rpow_lt_rpow_of_exponent_lt hq hx
    linarith

/-- Two-sided bounds `p ln 2 − 2 ≤ d_c(p) ≤ (p + 1) ln 2`, and `0 ≤ d_c(p)`. -/
theorem dc_bounds (hp : 2 ≤ p) :
    0 ≤ dc p ∧ (p : ℝ) * Real.log 2 - 2 ≤ dc p ∧ dc p ≤ ((p : ℝ) + 1) * Real.log 2 := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < p := by linarith
  set L := Real.log (2 - 2 / (p : ℝ)) with hLdef
  set l := Real.log (1 + 1 / (p : ℝ)) with hldef
  have h2p : 2 / (p : ℝ) ≤ 1 := by rw [div_le_one hP0]; linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hLle : L ≤ Real.log 2 := by
    apply Real.log_le_log (by linarith)
    have : (0 : ℝ) ≤ 2 / (p : ℝ) := by positivity
    linarith
  -- `L = log 2 + log (1 − 1/p) ≥ log 2 − 1/(p − 1)`
  have hLge : Real.log 2 - 1 / ((p : ℝ) - 1) ≤ L := by
    have hsplit : (2 : ℝ) - 2 / (p : ℝ) = 2 * (1 - 1 / (p : ℝ)) := by ring
    have h1p : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
      have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hP
      linarith
    rw [hLdef, hsplit, Real.log_mul (by norm_num) h1p.ne']
    have h := Real.one_sub_inv_le_log_of_pos h1p
    have e : 1 - (1 - 1 / (p : ℝ))⁻¹ = -(1 / ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [e] at h
    linarith
  have hl_le : l ≤ 1 / (p : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (p : ℝ) by positivity)
    rw [hldef]; linarith
  have hl_ge : 1 / ((p : ℝ) + 1) ≤ l := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + 1 / (p : ℝ) by positivity)
    have e : 1 - (1 + 1 / (p : ℝ))⁻¹ = 1 / ((p : ℝ) + 1) := by
      field_simp
      ring
    rw [e] at h
    rw [hldef]; exact h
  have hl0 : 0 < l := lt_of_lt_of_le (by positivity) hl_ge
  have hdc : dc p = L / l := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hdc]; positivity
  · -- `dc ≥ p L ≥ p log 2 − p/(p−1) ≥ p log 2 − 2`
    have h1 : (p : ℝ) * L ≤ L / l := by
      rw [le_div_iff₀ hl0]
      calc (p : ℝ) * L * l ≤ (p : ℝ) * L * (1 / (p : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hl_le; positivity
        _ = L := by field_simp
    have h2 : (p : ℝ) * (1 / ((p : ℝ) - 1)) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ (by linarith)]
      linarith
    have h3 : (p : ℝ) * (Real.log 2 - 1 / ((p : ℝ) - 1)) ≤ (p : ℝ) * L :=
      mul_le_mul_of_nonneg_left hLge hP0.le
    rw [hdc]
    nlinarith
  · -- `dc ≤ (p + 1) L ≤ (p + 1) log 2`
    have h1 : L / l ≤ ((p : ℝ) + 1) * L := by
      rw [div_le_iff₀ hl0]
      calc L = ((p : ℝ) + 1) * L * (1 / ((p : ℝ) + 1)) := by field_simp
        _ ≤ ((p : ℝ) + 1) * L * l := by
            apply mul_le_mul_of_nonneg_left hl_ge; positivity
    rw [hdc]
    calc L / l ≤ ((p : ℝ) + 1) * L := h1
      _ ≤ ((p : ℝ) + 1) * Real.log 2 := by
          apply mul_le_mul_of_nonneg_left hLle; positivity

theorem dcAsymptotic_proved : dcAsymptoticStatement := by
  refine ⟨2, 2, fun p _hp hp2 => ?_⟩
  obtain ⟨-, h1, h2⟩ := dc_bounds hp2
  have hl := Real.log_two_lt_d9
  rw [abs_le]
  constructor
  · linarith
  · nlinarith

end Phi

/-! ## Proposition 10.2: the bounded window (explicit constant `C = 20`) -/

section Window

/-- `φ(x) = (1 − 1/p) p^x (1 − (1 + 1/p)^{x − d_c(p)})`. -/
theorem phi_eq_dc {p : ℕ} (hp : 2 ≤ p) (x : ℝ) :
    phi p x = (1 - 1 / (p : ℝ)) * (p : ℝ) ^ x * (1 - (1 + 1 / (p : ℝ)) ^ (x - dc p)) := by
  have hq0 : (0 : ℝ) < 1 + 1 / (p : ℝ) := by positivity
  rw [phi_eq_mul (by omega)]
  have h : (1 + 1 / (p : ℝ)) ^ x =
      (1 + 1 / (p : ℝ)) ^ dc p * (1 + 1 / (p : ℝ)) ^ (x - dc p) := by
    rw [← Real.rpow_add hq0]
    congr 1
    ring
  rw [h, q_rpow_dc hp]
  ring

/-- `log_σ X ≤ log₂ X` for `X ≥ 1`, `σ ≥ 2`. -/
theorem logb_le_logb_two {σ : ℕ} (hσ : 2 ≤ σ) {X : ℝ} (hX : 1 ≤ X) :
    Real.logb (σ : ℝ) X ≤ Real.logb 2 X := by
  unfold Real.logb
  apply div_le_div_of_nonneg_left (Real.log_nonneg hX) (Real.log_pos (by norm_num))
  apply Real.log_le_log (by norm_num)
  exact_mod_cast hσ

/-- `log₂ m ≤ m`. -/
theorem logb_two_le_self (m : ℕ) (hm : 1 ≤ m) : Real.logb 2 (m : ℝ) ≤ m := by
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hm), Real.rpow_natCast]
  exact_mod_cast (Nat.lt_two_pow_self (n := m)).le

/-- `1 ≤ log₂ m` for `m ≥ 2`. -/
theorem one_le_logb_two {m : ℝ} (hm : 2 ≤ m) : 1 ≤ Real.logb 2 m := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
  exact hm

/-- `(k + 1) P ≤ P^{k+1}` for `P ≥ 2`. -/
theorem mul_le_pow_succ {P : ℝ} (hP : 2 ≤ P) (k : ℕ) : ((k : ℝ) + 1) * P ≤ P ^ (k + 1) := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ P - 1 by linarith) k
  rw [show 1 + (P - 1) = P by ring] at h
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : (k : ℝ) + 1 ≤ P ^ k := by nlinarith
  rw [pow_succ]
  nlinarith

/-- `log_σ(2 a m^k) ≤ 1 + (k + 1) log₂ m` whenever `1 ≤ a ≤ m` and `σ ≥ 2`
(used with `a = log₂ p ≤ m = p`, resp. `a = log₂(p+1) ≤ m = p + 1`). -/
theorem logb_prefactor_le {σ : ℕ} (hσ : 2 ≤ σ) {a m : ℝ} (ha : 1 ≤ a) (ham : a ≤ m) (k : ℕ) :
    Real.logb (σ : ℝ) (2 * a * m ^ k) ≤ 1 + ((k : ℝ) + 1) * Real.logb 2 m := by
  have hm1 : 1 ≤ m := le_trans ha ham
  have hm0 : 0 < m := by linarith
  have hmk : 1 ≤ m ^ k := one_le_pow₀ hm1
  have hX : 1 ≤ 2 * a * m ^ k := by nlinarith
  calc Real.logb (σ : ℝ) (2 * a * m ^ k) ≤ Real.logb 2 (2 * a * m ^ k) :=
        logb_le_logb_two hσ hX
    _ ≤ Real.logb 2 (2 * m * m ^ k) := by
        apply (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).mpr
        gcongr
    _ = 1 + ((k : ℝ) + 1) * Real.logb 2 m := by
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) hm0.ne',
          Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
        ring

/-- Part (i) of the window: below `d_c(p) − 20` the hypothesis of (i) holds. -/
theorem window_i {p σ d : ℕ} (hp3 : 3 ≤ p) (hσ : 2 ≤ σ) (hd : 1 ≤ d)
    (hwin : (d : ℝ) ≤ dc p - 20) :
    Real.logb (σ : ℝ) (2 * Real.logb 2 (p : ℝ) * (p : ℝ) ^ (d - 1)) < phi p (d : ℝ) := by
  have hp2 : 2 ≤ p := by omega
  have hP : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  obtain ⟨hdc0, -, hdcle⟩ := dc_bounds hp2
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h07 : ((p : ℝ) + 1) * Real.log 2 ≤ ((p : ℝ) + 1) * 0.7 := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hPbig : (29 : ℝ) ≤ p := by linarith
  have hL1 : 1 ≤ Real.logb 2 (p : ℝ) := one_le_logb_two (by linarith)
  have hLP : Real.logb 2 (p : ℝ) ≤ p := logb_two_le_self p (by omega)
  have hlhs := logb_prefactor_le hσ hL1 hLP (d - 1)
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · -- `d = 1`: `φ(1) = (p − 3)/2`
    have hd1' : d = 1 := by omega
    subst hd1'
    rw [phi_natCast]
    simp only [Nat.sub_self, Nat.cast_zero, zero_add, one_mul, pow_one] at hlhs ⊢
    -- `log₂ p < (p − 5)/2`
    have hlogP : Real.log (p : ℝ) ≤ (p : ℝ) / 8 + 3 * Real.log 2 - 1 := by
      have h8 : Real.log (p : ℝ) = Real.log 8 + Real.log ((p : ℝ) / 8) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]
        congr 1
        ring
      have h8' : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      have hle := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (p : ℝ) / 8 by positivity)
      linarith
    have hL : Real.logb 2 (p : ℝ) < ((p : ℝ) - 5) / 2 := by
      unfold Real.logb
      rw [div_lt_iff₀ (Real.log_pos (by norm_num))]
      nlinarith
    have hP0 : (0 : ℝ) < p := by linarith
    have e : (1 - 1 / (p : ℝ)) * (p : ℝ) - 1 / 2 * ((p : ℝ) + 1) = ((p : ℝ) - 3) / 2 := by
      field_simp
      ring
    rw [e]
    linarith
  · -- `d ≥ 2`
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 by omega] at hlhs ⊢
    rw [phi_eq_dc hp2, show ((k + 2 : ℕ) : ℝ) = ((k + 2 : ℕ) : ℝ) from rfl,
      Real.rpow_natCast]
    set q : ℝ := 1 + 1 / (p : ℝ) with hq
    set u : ℝ := q ^ (((k + 2 : ℕ) : ℝ) - dc p) with hu
    have hP0 : (0 : ℝ) < p := by linarith
    have hq1 : 1 ≤ q := by
      have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith
    have hq0 : 0 < q := by linarith
    have hu0 : 0 ≤ u := Real.rpow_nonneg hq0.le _
    -- `u · q^20 ≤ 1`
    have huq : u * q ^ (20 : ℝ) ≤ 1 := by
      have h1 : u ≤ q ^ (-(20 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      rw [Real.rpow_neg hq0.le] at h1
      have h2 : 0 < q ^ (20 : ℝ) := Real.rpow_pos_of_pos hq0 _
      calc u * q ^ (20 : ℝ) ≤ (q ^ (20 : ℝ))⁻¹ * q ^ (20 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 h2.le
        _ = 1 := inv_mul_cancel₀ h2.ne'
    -- Bernoulli: `q^20 ≥ 1 + 20/p`
    have hbern : 1 + 20 * (1 / (p : ℝ)) ≤ q ^ (20 : ℝ) :=
      one_add_mul_self_le_rpow_one_add (by
        have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        linarith) (by norm_num)
    have hu1 : u * ((p : ℝ) + 20) ≤ p := by
      have h3 : u * (1 + 20 * (1 / (p : ℝ))) ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_left hbern hu0) huq
      have e : u * ((p : ℝ) + 20) = (u * (1 + 20 * (1 / (p : ℝ)))) * p := by
        field_simp
      rw [e]
      nlinarith
    -- `(p − 1)(1 − u) ≥ 20/3`
    have hkey : (20 : ℝ) / 3 ≤ ((p : ℝ) - 1) * (1 - u) := by nlinarith
    have hpow := mul_le_pow_succ (show (2 : ℝ) ≤ p by linarith) k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hPk : 0 < (p : ℝ) ^ (k + 1) := by positivity
    have e : (1 - 1 / (p : ℝ)) * (p : ℝ) ^ (k + 2) * (1 - u) =
        ((p : ℝ) - 1) * (1 - u) * (p : ℝ) ^ (k + 1) := by
      field_simp
      ring
    rw [e]
    have hlhs' : 1 + (((k + 1 : ℕ) : ℝ) + 1) * Real.logb 2 (p : ℝ) ≤
        3 * (p : ℝ) ^ (k + 1) := by
      push_cast
      nlinarith
    nlinarith

/-- Part (ii) of the window: above `d_c(p) + 20` the hypothesis of (ii) holds. -/
theorem window_ii {p σ d : ℕ} (hp3 : 3 ≤ p) (hσ : 2 ≤ σ)
    (hwin : dc p + 20 ≤ (d : ℝ)) :
    phi p (d : ℝ) <
      -Real.logb (σ : ℝ) (2 * Real.logb 2 ((p : ℝ) + 1) * ((p : ℝ) + 1) ^ (d - 1)) := by
  have hp2 : 2 ≤ p := by omega
  have hP : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  obtain ⟨hdc0, -, -⟩ := dc_bounds hp2
  have hd20 : (20 : ℝ) ≤ d := by linarith
  have hd2 : 2 ≤ d := by
    have : (2 : ℝ) ≤ d := by linarith
    exact_mod_cast this
  have hL1 : 1 ≤ Real.logb 2 ((p : ℝ) + 1) := one_le_logb_two (by linarith)
  have hLP : Real.logb 2 ((p : ℝ) + 1) ≤ (p : ℝ) + 1 := by
    have h := logb_two_le_self (p + 1) (by omega)
    push_cast at h
    exact h
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hlhs := logb_prefactor_le hσ hL1 hLP (k + 2 - 1)
  rw [show k + 2 - 1 = k + 1 by omega] at hlhs ⊢
  rw [phi_eq_dc hp2, Real.rpow_natCast]
  set q : ℝ := 1 + 1 / (p : ℝ) with hq
  set u : ℝ := q ^ (((k + 2 : ℕ) : ℝ) - dc p) with hu
  have hP0 : (0 : ℝ) < p := by linarith
  have hq1 : 1 ≤ q := by
    have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    linarith
  have hq0 : 0 < q := by linarith
  have hu20 : q ^ (20 : ℝ) ≤ u := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hbern : 1 + 20 * (1 / (p : ℝ)) ≤ q ^ (20 : ℝ) :=
    one_add_mul_self_le_rpow_one_add (by
      have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith) (by norm_num)
  have hu1 : 20 ≤ (u - 1) * p := by
    have h3 : 1 + 20 * (1 / (p : ℝ)) ≤ u := le_trans hbern hu20
    have e : (1 + 20 * (1 / (p : ℝ)) - 1) * p = 20 := by field_simp; ring
    nlinarith
  have hkey : (40 : ℝ) / 3 ≤ ((p : ℝ) - 1) * (u - 1) := by nlinarith
  have hpow := mul_le_pow_succ (show (2 : ℝ) ≤ p by linarith) k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hPk : 0 < (p : ℝ) ^ (k + 1) := by positivity
  have e : (1 - 1 / (p : ℝ)) * (p : ℝ) ^ (k + 2) * (1 - u) =
      -(((p : ℝ) - 1) * (u - 1) * (p : ℝ) ^ (k + 1)) := by
    field_simp
    ring
  rw [e]
  have hlhs' : 1 + (((k + 1 : ℕ) : ℝ) + 1) * Real.logb 2 ((p : ℝ) + 1) ≤
      3 * (p : ℝ) ^ (k + 1) := by
    push_cast
    nlinarith
  nlinarith

end Window

/-- The window statement with the explicit constant `C = 20`. -/
theorem inversionExplicitWindow_proved : inversionExplicitWindowStatement := by
  refine ⟨20, fun p σ d _hp hp3 hσ hd => ⟨fun h => window_i hp3 hσ hd h, fun h => window_ii hp3 hσ h⟩⟩

theorem inversionWindow_proved : inversionWindowStatement := by
  refine ⟨20, fun p σ d hp hp3 hσ hd => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact inversionComposite_proved p σ d hp hp3 hσ hd (window_i hp3 hσ hd h)
  · exact inversionPrime_proved p σ d hp hp3 hσ hd (window_ii hp3 hσ h)

theorem inversionLaw_proved : inversionLawStatement :=
  ⟨inversionComposite_proved, inversionPrime_proved, phiSign_proved, dcAsymptotic_proved,
    inversionExplicitWindow_proved, inversionWindow_proved⟩

end ShiftSym.P09
