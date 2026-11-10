/-
Phase H, group 06 (BoundsProbability): proofs of every frozen statement of
`Shiftsym/Paper/S06_BoundsProbability.lean` (paper §6 and Corollary 7.1).

Each `<X>_proved` has literally the type `∀ params, <X>Statement params`.
Ingredients:
* `P06_BoundsProbability_Gauss` — Gaussian-binomial algebra (product formula,
  polynomiality, envelope at `d ≤ 2`, strict decrease of envelope terms);
* `P06_BoundsProbability_Count` — counting (union bound, GJS and CG bounds,
  `sopf_d` count, `|S| ≤ naive − 1` for prime `n`, `d ≥ 3`, one order-`p₁`
  subgroup);
* `P06_BoundsProbability_Real` — real estimates (closed form of 6.3(ii), the
  comparison inequalities, decay-rate algebra);
* the certified theorems `enumeration_proved`, `lowerBound_proved`,
  `enumerationRHS_prime` of the existing development.
-/
import Shiftsym.Paper.Proofs.P06_BoundsProbability_Gauss
import Shiftsym.Paper.Proofs.P06_BoundsProbability_Count
import Shiftsym.Paper.Proofs.P06_BoundsProbability_Real

namespace ShiftSym.P06

open ShiftSym

/-! ## §6.1 preamble -/

theorem gaussPolynomial_proved : gaussPolynomialStatement := by
  intro d r
  refine ⟨gaussPoly d r, fun q hq => ?_⟩
  rw [gaussPoly_eval, gaussProd_eq_gaussBinom hq]

theorem gaussProdEq_proved : gaussProdEqStatement := by
  intro q d r hq
  exact gaussProd_eq_gaussBinom hq d r

theorem envelopeIntegral_proved : envelopeIntegralStatement := by
  intro n d σ hn
  rw [paperEnvelope, lowerEnvelope]
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [gaussProd_eq_gaussBinom hn, rdCoeff]
  push_cast
  ring

theorem preamble_proved : preambleStatement :=
  ⟨gaussPolynomial_proved, gaussProdEq_proved, envelopeIntegral_proved⟩

/-! ## Prose after Theorem 6.1 -/

theorem envelopeTwo_proved : envelopeTwoStatement := lowerEnvelope_two

theorem e21_proved (n σ : ℕ) : e21Statement n σ := by
  intro hn _ hσ
  have h := lowerBound_proved n 2 σ hn (by norm_num) hσ
  rw [lowerEnvelope_two] at h
  exact h

theorem d2IsE21_proved : d2IsE21Statement := by
  intro n σ
  unfold lowerBoundStatement e21Statement numSS
  rw [lowerEnvelope_two]

theorem primesMeetEnvelope_proved : primesMeetEnvelopeStatement := by
  intro n d σ hn hd hσ
  have h := lowerBound_proved n d σ hn hd hσ
  refine ⟨fun hp => (h.2.mpr hp).symm, fun hnp => ?_⟩
  exact lt_of_le_of_ne h.1 (fun heq => hnp (h.2.mp heq))

/-! ## Remark 6.2 -/

/-- `(q^d - 1)/(q - 1) = [d 1]_q` in `ℚ`, `q ≥ 2`. -/
theorem geom_div_eq {q : ℕ} (hq : 2 ≤ q) (d : ℕ) :
    ((q : ℚ) ^ d - 1) / ((q : ℚ) - 1) = (gaussBinom q d 1 : ℚ) := by
  have h := sub_one_mul_gaussBinom (by omega : 1 ≤ q) d
  have h1 : 1 ≤ q ^ d := Nat.one_le_pow _ _ (by omega)
  have hQ : ((q : ℚ) - 1) * (gaussBinom q d 1 : ℚ) = (q : ℚ) ^ d - 1 := by
    have : (((q - 1) * gaussBinom q d 1 : ℕ) : ℚ) = ((q ^ d - 1 : ℕ) : ℚ) := by rw [h]
    push_cast [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub h1] at this
    exact this
  have hne : (q : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    linarith
  rw [div_eq_iff hne, ← hQ]
  ring

theorem naiveBound_eq {q d σ : ℕ} (hq : 2 ≤ q) :
    naiveBound q d σ = (gaussBinom q d 1 : ℚ) * (σ : ℚ) ^ (q ^ (d - 1))
      - (σ : ℚ) * ((gaussBinom q d 1 : ℚ) - 1) := by
  rw [naiveBound, geom_div_eq hq]
  ring

theorem numSS_lt_naive {p d σ : ℕ} (pp : p.Prime) (hd : 3 ≤ d) (hσ : 2 ≤ σ) :
    (numSS p d σ : ℚ) < naiveBound p d σ := by
  have h := numSS_le_naive_sub_one pp hd hσ
  have hQ : (numSS p d σ : ℚ)
      ≤ (gaussBinom p d 1 : ℚ) * (σ : ℚ) ^ (p ^ (d - 1))
        - ((gaussBinom p d 1 : ℚ) - 1) * σ - 1 := by
    exact_mod_cast h
  rw [naiveBound_eq pp.two_le]
  linarith

theorem naiveAtTwo_proved : naiveAtTwoStatement := by
  intro n σ hn
  rw [naiveBound_eq hn, gaussBinom_two_one]
  push_cast
  ring

theorem primeCountFullSum_proved : primeCountFullSumStatement := by
  intro p d σ pp hd hσ
  have h := enumeration_proved p d σ pp.two_le hd hσ
  rw [enumerationRHS_prime pp] at h
  exact h

theorem naiveFalse_proved : naiveFalseStatement := by
  intro d hd hclaim
  have h := (hclaim 2 2 le_rfl le_rfl).2.mpr Nat.prime_two
  have hlt := numSS_lt_naive Nat.prime_two hd le_rfl
  rw [h] at hlt
  exact lt_irrefl _ hlt

theorem naiveCounterexample_proved : naiveCounterexampleStatement := by
  refine ⟨by norm_num [naiveBound], ?_⟩
  have h := enumeration_proved 2 3 2 (by norm_num) (by norm_num) (by norm_num)
  rw [enumerationRHS_prime Nat.prime_two] at h
  have h72 : lowerEnvelope 2 3 2 = 72 := by decide
  rw [h72] at h
  show Nat.card {s : Config 2 3 (Fin 2) // IsShiftSymmetric s} = 72
  exact_mod_cast h

theorem naiveCoincide_proved : naiveCoincideStatement := by
  intro p d σ pp hd hσ
  constructor
  · intro heq
    by_contra hd2
    have hlt := numSS_lt_naive (d := d) pp (by omega) hσ
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · intro hd2
    have hcount := primeCountFullSum_proved p d σ pp hd (by omega)
    have hQ : (numSS p d σ : ℚ) = (lowerEnvelope p d σ : ℚ) := by exact_mod_cast hcount
    rw [hQ]
    rcases (show d = 1 ∨ d = 2 by omega) with rfl | rfl
    · rw [lowerEnvelope_one, naiveBound_eq pp.two_le]
      have : gaussBinom p 1 1 = 1 := gaussBinom_self p 1
      rw [this]
      push_cast
      ring
    · rw [lowerEnvelope_two, naiveAtTwo_proved p σ pp.two_le]
      push_cast
      ring

theorem truncationCoincide_proved : truncationCoincideStatement := by
  intro p d σ pp hd hσ
  constructor
  · intro heq
    by_contra hd2
    have hd3 : 3 ≤ d := by omega
    rw [min_eq_right (by omega : 2 ≤ d), lowerEnvelope_split (by omega : 2 ≤ d)] at heq
    have hpos := envelope_tail_pos (q := p) (d := d) (σ := σ) pp.two_le hσ hd3
    linarith
  · intro hd2
    rw [min_eq_left hd2]
    rfl

theorem remarkNaive_proved : remarkNaiveStatement :=
  ⟨naiveAtTwo_proved, naiveFalse_proved, naiveCounterexample_proved,
    primeCountFullSum_proved, naiveCoincide_proved, truncationCoincide_proved⟩

/-! ## `sopf_d` -/

theorem sopfFormula_proved : sopfFormulaStatement := by
  intro n d _ _
  rw [sopfD]
  push_cast
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [geom_div_eq (Nat.prime_of_mem_primeFactors hp).two_le]

theorem sopfCount_proved : sopfCountStatement := by
  intro n d hn _
  exact sopf_count hn

/-! ## Theorem 6.3 -/

theorem upperUnion_proved : upperUnionStatement := by
  intro n d σ hn _ _
  exact numSS_le_unionRHS hn

theorem upperClosed_proved : upperClosedStatement := by
  intro n d σ hn hd hσ
  calc (numSS n d σ : ℝ) ≤ (unionRHS n d σ : ℝ) := by exact_mod_cast numSS_le_unionRHS hn
    _ ≤ _ := unionRHS_le_closed hn hd hσ

theorem upperBounds_proved : upperBoundsStatement :=
  ⟨upperUnion_proved, upperClosed_proved⟩

/-! ## The comparison paragraph -/

theorem unionImpliesRate_proved : unionImpliesRateStatement := by
  intro n d σ hn hd hσ
  exact unionRHS_le_rateRHS hn hd hσ

theorem rateBound_proved : rateBoundStatement := by
  intro n d σ hn hd hσ
  calc (numSS n d σ : ℝ) ≤ (unionRHS n d σ : ℝ) := by exact_mod_cast numSS_le_unionRHS hn
    _ ≤ _ := unionRHS_le_rateRHS hn hd hσ

theorem gjsBound_proved : gjsBoundStatement := by
  intro n d σ hn _ _
  exact numSS_le_gjs hn

theorem cgBound_proved : cgBoundStatement := by
  intro n d σ hn _ hσ
  exact numSS_le_cg hn (by omega)

theorem cgSharpen_proved : cgSharpenStatement := by
  intro n d h
  exact cg_sharpen h

theorem tieAtTwo_proved : tieAtTwoStatement := by
  intro d _
  have hpf : Nat.primeFactors 2 = {2} := Nat.prime_two.primeFactors
  refine ⟨?_, fun σ => ?_⟩
  · rw [sopfD, hpf, Finset.sum_singleton, gaussBinom_two_d_one]
  · rw [unionRHS, hpf, Finset.sum_singleton, gaussBinom_two_d_one, Nat.prime_two.minFac_eq]

theorem evenImprove_proved : evenImproveStatement := by
  intro n d he hn hd
  exact even_improve he hn hd

theorem oddExponent_proved : oddExponentStatement := by
  intro n d hn hd ho
  exact odd_exponent hn hd ho

theorem e22Bound_proved : e22BoundStatement := by
  intro n σ hn hσ
  calc (numSS n 2 σ : ℝ) ≤ closedPrefactor n 2 * (σ : ℝ) ^ (((n ^ 2 : ℕ) : ℝ) / 2) :=
        upperClosed_proved n 2 σ hn (by norm_num) hσ
    _ ≤ _ := closed_le_e22 hn hσ

theorem e22Sharpen_proved : e22SharpenStatement := by
  intro n σ hn hσ
  exact e22_sharpen hn hσ

theorem comparison_proved : comparisonStatement :=
  ⟨unionImpliesRate_proved, rateBound_proved, gjsBound_proved, cgBound_proved,
    cgSharpen_proved, tieAtTwo_proved, evenImprove_proved, oddExponent_proved,
    e22Bound_proved, e22Sharpen_proved⟩

/-! ## Corollary 7.1 -/

theorem probUnif_pos {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ) :
    0 < probUnif n d σ := by
  rw [probUnif]
  have hS : (0 : ℝ) < numSS n d σ := by exact_mod_cast numSS_pos σ hn hd (by omega)
  have hσ' : (0 : ℝ) < σ := by exact_mod_cast (by omega : 0 < σ)
  positivity

theorem decayRate_eq {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ) :
    decayRate n d σ = 1 - Real.logb σ (numSS n d σ) / ((n ^ d : ℕ) : ℝ) := by
  rw [decayRate, probUnif]
  have h := rate_eq (S := numSS n d σ) (N := n ^ d) (σ := σ) (numSS_pos σ hn hd (by omega))
    (Nat.pos_of_ne_zero (by positivity)) hσ
  push_cast at h ⊢
  exact h

theorem decayIdentity_proved : decayIdentityStatement := by
  intro n d σ hn hd hσ
  have hP := probUnif_pos hn hd hσ
  have hN : ((n ^ d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by positivity : n ^ d ≠ 0)
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast (by omega : 0 < σ)
  have hσ1 : (σ : ℝ) ≠ 1 := by exact_mod_cast (by omega : σ ≠ 1)
  rw [decayRate, div_mul_cancel₀ _ hN, Real.rpow_neg hσ0.le,
    Real.rpow_logb hσ0 hσ1 (by positivity), one_div, inv_inv]

theorem probSandwich_proved : probSandwichStatement := by
  intro n d σ hn hd hσ
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast (by omega : 0 < σ)
  have hX := rpow_half_pos (σ := σ) (N := n ^ d) (by omega)
  have hσN : (0 : ℝ) < (σ : ℝ) ^ (n ^ d) := by positivity
  refine ⟨?_, ?_⟩
  · have hF : (lowerEnvelope n d σ : ℝ) ≤ (numSS n d σ : ℝ) := by
      have := (lowerBound_proved n d σ hn hd hσ).1
      exact_mod_cast this
    rw [Real.rpow_neg hσ0.le, Real.rpow_natCast, probUnif, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hF (by positivity)
  · have hS := upperClosed_proved n d σ hn hd hσ
    set X := (σ : ℝ) ^ (((n ^ d : ℕ) : ℝ) / 2) with hXdef
    have hX2 : (σ : ℝ) ^ (n ^ d) = X ^ 2 := by rw [hXdef, rpow_half_sq]
    rw [Real.rpow_neg hσ0.le, ← hXdef, probUnif, hX2]
    calc (numSS n d σ : ℝ) / X ^ 2 ≤ (closedPrefactor n d * X) / X ^ 2 :=
          div_le_div_of_nonneg_right hS (by positivity)
      _ = closedPrefactor n d * X⁻¹ := by field_simp

theorem singleSubgroup_proved : singleSubgroupStatement := by
  intro n d σ hn hd _
  exact single_subgroup σ hn hd

theorem probSingleLowerIsRateLower_proved : probSingleLowerIsRateLowerStatement := by
  intro n d σ hn hd hσ
  have hp : n.minFac ∣ n ^ d := (Nat.minFac_dvd n).trans (dvd_pow_self n (by omega))
  have hpR : ((n.minFac : ℕ) : ℝ) ≠ 0 := by
    have := Nat.minFac_pos n
    positivity
  have hσR : (0 : ℝ) < σ := by exact_mod_cast (by omega : 0 < σ)
  rw [← Nat.cast_div hp hpR, Real.rpow_sub hσR, Real.rpow_natCast, Real.rpow_natCast]
  unfold probUnif
  rw [div_le_div_iff_of_pos_right (by positivity)]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem probSingleLower_proved : probSingleLowerStatement := by
  intro n d σ hn hd hσ
  exact (probSingleLowerIsRateLower_proved n d σ hn hd hσ).mpr (pow_le_numSS σ hn hd)

theorem decayUpper_proved : decayUpperStatement := by
  intro n d σ hn hd hσ
  rw [decayRate_eq hn hd hσ]
  have hp : n.minFac ∣ n ^ d := (Nat.minFac_dvd n).trans (dvd_pow_self n (by omega))
  have hmf : (0 : ℝ) < (n.minFac : ℝ) := by exact_mod_cast Nat.minFac_pos n
  have hN : (0 : ℝ) < ((n ^ d : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  have hσ1 : (1 : ℝ) < σ := by exact_mod_cast hσ
  have hS : (0 : ℝ) < numSS n d σ := by exact_mod_cast numSS_pos σ hn hd (by omega)
  have hlog : ((n ^ d : ℕ) : ℝ) / (n.minFac : ℝ) ≤ Real.logb σ (numSS n d σ) := by
    rw [← Nat.cast_div hp hmf.ne', Real.le_logb_iff_rpow_le hσ1 hS, Real.rpow_natCast]
    exact_mod_cast pow_le_numSS σ hn hd
  have h1 : 1 / (n.minFac : ℝ) = (((n ^ d : ℕ) : ℝ) / (n.minFac : ℝ)) / ((n ^ d : ℕ) : ℝ) := by
    field_simp
  have h2 : (((n ^ d : ℕ) : ℝ) / (n.minFac : ℝ)) / ((n ^ d : ℕ) : ℝ)
      ≤ Real.logb σ (numSS n d σ) / ((n ^ d : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hlog hN.le
  linarith

theorem decayLowerExplicit_proved : decayLowerExplicitStatement := by
  intro n d σ hn hd hσ
  rw [decayRate_eq hn hd hσ]
  have hN : (0 : ℝ) < ((n ^ d : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast (by omega : 0 < σ)
  have hσ1 : (1 : ℝ) < σ := by exact_mod_cast hσ
  have hS : (0 : ℝ) < numSS n d σ := by exact_mod_cast numSS_pos σ hn hd (by omega)
  have hK := closedPrefactor_pos hn hd
  have hX := rpow_half_pos (σ := σ) (N := n ^ d) (by omega)
  have hup := upperClosed_proved n d σ hn hd hσ
  have hlog : Real.logb σ (numSS n d σ)
      ≤ Real.logb σ (closedPrefactor n d) + ((n ^ d : ℕ) : ℝ) / 2 := by
    have := (Real.logb_le_logb hσ1 hS (by positivity)).mpr hup
    rw [Real.logb_mul hK.ne' hX.ne', Real.logb_rpow hσ0 hσ1.ne'] at this
    exact this
  have h2 : Real.logb σ (numSS n d σ) / ((n ^ d : ℕ) : ℝ)
      ≤ (Real.logb σ (closedPrefactor n d) + ((n ^ d : ℕ) : ℝ) / 2) / ((n ^ d : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hlog hN.le
  have h3 : (Real.logb σ (closedPrefactor n d) + ((n ^ d : ℕ) : ℝ) / 2) / ((n ^ d : ℕ) : ℝ)
      = Real.logb σ (closedPrefactor n d) / ((n ^ d : ℕ) : ℝ) + 1 / 2 := by
    field_simp
  linarith

/-- The explicit `o(1)` estimate: `log_σ K / N ≤ ε` once `N ≥ 6/(ε log 2)^2`. -/
theorem logb_closed_div_le {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ)
    {ε : ℝ} (hε : 0 < ε) (hNM : 6 / (ε * Real.log 2) ^ 2 ≤ ((n ^ d : ℕ) : ℝ)) :
    Real.logb σ (closedPrefactor n d) / ((n ^ d : ℕ) : ℝ) ≤ ε := by
  set N : ℝ := ((n ^ d : ℕ) : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  have hN1 : (1 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c := ε * Real.log 2 with hc
  have hcpos : 0 < c := mul_pos hε hlog2
  have hK1 := one_le_closedPrefactor hn hd
  have hK3 := closedPrefactor_le_three_N hn hd
  rw [← hNdef] at hK3
  have hlogK : 0 ≤ Real.log (closedPrefactor n d) := Real.log_nonneg hK1
  have hσlog : Real.log 2 ≤ Real.log σ :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hσ)
  -- `log(3N) ≤ c N`
  set y := Real.log (3 * N) with hy
  have hy0 : 0 ≤ y := Real.log_nonneg (by linarith)
  have hexp : y ^ 2 / 2 ≤ 3 * N := by
    have := Real.pow_div_factorial_le_exp y hy0 2
    rw [hy, Real.exp_log (by linarith)] at this
    simpa using this
  have h6 : 6 * N ≤ (c * N) ^ 2 := by
    have : 6 ≤ c ^ 2 * N := by
      rw [div_le_iff₀ (by positivity)] at hNM
      linarith
    nlinarith
  have hyc : y ≤ c * N := by
    have : y ^ 2 ≤ (c * N) ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ hy0 (by positivity) (by norm_num)).mp this
  have hlogK3 : Real.log (closedPrefactor n d) ≤ y :=
    Real.log_le_log (by linarith) hK3
  have hlogb : Real.logb σ (closedPrefactor n d) ≤ ε * N := by
    rw [Real.logb]
    calc Real.log (closedPrefactor n d) / Real.log σ
        ≤ Real.log (closedPrefactor n d) / Real.log 2 :=
          div_le_div_of_nonneg_left hlogK hlog2 hσlog
      _ ≤ (c * N) / Real.log 2 := div_le_div_of_nonneg_right (by linarith) hlog2.le
      _ = ε * N := by rw [hc]; field_simp
  rw [div_le_iff₀ hN]
  exact hlogb

theorem decayLowerUniform_proved : decayLowerUniformStatement := by
  intro ε hε
  refine ⟨⌈6 / (ε * Real.log 2) ^ 2⌉₊, fun n d σ hn hd hσ hM => ?_⟩
  have hNM : 6 / (ε * Real.log 2) ^ 2 ≤ ((n ^ d : ℕ) : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hM)
  have h1 := decayLowerExplicit_proved n d σ hn hd hσ
  have h2 := logb_closed_div_le hn hd hσ hε hNM
  linarith

theorem decayInterval_proved : decayIntervalStatement :=
  ⟨decayLowerUniform_proved, decayUpper_proved⟩

theorem probUnifCorollary_proved : probUnifCorollaryStatement :=
  ⟨probSandwich_proved, decayIdentity_proved, decayInterval_proved,
    decayLowerExplicit_proved, singleSubgroup_proved, probSingleLower_proved,
    probSingleLowerIsRateLower_proved⟩

end ShiftSym.P06
