/-
Phase H, group 10 — proofs of the frozen statements of Appendix A ("Proof of Theorem 6.1",
paper lines 1166–1342), `Shiftsym/Paper/S10_AppendixLemmas.lean`, namespace `ShiftSym.P10`.

Route. The analytic AUXILIARY claims (Lemma A.2, the product bound, conditions (I)/(II),
Lemma A.4's proviso and log condition) are proved as stated (helper `…_Analytic`). For the
counting claims we use the union interpretation of the truncations, certified on `Z_n^d`
(helper `…_Core`): for a subgroup `K` of order coprime to `p_1 ⋯ p_m`,

  q^m(1/|K|) = |Fix(K) ∩ ⋃_{C prime order p_i, i<m} Fix(C)|.

With `K = ⊥` this gives `q^k = |S|` (`qkEqCard`), the monotone chain `q^1 ≤ ⋯ ≤ q^k`
(monotonicity of a union — shorter than the paper's analytic proof of Lemma A.3, which
remains available through `decomposition`, (I), (II) as frozen auxiliary claims), and
`q^1 ≥ σ^{n^d/p_1} > F_d` at composite `n` (base cases, all `d ≥ 1`; the strict inequality
reuses the certified envelope estimate of `Lemmas/Ineq.lean`). With `K = ker(Z_n^d → T_j)`
(`|K| = p^j`, helper `…_Torus`) it gives Lemma A.1 and the union interpretation on `T_j`.

Options: none (no `set_option`). No `sorry`; axioms: propext, Classical.choice, Quot.sound.
-/
import Shiftsym.Paper.Proofs.P10_AppendixLemmas_Basic
import Shiftsym.Paper.Proofs.P10_AppendixLemmas_Analytic
import Shiftsym.Paper.Proofs.P10_AppendixLemmas_Core
import Shiftsym.Paper.Proofs.P10_AppendixLemmas_Torus

open scoped Classical

namespace ShiftSym.P10

open Finset

variable {n d : ℕ}

/-! ### `q^m(1)` as a union count on `Z_n^d` (`K = ⊥`) -/

theorem qm_eq_card [NeZero n] {m : ℕ} (hn : 2 ≤ n) (hm : m ≤ kOf n) (σ : ℕ) :
    qm n d σ m = (((lowSubs n d m).biUnion (fixedByA (Fin σ))).card : ℝ) := by
  have hcore := core_card (d := d) hm σ ⊥
    (by rw [AddSubgroup.card_bot]; exact Nat.coprime_one_left _)
  rw [AddSubgroup.card_bot, fixedByA_bot, Finset.univ_inter] at hcore
  have hbr := qTruncZBridge_proved' n d σ m 1 hn hm le_rfl
    (fun v => by rw [one_mul]; exact prod_primeAt_pow_dvd_pow (by omega) hm v)
  rw [qm, show (1 : ℝ) = ((1 : ℕ) : ℝ)⁻¹ by simp, hbr, ← hcore]
  push_cast
  rfl

theorem lowSubs_mono [NeZero n] {a b : ℕ} (hab : a ≤ b) : lowSubs n d a ⊆ lowSubs n d b := by
  intro C hC
  obtain ⟨hCP, i, hi, hCi⟩ := Finset.mem_filter.mp hC
  exact Finset.mem_filter.mpr ⟨hCP, i, by omega, hCi⟩

theorem lowSubs_top [NeZero n] : lowSubs n d (kOf n) = primeOrderSubs n d := by
  ext C
  simp only [lowSubs, Finset.mem_filter, and_iff_left_iff_imp]
  intro hC
  obtain ⟨i, hi, hiC⟩ := exists_primeAt (card_mem_primeFactors (mem_primeOrderSubs.mp hC))
  exact ⟨i, hi, hiC.symm⟩

theorem qm_mono [NeZero n] {a b : ℕ} (hn : 2 ≤ n) (hab : a ≤ b) (hb : b ≤ kOf n) (σ : ℕ) :
    qm n d σ a ≤ qm n d σ b := by
  rw [qm_eq_card hn (le_trans hab hb), qm_eq_card hn hb]
  exact_mod_cast Finset.card_le_card
    (Finset.biUnion_subset_biUnion_of_subset_left _ (lowSubs_mono hab))

/-- `q^1 ≥ σ^{n^d/p_1}`: one order-`p_1` subgroup already fixes that many configurations. -/
theorem q1_ge [NeZero n] (hn : 2 ≤ n) (hd : 1 ≤ d) (σ : ℕ) :
    ((σ ^ (n ^ d / n.minFac) : ℕ) : ℝ) ≤ qm n d σ 1 := by
  have pp : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨C, hC⟩ := exists_orderP_subgroup (d := d) pp (Nat.minFac_dvd n) hd
  have hmem : C ∈ lowSubs n d 1 :=
    Finset.mem_filter.mpr ⟨mem_primeOrderSubs.mpr (hC ▸ pp), 0, Nat.one_pos,
      by rw [hC, primeAt_zero hn]⟩
  rw [qm_eq_card hn (kOf_pos hn) σ]
  have hle := Finset.card_le_card (Finset.subset_biUnion_of_mem (fixedByA (Fin σ)) hmem)
  rw [card_fixedByA_fin, hC] at hle
  exact_mod_cast hle

/-- At composite `n` the envelope is beaten by a single fixed-set: `F_d < σ^{n^d/p_1}`
(the estimate of the certified `lowerEnvelope_lt_card`, Lemmas/LowerBound.lean). -/
theorem lowerEnvelope_lt_pow (hc : IsComposite n) (hd : 1 ≤ d) {σ : ℕ} (hσ : 2 ≤ σ) :
    lowerEnvelope n d σ < (σ : ℤ) ^ (n ^ d / n.minFac) := by
  have hn2 := hc.1
  set p := n.minFac with hpdef
  have pp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := n.minFac_dvd
  have hp2 : 2 ≤ p := pp.two_le
  have hsq : p * p ≤ n := by
    have h := Nat.minFac_sq_le_self (by omega : 0 < n) hc.2
    calc p * p = p ^ 2 := (sq p).symm
    _ ≤ n := h
  have hn4 : 4 ≤ n := le_trans (Nat.mul_le_mul hp2 hp2) hsq
  have hdiv2 : 2 ≤ n / p := by
    rw [Nat.le_div_iff_mul_le pp.pos]
    calc 2 * p ≤ p * p := Nat.mul_le_mul_right p hp2
    _ ≤ n := hsq
  have hexp : 2 * n ^ (d - 1) ≤ n ^ d / p := by
    have h1 : n ^ d = n ^ (d - 1) * n := by
      conv_lhs => rw [show d = (d - 1) + 1 by omega]
      ring
    rw [h1, Nat.mul_div_assoc _ hpn]
    calc 2 * n ^ (d - 1) = n ^ (d - 1) * 2 := by ring
    _ ≤ n ^ (d - 1) * (n / p) := Nat.mul_le_mul_left _ hdiv2
  have hKσ : (gaussBinom n d 1 + (d - 2) * 2 ^ d * n ^ d.choose 2 : ℕ)
      < σ ^ n ^ (d - 1) := by
    calc _ < 2 ^ n ^ (d - 1) := envelope_coeff_lt_two_pow hn4 hd
    _ ≤ σ ^ n ^ (d - 1) := Nat.pow_le_pow_left hσ _
  have hσpos : (0 : ℤ) < (σ : ℤ) ^ n ^ (d - 1) :=
    pow_pos (by exact_mod_cast (by omega : 0 < σ)) _
  calc lowerEnvelope n d σ
      ≤ ((gaussBinom n d 1 + (d - 2) * 2 ^ d * n ^ d.choose 2 : ℕ) : ℤ)
          * (σ : ℤ) ^ n ^ (d - 1) :=
        lowerEnvelope_le_K (by omega) (by omega) hd
    _ < (σ : ℤ) ^ n ^ (d - 1) * (σ : ℤ) ^ n ^ (d - 1) := by
        apply mul_lt_mul_of_pos_right ?_ hσpos
        exact_mod_cast hKσ
    _ = (σ : ℤ) ^ (2 * n ^ (d - 1)) := by
        rw [← pow_add]
        congr 1
        ring
    _ ≤ (σ : ℤ) ^ (n ^ d / p) :=
        pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ σ)) hexp

/-- `q^1 > F_d` at every composite `n`, every `d ≥ 1`. -/
theorem base_all (hc : IsComposite n) (hd : 1 ≤ d) {σ : ℕ} (hσ : 2 ≤ σ) :
    (lowerEnvelope n d σ : ℝ) < qm n d σ 1 := by
  have : NeZero n := ⟨by have := hc.1; omega⟩
  have h1 := lowerEnvelope_lt_pow hc hd hσ
  have h2 := q1_ge (d := d) hc.1 hd σ
  have h1' : (lowerEnvelope n d σ : ℝ) < ((σ ^ (n ^ d / n.minFac) : ℕ) : ℝ) := by
    exact_mod_cast h1
  linarith

/-! ### The frozen statements -/

theorem qkEqCard_proved : qkEqCardStatement := by
  intro n d σ hn _ _
  have : NeZero n := ⟨by omega⟩
  rw [qm_eq_card hn le_rfl σ, lowSubs_top, numSS_eq_filter]
  congr 2
  ext s
  rw [Finset.mem_filter, isShiftSymmetric_iff_mem_biUnion]
  simp only [Finset.mem_univ, true_and, Finset.mem_biUnion, fixedByA_eq_fixedByF]

theorem primeEquality_proved : primeEqualityStatement := primeEquality_proved'

theorem chainOverview_proved : chainOverviewStatement := by
  intro n d σ a b hc _ _ _ hab hb
  have : NeZero n := ⟨by have := hc.1; omega⟩
  exact qm_mono hc.1 hab hb σ

theorem baseAllDims_proved : baseAllDimsStatement := by
  intro n d σ hc hd hσ
  exact base_all hc hd hσ

theorem strictComposite_proved : strictCompositeStatement := strictComposite_proved'

theorem appendixOverview_proved : appendixOverviewStatement :=
  ⟨qkEqCard_proved, primeEquality_proved, chainOverview_proved, baseAllDims_proved,
    strictComposite_proved⟩

theorem lemA1Sandwich_proved : lemA1SandwichStatement := lemA1Sandwich_proved'

theorem lemA1UnionBound_proved : lemA1UnionBoundStatement := lemA1UnionBound_proved'

theorem lemA1_proved : lemA1Statement := ⟨lemA1Sandwich_proved, lemA1UnionBound_proved⟩

theorem rectTorus_proved : rectTorusStatement := rectTorus_proved'

theorem unionInterpretation_proved : unionInterpretationStatement :=
  unionInterpretation_proved'

theorem exponentIntegrality_proved : exponentIntegralityStatement :=
  exponentIntegrality_proved'

theorem lemA2Part1_proved : lemA2Part1Statement := lemA2Part1_proved'

theorem lemA2Part2_proved : lemA2Part2Statement := lemA2Part2_proved'

theorem lemA2Part3_proved : lemA2Part3Statement := lemA2Part3_proved'

theorem lemA2_proved : lemA2Statement := ⟨lemA2Part1_proved, lemA2Part2_proved, lemA2Part3_proved⟩

theorem lemA2ProductBound_proved : lemA2ProductBoundStatement := lemA2ProductBound_proved'

theorem lemA3Chain_proved : lemA3ChainStatement := by
  intro n d σ m hc _ _ _ _ hmk
  have : NeZero n := ⟨by have := hc.1; omega⟩
  exact qm_mono hc.1 (Nat.le_succ m) hmk σ

theorem decomposition_proved : decompositionStatement := decomposition_proved'

theorem condI_proved : condIStatement := condI_proved'

theorem condII_proved : condIIStatement := condII_proved'

theorem lemA4Base_proved : lemA4BaseStatement := by
  intro n d σ hc hσ hd
  exact base_all hc (by omega) hσ

theorem lemA4Proviso_proved : lemA4ProvisoStatement := lemA4Proviso_proved'

theorem lemA4LogCondition_proved : lemA4LogConditionStatement := lemA4LogCondition_proved'

theorem envelopeD1_proved : envelopeD1Statement := envelopeD1_proved'

theorem primeD1_proved : primeD1Statement := primeD1_proved'

theorem compositeD1_proved : compositeD1Statement := compositeD1_proved'

theorem envelopeD2_proved : envelopeD2Statement := envelopeD2_proved'

theorem baseD2_proved : baseD2Statement := by
  intro n σ hc hσ
  have h := base_all (d := 2) hc (by norm_num) hσ
  rw [envelopeD2_proved n σ hc.1 hσ] at h
  push_cast at h
  exact h

theorem proofLowDim_proved : proofLowDimStatement :=
  ⟨envelopeD1_proved, primeD1_proved, compositeD1_proved, envelopeD2_proved, baseD2_proved⟩

theorem proofOfThm61_proved : proofOfThm61Statement :=
  ⟨proofLowDim_proved, primeEquality_proved, qkEqCard_proved, lemA3Chain_proved,
    lemA4Base_proved, strictComposite_proved⟩

theorem gaussBinomEqProd_proved : gaussBinomEqProdStatement := gaussBinomEqProd_proved'

theorem qTruncZBridge_proved : qTruncZBridgeStatement := qTruncZBridge_proved'

end ShiftSym.P10
