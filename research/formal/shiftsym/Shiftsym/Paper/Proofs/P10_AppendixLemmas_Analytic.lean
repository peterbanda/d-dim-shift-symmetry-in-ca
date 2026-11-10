/-
Phase H, group 10 (Appendix A) — proof helpers, part 2 ("Analytic").

Real/natural-number inequalities of Appendix A:
* the numerical product bound `∏ (1 − 2^{−i}) ≥ 147/512 > 1/4` (all partial products) and
  the `tsum` identity;
* Lemma A.2 (coefficient estimates for the product-formula Gaussian binomial, real `q ≥ 2`);
* Lemma A.4's proviso `2^{n^{d−1}} ≥ 12 d n^D` and its log condition;
* conditions (I) and (II) of Lemma A.3.

No `sorry`; only the standard axioms.
-/
import Shiftsym.Paper.Proofs.P10_AppendixLemmas_Basic

namespace ShiftSym.P10

open Finset

/-! ### The numerical product bound -/

theorem prodIcc_eq_range (f : ℕ → ℝ) (M : ℕ) :
    ∏ i ∈ Finset.Icc 1 M, f i = ∏ i ∈ Finset.range M, f (i + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp [add_comm]

theorem two_zpow_neg (i : ℕ) : (2 : ℝ) ^ (-(i : ℤ)) = ((2 : ℝ) ^ i)⁻¹ := by
  rw [zpow_neg, zpow_natCast]

theorem prodBound_aux (M : ℕ) (hM : 3 ≤ M) :
    (21 / 64 : ℝ) * (7 / 8 + ((2 : ℝ) ^ M)⁻¹) ≤ ∏ i ∈ Finset.Icc 1 M, (1 - ((2 : ℝ) ^ i)⁻¹) := by
  induction M, hM using Nat.le_induction with
  | base =>
    rw [show Finset.Icc 1 3 = {1, 2, 3} from rfl]
    simp [Finset.prod_insert]
    norm_num
  | succ M hM ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    set x : ℝ := ((2 : ℝ) ^ M)⁻¹ with hx
    have hx0 : 0 ≤ x := by positivity
    have hx8 : x ≤ 1 / 8 := by
      rw [hx]
      have : (8 : ℝ) ≤ 2 ^ M := by
        calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hM
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    have hx2 : ((2 : ℝ) ^ (M + 1))⁻¹ = x / 2 := by
      rw [hx, pow_succ, mul_inv]; ring
    rw [hx2]
    have hP0 : 0 ≤ 1 - x / 2 := by linarith
    calc (21 / 64 : ℝ) * (7 / 8 + x / 2)
        ≤ (21 / 64 : ℝ) * (7 / 8 + x) * (1 - x / 2) := by nlinarith
      _ ≤ (∏ i ∈ Finset.Icc 1 M, (1 - ((2 : ℝ) ^ i)⁻¹)) * (1 - x / 2) :=
          mul_le_mul_of_nonneg_right ih hP0

theorem prodBound_partial (M : ℕ) :
    (147 / 512 : ℝ) ≤ ∏ i ∈ Finset.Icc 1 M, (1 - ((2 : ℝ) ^ i)⁻¹) := by
  rcases Nat.lt_or_ge M 3 with h | h
  · interval_cases M
    · simp; norm_num
    · rw [show Finset.Icc 1 1 = {1} from rfl]; simp; norm_num
    · rw [show Finset.Icc 1 2 = {1, 2} from rfl]; simp [Finset.prod_insert]; norm_num
  · refine le_trans ?_ (prodBound_aux M h)
    have : 0 ≤ ((2 : ℝ) ^ M)⁻¹ := by positivity
    nlinarith

theorem lemA2ProductBound_proved' : lemA2ProductBoundStatement := by
  refine ⟨fun M => ?_, ?_, by norm_num⟩
  · simp only [two_zpow_neg]; exact prodBound_partial M
  · have h : ∀ i : ℕ, (2 : ℝ) ^ (-((i + 4 : ℕ) : ℤ)) = (1 / 16) * (1 / 2) ^ i := by
      intro i
      rw [two_zpow_neg, pow_add, mul_inv, one_div_pow]
      norm_num
      ring
    simp_rw [h]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num

/-! ### Lemma A.2 -/

theorem prod_pow_sub_eq {q : ℝ} (hq : 2 ≤ q) (d j : ℕ) :
    gaussProd q d j * ∏ i ∈ Finset.range j, (q ^ (i + 1) - 1)
      = ∏ i ∈ Finset.range j, (q ^ (d - i) - 1) := by
  rw [gaussProd, Finset.prod_div_distrib]
  exact div_mul_cancel₀ _ (Finset.prod_ne_zero_iff.mpr fun i _ => pow_sub_one_ne hq i)

theorem prod_pow_shift {q : ℝ} : ∀ {d j : ℕ}, j ≤ d →
    ∏ i ∈ Finset.range j, q ^ (d - i) = q ^ (j * (d - j)) * ∏ i ∈ Finset.range j, q ^ (i + 1)
  | d, 0, _ => by simp
  | d, j + 1, h => by
    rw [Finset.prod_range_succ, Finset.prod_range_succ, prod_pow_shift (by omega : j ≤ d)]
    obtain ⟨e, rfl⟩ : ∃ e, d = j + 1 + e := ⟨d - (j + 1), by omega⟩
    rw [show j + 1 + e - j = e + 1 by omega, show j + 1 + e - (j + 1) = e by omega]
    ring

theorem gaussProd_mul_le {q : ℝ} (hq : 2 ≤ q) {d j : ℕ} (hj : j ≤ d) :
    gaussProd q d j * ∏ i ∈ Finset.range j, (1 - (q ^ (i + 1))⁻¹) ≤ q ^ (j * (d - j)) := by
  have hq0 : 0 < q := by linarith
  have hA : 0 < ∏ i ∈ Finset.range j, q ^ (i + 1) :=
    Finset.prod_pos fun i _ => pow_pos hq0 _
  have hsplit : ∏ i ∈ Finset.range j, (q ^ (i + 1) - 1)
      = (∏ i ∈ Finset.range j, q ^ (i + 1)) * ∏ i ∈ Finset.range j, (1 - (q ^ (i + 1))⁻¹) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_sub, mul_one, mul_inv_cancel₀ (pow_ne_zero _ hq0.ne')]
  have hnum : ∏ i ∈ Finset.range j, (q ^ (d - i) - 1) ≤ ∏ i ∈ Finset.range j, q ^ (d - i) := by
    apply Finset.prod_le_prod
    · intro i _
      have : (1 : ℝ) ≤ q ^ (d - i) := one_le_pow₀ (by linarith)
      linarith
    · intro i _; linarith
  have key := prod_pow_sub_eq hq d j
  rw [hsplit] at key
  have h2 : (∏ i ∈ Finset.range j, q ^ (i + 1)) *
      (gaussProd q d j * ∏ i ∈ Finset.range j, (1 - (q ^ (i + 1))⁻¹))
      ≤ (∏ i ∈ Finset.range j, q ^ (i + 1)) * q ^ (j * (d - j)) := by
    calc _ = ∏ i ∈ Finset.range j, (q ^ (d - i) - 1) := by rw [← key]; ring
    _ ≤ ∏ i ∈ Finset.range j, q ^ (d - i) := hnum
    _ = _ := by rw [prod_pow_shift hj]; ring
  exact le_of_mul_le_mul_left h2 hA

theorem prod_one_sub_ge {q : ℝ} (hq : 2 ≤ q) (j : ℕ) :
    (1 / 4 : ℝ) < ∏ i ∈ Finset.range j, (1 - (q ^ (i + 1))⁻¹) := by
  have h1 : ∏ i ∈ Finset.range j, (1 - ((2 : ℝ) ^ (i + 1))⁻¹)
      ≤ ∏ i ∈ Finset.range j, (1 - (q ^ (i + 1))⁻¹) := by
    apply Finset.prod_le_prod
    · intro i _
      have : ((2 : ℝ) ^ (i + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      linarith
    · intro i _
      have : (q ^ (i + 1))⁻¹ ≤ ((2 : ℝ) ^ (i + 1))⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hq _)
      linarith
  have h2 := prodBound_partial j
  rw [prodIcc_eq_range] at h2
  linarith

theorem lemA2Part1_proved' : lemA2Part1Statement := by
  intro q d j hq _ hj
  have hP := prod_one_sub_ge hq j
  have hPpos : 0 < ∏ i ∈ Finset.range j, (1 - (q ^ (i + 1))⁻¹) := by linarith
  have h := gaussProd_mul_le hq hj
  have hX : 0 ≤ q ^ (j * (d - j)) := pow_nonneg (by linarith) _
  rw [← le_div_iff₀ hPpos] at h
  refine le_trans h ?_
  rw [div_le_iff₀ hPpos]
  nlinarith

theorem lemA2Part2_proved' : lemA2Part2Statement := by
  intro q d hq hd
  have hg : gaussProd q d 1 = (q ^ d - 1) / (q - 1) := by
    simp [gaussProd]
  rw [hg, div_le_iff₀ (by linarith)]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  have : 0 ≤ q ^ e := pow_nonneg (by linarith) _
  nlinarith

theorem DD_eq_choose (d : ℕ) : DD d = d.choose 2 := by
  rw [DD, Nat.choose_two_right]

theorem lemA2Part3_proved' : lemA2Part3Statement := by
  intro q d hq hd
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hterm : ∀ j ∈ Finset.Icc 2 d, rdReal q d j ≤ 4 * q ^ DD d := by
    intro j hj
    obtain ⟨_, hjd⟩ := Finset.mem_Icc.mp hj
    rw [rdReal]
    calc q ^ j.choose 2 * gaussProd q d j ≤ q ^ j.choose 2 * (4 * q ^ (j * (d - j))) :=
          mul_le_mul_of_nonneg_left (lemA2Part1_proved' q d j hq hd hjd) (pow_nonneg (by linarith) _)
    _ = 4 * q ^ (j.choose 2 + j * (d - j)) := by rw [pow_add]; ring
    _ ≤ 4 * q ^ DD d := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply pow_le_pow_right₀ hq1
        rw [DD_eq_choose]
        have := ShiftSym.choose_two_split hjd
        omega
  calc ∑ j ∈ Finset.Icc 2 d, rdReal q d j ≤ (Finset.Icc 2 d).card • (4 * q ^ DD d) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
  _ = 4 * ((d : ℝ) - 1) * q ^ DD d := by
      rw [Nat.card_Icc, nsmul_eq_mul, Nat.cast_sub (by omega)]
      push_cast
      ring


/-! ### Lemma A.4: proviso and log condition -/

theorem nine_sq_le (d : ℕ) (hd : 3 ≤ d) : 9 * d ^ 2 ≤ 2 ^ (2 * d + 1) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    have e : 2 ^ (2 * (d + 1) + 1) = 4 * 2 ^ (2 * d + 1) := by ring
    rw [e]
    nlinarith

/-- `12 d n^{C(d,2)} ≤ 2^{n^{d-1}}` for `n ≥ 4`, `d ≥ 3` (squared comparison, via the
certified `exp_ineq`). -/
theorem twelve_le_two_pow {n d : ℕ} (hn : 4 ≤ n) (hd : 3 ≤ d) :
    12 * d * n ^ d.choose 2 ≤ 2 ^ (n ^ (d - 1)) := by
  have hexp := ShiftSym.exp_ineq hn hd
  have h9 := nine_sq_le d hd
  have hsq : (12 * d * n ^ d.choose 2) ^ 2 ≤ (2 ^ (n ^ (d - 1))) ^ 2 := by
    have e1 : (12 * d * n ^ d.choose 2) ^ 2 = 16 * (9 * d ^ 2) * (n ^ 2) ^ d.choose 2 := by ring
    have h10 : (n ^ 2) ^ d.choose 2 ≤ (2 ^ n) ^ d.choose 2 :=
      Nat.pow_le_pow_left (ShiftSym.sq_le_two_pow hn) _
    have e2 : ((2 : ℕ) ^ (n ^ (d - 1))) ^ 2 = 2 ^ (2 * n ^ (d - 1)) := by
      rw [← pow_mul, mul_comm]
    have e3 : 16 * 2 ^ (2 * d + 1) * (2 ^ n) ^ d.choose 2 = 2 ^ (2 * d + 5 + n * d.choose 2) := by
      rw [← pow_mul, show 2 * d + 5 + n * d.choose 2 = (2 * d + 1) + 4 + n * d.choose 2 by ring,
        pow_add, pow_add]
      ring
    rw [e1, e2]
    calc 16 * (9 * d ^ 2) * (n ^ 2) ^ d.choose 2
        ≤ 16 * 2 ^ (2 * d + 1) * (2 ^ n) ^ d.choose 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h9) h10
      _ = 2 ^ (2 * d + 5 + n * d.choose 2) := e3
      _ ≤ 2 ^ (2 * n ^ (d - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hsq

theorem lemA4Proviso_proved' : lemA4ProvisoStatement := by
  intro n d hc hd
  have hn4 : 4 ≤ n := by
    have pp := Nat.minFac_prime (show n ≠ 1 by have := hc.1; omega)
    have h := Nat.minFac_sq_le_self (by have := hc.1; omega : 0 < n) hc.2
    nlinarith [pp.two_le]
  rw [DD_eq_choose]
  exact twelve_le_two_pow hn4 hd

theorem logb_le_half {n : ℕ} (hn : 4 ≤ n) : Real.logb 2 n ≤ (n : ℝ) / 2 := by
  have hsq : ((n : ℝ)) ^ 2 ≤ (2 : ℝ) ^ n := by exact_mod_cast ShiftSym.sq_le_two_pow hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hlog := Real.log_le_log hpos hsq
  rw [Real.log_pow, Real.log_pow] at hlog
  rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
  push_cast at hlog
  linarith

theorem logCond_nat (n : ℕ) (hn : 4 ≤ n) :
    ∀ e : ℕ, 16 + 4 * (e + 3) + n * (e + 3) * (e + 2) ≤ 4 * n ^ (e + 2) := by
  intro e
  induction e with
  | zero => norm_num; nlinarith
  | succ e ih =>
    have e1 : 4 * n ^ (e + 1 + 2) = n * (4 * n ^ (e + 2)) := by ring
    rw [e1]
    have h2 : n * (16 + 4 * (e + 3) + n * (e + 3) * (e + 2)) ≤ n * (4 * n ^ (e + 2)) :=
      Nat.mul_le_mul_left n ih
    set A := n * (e + 3) * (e + 2) with hA
    have hB : n * (e + 1 + 3) * (e + 1 + 2) ≤ 4 * A := by
      have h7 : n * (e + 3) * (e + 4) ≤ n * (e + 3) * (4 * (e + 2)) :=
        Nat.mul_le_mul_left _ (by omega)
      calc n * (e + 1 + 3) * (e + 1 + 2) = n * (e + 3) * (e + 4) := by ring
      _ ≤ n * (e + 3) * (4 * (e + 2)) := h7
      _ = 4 * A := by rw [hA]; ring
    have h5 : 4 * A ≤ n * A := Nat.mul_le_mul_right A hn
    have h6 : 4 * (16 + 4 * (e + 3)) ≤ n * (16 + 4 * (e + 3)) := Nat.mul_le_mul_right _ hn
    have e2 : n * (16 + 4 * (e + 3) + A) = n * (16 + 4 * (e + 3)) + n * A := by ring
    omega

theorem lemA4LogCondition_proved' : lemA4LogConditionStatement := by
  intro n d hn hd
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
  have hlog := logb_le_half hn
  have hnat := logCond_nat n hn e
  have hreal : (16 : ℝ) + 4 * ((e : ℝ) + 3) + (n : ℝ) * ((e : ℝ) + 3) * ((e : ℝ) + 2)
      ≤ 4 * (n : ℝ) ^ (e + 2) := by exact_mod_cast hnat
  rw [show e + 3 - 1 = e + 2 by omega]
  push_cast
  have hc : (0 : ℝ) ≤ ((e : ℝ) + 3) * ((e : ℝ) + 3 - 1) / 2 := by
    have : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg e
    apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have := mul_le_mul_of_nonneg_left hlog hc
  nlinarith

/-! ### Conditions (I) and (II) -/

theorem four_mul_le_two_pow (x : ℕ) (hx : 4 ≤ x) : 4 * x ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih => rw [pow_succ]; omega

theorem eight_mul_le_two_pow (x : ℕ) (hx : 6 ≤ x) : 8 * x ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih => rw [pow_succ]; omega

/-- Arithmetic of `p = p_{m+1}` (`1 ≤ m < k`): `p ≥ 2`, `p ∣ n` and `n/p ≥ 2`. -/
theorem bigPrime_facts {n m : ℕ} (hn : 2 ≤ n) (hm1 : 1 ≤ m) (hmk : m < kOf n) :
    2 ≤ primeAt n m ∧ primeAt n m ∣ n ∧ 2 * primeAt n m ≤ n := by
  have hP := primeAt_prime hmk
  have h0 := primeAt_prime (by omega : 0 < kOf n)
  have hlt := primeAt_lt (by omega : 0 < m) hmk
  have hcop : Nat.Coprime (primeAt n 0) (primeAt n m) :=
    (Nat.coprime_primes h0 hP).mpr hlt.ne
  have hdvd : primeAt n 0 * primeAt n m ∣ n :=
    hcop.mul_dvd_of_dvd_of_dvd (primeAt_dvd (by omega)) (primeAt_dvd hmk)
  refine ⟨hP.two_le, primeAt_dvd hmk, ?_⟩
  calc 2 * primeAt n m ≤ primeAt n 0 * primeAt n m := Nat.mul_le_mul_right _ h0.two_le
  _ ≤ n := Nat.le_of_dvd (by omega) hdvd

/-- `N_1 ≥ 2 n^{d-1}` in `ℝ`. -/
theorem N1_ge {n d P : ℕ} (hd : 1 ≤ d) (hP : 2 ≤ P) (h2P : 2 * P ≤ n) :
    2 * (n : ℝ) ^ (d - 1) ≤ Nj n d P 1 := by
  rw [Nj, pow_one, le_div_iff₀ (by positivity)]
  have hn : (2 : ℝ) * P ≤ n := by exact_mod_cast h2P
  have e : (n : ℝ) ^ d = (n : ℝ) ^ (d - 1) * n := by
    rw [← pow_succ]; congr 1; omega
  rw [e]
  have : (0 : ℝ) ≤ (n : ℝ) ^ (d - 1) := by positivity
  nlinarith

theorem two_rpow_le {σ : ℕ} (hσ : 2 ≤ σ) {x : ℝ} (k : ℕ) (hk : (k : ℝ) ≤ x) :
    ((2 ^ k : ℕ) : ℝ) ≤ (σ : ℝ) ^ x := by
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg k) hk
  push_cast
  rw [← Real.rpow_natCast]
  calc (2 : ℝ) ^ (k : ℝ) ≤ (2 : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le (by norm_num) hk
  _ ≤ (σ : ℝ) ^ x := Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hσ) hx0

theorem condI_proved' : condIStatement := by
  intro n d σ m hc hn6 hd hσ hm1 hmk
  obtain ⟨hP2, hPn, h2P⟩ := bigPrime_facts hc.1 hm1 hmk
  set P := primeAt n m
  have hN1 := N1_ge (by omega : 1 ≤ d) hP2 h2P
  have ht : (n : ℝ) / P ≤ n := div_le_self (by positivity) (by exact_mod_cast (by omega : 1 ≤ P))
  have ht0 : 0 ≤ (n : ℝ) / P := by positivity
  have hx4 : 4 ≤ n ^ (d - 1) :=
    le_trans (by omega) (Nat.le_self_pow (by omega : d - 1 ≠ 0) n)
  have hnat := four_mul_le_two_pow _ hx4
  calc 4 * ((n : ℝ) / P) ^ (d - 1) ≤ 4 * (n : ℝ) ^ (d - 1) := by
        gcongr
    _ = ((4 * n ^ (d - 1) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ (n ^ (d - 1)) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ ≤ (σ : ℝ) ^ (Nj n d P 1 / 2) := by
        apply two_rpow_le hσ
        push_cast
        linarith

theorem condII_proved' : condIIStatement := by
  intro n d σ m hc hn6 hd hσ hm1 hmk
  obtain ⟨hP2, hPn, h2P⟩ := bigPrime_facts hc.1 hm1 hmk
  set P := primeAt n m
  have hN1 := N1_ge (by omega : 1 ≤ d) hP2 h2P
  -- the exponent gap
  have hgap : (n : ℝ) ^ (d - 1) ≤ Nj n d P 1 - Nj n d P 2 := by
    have hP : (2 : ℝ) ≤ P := by exact_mod_cast hP2
    have e : Nj n d P 2 = Nj n d P 1 / P := by
      rw [Nj, Nj, pow_one, div_div, sq]
    rw [e]
    have hN0 : 0 ≤ Nj n d P 1 := by rw [Nj]; positivity
    have : Nj n d P 1 / P ≤ Nj n d P 1 / 2 := div_le_div_of_nonneg_left hN0 (by norm_num) hP
    linarith
  -- the natural-number core
  have hnat : 8 * (d - 1) * n ^ DD d ≤ 2 ^ (n ^ (d - 1)) := by
    rcases Nat.lt_or_ge d 3 with h3 | h3
    · obtain rfl : d = 2 := by omega
      rw [show DD 2 = 1 from rfl]
      simpa using eight_mul_le_two_pow n hn6
    · rw [DD_eq_choose]
      refine le_trans ?_ (twelve_le_two_pow (by omega) h3)
      exact Nat.mul_le_mul_right _ (by omega)
  have hPle : (P : ℝ) ≤ n := by exact_mod_cast (by omega : P ≤ n)
  calc 8 * ((d : ℝ) - 1) * (P : ℝ) ^ DD d ≤ 8 * ((d : ℝ) - 1) * (n : ℝ) ^ DD d := by
        have : (0 : ℝ) ≤ 8 * ((d : ℝ) - 1) := by
          have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
          linarith
        gcongr
    _ = ((8 * (d - 1) * n ^ DD d : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
    _ ≤ ((2 ^ (n ^ (d - 1)) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ ≤ (σ : ℝ) ^ (Nj n d P 1 - Nj n d P 2) := by
        apply two_rpow_le hσ
        push_cast
        linarith

end ShiftSym.P10
