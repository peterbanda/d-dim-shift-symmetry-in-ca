/-
Phase H, group 06 (BoundsProbability), proof helper 1: Gaussian-binomial
algebra.

* the ratio identity `[d, r+1]_q (q^{r+1} - 1) = [d r]_q (q^{d-r} - 1)`,
  derived from the certified product identity `gaussBinom_mul_prod_int`;
* the paper's product formula equals the `q`-Pascal `gaussBinom`
  (`gaussProd_eq_gaussBinom`), and a polynomial in `ℕ[X]` evaluating to it;
* the envelope at `d = 1, 2` and the paper-envelope bridge;
* strict decrease of the terms `T_r = r_d(q,r) σ^{q^{d-r}}` and positivity
  of alternating tails, giving the truncation statement of Remark 6.2.
-/
import Shiftsym.Paper.S06_BoundsProbability
import Shiftsym.Lemmas.LowerBound

namespace ShiftSym.P06

open ShiftSym

/-! ### Basic facts about `gaussBinom` -/

theorem gaussBinom_zero_right' (q d : ℕ) : gaussBinom q d 0 = 1 := by
  cases d <;> rfl

theorem gaussBinom_pos' {q : ℕ} : ∀ {d r : ℕ}, r ≤ d → 0 < gaussBinom q d r
  | d, 0, _ => by rw [gaussBinom_zero_right']; exact Nat.one_pos
  | 0, _ + 1, h => absurd h (by omega)
  | d + 1, r + 1, h => by
    have ih : 0 < gaussBinom q d r := gaussBinom_pos' (by omega)
    show 0 < gaussBinom q d r + q ^ (r + 1) * gaussBinom q d (r + 1)
    omega

/-! ### The ratio identity -/

private theorem prod_split' (x : ℤ) (e r : ℕ) :
    ∏ i : Fin (r + 1), (x ^ (e + 1) - x ^ (i : ℕ))
      = (x ^ (e + 1) - 1) * x ^ r * ∏ i : Fin r, (x ^ e - x ^ (i : ℕ)) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, pow_zero, Fin.val_succ]
  have key : ∀ i : Fin r, x ^ (e + 1) - x ^ ((i : ℕ) + 1)
      = x * (x ^ e - x ^ (i : ℕ)) := by
    intro i
    rw [pow_succ, pow_succ]
    ring
  rw [Finset.prod_congr rfl (fun i _ => key i), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- Ratio identity, multiplied out (in `ℤ`). -/
theorem gauss_ratio_int {q : ℕ} (hq : 2 ≤ q) (d r : ℕ) :
    (gaussBinom q d (r + 1) : ℤ) * ((q : ℤ) ^ (r + 1) - 1) * (q : ℤ) ^ r
      = (gaussBinom q d r : ℤ) * ((q : ℤ) ^ d - (q : ℤ) ^ r) := by
  have h1 := gaussBinom_mul_prod_int q d r
  have h2 := gaussBinom_mul_prod_int q d (r + 1)
  have hsplit2 : ∏ i : Fin (r + 1), ((q : ℤ) ^ d - (q : ℤ) ^ (i : ℕ))
      = (∏ i : Fin r, ((q : ℤ) ^ d - (q : ℤ) ^ (i : ℕ)))
        * ((q : ℤ) ^ d - (q : ℤ) ^ r) := by
    rw [Fin.prod_univ_castSucc]
    simp
  have hP : ∏ i : Fin r, ((q : ℤ) ^ r - (q : ℤ) ^ (i : ℕ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    have : (q : ℤ) ^ (i : ℕ) < (q : ℤ) ^ r :=
      pow_lt_pow_right₀ (by exact_mod_cast hq) i.2
    exact sub_ne_zero.mpr (ne_of_gt this)
  rw [prod_split' (q : ℤ) r r, hsplit2, ← h1] at h2
  apply mul_right_cancel₀ hP
  linear_combination h2

/-- **Ratio identity** in `ℚ`: `[d, r+1]_q (q^{r+1} - 1) = [d r]_q (q^{d-r} - 1)`
(`ℕ`-subtraction `d - r`; both sides vanish for `r ≥ d`). -/
theorem gauss_ratio {q : ℕ} (hq : 2 ≤ q) (d r : ℕ) :
    (gaussBinom q d (r + 1) : ℚ) * ((q : ℚ) ^ (r + 1) - 1)
      = (gaussBinom q d r : ℚ) * ((q : ℚ) ^ (d - r) - 1) := by
  by_cases hrd : r < d
  · have hZ := gauss_ratio_int hq d r
    have hQ : (gaussBinom q d (r + 1) : ℚ) * ((q : ℚ) ^ (r + 1) - 1) * (q : ℚ) ^ r
        = (gaussBinom q d r : ℚ) * ((q : ℚ) ^ d - (q : ℚ) ^ r) := by
      exact_mod_cast hZ
    have hqr : (q : ℚ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))
    have hd : (q : ℚ) ^ d = (q : ℚ) ^ (d - r) * (q : ℚ) ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hrd.le]
    apply mul_right_cancel₀ hqr
    rw [hQ, hd]
    ring
  · have hz : gaussBinom q d (r + 1) = 0 := gaussBinom_eq_zero_of_lt (by omega)
    have hdr : d - r = 0 := by omega
    rw [hz, hdr]
    simp

/-- The ratio identity in `ℕ`. -/
theorem gauss_ratio_nat {q : ℕ} (hq : 2 ≤ q) (d r : ℕ) :
    gaussBinom q d (r + 1) * (q ^ (r + 1) - 1)
      = gaussBinom q d r * (q ^ (d - r) - 1) := by
  have h := gauss_ratio hq d r
  have h1 : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ (d - r) := Nat.one_le_pow _ _ (by omega)
  have : ((gaussBinom q d (r + 1) * (q ^ (r + 1) - 1) : ℕ) : ℚ)
      = ((gaussBinom q d r * (q ^ (d - r) - 1) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    exact h
  exact_mod_cast this

/-! ### Product formula = `q`-Pascal -/

/-- The paper's product formula equals `gaussBinom` at every `q ≥ 2`. -/
theorem gaussProd_eq_gaussBinom {q : ℕ} (hq : 2 ≤ q) (d : ℕ) :
    ∀ r : ℕ, gaussProd q d r = (gaussBinom q d r : ℚ)
  | 0 => by simp [gaussProd, gaussBinom_zero_right']
  | r + 1 => by
    rw [gaussProd, Finset.prod_range_succ, ← gaussProd, gaussProd_eq_gaussBinom hq d r]
    have hden : (q : ℚ) ^ (r + 1) - 1 ≠ 0 := by
      have : (1 : ℚ) < (q : ℚ) ^ (r + 1) :=
        one_lt_pow₀ (by exact_mod_cast (by omega : 1 < q)) (by omega)
      linarith
    rw [mul_div_assoc', div_eq_iff hden, gauss_ratio hq d r]

/-- The `q`-Pascal recursion in `ℕ[X]`. -/
noncomputable def gaussPoly : ℕ → ℕ → Polynomial ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | dd + 1, r + 1 => gaussPoly dd r + Polynomial.X ^ (r + 1) * gaussPoly dd (r + 1)

theorem gaussPoly_eval (q : ℕ) : ∀ d r : ℕ, (gaussPoly d r).eval q = gaussBinom q d r
  | d, 0 => by cases d <;> simp [gaussPoly, gaussBinom]
  | 0, r + 1 => by simp [gaussPoly, gaussBinom]
  | d + 1, r + 1 => by
    rw [gaussPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, gaussPoly_eval q d r, gaussPoly_eval q d (r + 1)]
    rfl

/-! ### The envelope at small `d` -/

theorem gaussBinom_two_one (q : ℕ) : gaussBinom q 2 1 = q + 1 := by
  simp [gaussBinom]; ring

theorem gaussBinom_self (q : ℕ) : ∀ d : ℕ, gaussBinom q d d = 1
  | 0 => rfl
  | d + 1 => by
    show gaussBinom q d d + q ^ (d + 1) * gaussBinom q d (d + 1) = 1
    rw [gaussBinom_self q d, gaussBinom_eq_zero_of_lt (by omega)]
    simp

theorem lowerEnvelope_two (n σ : ℕ) :
    lowerEnvelope n 2 σ = ((n : ℤ) + 1) * (σ : ℤ) ^ n - (n : ℤ) * σ := by
  rw [lowerEnvelope]
  rw [show Finset.Icc 1 2 = {1, 2} by decide]
  rw [Finset.sum_pair (by norm_num)]
  simp only [rdCoeff, gaussBinom_two_one, gaussBinom_self]
  norm_num
  ring

theorem lowerEnvelope_one (n σ : ℕ) : lowerEnvelope n 1 σ = (σ : ℤ) := by
  rw [lowerEnvelope]
  simp [rdCoeff, gaussBinom_self]

/-! ### Strict decrease of the envelope terms and alternating tails -/

theorem two_mul_le_two_pow (x : ℕ) : 2 * x ≤ 2 ^ x := by
  induction x with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; norm_num
    · have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ]
      omega

/-- The key exponential inequality behind the decrease of the terms:
`q^r (q m - 1) σ^m < σ^{q m} (q^{r+1} - 1)` for `q, σ ≥ 2`, `m ≥ 1`. -/
theorem term_core {q σ m r : ℕ} (hq : 2 ≤ q) (hσ : 2 ≤ σ) (hm : 1 ≤ m) :
    q ^ r * (q * m - 1) * σ ^ m < σ ^ (q * m) * (q ^ (r + 1) - 1) := by
  set a := (q - 1) * m with ha
  have ha1 : 1 ≤ a := by
    rw [ha]; exact Nat.mul_pos (by omega) hm
  have hqm : q * m = m + a := by
    rw [ha]
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hσa : 2 * a ≤ σ ^ a :=
    le_trans (two_mul_le_two_pow a) (Nat.pow_le_pow_left hσ a)
  have hqr : q ^ r ≤ q ^ (r + 1) - 1 := by
    have : q ^ (r + 1) = q * q ^ r := by ring
    have h1 : 1 ≤ q ^ r := Nat.one_le_pow _ _ (by omega)
    have h2 : 2 * q ^ r ≤ q * q ^ r := Nat.mul_le_mul_right _ hq
    omega
  have hlin : q * m - 1 < 2 * a := by
    have h3 : 2 * m ≤ q * m := Nat.mul_le_mul_right _ hq
    omega
  have hσm : 0 < σ ^ m := Nat.pos_of_ne_zero (by positivity)
  have hqr0 : 0 < q ^ r := Nat.pos_of_ne_zero (by positivity)
  calc q ^ r * (q * m - 1) * σ ^ m
      < q ^ r * (2 * a) * σ ^ m := by
        apply Nat.mul_lt_mul_of_pos_right _ hσm
        exact Nat.mul_lt_mul_of_pos_left hlin hqr0
    _ ≤ (q ^ (r + 1) - 1) * σ ^ a * σ ^ m := by
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul hqr hσa
    _ = σ ^ (q * m) * (q ^ (r + 1) - 1) := by
        rw [hqm, pow_add]; ring

/-- The envelope term `T_r = r_d(q, r) σ^{q^{d-r}}` (natural number). -/
def envTerm (q d σ r : ℕ) : ℕ := rdCoeff q r d * σ ^ (q ^ (d - r))

/-- **Strict decrease**: `T_{r+1} < T_r` for `r + 1 ≤ d`, `q, σ ≥ 2`. -/
theorem envTerm_succ_lt {q d σ r : ℕ} (hq : 2 ≤ q) (hσ : 2 ≤ σ) (hrd : r + 1 ≤ d) :
    envTerm q d σ (r + 1) < envTerm q d σ r := by
  set m := q ^ (d - (r + 1)) with hm
  have hm1 : 1 ≤ m := Nat.one_le_pow _ _ (by omega)
  have hqm : q ^ (d - r) = q * m := by
    rw [hm, show d - r = (d - (r + 1)) + 1 by omega, pow_succ]; ring
  have hG : 0 < gaussBinom q d r := gaussBinom_pos' (by omega)
  have hratio := gauss_ratio_nat hq d r
  have hchoose : (r + 1).choose 2 = r.choose 2 + r := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have hden : 0 < q ^ (r + 1) - 1 := by
    have : 2 ≤ q ^ (r + 1) :=
      le_trans hq (by
        calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hcore := term_core (r := r) hq hσ hm1
  have hpos : 0 < q ^ r.choose 2 * gaussBinom q d r :=
    Nat.mul_pos (Nat.pos_of_ne_zero (by positivity)) hG
  apply Nat.lt_of_mul_lt_mul_right (a := q ^ (r + 1) - 1)
  calc envTerm q d σ (r + 1) * (q ^ (r + 1) - 1)
      = q ^ r.choose 2 * q ^ r * (gaussBinom q d (r + 1) * (q ^ (r + 1) - 1))
          * σ ^ m := by
        rw [envTerm, rdCoeff, hchoose, pow_add, ← hm]; ring
    _ = (q ^ r.choose 2 * gaussBinom q d r) * (q ^ r * (q * m - 1) * σ ^ m) := by
        rw [hratio, hqm]; ring
    _ < (q ^ r.choose 2 * gaussBinom q d r) * (σ ^ (q * m) * (q ^ (r + 1) - 1)) :=
        Nat.mul_lt_mul_of_pos_left hcore hpos
    _ = envTerm q d σ r * (q ^ (r + 1) - 1) := by
        rw [envTerm, rdCoeff, hqm]; ring

/-- Alternating sums of a strictly decreasing positive sequence are positive
and at most their first term. -/
theorem alt_sum_pos (f : ℕ → ℤ) :
    ∀ (k a : ℕ), (∀ i ≤ k, 0 < f (a + i)) → (∀ i < k, f (a + i + 1) < f (a + i)) →
      0 < ∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ i * f (a + i)
        ∧ ∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ i * f (a + i) ≤ f a
  | 0, a, hpos, _ => by
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
      add_zero]
    exact ⟨by simpa using hpos 0 le_rfl, le_rfl⟩
  | k + 1, a, hpos, hdec => by
    have ih := alt_sum_pos f k (a + 1)
      (fun i hi => by have := hpos (i + 1) (by omega); rwa [show a + (i + 1) = a + 1 + i by ring] at this)
      (fun i hi => by
        have := hdec (i + 1) (by omega)
        rwa [show a + (i + 1) = a + 1 + i by ring] at this)
    rw [Finset.sum_range_succ']
    have hrw : ∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ (i + 1) * f (a + (i + 1))
        = -∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ i * f (a + 1 + i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show a + (i + 1) = a + 1 + i by ring, pow_succ]
      ring
    rw [hrw]
    simp only [pow_zero, one_mul, add_zero]
    have h01 : f (a + 1) < f a := by simpa using hdec 0 (by omega)
    constructor
    · linarith [ih.2]
    · linarith [ih.1]

/-- The tail `Σ_{r=3}^{d} (-1)^{r+1} T_r` of the envelope is positive for
`d ≥ 3`, `q, σ ≥ 2`. -/
theorem envelope_tail_pos {q d σ : ℕ} (hq : 2 ≤ q) (hσ : 2 ≤ σ) (hd : 3 ≤ d) :
    0 < ∑ r ∈ Finset.Icc 3 d,
      (-1 : ℤ) ^ (r + 1) * (rdCoeff q r d : ℤ) * (σ : ℤ) ^ (q ^ (d - r)) := by
  have hIcc : Finset.Icc 3 d = Finset.Ico 3 (d + 1) := rfl
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  rw [show d + 1 - 3 = (d - 3) + 1 by omega]
  have key := alt_sum_pos (fun r => (envTerm q d σ r : ℤ)) (d - 3) 3
    (fun i hi => by
      have : 0 < envTerm q d σ (3 + i) := by
        rw [envTerm, rdCoeff]
        exact Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero (by positivity))
          (gaussBinom_pos' (by omega))) (Nat.pos_of_ne_zero (by positivity))
      exact_mod_cast this)
    (fun i hi => by
      have := envTerm_succ_lt (q := q) (d := d) (σ := σ) (r := 3 + i) hq hσ (by omega)
      exact_mod_cast this)
  convert key.1 using 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [envTerm]
  push_cast
  rw [show 3 + i + 1 = i + 2 * 2 by ring, pow_add, pow_mul]
  norm_num
  ring

/-- Splitting the envelope at `r = 2`. -/
theorem lowerEnvelope_split {q d σ : ℕ} (hd : 2 ≤ d) :
    lowerEnvelope q d σ
      = (∑ r ∈ Finset.Icc 1 2,
          (-1 : ℤ) ^ (r + 1) * (rdCoeff q r d : ℤ) * (σ : ℤ) ^ (q ^ (d - r)))
        + ∑ r ∈ Finset.Icc 3 d,
          (-1 : ℤ) ^ (r + 1) * (rdCoeff q r d : ℤ) * (σ : ℤ) ^ (q ^ (d - r)) := by
  rw [lowerEnvelope]
  have h1 : Finset.Icc 1 d = Finset.Ico 1 (d + 1) := rfl
  have h2 : Finset.Icc 1 2 = Finset.Ico 1 3 := rfl
  have h3 : Finset.Icc 3 d = Finset.Ico 3 (d + 1) := rfl
  rw [h1, h2, h3, Finset.sum_Ico_consecutive _ (by omega) (by omega)]

end ShiftSym.P06
