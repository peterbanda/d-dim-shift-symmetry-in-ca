/-
Phase E, part 1: elementary inequalities for the lower-bound theorem
(claim C009). Everything here is ℕ-arithmetic:

* `gaussBinom_le_pow`  — [d r]_q ≤ 2^d q^{r(d−r)} (q-Pascal induction);
* `rdCoeff_le`         — r_d(n,r) ≤ 2^d n^{C(d,2)};
* `gaussBinom_d_one_le`— [d 1]_n ≤ 2 n^{d−1};
* `envelope_coeff_lt_two_pow` — the core:
      [d 1]_n + (d−2)·2^d·n^{C(d,2)} < 2^{n^{d−1}}   (n ≥ 4, d ≥ 1),
  which is what makes a single fixed-set of an order-p₁ subgroup beat
  the whole lower envelope at composite n.
-/
import Shiftsym.Lemmas.GaussCount

namespace ShiftSym

theorem two_mul_choose_two (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.mul_add, Nat.choose_one_right, ih]
    cases m with
    | zero => rfl
    | succ a =>
      simp only [Nat.add_sub_cancel]
      ring

theorem choose_two_split {r d : ℕ} (hrd : r ≤ d) :
    r.choose 2 + r * (d - r) + (d - r).choose 2 = d.choose 2 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrd
  rw [Nat.add_sub_cancel_left]
  have h2 : 2 * (r.choose 2 + r * s + s.choose 2)
      = 2 * ((r + s).choose 2) := by
    rw [Nat.mul_add, Nat.mul_add, two_mul_choose_two, two_mul_choose_two,
      two_mul_choose_two]
    rcases r with _ | a
    · simp
    · rcases s with _ | b
      · simp
      · have hsub : a + 1 + (b + 1) - 1 = a + b + 1 := by omega
        rw [hsub]
        simp only [Nat.add_sub_cancel]
        ring
  omega

theorem gaussBinom_le_pow {q : ℕ} (hq : 1 ≤ q) :
    ∀ d r, gaussBinom q d r ≤ 2 ^ d * q ^ (r * (d - r)) := by
  intro d
  induction d with
  | zero =>
    intro r
    cases r with
    | zero => simp [gaussBinom]
    | succ r => simp [gaussBinom]
  | succ d ih =>
    intro r
    cases r with
    | zero =>
      simp only [gaussBinom, Nat.zero_mul, pow_zero, Nat.mul_one]
      exact Nat.one_le_two_pow
    | succ r =>
      show gaussBinom q d r + q ^ (r + 1) * gaussBinom q d (r + 1)
        ≤ 2 ^ (d + 1) * q ^ ((r + 1) * (d + 1 - (r + 1)))
      rw [Nat.succ_sub_succ]
      by_cases hrd : r < d
      · have e2 : (r + 1) + (r + 1) * (d - (r + 1)) = (r + 1) * (d - r) := by
          have hd1 : d - r = (d - (r + 1)) + 1 := by omega
          rw [hd1]
          ring
        calc gaussBinom q d r + q ^ (r + 1) * gaussBinom q d (r + 1)
            ≤ 2 ^ d * q ^ (r * (d - r))
              + q ^ (r + 1) * (2 ^ d * q ^ ((r + 1) * (d - (r + 1)))) :=
              Nat.add_le_add (ih r) (Nat.mul_le_mul_left _ (ih (r + 1)))
          _ = 2 ^ d * q ^ (r * (d - r))
              + 2 ^ d * q ^ ((r + 1) + (r + 1) * (d - (r + 1))) := by ring
          _ = 2 ^ d * q ^ (r * (d - r)) + 2 ^ d * q ^ ((r + 1) * (d - r)) := by
              rw [e2]
          _ ≤ 2 ^ d * q ^ ((r + 1) * (d - r))
              + 2 ^ d * q ^ ((r + 1) * (d - r)) :=
              Nat.add_le_add_right (Nat.mul_le_mul_left _
                (Nat.pow_le_pow_right hq
                  (Nat.mul_le_mul_right _ (Nat.le_succ r)))) _
          _ = 2 ^ (d + 1) * q ^ ((r + 1) * (d - r)) := by ring
      · have hz : gaussBinom q d (r + 1) = 0 :=
          gaussBinom_eq_zero_of_lt (by omega)
        rw [hz, Nat.mul_zero, Nat.add_zero]
        by_cases hrd2 : r = d
        · subst hrd2
          calc gaussBinom q r r ≤ 2 ^ r * q ^ (r * (r - r)) := ih r
            _ = 2 ^ r := by simp
            _ ≤ 2 ^ (r + 1) * q ^ ((r + 1) * (r - r)) := by
                simp only [Nat.sub_self, Nat.mul_zero, pow_zero,
                  Nat.mul_one]
                exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ r)
        · rw [gaussBinom_eq_zero_of_lt (by omega)]
          exact Nat.zero_le _

theorem rdCoeff_le {n r d : ℕ} (hn : 1 ≤ n) (hrd : r ≤ d) :
    rdCoeff n r d ≤ 2 ^ d * n ^ d.choose 2 := by
  rw [rdCoeff]
  calc n ^ r.choose 2 * gaussBinom n d r
      ≤ n ^ r.choose 2 * (2 ^ d * n ^ (r * (d - r))) :=
        Nat.mul_le_mul_left _ (gaussBinom_le_pow hn d r)
    _ = 2 ^ d * n ^ (r.choose 2 + r * (d - r)) := by ring
    _ ≤ 2 ^ d * n ^ d.choose 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn (by
          have := choose_two_split hrd
          omega))

theorem gaussBinom_d_one_le {n : ℕ} (hn : 2 ≤ n) (d : ℕ) :
    gaussBinom n d 1 ≤ 2 * n ^ (d - 1) := by
  cases d with
  | zero => simp [gaussBinom]
  | succ e =>
    have hgeom := sub_one_mul_gaussBinom (by omega : 1 ≤ n) (e + 1)
    have hx : 2 * n ^ e ≤ n * n ^ e :=
      Nat.mul_le_mul_right _ hn
    have h1 : 1 ≤ n ^ e := Nat.one_le_pow _ _ (by omega)
    have key : (n - 1) * gaussBinom n (e + 1) 1 ≤ (n - 1) * (2 * n ^ e) := by
      rw [hgeom]
      have hpow : n ^ (e + 1) = n * n ^ e := by ring
      have hexp : (n - 1) * (2 * n ^ e) = 2 * (n * n ^ e) - 2 * n ^ e := by
        rw [Nat.sub_mul, one_mul]
        have : n * (2 * n ^ e) = 2 * (n * n ^ e) := by ring
        rw [this]
      rw [hpow, hexp]
      omega
    have := Nat.le_of_mul_le_mul_left key (show 0 < n - 1 by omega)
    simpa [Nat.add_sub_cancel] using this

theorem sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h4m : 4 * m ≤ m * m := Nat.mul_le_mul_right m hm
    have e1 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
    have e2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have e3 : m ^ 2 = m * m := by ring
    omega

theorem coeff_sum_le {d : ℕ} (hd : 1 ≤ d) :
    2 + (d - 2) * 2 ^ d ≤ 4 ^ d := by
  have hlt : d < 2 ^ d := Nat.lt_two_pow_self
  have h3 : (4 : ℕ) ^ d = 2 ^ d * 2 ^ d := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, Nat.mul_pow]
  have h4 : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have hself : 2 ^ d ≤ 2 ^ d * 2 ^ d :=
    Nat.le_mul_of_pos_left _ (by omega)
  calc 2 + (d - 2) * 2 ^ d
      ≤ 2 ^ d + (2 ^ d - 1) * 2 ^ d := by
        have h1 : (d - 2) * 2 ^ d ≤ (2 ^ d - 1) * 2 ^ d :=
          Nat.mul_le_mul_right _ (by omega)
        omega
    _ = 2 ^ d + (2 ^ d * 2 ^ d - 2 ^ d) := by
        rw [Nat.sub_mul, one_mul]
    _ = 2 ^ d * 2 ^ d := by omega
    _ = 4 ^ d := h3.symm

theorem exp_aux {d : ℕ} (hd : 3 ≤ d) :
    d + d.choose 2 + 1 ≤ 2 * 4 ^ (d - 2) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hc : (m + 1).choose 2 = m + m.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    have he : (4 : ℕ) ^ (m + 1 - 2) = 4 * 4 ^ (m - 2) := by
      have h1 : m + 1 - 2 = (m - 2) + 1 := by omega
      rw [h1]
      ring
    rw [hc, he]
    omega

theorem exp_ineq {n d : ℕ} (hn : 4 ≤ n) (hd : 3 ≤ d) :
    4 * d + n * d.choose 2 + 1 ≤ 2 * n ^ (d - 1) := by
  have haux := exp_aux hd
  have hAB : (4 : ℕ) ^ (d - 2) ≤ n ^ (d - 2) :=
    Nat.pow_le_pow_left hn _
  have e1 : n ^ (d - 1) = n ^ (d - 2) * n := by
    have h1 : d - 1 = (d - 2) + 1 := by omega
    rw [h1]
    ring
  have h5 : n * (d + d.choose 2 + 1) ≤ n * (2 * 4 ^ (d - 2)) :=
    Nat.mul_le_mul_left n haux
  have h6 : n * (2 * 4 ^ (d - 2)) ≤ n * (2 * n ^ (d - 2)) :=
    Nat.mul_le_mul_left n (Nat.mul_le_mul_left 2 hAB)
  have h7 : n * (d + d.choose 2 + 1)
      = n * d + n * d.choose 2 + n := by ring
  have h8 : 4 * d ≤ n * d := Nat.mul_le_mul_right d hn
  have h9 : n * (2 * n ^ (d - 2)) = 2 * (n ^ (d - 2) * n) := by ring
  omega

/-- **The core inequality of the composite case**: the total envelope
coefficient is beaten by `2^{n^{d−1}}` once `n ≥ 4`. -/
theorem envelope_coeff_lt_two_pow {n d : ℕ} (hn : 4 ≤ n) (hd : 1 ≤ d) :
    gaussBinom n d 1 + (d - 2) * 2 ^ d * n ^ d.choose 2
      < 2 ^ n ^ (d - 1) := by
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  · interval_cases d
    · -- d = 1
      have h1 : gaussBinom n 1 1 = 1 := by simp [gaussBinom]
      simp [h1]
    · -- d = 2
      have h1 : gaussBinom n 2 1 = 1 + n * 1 := by
        show gaussBinom n 1 0 + n ^ 1 * gaussBinom n 1 1 = 1 + n * 1
        have h2 : gaussBinom n 1 1 = 1 := by simp [gaussBinom]
        have h3 : gaussBinom n 1 0 = 1 := by simp [gaussBinom]
        rw [h2, h3, pow_one]
      have hsq := sq_le_two_pow hn
      have h4n : 4 * n ≤ n * n := Nat.mul_le_mul_right n hn
      have e3 : n ^ 2 = n * n := by ring
      simp only [h1]
      have hpow : n ^ (2 - 1) = n := by norm_num
      rw [hpow]
      omega
  · -- d ≥ 3
    have hcast : gaussBinom n d 1 ≤ 2 * n ^ d.choose 2 := by
      have h1 := gaussBinom_d_one_le (by omega : 2 ≤ n) d
      have h2 : n ^ (d - 1) ≤ n ^ d.choose 2 := by
        apply Nat.pow_le_pow_right (by omega)
        have h3 := two_mul_choose_two d
        have h4 : 2 * (d - 1) ≤ d * (d - 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      omega
    have hsum : gaussBinom n d 1 + (d - 2) * 2 ^ d * n ^ d.choose 2
        ≤ 4 ^ d * n ^ d.choose 2 := by
      have h5 := coeff_sum_le (by omega : 1 ≤ d)
      have h6 : (2 + (d - 2) * 2 ^ d) * n ^ d.choose 2
          ≤ 4 ^ d * n ^ d.choose 2 :=
        Nat.mul_le_mul_right _ h5
      have h7 : (2 + (d - 2) * 2 ^ d) * n ^ d.choose 2
          = 2 * n ^ d.choose 2 + (d - 2) * 2 ^ d * n ^ d.choose 2 := by
        ring
      omega
    -- squared comparison: (4^d n^C)² ≤ 2^{4d + nC} < 2^{2·n^{d−1}}
    have hsq2 : (4 ^ d * n ^ d.choose 2) ^ 2 < (2 ^ n ^ (d - 1)) ^ 2 := by
      have e4 : (4 : ℕ) ^ d = 2 ^ (2 * d) := by
        rw [pow_mul]
        norm_num
      have e1 : (4 ^ d * n ^ d.choose 2) ^ 2
          = 2 ^ (4 * d) * (n ^ 2) ^ d.choose 2 := by
        rw [mul_pow, e4, ← pow_mul, ← pow_mul, ← pow_mul,
          show 2 * d * 2 = 4 * d from by ring,
          show d.choose 2 * 2 = 2 * d.choose 2 from by ring]
      have e2 : ((2 : ℕ) ^ n ^ (d - 1)) ^ 2 = 2 ^ (2 * n ^ (d - 1)) := by
        rw [← pow_mul, show n ^ (d - 1) * 2 = 2 * n ^ (d - 1) from by ring]
      have h10 : (n ^ 2) ^ d.choose 2 ≤ (2 ^ n) ^ d.choose 2 :=
        Nat.pow_le_pow_left (sq_le_two_pow hn) _
      have h11 : 2 ^ (4 * d) * (n ^ 2) ^ d.choose 2
          ≤ 2 ^ (4 * d) * (2 ^ n) ^ d.choose 2 :=
        Nat.mul_le_mul_left _ h10
      have e3 : 2 ^ (4 * d) * ((2 : ℕ) ^ n) ^ d.choose 2
          = 2 ^ (4 * d + n * d.choose 2) := by
        rw [← pow_mul, ← pow_add]
      have h12 : (2 : ℕ) ^ (4 * d + n * d.choose 2)
          < 2 ^ (2 * n ^ (d - 1)) := by
        apply Nat.pow_lt_pow_right (by norm_num)
        have := exp_ineq hn hd3
        omega
      calc (4 ^ d * n ^ d.choose 2) ^ 2
          = 2 ^ (4 * d) * (n ^ 2) ^ d.choose 2 := e1
        _ ≤ 2 ^ (4 * d) * (2 ^ n) ^ d.choose 2 := h11
        _ = 2 ^ (4 * d + n * d.choose 2) := e3
        _ < 2 ^ (2 * n ^ (d - 1)) := h12
        _ = (2 ^ n ^ (d - 1)) ^ 2 := e2.symm
    have hlt : 4 ^ d * n ^ d.choose 2 < 2 ^ n ^ (d - 1) := by
      rcases Nat.lt_or_ge (4 ^ d * n ^ d.choose 2) (2 ^ n ^ (d - 1)) with
        h | h
      · exact h
      · exact absurd (Nat.pow_le_pow_left h 2) (Nat.not_le_of_lt hsq2)
    omega

end ShiftSym
