/-
Group 11 (Numerics), proof helpers, part 4: Observation 10.5(c) in general
form — for every alphabet `σ ≥ 2` and every prime `p ≥ 3`, once
`log₁₀[P_{(p+1)^d}/P_{p^d}] < 0`, it strictly decreases at `d + 1`.

Proof: one fixed set and the union bound give, with
`K = Σ_{q ∣ p+1} [d+1 1]_q` and `G = [d 1]_p`, the sufficient condition
`K·G^{p+1} ≤ σ^{(p−1)p^{d−1}}` (`deepens_core_nat`); it holds except for
`p = 3`, `(d, σ) ∈ {(2,2), (2,3), (3,2)}`, which are exact computations.
At `d = 1` the hypothesis is impossible.
-/
import Shiftsym.Paper.Proofs.P11_Numerics_Real

open Real

namespace ShiftSym.P11

open ShiftSym

/-! ### Bounds in the shape needed here -/

theorem pow_div_self' {p d : ℕ} (hp : 0 < p) (hd : 1 ≤ d) : p ^ d / p = p ^ (d - 1) := by
  rw [show p ^ d = p ^ (d - 1) * p by rw [← pow_succ]; congr 1; omega]
  exact Nat.mul_div_cancel _ hp

theorem numSS_prime_le {p d σ : ℕ} (hp : p.Prime) (hd : 1 ≤ d) :
    numSS p d σ ≤ gaussBinom p d 1 * σ ^ (p ^ (d - 1)) := by
  have h := numSS_le_union (n := p) (d := d) (σ := σ) hp.two_le
  rw [hp.primeFactors, Finset.sum_singleton, pow_div_self' hp.pos hd] at h
  exact h

theorem numSS_prime_ge {p d σ : ℕ} (hp : p.Prime) (hd : 1 ≤ d) :
    σ ^ (p ^ (d - 1)) ≤ numSS p d σ := by
  have h := numSS_ge_fix (σ := σ) hp.two_le hd hp (dvd_refl p)
  rwa [pow_div_self' hp.pos hd] at h

theorem gaussBinom_one_le_pow {q D : ℕ} (hq : 2 ≤ q) : gaussBinom q D 1 ≤ q ^ D := by
  have h := sub_one_mul_gaussBinom (by omega : 1 ≤ q) D
  have h1 : gaussBinom q D 1 ≤ (q - 1) * gaussBinom q D 1 :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem gaussBinom_one_pos' {q D : ℕ} (hq : 2 ≤ q) (hD : 1 ≤ D) : 0 < gaussBinom q D 1 :=
  gaussBinom_one_pos hq hD

/-- The union bound on the even side, all terms raised to the order-2 exponent. -/
theorem numSS_even_le {c D σ : ℕ} (hc : 2 ≤ c) (hσ : 1 ≤ σ) :
    numSS c D σ ≤ (∑ q ∈ c.primeFactors, gaussBinom q D 1) * σ ^ (c ^ D / 2) := by
  refine (numSS_le_union hc).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q hq
  have hq2 := (Nat.prime_of_mem_primeFactors hq).two_le
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right hσ (Nat.div_le_div_left hq2 (by norm_num))

/-- `Σ_{q ∣ c prime} [D 1]_q ≤ c^{D+1}`. -/
theorem sum_gauss_le {c D : ℕ} (hc : 1 ≤ c) :
    ∑ q ∈ c.primeFactors, gaussBinom q D 1 ≤ c ^ (D + 1) := by
  have h1 : ∑ q ∈ c.primeFactors, gaussBinom q D 1 ≤ ∑ _q ∈ c.primeFactors, c ^ D := by
    apply Finset.sum_le_sum
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqc : q ≤ c := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq)
    exact (gaussBinom_one_le_pow hqp.two_le).trans (Nat.pow_le_pow_left hqc D)
  have h2 : c.primeFactors.card ≤ c := by
    have hsub : c.primeFactors ⊆ Finset.Icc 1 c := by
      intro q hq
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqc : q ≤ c := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq)
      exact Finset.mem_Icc.mpr ⟨hqp.one_lt.le, hqc⟩
    have := Finset.card_le_card hsub
    simpa using this
  rw [Finset.sum_const, smul_eq_mul] at h1
  calc _ ≤ c.primeFactors.card * c ^ D := h1
    _ ≤ c * c ^ D := Nat.mul_le_mul_right _ h2
    _ = c ^ (D + 1) := by ring

/-! ### The core inequality -/

theorem deepens_core_nat {σ p c m v r K G Sc0 Sc1 Sp0 Sp1 : ℕ} (hσ : 1 ≤ σ) (hc : c = p + 1)
    (hp : 1 ≤ p) (hr : r + m = p * m)
    (hSc0 : σ ^ v ≤ Sc0) (hSc1 : Sc1 ≤ K * σ ^ (c * v)) (hSp0 : Sp0 ≤ G * σ ^ m)
    (hSp1 : σ ^ (p * m) ≤ Sp1) (hK : 0 < K) (hG : 0 < G)
    (hC : K * G ^ (p + 1) ≤ σ ^ r)
    (hyp : Sc0 * σ ^ (p * m) < Sp0 * σ ^ (2 * v)) :
    Sc1 * Sp0 * σ ^ (2 * v) * σ ^ (p * (p * m))
      < Sc0 * Sp1 * σ ^ (2 * (c * v)) * σ ^ (p * m) := by
  have hσp : ∀ k, 0 < σ ^ k := fun k => pow_pos (by omega) k
  have H0 : σ ^ v * σ ^ (p * m) < G * σ ^ m * σ ^ (2 * v) :=
    calc σ ^ v * σ ^ (p * m) ≤ Sc0 * σ ^ (p * m) := Nat.mul_le_mul_right _ hSc0
      _ < Sp0 * σ ^ (2 * v) := hyp
      _ ≤ G * σ ^ m * σ ^ (2 * v) := Nat.mul_le_mul_right _ hSp0
  have H1 : σ ^ (p * m) < G * σ ^ (m + v) := by
    have h : σ ^ (p * m) * σ ^ v < G * σ ^ (m + v) * σ ^ v := by
      calc σ ^ (p * m) * σ ^ v = σ ^ v * σ ^ (p * m) := Nat.mul_comm _ _
        _ < G * σ ^ m * σ ^ (2 * v) := H0
        _ = G * σ ^ (m + v) * σ ^ v := by rw [two_mul, pow_add, pow_add]; ring
    exact Nat.lt_of_mul_lt_mul_right h
  have H2 : σ ^ (p * (p * m)) < G ^ p * σ ^ (p * (m + v)) := by
    have h := Nat.pow_lt_pow_left H1 (by omega : p ≠ 0)
    rw [← pow_mul, mul_pow, ← pow_mul] at h
    rw [Nat.mul_comm p (p * m), Nat.mul_comm p (m + v)]
    exact h
  have hexp : r + (c * v + m + 2 * v + p * (m + v)) = v + p * m + 2 * (c * v) + p * m := by
    subst hc
    nlinarith [hr]
  calc Sc1 * Sp0 * σ ^ (2 * v) * σ ^ (p * (p * m))
      ≤ (K * σ ^ (c * v)) * (G * σ ^ m) * σ ^ (2 * v) * σ ^ (p * (p * m)) := by
        gcongr
    _ < (K * σ ^ (c * v)) * (G * σ ^ m) * σ ^ (2 * v) * (G ^ p * σ ^ (p * (m + v))) := by
        apply Nat.mul_lt_mul_of_pos_left H2
        have := hσp (c * v); have := hσp m; have := hσp (2 * v)
        positivity
    _ = (K * G ^ (p + 1)) * σ ^ (c * v + m + 2 * v + p * (m + v)) := by
        rw [pow_succ, pow_add, pow_add, pow_add]; ring
    _ ≤ σ ^ r * σ ^ (c * v + m + 2 * v + p * (m + v)) := Nat.mul_le_mul_right _ hC
    _ = σ ^ v * σ ^ (p * m) * σ ^ (2 * (c * v)) * σ ^ (p * m) := by
        rw [← pow_add, hexp, pow_add, pow_add, pow_add]
    _ ≤ Sc0 * Sp1 * σ ^ (2 * (c * v)) * σ ^ (p * m) := by
        gcongr

/-- The decrease `f(d+1) < f(d)` from a comparison of naturals. -/
theorem ilr_step_of_nat {σ p d : ℕ} (hσ1 : 1 ≤ σ) (hp : 2 ≤ p) (hd : 1 ≤ d)
    (h : numSS (p + 1) (d + 1) σ * numSS p d σ * σ ^ ((p + 1) ^ d) * σ ^ (p ^ (d + 1))
      < numSS (p + 1) d σ * numSS p (d + 1) σ * σ ^ ((p + 1) ^ (d + 1)) * σ ^ (p ^ d)) :
    inversionLogRatio σ p (d + 1) < inversionLogRatio σ p d := by
  rw [ilr_lt_iff hp hd (by omega) hσ1]
  have hp0 := probUnif_pos (n := p) (d := d) (σ := σ) hp hd hσ1
  have hp1 := probUnif_pos (n := p) (d := d + 1) (σ := σ) hp (by omega) hσ1
  rw [div_lt_div_iff₀ hp1 hp0]
  unfold probUnif
  have hs : (0 : ℝ) < σ := by exact_mod_cast (show 0 < σ by omega)
  rw [div_mul_div_comm, div_mul_div_comm, div_lt_div_iff₀ (by positivity) (by positivity)]
  have h' : ((numSS (p + 1) (d + 1) σ * numSS p d σ * σ ^ ((p + 1) ^ d) * σ ^ (p ^ (d + 1)) : ℕ) : ℝ)
      < ((numSS (p + 1) d σ * numSS p (d + 1) σ * σ ^ ((p + 1) ^ (d + 1)) * σ ^ (p ^ d) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith [h']

/-- From the condition `K·G^{p+1} ≤ σ^{(p−1)p^{d−1}}` to the decrease. -/
theorem deepens_of_cond {σ p d : ℕ} (hσ : 2 ≤ σ) (hp : p.Prime) (hp3 : 3 ≤ p) (hd : 1 ≤ d)
    (hC : (∑ q ∈ (p + 1).primeFactors, gaussBinom q (d + 1) 1) * gaussBinom p d 1 ^ (p + 1)
      ≤ σ ^ ((p - 1) * p ^ (d - 1)))
    (hneg : inversionLogRatio σ p d < 0) :
    inversionLogRatio σ p (d + 1) < inversionLogRatio σ p d := by
  have hσ1 : 1 ≤ σ := by omega
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hev : 2 ∣ p + 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  set c := p + 1 with hcdef
  set m := p ^ (d - 1) with hmdef
  set v := c ^ d / 2 with hvdef
  have hpd : p ^ d = p * m := by
    rw [hmdef, ← pow_succ']; congr 1; omega
  have hpd1 : p ^ (d + 1) = p * (p * m) := by rw [pow_succ', hpd]
  have hcd : c ^ d = 2 * v := by
    rw [hvdef]
    have : 2 ∣ c ^ d := dvd_pow hev (by omega)
    omega
  have hcd1 : c ^ (d + 1) = 2 * (c * v) := by rw [pow_succ', hcd]; ring
  have hcd1h : c ^ (d + 1) / 2 = c * v := by rw [hcd1]; omega
  -- the four bounds
  have hSc0 : σ ^ v ≤ numSS c d σ :=
    numSS_ge_fix (by omega) hd Nat.prime_two hev
  have hSc1 : numSS c (d + 1) σ
      ≤ (∑ q ∈ c.primeFactors, gaussBinom q (d + 1) 1) * σ ^ (c * v) := by
    have := numSS_even_le (c := c) (D := d + 1) (by omega) hσ1
    rwa [hcd1h] at this
  have hSp0 : numSS p d σ ≤ gaussBinom p d 1 * σ ^ m := numSS_prime_le hp hd
  have hSp1 : σ ^ (p * m) ≤ numSS p (d + 1) σ := by
    have := numSS_prime_ge (σ := σ) hp (by omega : 1 ≤ d + 1)
    rwa [Nat.add_sub_cancel, hpd] at this
  have hK : 0 < ∑ q ∈ c.primeFactors, gaussBinom q (d + 1) 1 := by
    have h2 : 2 ∈ c.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hev, by omega⟩
    exact lt_of_lt_of_le (gaussBinom_one_pos (le_refl 2) (by omega : 1 ≤ d + 1))
      (Finset.single_le_sum (f := fun q => gaussBinom q (d + 1) 1)
        (fun _ _ => Nat.zero_le _) h2)
  have hG : 0 < gaussBinom p d 1 := gaussBinom_one_pos hp.two_le hd
  have hr : (p - 1) * m + m = p * m := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  -- hypothesis in naturals
  have hyp : numSS c d σ * σ ^ (p * m) < numSS p d σ * σ ^ (2 * v) := by
    have h := (ilr_neg_iff hp.two_le hd hσ1).mp hneg
    rw [probUnif_lt_iff hσ1, hpd, hcd] at h
    exact h
  have core := deepens_core_nat hσ1 rfl (by omega) hr hSc0 hSc1 hSp0 hSp1 hK hG hC hyp
  apply ilr_step_of_nat hσ1 hp.two_le hd
  rw [hpd, hpd1, hcd, hcd1]
  exact core

/-! ### `d = 1`: the ratio is never negative -/

theorem gaussBinom_one_one (q : ℕ) : gaussBinom q 1 1 = 1 := by simp [gaussBinom]

theorem gaussBinom_two_one (q : ℕ) : gaussBinom q 2 1 = q + 1 := by
  simp [gaussBinom]; ring

theorem ilr_one_nonneg {σ p : ℕ} (hσ : 2 ≤ σ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    0 ≤ inversionLogRatio σ p 1 := by
  have hσ1 : 1 ≤ σ := by omega
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hev : 2 ∣ p + 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  rw [ilr_nonneg_iff hp.two_le le_rfl hσ1, probUnif_le_iff hσ1]
  have h1 : numSS p 1 σ ≤ σ := by
    have := numSS_prime_le (σ := σ) hp le_rfl
    simpa [gaussBinom_one_one] using this
  have h2 : σ ^ ((p + 1) / 2) ≤ numSS (p + 1) 1 σ := by
    have := numSS_ge_fix (σ := σ) (n := p + 1) (d := 1) (by omega) le_rfl Nat.prime_two hev
    simpa using this
  simp only [pow_one]
  calc numSS p 1 σ * σ ^ (p + 1) ≤ σ * σ ^ (p + 1) := Nat.mul_le_mul_right _ h1
    _ = σ ^ (p + 2) := by ring
    _ ≤ σ ^ ((p + 1) / 2 + p) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = σ ^ ((p + 1) / 2) * σ ^ p := by rw [pow_add]
    _ ≤ numSS (p + 1) 1 σ * σ ^ p := Nat.mul_le_mul_right _ h2

/-! ### The sufficient condition, case by case -/

theorem sq_succ_le_two_pow {p : ℕ} (hp : 7 ≤ p) : (p + 1) ^ 2 ≤ 2 ^ (p - 1) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have e : k + 1 - 1 = (k - 1) + 1 := by omega
    rw [e, pow_succ 2 (k - 1)]
    nlinarith [ih]

theorem lin_le_pow {p : ℕ} (hp : 3 ≤ p) (e : ℕ) : (e + 3) * (p + 2) + 2 ≤ 2 * p ^ (e + 2) := by
  induction e with
  | zero => norm_num; nlinarith
  | succ k ih =>
    have h1 : 1 ≤ p ^ (k + 2) := Nat.one_le_pow _ _ (by omega)
    have h2 : p ^ (k + 1 + 2) = p * p ^ (k + 2) := by ring
    rw [h2]
    nlinarith

/-- `(p+1)^E ≤ 2^{(p−1)Y}` from `(p+1)^2 ≤ 2^{p−1}` and `E ≤ 2Y`. -/
theorem pow_le_of_sq {p E Y : ℕ} (hsq : (p + 1) ^ 2 ≤ 2 ^ (p - 1)) (hE : E ≤ 2 * Y) :
    (p + 1) ^ E ≤ 2 ^ ((p - 1) * Y) := by
  have h : ((p + 1) ^ E) ^ 2 ≤ (2 ^ ((p - 1) * Y)) ^ 2 := by
    calc ((p + 1) ^ E) ^ 2 = ((p + 1) ^ 2) ^ E := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (2 ^ (p - 1)) ^ E := Nat.pow_le_pow_left hsq E
      _ = 2 ^ ((p - 1) * E) := by rw [← pow_mul]
      _ ≤ 2 ^ ((p - 1) * (2 * Y)) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hE)
      _ = (2 ^ ((p - 1) * Y)) ^ 2 := by rw [← pow_mul]; ring_nf
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h

theorem cond_ge7 {σ p d : ℕ} (hσ : 2 ≤ σ) (hp7 : 7 ≤ p) (hd : 2 ≤ d) :
    (∑ q ∈ (p + 1).primeFactors, gaussBinom q (d + 1) 1) * gaussBinom p d 1 ^ (p + 1)
      ≤ σ ^ ((p - 1) * p ^ (d - 1)) := by
  have hK := sum_gauss_le (c := p + 1) (D := d + 1) (by omega)
  have hsq := sq_succ_le_two_pow hp7
  have h2σ : 2 ^ ((p - 1) * p ^ (d - 1)) ≤ σ ^ ((p - 1) * p ^ (d - 1)) :=
    Nat.pow_le_pow_left hσ _
  refine le_trans ?_ h2σ
  rcases Nat.eq_or_lt_of_le hd with h | h
  · subst h
    rw [gaussBinom_two_one]
    calc (∑ q ∈ (p + 1).primeFactors, gaussBinom q (2 + 1) 1) * (p + 1) ^ (p + 1)
        ≤ (p + 1) ^ (2 + 1 + 1) * (p + 1) ^ (p + 1) := Nat.mul_le_mul_right _ hK
      _ = (p + 1) ^ (p + 5) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ ((p - 1) * p ^ (2 - 1)) := by
          apply pow_le_of_sq hsq
          simp only [Nat.add_one_sub_one, pow_one]
          omega
  · have hG : gaussBinom p d 1 ≤ (p + 1) ^ d :=
      (gaussBinom_one_le_pow (by omega)).trans (Nat.pow_le_pow_left (by omega) d)
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
    calc (∑ q ∈ (p + 1).primeFactors, gaussBinom q (e + 3 + 1) 1) * gaussBinom p (e + 3) 1 ^ (p + 1)
        ≤ (p + 1) ^ (e + 3 + 1 + 1) * ((p + 1) ^ (e + 3)) ^ (p + 1) :=
          Nat.mul_le_mul hK (Nat.pow_le_pow_left hG _)
      _ = (p + 1) ^ ((e + 3) * (p + 2) + 2) := by rw [← pow_mul, ← pow_add]; ring_nf
      _ ≤ 2 ^ ((p - 1) * p ^ (e + 3 - 1)) := by
          apply pow_le_of_sq hsq
          have := lin_le_pow (p := p) (by omega) e
          simpa using this

theorem pf_four : (3 + 1 : ℕ).primeFactors = {2} := by
  simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]

theorem pf_six : (5 + 1 : ℕ).primeFactors = {2, 3} := by
  simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]

theorem cond_five {σ d : ℕ} (hσ : 2 ≤ σ) (hd : 2 ≤ d) :
    (∑ q ∈ (5 + 1).primeFactors, gaussBinom q (d + 1) 1) * gaussBinom 5 d 1 ^ (5 + 1)
      ≤ σ ^ ((5 - 1) * 5 ^ (d - 1)) := by
  have h2σ : 2 ^ ((5 - 1) * 5 ^ (d - 1)) ≤ σ ^ ((5 - 1) * 5 ^ (d - 1)) :=
    Nat.pow_le_pow_left hσ _
  refine le_trans ?_ h2σ
  rcases Nat.eq_or_lt_of_le hd with h | h
  · subst h
    rw [pf_six]
    decide
  · have hK := sum_gauss_le (c := 5 + 1) (D := d + 1) (by omega)
    have hG : gaussBinom 5 d 1 ≤ 6 ^ d :=
      (gaussBinom_one_le_pow (by omega)).trans (Nat.pow_le_pow_left (by omega) d)
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
    have hlin : ∀ k : ℕ, 3 * (7 * (k + 3) + 2) ≤ 4 * 5 ^ (k + 2) := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        have h2 : 5 ^ (k + 1 + 2) = 5 * 5 ^ (k + 2) := by ring
        rw [h2]; nlinarith
    calc (∑ q ∈ (5 + 1).primeFactors, gaussBinom q (e + 3 + 1) 1) * gaussBinom 5 (e + 3) 1 ^ (5 + 1)
        ≤ 6 ^ (e + 3 + 1 + 1) * (6 ^ (e + 3)) ^ (5 + 1) :=
          Nat.mul_le_mul hK (Nat.pow_le_pow_left hG _)
      _ = 6 ^ (7 * (e + 3) + 2) := by rw [← pow_mul, ← pow_add]; ring_nf
      _ ≤ 8 ^ (7 * (e + 3) + 2) := Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ (3 * (7 * (e + 3) + 2)) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ ((5 - 1) * 5 ^ (e + 3 - 1)) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have := hlin e
          simpa using this

theorem cond_three {σ d : ℕ} (hσ : 2 ≤ σ) (hd : 2 ≤ d)
    (hex : ¬ (d = 2 ∧ σ ≤ 3) ∧ ¬ (d = 3 ∧ σ = 2)) :
    (∑ q ∈ (3 + 1).primeFactors, gaussBinom q (d + 1) 1) * gaussBinom 3 d 1 ^ (3 + 1)
      ≤ σ ^ ((3 - 1) * 3 ^ (d - 1)) := by
  rw [pf_four, Finset.sum_singleton]
  rcases Nat.lt_or_ge d 4 with h | h
  · interval_cases d
    · have hσ4 : 4 ≤ σ := by omega
      calc gaussBinom 2 (2 + 1) 1 * gaussBinom 3 2 1 ^ (3 + 1) ≤ 4 ^ ((3 - 1) * 3 ^ (2 - 1)) := by
            decide
        _ ≤ σ ^ ((3 - 1) * 3 ^ (2 - 1)) := Nat.pow_le_pow_left hσ4 _
    · have hσ3 : 3 ≤ σ := by omega
      calc gaussBinom 2 (3 + 1) 1 * gaussBinom 3 3 1 ^ (3 + 1) ≤ 3 ^ ((3 - 1) * 3 ^ (3 - 1)) := by
            decide
        _ ≤ σ ^ ((3 - 1) * 3 ^ (3 - 1)) := Nat.pow_le_pow_left hσ3 _
  · have hK : gaussBinom 2 (d + 1) 1 ≤ 2 ^ (d + 1) := gaussBinom_one_le_pow le_rfl
    have hG : gaussBinom 3 d 1 ≤ 4 ^ d :=
      (gaussBinom_one_le_pow (by omega)).trans (Nat.pow_le_pow_left (by omega) d)
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 4 := ⟨d - 4, by omega⟩
    have hlin : ∀ k : ℕ, 9 * (k + 4) + 1 ≤ 2 * 3 ^ (k + 3) := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        have h2 : 3 ^ (k + 1 + 3) = 3 * 3 ^ (k + 3) := by ring
        rw [h2]; nlinarith
    calc gaussBinom 2 (e + 4 + 1) 1 * gaussBinom 3 (e + 4) 1 ^ (3 + 1)
        ≤ 2 ^ (e + 4 + 1) * (4 ^ (e + 4)) ^ (3 + 1) := Nat.mul_le_mul hK (Nat.pow_le_pow_left hG _)
      _ = 2 ^ (9 * (e + 4) + 1) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]; ring_nf
      _ ≤ 2 ^ ((3 - 1) * 3 ^ (e + 4 - 1)) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have := hlin e
          simpa using this
      _ ≤ σ ^ ((3 - 1) * 3 ^ (e + 4 - 1)) := Nat.pow_le_pow_left hσ _

/-! ### The three exceptional cases (`p = 3`) -/

theorem numSS3 (d σ : ℕ) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    (numSS 3 d σ : ℤ) = lowerEnvelope 3 d σ := numSS_prime_int Nat.prime_three hd hσ

theorem numSS_four_le (D σ : ℕ) (hσ : 1 ≤ σ) :
    numSS 4 D σ ≤ gaussBinom 2 D 1 * σ ^ (4 ^ D / 2) := by
  have h := numSS_even_le (c := 4) (D := D) (σ := σ) (by norm_num) hσ
  have hpf : (4 : ℕ).primeFactors = {2} := by simp [Nat.primeFactors, Nat.primeFactorsList_ofNat]
  rwa [hpf, Finset.sum_singleton] at h

theorem numSS_four_ge (D σ : ℕ) (hD : 1 ≤ D) : σ ^ (4 ^ D / 2) ≤ numSS 4 D σ :=
  numSS_ge_fix (by norm_num) hD Nat.prime_two (by norm_num)

theorem numSS_prime_val {p d σ : ℕ} (hp : p.Prime) (hd : 1 ≤ d) (hσ : 1 ≤ σ) (v : ℕ)
    (h : lowerEnvelope p d σ = (v : ℤ)) : numSS p d σ = v := by
  have := numSS_prime_int hp hd hσ
  rw [h] at this
  exact_mod_cast this

theorem exc_generic {σ d a b : ℕ} (hσ1 : 1 ≤ σ) (hd : 1 ≤ d) (ha : numSS 3 d σ = a)
    (hb : numSS 3 (d + 1) σ = b)
    (h : gaussBinom 2 (d + 1) 1 * σ ^ (4 ^ (d + 1) / 2) * a * σ ^ (4 ^ d) * σ ^ (3 ^ (d + 1))
      < σ ^ (4 ^ d / 2) * b * σ ^ (4 ^ (d + 1)) * σ ^ (3 ^ d)) :
    inversionLogRatio σ 3 (d + 1) < inversionLogRatio σ 3 d := by
  apply ilr_step_of_nat hσ1 (by norm_num) hd
  have hU := numSS_four_le (d + 1) σ hσ1
  have hL := numSS_four_ge d σ hd
  rw [ha, hb]
  calc numSS (3 + 1) (d + 1) σ * a * σ ^ ((3 + 1) ^ d) * σ ^ (3 ^ (d + 1))
      ≤ gaussBinom 2 (d + 1) 1 * σ ^ (4 ^ (d + 1) / 2) * a * σ ^ (4 ^ d) * σ ^ (3 ^ (d + 1)) := by
        gcongr
    _ < σ ^ (4 ^ d / 2) * b * σ ^ (4 ^ (d + 1)) * σ ^ (3 ^ d) := h
    _ ≤ numSS (3 + 1) d σ * b * σ ^ ((3 + 1) ^ (d + 1)) * σ ^ (3 ^ d) := by
        gcongr

theorem exc_2_2 : inversionLogRatio 2 3 (2 + 1) < inversionLogRatio 2 3 2 :=
  exc_generic (a := 26) (b := 6398) (by norm_num) (by norm_num)
    (numSS_prime_val Nat.prime_three (by norm_num) (by norm_num) 26 (by decide))
    (numSS_prime_val Nat.prime_three (by norm_num) (by norm_num) 6398 (by decide))
    (by decide +kernel)

theorem exc_2_3 : inversionLogRatio 3 3 (2 + 1) < inversionLogRatio 3 3 2 :=
  exc_generic (a := 99) (b := 254907) (by norm_num) (by norm_num)
    (numSS_prime_val Nat.prime_three (by norm_num) (by norm_num) 99 (by decide))
    (numSS_prime_val Nat.prime_three (by norm_num) (by norm_num) 254907 (by decide))
    (by decide +kernel)

theorem exc_3_2 : inversionLogRatio 2 3 (3 + 1) < inversionLogRatio 2 3 3 :=
  exc_generic (a := 6398) (b := 5368516622) (by norm_num) (by norm_num)
    (numSS_prime_val Nat.prime_three (by norm_num) (by norm_num) 6398 (by decide))
    (numSS_prime_val Nat.prime_three (by norm_num) (by norm_num) 5368516622 (by decide))
    (by decide +kernel)

/-! ### Observation 10.5(c), general form -/

theorem inversionDeepens_thm (σ : ℕ) (hσ : 2 ≤ σ) (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hneg : inversionLogRatio σ p d < 0) :
    inversionLogRatio σ p (d + 1) < inversionLogRatio σ p d := by
  rcases Nat.eq_or_lt_of_le hd with h1 | h2
  · subst h1
    exact absurd hneg (not_lt.mpr (ilr_one_nonneg hσ hp hp3))
  have hd2 : 2 ≤ d := h2
  rcases Nat.lt_or_ge p 7 with hlt | hge
  · -- p ∈ {3, 5}
    have hp35 : p = 3 ∨ p = 5 := by
      interval_cases p <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hp; decide)
    rcases hp35 with rfl | rfl
    · by_cases hex : (d = 2 ∧ σ ≤ 3) ∨ (d = 3 ∧ σ = 2)
      · rcases hex with ⟨hd', hσ'⟩ | ⟨hd', hσ'⟩
        · subst hd'
          interval_cases σ
          · exact exc_2_2
          · exact exc_2_3
        · subst hd' hσ'
          exact exc_3_2
      · push Not at hex
        exact deepens_of_cond hσ hp hp3 hd (cond_three hσ hd2 ⟨fun h => by omega, fun h => by omega⟩)
          hneg
    · exact deepens_of_cond hσ hp hp3 hd (cond_five hσ hd2) hneg
  · exact deepens_of_cond hσ hp hp3 hd (cond_ge7 hσ hge hd2) hneg

end ShiftSym.P11
