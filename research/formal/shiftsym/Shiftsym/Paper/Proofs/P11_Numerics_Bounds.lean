/-
Group 11 (Numerics), proof helpers, part 1: general facts about `|S|`
used by the exact computations of `P11_Numerics.lean`.

* `numSS_ge_fix`   — one fixed set: `σ^{N/q} ≤ |S|` for a prime `q ∣ n`;
* `numSS_le_union` — the union bound over prime-order subgroups:
  `|S| ≤ Σ_{q ∣ n prime} [d 1]_q σ^{N/q}`;
* `numSS_prime_int`, `lowerEnvelope_ge` — the prime case of Theorem 4.3
  and its first two terms as a lower bound;
* `enumerationRHS_primePow`, `enumerationRHS_twoPrime` — the closed form
  for `rad n = p` and `rad n = p q`, in a kernel-evaluable shape.
All results rest on the certified `enumeration_proved`.
-/
import Shiftsym.Paper.S11_Numerics
import Shiftsym.Lemmas.Evaluate
import Shiftsym.Lemmas.LowerBound
import Shiftsym.Lemmas.PrimeCase

open scoped Classical

namespace ShiftSym.P11

open ShiftSym

/-- `|S|` as an integer is the certified closed form (Theorem 4.3). -/
theorem numSS_int (n d σ : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    (numSS n d σ : ℤ) = enumerationRHS n d σ :=
  enumeration_proved n d σ hn hd hσ

/-- Prime case of Theorem 4.3 (Corollary 4.4). -/
theorem numSS_prime_int {p d σ : ℕ} (hp : p.Prime) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    (numSS p d σ : ℤ) = lowerEnvelope p d σ := by
  rw [numSS_int p d σ hp.two_le hd hσ, enumerationRHS_prime hp]

/-- One fixed set: `σ^{n^d/q} ≤ |S_{n^d}|` for every prime `q ∣ n`. -/
theorem numSS_ge_fix {n d σ q : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hq : q.Prime)
    (hqn : q ∣ n) : σ ^ (n ^ d / q) ≤ numSS n d σ := by
  have : NeZero n := ⟨by omega⟩
  unfold numSS
  rw [natCard_shiftSymmetric_eq_filterCard]
  exact card_SS_ge_fix σ hq hqn hd

/-- The union bound over prime-order subgroups:
`|S_{n^d}| ≤ Σ_{q ∣ n prime} [d 1]_q σ^{n^d/q}`. -/
theorem numSS_le_union {n d σ : ℕ} (hn : 2 ≤ n) :
    numSS n d σ ≤ ∑ q ∈ n.primeFactors, gaussBinom q d 1 * σ ^ (n ^ d / q) := by
  have : NeZero n := ⟨by omega⟩
  unfold numSS
  rw [natCard_shiftSymmetric_eq_filterCard]
  have hunion : Finset.univ.filter (fun s : Config n d (Fin σ) => IsShiftSymmetric s)
      = (primeOrderSubs n d).biUnion (fun C => fixedByF σ C) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isShiftSymmetric_iff_mem_biUnion σ s
  rw [hunion]
  refine Finset.card_biUnion_le.trans ?_
  simp_rw [card_fixedByF]
  have hmaps : ∀ C ∈ primeOrderSubs n d, Nat.card C ∈ n.primeFactors := by
    intro C hC
    rw [mem_primeOrderSubs] at hC
    have hdvd : Nat.card C ∣ n ^ d := by
      have := AddSubgroup.card_addSubgroup_dvd_card C
      rwa [card_lat] at this
    exact Nat.mem_primeFactors.mpr ⟨hC, hC.dvd_of_dvd_pow hdvd, by omega⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqn := Nat.dvd_of_mem_primeFactors hq
  rw [Finset.sum_congr rfl (fun C hC => by rw [(Finset.mem_filter.mp hC).2])]
  rw [Finset.sum_const, smul_eq_mul]
  apply Nat.mul_le_mul_right
  rw [← card_orderP_subgroups (n := n) (d := d) hqp hqn, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  apply Finset.card_le_card
  intro C hC
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
  exact hC.2

/-- The first two terms of Corollary 4.4 bound the prime case from below:
`F_d(p,σ) ≥ r_d(p,1) σ^{p^{d-1}} − (Σ_{r=2}^d r_d(p,r)) σ^{p^{d-2}}`. -/
theorem lowerEnvelope_ge (p d σ : ℕ) (hp : 1 ≤ p) (hd : 2 ≤ d) (hσ : 1 ≤ σ) :
    (rdCoeff p 1 d : ℤ) * (σ : ℤ) ^ (p ^ (d - 1))
      - (∑ r ∈ Finset.Icc 2 d, (rdCoeff p r d : ℤ)) * (σ : ℤ) ^ (p ^ (d - 2))
      ≤ lowerEnvelope p d σ := by
  unfold lowerEnvelope
  have hsplit : Finset.Icc 1 d = insert 1 (Finset.Icc 2 d) := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have h1 : (-1 : ℤ) ^ (1 + 1) * (rdCoeff p 1 d : ℤ) * (σ : ℤ) ^ (p ^ (d - 1))
      = (rdCoeff p 1 d : ℤ) * (σ : ℤ) ^ (p ^ (d - 1)) := by norm_num
  rw [h1]
  have h2 : -((∑ r ∈ Finset.Icc 2 d, (rdCoeff p r d : ℤ)) * (σ : ℤ) ^ (p ^ (d - 2)))
      ≤ ∑ r ∈ Finset.Icc 2 d,
          (-1 : ℤ) ^ (r + 1) * (rdCoeff p r d : ℤ) * (σ : ℤ) ^ (p ^ (d - r)) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro r hr
    obtain ⟨hr2, hrd⟩ := Finset.mem_Icc.mp hr
    have hσ' : (1 : ℤ) ≤ σ := by exact_mod_cast hσ
    have hpow : (σ : ℤ) ^ (p ^ (d - r)) ≤ (σ : ℤ) ^ (p ^ (d - 2)) :=
      pow_le_pow_right₀ hσ' (Nat.pow_le_pow_right hp (by omega))
    have hpos : (0 : ℤ) ≤ (σ : ℤ) ^ (p ^ (d - r)) := by positivity
    have hc : (0 : ℤ) ≤ (rdCoeff p r d : ℤ) := by positivity
    rcases neg_one_pow_eq_or ℤ (r + 1) with h | h <;> rw [h] <;> nlinarith
  linarith

theorem gaussBinom_zero_right (q d : ℕ) : gaussBinom q d 0 = 1 := by
  cases d <;> rfl

theorem rdCoeff_zero (q d : ℕ) : rdCoeff q 0 d = 1 := by
  simp [rdCoeff, gaussBinom_zero_right]

theorem rad_primePow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : rad (p ^ k) = p := by
  rw [rad, Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton]

/-- Closed form for `rad n = p` (prime powers `n = p^k`). -/
theorem enumerationRHS_primePow {n p : ℕ} (pp : p.Prime) (hrad : rad n = p) (d σ : ℕ) :
    enumerationRHS n d σ
      = ∑ r ∈ Finset.Icc 1 d,
          (-1 : ℤ) ^ (r + 1) * (rdCoeff p r d : ℤ) * (((σ ^ (n ^ d / p ^ r)) : ℕ) : ℤ) := by
  have hst : ((p : ℕ) ^ d).divisors.erase 1
      = (Finset.Icc 1 d).map
          ⟨(p ^ ·), Nat.pow_right_injective pp.two_le⟩ := by
    rw [Nat.divisors_prime_pow pp]
    have hIcc : Finset.Icc 1 d = (Finset.range (d + 1)).erase 0 := by
      ext a
      rw [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
      omega
    rw [hIcc, Finset.map_erase]
    congr 1
  rw [enumerationRHS, hrad, hst, Finset.sum_map]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨hr1, hrd⟩ := Finset.mem_Icc.mp hr
  simp only [Function.Embedding.coeFn_mk]
  rw [coeffOf_prime_pow pp hr1 d]
  push_cast
  ring

/-- Closed form for `rad n = p q` with distinct primes `p, q`, as a double
sum over the exponents (the `(0,0)` term is `−σ^{n^d}`, compensated). -/
theorem enumerationRHS_twoPrime {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hrad : rad n = p * q) (d σ : ℕ) :
    enumerationRHS n d σ
      = (∑ a ∈ Finset.range (d + 1), ∑ b ∈ Finset.range (d + 1),
          (-1 : ℤ) ^ (1 + a + b) * (rdCoeff p a d : ℤ) * (rdCoeff q b d : ℤ) *
            (((σ ^ (n ^ d / (p ^ a * q ^ b))) : ℕ) : ℤ))
        + (((σ ^ (n ^ d)) : ℕ) : ℤ) := by
  have hpq0 : p * q ≠ 0 := Nat.mul_ne_zero hp.ne_zero hq.ne_zero
  have hdiv : ((p * q) ^ d).divisors
      = ((Finset.range (d + 1)) ×ˢ (Finset.range (d + 1))).image
          (fun ab => p ^ ab.1 * q ^ ab.2) := by
    ext h
    simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨hdvd, -⟩
      rw [mul_pow] at hdvd
      obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp hdvd
      obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow hp).mp hy
      obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow hq).mp hz
      exact ⟨(a, b), ⟨by omega, by omega⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      refine ⟨?_, pow_ne_zero _ hpq0⟩
      rw [mul_pow]
      exact mul_dvd_mul (pow_dvd_pow _ (by omega)) (pow_dvd_pow _ (by omega))
  have hfac : ∀ a b : ℕ, (p ^ a * q ^ b).factorization
      = Finsupp.single p a + Finsupp.single q b := by
    intro a b
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
      hp.factorization_pow, hq.factorization_pow]
  have hfp : ∀ a b : ℕ, (p ^ a * q ^ b).factorization p = a := by
    intro a b
    rw [hfac]
    simp [hpq]
  have hfq : ∀ a b : ℕ, (p ^ a * q ^ b).factorization q = b := by
    intro a b
    rw [hfac]
    simp [Ne.symm hpq]
  have hinj : Set.InjOn (fun ab : ℕ × ℕ => p ^ ab.1 * q ^ ab.2)
      ↑((Finset.range (d + 1)) ×ˢ (Finset.range (d + 1))) := by
    rintro ⟨a, b⟩ - ⟨a', b'⟩ - h
    simp only at h
    have h1 := hfp a b
    have h2 := hfq a b
    rw [h, hfp] at h1
    rw [h, hfq] at h2
    rw [h1, h2]
  have hcoeff : ∀ a b : ℕ, coeffOf d (p ^ a * q ^ b)
      = (-1 : ℤ) ^ (1 + a + b) * (rdCoeff p a d : ℤ) * (rdCoeff q b d : ℤ) := by
    intro a b
    have hbig : bigOmega (p ^ a * q ^ b) = a + b := by
      rw [bigOmega, hfac, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
    have hsub : (p ^ a * q ^ b).primeFactors ⊆ {p, q} := by
      intro x hx
      have hxp := Nat.prime_of_mem_primeFactors hx
      have hxd := Nat.dvd_of_mem_primeFactors hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases (Nat.Prime.dvd_mul hxp).mp hxd with h | h
      · left; exact (Nat.prime_dvd_prime_iff_eq hxp hp).mp (hxp.dvd_of_dvd_pow h)
      · right; exact (Nat.prime_dvd_prime_iff_eq hxp hq).mp (hxp.dvd_of_dvd_pow h)
    have hprod : ∏ r ∈ (p ^ a * q ^ b).primeFactors,
          (rdCoeff r ((p ^ a * q ^ b).factorization r) d : ℤ)
        = (rdCoeff p a d : ℤ) * (rdCoeff q b d : ℤ) := by
      rw [Finset.prod_subset hsub]
      · rw [Finset.prod_pair hpq, hfp, hfq]
      · intro x _ hx
        have hx0 : (p ^ a * q ^ b).factorization x = 0 :=
          Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
        rw [hx0, rdCoeff_zero]
        norm_num
    rw [coeffOf, hbig, hprod]
    ring
  have h1mem : (1 : ℕ) ∈ ((p * q) ^ d).divisors :=
    Nat.one_mem_divisors.mpr (pow_ne_zero _ hpq0)
  have hc1 : coeffOf d 1 = -1 := by simp [coeffOf, bigOmega]
  rw [enumerationRHS, hrad, Finset.sum_erase_eq_sub h1mem, hc1, hdiv,
    Finset.sum_image hinj, Finset.sum_product]
  simp only [hcoeff, Nat.div_one]
  push_cast
  ring

end ShiftSym.P11
