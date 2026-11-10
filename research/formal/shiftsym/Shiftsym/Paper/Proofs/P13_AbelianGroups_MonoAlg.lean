/-
Paper group 13 (Section 4.5) — proof helper module for Corollary 4.8(ii) (`cor:abelian-ranks`):
the algebra of the right-hand side of Theorem 4.7 in complement form.

* `cq q e v = (-1)^v q^(v choose 2) [e v]_q` and the step rule
  `cq q e (v+1) - cq q (e+1) (v+1) = q^e cq q e v` (`cq_step`), from the second `q`-Pascal rule
  `[n+1, k+1]_q = q^(n-k) [n, k]_q + [n, k+1]_q` (`gaussBinom_pascal2`, proved from the defining
  recurrence for every `q`);
* the complement sum `FF σ P e M = Σ_{h ∣ ∏_{q ∈ P} q^(e q)} (∏_{q ∣ h} cq q (e q) v_q(h)) σ^(M/h)`;
  `σ^N - abelianRHS N e σ = FF σ N.primeFactors e N` (`acR_eq_FF`);
* splitting one prime off the divisor sum (`FF_insert`), and the step identity
  `ac(N, e) - ac(N, e + e_p) = p^(e p) ac(N/p, e)` (`acR_step`).

Helpers live in `ShiftSym.P13.Mono`. Frozen statements: `Shiftsym/Paper/S13_AbelianGroups.lean`.
-/
import Shiftsym.Paper.Proofs.P13_AbelianGroups

namespace ShiftSym.P13.Mono

open ShiftSym ShiftSym.P13

/-! ### The second `q`-Pascal rule -/

theorem gaussBinom_zero_right (q d : ℕ) : gaussBinom q d 0 = 1 := by
  cases d <;> rfl

theorem gaussBinom_succ_succ (q d r : ℕ) :
    gaussBinom q (d + 1) (r + 1) = gaussBinom q d r + q ^ (r + 1) * gaussBinom q d (r + 1) :=
  rfl

theorem gaussBinom_self (q : ℕ) : ∀ d : ℕ, gaussBinom q d d = 1
  | 0 => rfl
  | d + 1 => by
    rw [gaussBinom_succ_succ, gaussBinom_self q d, gaussBinom_eq_zero_of_lt (by omega)]
    simp

/-- The second `q`-Pascal rule `[n+1, k+1] = q^m [n, k] + [n, k+1]` for `n = k + m`
(every `q`). -/
theorem gaussBinom_pascal2 (q : ℕ) : ∀ n k m : ℕ, k + m = n →
    (gaussBinom q (n + 1) (k + 1) : ℤ)
      = (q : ℤ) ^ m * gaussBinom q n k + gaussBinom q n (k + 1) := by
  intro n
  induction n with
  | zero =>
    intro k m hkm
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ m = 0 := by omega
    simp [gaussBinom]
  | succ n ih =>
    intro k m hkm
    rcases k with _ | k
    · -- `k = 0`, `m = n + 1`
      obtain rfl : m = n + 1 := by omega
      have E0 := ih 0 n (by omega)
      have Ra : (gaussBinom q (n + 1 + 1) (0 + 1) : ℤ)
          = gaussBinom q (n + 1) 0 + (q : ℤ) ^ (0 + 1) * gaussBinom q (n + 1) (0 + 1) := by
        rw [gaussBinom_succ_succ]; push_cast; ring
      have Rb : (gaussBinom q (n + 1) (0 + 1) : ℤ)
          = gaussBinom q n 0 + (q : ℤ) ^ (0 + 1) * gaussBinom q n (0 + 1) := by
        rw [gaussBinom_succ_succ]; push_cast; ring
      rw [gaussBinom_zero_right] at Ra Rb E0
      rw [Ra, gaussBinom_zero_right]
      push_cast at Ra Rb E0 ⊢
      linear_combination (q : ℤ) * E0 - Rb
    · rcases m with _ | m
      · -- `m = 0`, `k = n`
        obtain rfl : k = n := by omega
        rw [gaussBinom_self, gaussBinom_self, gaussBinom_eq_zero_of_lt (by omega)]
        simp
      · -- `k + 1 + (m + 1) = n + 1`
        have E1 := ih k (m + 1) (by omega)
        have E2 := ih (k + 1) m (by omega)
        have E3 : (gaussBinom q (n + 1) (k + 1) : ℤ)
            = gaussBinom q n k + (q : ℤ) ^ (k + 1) * gaussBinom q n (k + 1) := by
          rw [gaussBinom_succ_succ]; push_cast; ring
        have E4 : (gaussBinom q (n + 1) (k + 1 + 1) : ℤ)
            = gaussBinom q n (k + 1) + (q : ℤ) ^ (k + 1 + 1) * gaussBinom q n (k + 1 + 1) := by
          rw [gaussBinom_succ_succ]; push_cast; ring
        have G : (gaussBinom q (n + 1 + 1) (k + 1 + 1) : ℤ)
            = gaussBinom q (n + 1) (k + 1)
              + (q : ℤ) ^ (k + 1 + 1) * gaussBinom q (n + 1) (k + 1 + 1) := by
          rw [gaussBinom_succ_succ]; push_cast; ring
        rw [G]
        linear_combination E1 + (q : ℤ) ^ (k + 1 + 1) * E2 - (q : ℤ) ^ (m + 1) * E3 - E4

/-! ### The coefficients `c(q, e, v)` -/

/-- `c(q, e, v) = (-1)^v q^(v choose 2) [e v]_q`, i.e. `(-1)^v r_e(q, v)`. -/
def cq (q e v : ℕ) : ℤ := (-1 : ℤ) ^ v * (rdCoeff q v e : ℤ)

theorem cq_zero (q e : ℕ) : cq q e 0 = 1 := by
  simp [cq, rdCoeff, gaussBinom_zero_right]

theorem cq_eq_zero {q e v : ℕ} (h : e < v) : cq q e v = 0 := by
  simp [cq, rdCoeff, gaussBinom_eq_zero_of_lt h]

/-- `c(q, e, v+1) - c(q, e+1, v+1) = q^e c(q, e, v)` for `v ≤ e`. -/
theorem cq_step (q : ℕ) {e v : ℕ} (hv : v ≤ e) :
    cq q e (v + 1) - cq q (e + 1) (v + 1) = (q : ℤ) ^ e * cq q e v := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hv
  have P := gaussBinom_pascal2 q (v + m) v m rfl
  have hch : (v + 1).choose 2 = v.choose 2 + v := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  simp only [cq, rdCoeff]
  push_cast
  rw [P, hch]
  ring

/-! ### The complement sum -/

/-- `∏_{q ∈ P} q ^ e q`. -/
def radP (P : Finset ℕ) (e : ℕ → ℕ) : ℕ := ∏ q ∈ P, q ^ e q

/-- The complement coefficient of a divisor `h`: `∏_{q ∣ h} c(q, e q, v_q(h))`. -/
noncomputable def negC (e : ℕ → ℕ) (h : ℕ) : ℤ :=
  ∏ q ∈ h.primeFactors, cq q (e q) (h.factorization q)

/-- The complement sum `Σ_{h ∣ radP P e} negC e h σ^(M/h)`. -/
noncomputable def FF (σ : ℕ) (P : Finset ℕ) (e : ℕ → ℕ) (M : ℕ) : ℤ :=
  ∑ h ∈ (radP P e).divisors, negC e h * (σ : ℤ) ^ (M / h)

theorem radP_ne_zero {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) (e : ℕ → ℕ) : radP P e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun q hq => pow_ne_zero _ (hP q hq).ne_zero

theorem primeFactors_radP_subset {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) (e : ℕ → ℕ) :
    (radP P e).primeFactors ⊆ P := by
  intro q hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqd : q ∣ radP P e := Nat.dvd_of_mem_primeFactors hq
  obtain ⟨r, hr, hqr⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).mp hqd
  have heq : q = r := (Nat.prime_dvd_prime_iff_eq hqp (hP r hr)).mp (hqp.dvd_of_dvd_pow hqr)
  exact heq ▸ hr

theorem negC_superset (e : ℕ → ℕ) {h : ℕ} {S : Finset ℕ} (hS : h.primeFactors ⊆ S) :
    negC e h = ∏ q ∈ S, cq q (e q) (h.factorization q) := by
  unfold negC
  refine Finset.prod_subset hS fun q _ hq => ?_
  have h0 : h.factorization q = 0 := by
    rw [← Nat.support_factorization] at hq
    exact Finsupp.notMem_support_iff.mp hq
  rw [h0, cq_zero]

theorem negC_congr {e e' : ℕ → ℕ} {h : ℕ} (he : ∀ q ∈ h.primeFactors, e q = e' q) :
    negC e h = negC e' h :=
  Finset.prod_congr rfl fun q hq => by rw [he q hq]

theorem negC_one (e : ℕ → ℕ) : negC e 1 = 1 := by
  simp [negC]

theorem negC_eq_neg_coeffA (e : ℕ → ℕ) (h : ℕ) : negC e h = - coeffA e h := by
  unfold negC coeffA cq
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hΩ : bigOmega h = ∑ q ∈ h.primeFactors, h.factorization q := by
    rw [bigOmega, ← Nat.support_factorization]
    rfl
  rw [hΩ, pow_add, pow_one]
  ring

/-- `σ^N - abelianRHS N e σ` is the complement sum over `N.primeFactors`. -/
theorem acR_eq_FF (N : ℕ) (e : ℕ → ℕ) (σ : ℕ) :
    (σ : ℤ) ^ N - abelianRHS N e σ = FF σ N.primeFactors e N := by
  unfold FF abelianRHS
  have hR : radP N.primeFactors e = rankRad N e := rfl
  rw [hR]
  have h1 : (1 : ℕ) ∈ (rankRad N e).divisors :=
    Nat.one_mem_divisors.mpr (Gen.rankRad_ne_zero _ _)
  rw [← Finset.add_sum_erase _ _ h1, negC_one, Nat.div_one, one_mul]
  have hs : ∑ x ∈ (rankRad N e).divisors.erase 1, negC e x * (σ : ℤ) ^ (N / x)
      = - ∑ x ∈ (rankRad N e).divisors.erase 1, coeffA e x * (σ : ℤ) ^ (N / x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [negC_eq_neg_coeffA]; ring
  rw [hs]
  ring

theorem FF_congr (σ : ℕ) {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) {e e' : ℕ → ℕ}
    (he : ∀ q ∈ P, e q = e' q) (M : ℕ) : FF σ P e M = FF σ P e' M := by
  unfold FF
  have hR : radP P e = radP P e' := Finset.prod_congr rfl fun q hq => by rw [he q hq]
  rw [← hR]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hsub : h.primeFactors ⊆ P :=
    (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hh) (radP_ne_zero hP e)).trans
      (primeFactors_radP_subset hP e)
  rw [negC_congr fun q hq => he q (hsub hq)]

/-- The right-hand side only reads the ranks at the primes dividing `N`. -/
theorem abelianRHS_congr_pf {N : ℕ} {e e' : ℕ → ℕ} (he : ∀ q ∈ N.primeFactors, e q = e' q)
    (σ : ℕ) : abelianRHS N e σ = abelianRHS N e' σ := by
  have h1 := acR_eq_FF N e σ
  have h2 := acR_eq_FF N e' σ
  rw [FF_congr σ (fun q hq => Nat.prime_of_mem_primeFactors hq) he] at h1
  linarith

/-! ### Splitting one prime off the divisor sum -/

theorem negC_pow_mul {p : ℕ} (hp : p.Prime) (e : ℕ → ℕ) (a : ℕ) {h₀ : ℕ} (h₀0 : h₀ ≠ 0)
    (hph₀ : ¬ p ∣ h₀) : negC e (p ^ a * h₀) = cq p (e p) a * negC e h₀ := by
  have hpa : p ^ a ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hsub : (p ^ a * h₀).primeFactors ⊆ insert p h₀.primeFactors := by
    intro q hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    rcases (Nat.Prime.dvd_mul hqp).mp hqd with h1 | h1
    · rw [(Nat.prime_dvd_prime_iff_eq hqp hp).mp (hqp.dvd_of_dvd_pow h1)]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hqp, h1, h₀0⟩)
  have hpn : p ∉ h₀.primeFactors := fun hm => hph₀ (Nat.dvd_of_mem_primeFactors hm)
  have hfac : (p ^ a * h₀).factorization = Finsupp.single p a + h₀.factorization := by
    rw [Nat.factorization_mul hpa h₀0, hp.factorization_pow]
  rw [negC_superset e hsub, Finset.prod_insert hpn, hfac]
  congr 1
  · rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hph₀,
      add_zero]
  · refine Finset.prod_congr rfl fun q hq => ?_
    have hqp : q ≠ p := fun h => hpn (h ▸ hq)
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hqp, zero_add]

/-- **Splitting the prime `p` off the complement sum.** -/
theorem FF_insert (σ : ℕ) {p : ℕ} (hp : p.Prime) {P : Finset ℕ} (hpP : p ∉ P)
    (hP : ∀ q ∈ P, q.Prime) (e : ℕ → ℕ) (M : ℕ) :
    FF σ (insert p P) e M
      = ∑ j ∈ Finset.range (e p + 1), cq p (e p) j * FF σ P e (M / p ^ j) := by
  set R₀ := radP P e with hR₀def
  have hR : radP (insert p P) e = p ^ e p * R₀ := Finset.prod_insert hpP
  have hR₀ : R₀ ≠ 0 := radP_ne_zero hP e
  have hpR₀ : ¬ p ∣ R₀ := by
    intro hd
    obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hd
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp (hP r hr)).mp (hp.dvd_of_dvd_pow hpr)
    exact hpP (heq ▸ hr)
  have hpe : p ^ e p ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hRne : p ^ e p * R₀ ≠ 0 := mul_ne_zero hpe hR₀
  unfold FF
  rw [hR]
  simp only [← hR₀def, Finset.mul_sum]
  rw [← Finset.sum_product (Finset.range (e p + 1)) R₀.divisors
    (fun x => cq p (e p) x.1 * (negC e x.2 * (σ : ℤ) ^ (M / p ^ x.1 / x.2)))]
  symm
  refine Finset.sum_nbij' (fun x => p ^ x.1 * x.2)
    (fun h => (h.factorization p, h / p ^ h.factorization p)) ?_ ?_ ?_ ?_ ?_
  · -- maps into the divisors
    rintro ⟨a, h₀⟩ hx
    obtain ⟨ha, hh₀⟩ := Finset.mem_product.mp hx
    rw [Finset.mem_range] at ha
    refine Nat.mem_divisors.mpr ⟨?_, hRne⟩
    exact Nat.mul_dvd_mul (pow_dvd_pow p (by simpa using Nat.lt_succ_iff.mp ha))
      (Nat.dvd_of_mem_divisors hh₀)
  · -- the inverse maps into the product
    intro h hh
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hh
    have hh0 : h ≠ 0 := (Nat.pos_of_mem_divisors hh).ne'
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      have hle := (Nat.factorization_le_iff_dvd hh0 hRne).mpr hdvd
      have hlp := Finsupp.le_def.mp hle p
      rwa [Nat.factorization_mul hpe hR₀, Finsupp.add_apply, hp.factorization_pow,
        Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpR₀, add_zero] at hlp
    · refine Nat.mem_divisors.mpr ⟨?_, hR₀⟩
      have hcop : Nat.Coprime (h / p ^ h.factorization p) (p ^ e p) :=
        (Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hh0)).symm
      exact hcop.dvd_of_dvd_mul_left ((Nat.ordCompl_dvd h p).trans hdvd)
  · -- left inverse
    rintro ⟨a, h₀⟩ hx
    obtain ⟨-, hh₀⟩ := Finset.mem_product.mp hx
    have hh₀0 : h₀ ≠ 0 := (Nat.pos_of_mem_divisors hh₀).ne'
    have hph₀ : ¬ p ∣ h₀ := fun hd => hpR₀ (hd.trans (Nat.dvd_of_mem_divisors hh₀))
    have hfa : (p ^ a * h₀).factorization p = a := by
      rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hh₀0, Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hph₀, add_zero]
    simp only [hfa]
    rw [Nat.mul_div_cancel_left _ (pow_pos hp.pos a)]
  · -- right inverse
    intro h _
    exact Nat.ordProj_mul_ordCompl_eq_self h p
  · -- the summands agree
    rintro ⟨a, h₀⟩ hx
    obtain ⟨-, hh₀⟩ := Finset.mem_product.mp hx
    have hh₀0 : h₀ ≠ 0 := (Nat.pos_of_mem_divisors hh₀).ne'
    have hph₀ : ¬ p ∣ h₀ := fun hd => hpR₀ (hd.trans (Nat.dvd_of_mem_divisors hh₀))
    simp only
    rw [negC_pow_mul hp e a hh₀0 hph₀, Nat.div_div_eq_div_mul]
    ring

/-- **The step identity for the complement sums**: raising the rank at `p` by one lowers the
complement sum by `p^(e p)` times the complement sum at `M / p`. -/
theorem FF_step (σ : ℕ) {p : ℕ} (hp : p.Prime) {P₀ : Finset ℕ} (hpP : p ∉ P₀)
    (hP : ∀ q ∈ P₀, q.Prime) {e e' : ℕ → ℕ} (he' : e' p = e p + 1)
    (hagree : ∀ q ∈ P₀, e' q = e q) (M : ℕ) :
    FF σ (insert p P₀) e M - FF σ (insert p P₀) e' M
      = (p : ℤ) ^ e p * FF σ (insert p P₀) e (M / p) := by
  rw [FF_insert σ hp hpP hP e M, FF_insert σ hp hpP hP e' M, FF_insert σ hp hpP hP e (M / p), he']
  have hc : ∀ j, FF σ P₀ e' (M / p ^ j) = FF σ P₀ e (M / p ^ j) :=
    fun j => FF_congr σ hP hagree _
  simp only [hc]
  set a := e p
  set f : ℕ → ℤ := fun j => FF σ P₀ e (M / p ^ j) with hf
  have hshift : ∀ i, FF σ P₀ e (M / p / p ^ i) = f (i + 1) := by
    intro i
    simp only [hf, Nat.div_div_eq_div_mul, pow_succ']
  simp only [hshift]
  have hext : ∑ j ∈ Finset.range (a + 1), cq p a j * f j
      = ∑ j ∈ Finset.range (a + 1 + 1), cq p a j * f j := by
    rw [Finset.sum_range_succ _ (a + 1), cq_eq_zero (by omega), zero_mul, add_zero]
  rw [hext, ← Finset.sum_sub_distrib, Finset.sum_range_succ', cq_zero, cq_zero, sub_self,
    add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hia : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← sub_mul, cq_step p hia]
  ring

/-- **The step identity for the right-hand sides of Theorem 4.7** (complement form):
`ac(N, e) - ac(N, e') = p^(e p) ac(N/p, e)` when `e'` raises the rank at `p` by one, provided
`p ∣ N / p` or `e p = 0`. -/
theorem acR_step (σ : ℕ) {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hN : N ≠ 0) {e e' : ℕ → ℕ}
    (he' : e' p = e p + 1) (hagree : ∀ q, q.Prime → q ≠ p → e' q = e q)
    (hcond : p ∣ N / p ∨ e p = 0) :
    ((σ : ℤ) ^ N - abelianRHS N e σ) - ((σ : ℤ) ^ N - abelianRHS N e' σ)
      = (p : ℤ) ^ e p * ((σ : ℤ) ^ (N / p) - abelianRHS (N / p) e σ) := by
  rw [acR_eq_FF, acR_eq_FF, acR_eq_FF]
  have hpmem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, hN⟩
  set P₀ := N.primeFactors.erase p with hP₀
  have hins : insert p P₀ = N.primeFactors := Finset.insert_erase hpmem
  have hpP : p ∉ P₀ := Finset.notMem_erase p _
  have hP : ∀ q ∈ P₀, q.Prime := fun q hq =>
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
  have hag : ∀ q ∈ P₀, e' q = e q := fun q hq =>
    hagree q (hP q hq) (Finset.ne_of_mem_erase hq)
  rw [← hins, FF_step σ hp hpP hP he' hag N, hins]
  congr 1
  -- `radP N.primeFactors e = radP (N / p).primeFactors e`
  have hNp : N / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hpN) hp.pos).ne'
  have hpf : N.primeFactors = insert p (N / p).primeFactors := by
    conv_lhs => rw [← Nat.mul_div_cancel' hpN]
    rw [Nat.primeFactors_mul hp.ne_zero hNp, hp.primeFactors]
    rfl
  have hrad : radP N.primeFactors e = radP (N / p).primeFactors e := by
    rw [hpf]
    by_cases hm : p ∈ (N / p).primeFactors
    · rw [Finset.insert_eq_of_mem hm]
    · have hndvd : ¬ p ∣ N / p := fun hd => hm (Nat.mem_primeFactors.mpr ⟨hp, hd, hNp⟩)
      have he0 : e p = 0 := hcond.resolve_left hndvd
      unfold radP
      rw [Finset.prod_insert hm, he0, pow_zero, one_mul]
  unfold FF
  rw [hrad]

end ShiftSym.P13.Mono
