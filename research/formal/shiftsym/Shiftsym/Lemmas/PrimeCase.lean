/-
Phase E, part 2: at a prime `n = p` the machine-checked enumeration
formula collapses to the lower envelope `F_d(p, σ)` — the equality half
of the lower-bound theorem (paper Theorem 6.1, claim C009).

The reindexing is `h = p^r ↔ r`: the divisors of `rad(p)^d = p^d` other
than 1 are exactly `p^1, …, p^d`, and `coeffOf` at `p^r` is the single
signed coefficient `(−1)^{r+1} r_d(p, r)`.
-/
import Shiftsym.Statement

open scoped Classical

namespace ShiftSym

theorem rad_prime {p : ℕ} (pp : p.Prime) : rad p = p := by
  rw [rad, pp.primeFactors, Finset.prod_singleton]

theorem coeffOf_prime_pow {p : ℕ} (pp : p.Prime) {r : ℕ} (hr : 1 ≤ r)
    (d : ℕ) :
    coeffOf d (p ^ r) = (-1 : ℤ) ^ (r + 1) * (rdCoeff p r d : ℤ) := by
  have hfac : (p ^ r).factorization = Finsupp.single p r :=
    pp.factorization_pow
  have hbig : bigOmega (p ^ r) = r := by
    rw [bigOmega, hfac, Finsupp.sum_single_index rfl]
  have hpf : (p ^ r).primeFactors = {p} := by
    rw [Nat.primeFactors_pow _ (by omega), pp.primeFactors]
  rw [coeffOf, hbig, hpf, Finset.prod_singleton, hfac,
    Finsupp.single_eq_same, Nat.add_comm 1 r]

/-- **Prime-case collapse**: the enumeration right-hand side at a prime
equals the lower envelope. -/
theorem enumerationRHS_prime {p : ℕ} (pp : p.Prime) (d σ : ℕ) :
    enumerationRHS p d σ = lowerEnvelope p d σ := by
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
  rw [enumerationRHS, lowerEnvelope, rad_prime pp, hst, Finset.sum_map]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨hr1, hrd⟩ := Finset.mem_Icc.mp hr
  simp only [Function.Embedding.coeFn_mk]
  rw [coeffOf_prime_pow pp hr1 d, Nat.pow_div hrd pp.pos]

end ShiftSym
