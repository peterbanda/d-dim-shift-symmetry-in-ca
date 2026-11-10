/-
Frozen formal targets (no proofs here — these are `Prop`-valued
definitions, not axioms; see the formalization plan for the proof
roadmap):

* `enumerationStatement` — the main enumeration theorem (paper
  Theorem 4.3, claim C001, contract research/problem.md);
* `lowerBoundStatement` — the tight lower bound (paper Theorem 6.1,
  claim C009).

The vector-indexed sum of the paper is re-indexed here by the divisor
`h = ∏ p_i ^ v_i` of `rad(n)^d`; the bijection and all conventions are
documented in research/formal/STATEMENT_PRESERVATION.md.
-/
import Shiftsym.Definitions

namespace ShiftSym

/-- Gaussian binomial `[d r]_q` via the `q`-Pascal recurrence
`[d+1, r+1] = [d, r] + q^(r+1) [d, r+1]`. -/
def gaussBinom (q : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | dd + 1, r + 1 => gaussBinom q dd r + q ^ (r + 1) * gaussBinom q dd (r + 1)

/-- The coefficient `r_d(q, v) = q^(v choose 2) * [d v]_q`. -/
def rdCoeff (q v dd : ℕ) : ℕ := q ^ (v.choose 2) * gaussBinom q dd v

/-- Radical: product of the distinct prime factors. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- Number of prime factors of `h` counted with multiplicity. -/
def bigOmega (h : ℕ) : ℕ := h.factorization.sum fun _ e => e

/-- The signed coefficient attached to the divisor `h = ∏ pᵢ^{vᵢ}`:
`(-1)^(1+|v|) ∏ᵢ r_d(pᵢ, vᵢ)`. -/
def coeffOf (dd h : ℕ) : ℤ :=
  (-1 : ℤ) ^ (1 + bigOmega h) *
    ∏ p ∈ h.primeFactors, (rdCoeff p (h.factorization p) dd : ℤ)

/-- Right-hand side of the enumeration formula, indexed by the divisors
`h ≠ 1` of `rad(n)^d`. -/
def enumerationRHS (n dd σ : ℕ) : ℤ :=
  ∑ h ∈ ((rad n) ^ dd).divisors.erase 1,
    coeffOf dd h * (σ : ℤ) ^ (n ^ dd / h)

/-- **Frozen main target** (= research/problem.md main statement, with
`Σ = Fin σ`): for `n ≥ 2`, `d ≥ 1`, `σ ≥ 1`, the number of
shift-symmetric configurations equals the closed formula. -/
def enumerationStatement (n dd σ : ℕ) : Prop :=
  2 ≤ n → 1 ≤ dd → 1 ≤ σ →
    (Nat.card {s : Config n dd (Fin σ) // IsShiftSymmetric s} : ℤ)
      = enumerationRHS n dd σ

/-- `F_d(n, σ)`: the lower-bound envelope (Gaussian binomials evaluated
at the — possibly composite — integer `q = n`). -/
def lowerEnvelope (n dd σ : ℕ) : ℤ :=
  ∑ r ∈ Finset.Icc 1 dd,
    (-1 : ℤ) ^ (r + 1) * (rdCoeff n r dd : ℤ) * (σ : ℤ) ^ (n ^ (dd - r))

/-- **Frozen lower-bound target** (paper Theorem 6.1, claim C009):
`F_d(n,σ) ≤ |S|`, with equality iff `n` is prime. -/
def lowerBoundStatement (n dd σ : ℕ) : Prop :=
  2 ≤ n → 1 ≤ dd → 2 ≤ σ →
    lowerEnvelope n dd σ
        ≤ (Nat.card {s : Config n dd (Fin σ) // IsShiftSymmetric s} : ℤ)
      ∧ (lowerEnvelope n dd σ
          = (Nat.card {s : Config n dd (Fin σ) // IsShiftSymmetric s} : ℤ)
        ↔ n.Prime)

/-- Geometric-series identity for the first Gaussian binomial:
`a * [d 1]_{a+1} + 1 = (a+1)^d`. -/
theorem gaussBinom_geom (a d : ℕ) :
    a * gaussBinom (a + 1) d 1 + 1 = (a + 1) ^ d := by
  induction d with
  | zero => simp [gaussBinom]
  | succ d ih =>
    have hstep : gaussBinom (a + 1) (d + 1) 1
        = 1 + (a + 1) ^ 1 * gaussBinom (a + 1) d 1 := by
      simp [gaussBinom]
    rw [hstep, pow_one]
    calc a * (1 + (a + 1) * gaussBinom (a + 1) d 1) + 1
        = (a + 1) * (a * gaussBinom (a + 1) d 1 + 1) := by ring
      _ = (a + 1) * (a + 1) ^ d := by rw [ih]
      _ = (a + 1) ^ (d + 1) := by ring

/-- `(q-1) * [d 1]_q = q^d - 1` for `q ≥ 1`. -/
theorem sub_one_mul_gaussBinom {q : ℕ} (hq : 1 ≤ q) (d : ℕ) :
    (q - 1) * gaussBinom q d 1 = q ^ d - 1 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hq
  have h := gaussBinom_geom a d
  rw [Nat.add_comm 1 a]
  simp only [Nat.add_sub_cancel]
  exact Nat.eq_sub_of_add_eq h

/-- Integrality: every index `h` of `enumerationRHS` divides `n ^ d`, so
the `ℕ`-division in the exponent is exact (closes the division caveat in
STATEMENT_PRESERVATION.md). -/
theorem dvd_pow_of_mem_divisors_rad {n dd h : ℕ}
    (hh : h ∈ ((rad n) ^ dd).divisors) : h ∣ n ^ dd :=
  (Nat.mem_divisors.mp hh).1.trans
    (pow_dvd_pow_of_dvd (Nat.prod_primeFactors_dvd n) dd)

/- Sanity checks on the combinatorial ingredients (kernel-reducible). -/
example : gaussBinom 2 2 1 = 3 := rfl
example : gaussBinom 2 3 1 = 7 := rfl
example : gaussBinom 2 3 2 = 7 := rfl
example : gaussBinom 2 4 2 = 35 := rfl
example : gaussBinom 3 3 1 = 13 := rfl
example : rdCoeff 2 2 3 = 14 := rfl
example : rdCoeff 2 3 3 = 8 := rfl

end ShiftSym
