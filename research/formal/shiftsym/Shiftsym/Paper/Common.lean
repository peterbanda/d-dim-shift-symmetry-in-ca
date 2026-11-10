/-
Shared definitions for the paper-wide formalization (Phase H, 2026-10-15):
every numbered statement of `shift_symmetry_d_dimensions.tex` gets a frozen
`Prop` in `Shiftsym/Paper/S??_*.lean` and a proof in
`Shiftsym/Paper/Proofs/P??_*.lean`. Only notation-level abbreviations live
here; each is checked against the paper like every frozen statement.
-/
import Shiftsym.Statement

namespace ShiftSym

/-- `|S_{n^d}|`: the number of shift-symmetric configurations over the
alphabet `Fin σ` (paper Definition 2.2). This is literally the expression
that occurs inside `enumerationStatement` and `lowerBoundStatement`. -/
noncomputable def numSS (n d σ : ℕ) : ℕ :=
  Nat.card {s : Config n d (Fin σ) // IsShiftSymmetric s}

/-- `sopf_d(n) = Σ_{p ∣ n, p prime} [d 1]_p` (paper §6.2, before
Theorem 6.3): the number of order-`p` cyclic subgroups over all `p ∣ n`. -/
def sopfD (n d : ℕ) : ℕ := ∑ p ∈ n.primeFactors, gaussBinom p d 1

/-- `P^unif_{n^d} = |S_{n^d}| / σ^{n^d}` (paper Corollary 7.1): the
probability that a uniformly random configuration is shift-symmetric. -/
noncomputable def probUnif (n d σ : ℕ) : ℝ :=
  (numSS n d σ : ℝ) / (σ : ℝ) ^ (n ^ d)

end ShiftSym
