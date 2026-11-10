/-
Phase H, group 12 (added 2026-10-18 after the independent review, finding 1):
the necklace identification in Remark 4.5(ii) of the paper.

Paper (v4, lines 462–468): "$d=1$ recovers the classical count of
non-primitive words (proper powers $u^j$, $j\ge2$; equivalently, words, i.e.\
configurations on $\ZZ_n$, fixed by a nontrivial cyclic rotation), the
complement $\sigma^n-\sum_{m\mid n}\mu(m)\,\sigma^{n/m}$ ($\mu$ the
number-theoretic M\"obius function) of the number of primitive words, which is
$n$ times the Moreau--Witt count of primitive necklaces
\cite{moreau1872,witt1937}."

The count of non-primitive words is already certified in group 04
(`ShiftSym.P04.remark45d1Count_proved`, `classicalNonprimitiveCount_proved`).
This group freezes the remaining mathematical content: the set-level
equivalence of the two descriptions of non-primitive words (proper powers vs.
fixed by a nontrivial rotation; group 04 freezes only their equal
cardinalities), the number of primitive words, and the factor `n` between
primitive words and primitive necklaces (the Moreau–Witt necklace count).
Review note (round 1, literal reviewer): the "equivalently" clause was added
as `nonPrimitiveIffRotationStatement`.

Model (the paper's own, as the quoted sentence says "words, i.e.
configurations on Z_n"): a word of length `n` over `σ` letters is a
configuration `Config n 1 (Fin σ)` on `Z_n = (ZMod n)^1`; rotation by `v` is
`ShiftSym.shift v`; a word is primitive iff no nonzero rotation fixes it,
i.e. `¬ IsShiftSymmetric`. A necklace is a rotation class of words; since
primitivity is rotation-invariant, the primitive necklaces are exactly the
rotation classes of primitive words, formalized literally as the quotient of
the primitive words by "is a rotation of" (`Quot` needs no equivalence proof;
the relation is already an equivalence, so its classes are the orbits).

NON-MATHEMATICAL: the attribution to Moreau (1872) and Witt (1937).
-/
import Shiftsym.Paper.Common
import Shiftsym.Paper.S04_EnumerationCorollaries

namespace ShiftSym.P12

open ShiftSym

/-- Primitive words of length `n` over `σ` letters: configurations on `Z_n`
fixed by no nonzero rotation. -/
def PrimWord (n σ : ℕ) := {s : Config n 1 (Fin σ) // ¬ IsShiftSymmetric s}

/-- "is a rotation of" on primitive words. -/
def IsRotationOf {n σ : ℕ} (a b : PrimWord n σ) : Prop :=
  ∃ v : Lat n 1, shift v a.1 = b.1

/-- Primitive necklaces: rotation classes of primitive words. -/
def PrimNecklace (n σ : ℕ) := Quot (@IsRotationOf n σ)

/-- **Remark 4.5(ii): "proper powers $u^j$, $j\ge2$; equivalently, words,
i.e. configurations on $\ZZ_n$, fixed by a nontrivial cyclic rotation"**
(lines 463–465), as an identity of SETS: a configuration on `Z_n` is fixed by
some nonzero rotation iff the word read off from it (`i ↦ s(i)`, `i : Fin n`)
is a proper power in the sense of group 04's `IsNonPrimitive` (constant on the
residue classes mod a proper divisor `t` of `n`).

Delta: `n ≥ 1`; any `σ`; the read-off map `Fin n → Lat n 1`, `i ↦ (fun _ =>
(i : ZMod n))`, is a bijection for `n ≥ 1`. This is also what justifies
modelling "primitive words" by `¬ IsShiftSymmetric` below. PAPER ISSUE: none. -/
def nonPrimitiveIffRotationStatement : Prop :=
  ∀ n σ : ℕ, 1 ≤ n → ∀ s : Config n 1 (Fin σ),
    IsShiftSymmetric s ↔
      P04.IsNonPrimitive (fun i : Fin n => s (fun _ => ((i : ℕ) : ZMod n)))

/-- **Remark 4.5(ii): number of primitive words** (lines 465–467): the number
of primitive words is `∑_{m∣n} μ(m) σ^{n/m}` (the complement of the
non-primitive count `σ^n − ∑_{m∣n} μ(m) σ^{n/m}`).

Delta: `n ≥ 1`, `σ ≥ 1` (as in group 04's `remark45d1CountStatement`); the
count is in `ℤ` because `μ` takes negative values. PAPER ISSUE: none. -/
def primitiveWordCountStatement : Prop :=
  ∀ n σ : ℕ, 1 ≤ n → 1 ≤ σ →
    (Nat.card (PrimWord n σ) : ℤ)
      = ∑ m ∈ n.divisors, ArithmeticFunction.moebius m * (σ : ℤ) ^ (n / m)

/-- **Remark 4.5(ii): the factor `n`** (lines 467–468): the number of
primitive words "is $n$ times the … count of primitive necklaces" (the total
count relation, as the paper states it; the reason is that every rotation
class of a primitive word has exactly `n` elements, which the proof shows).

Delta: `n ≥ 1`, `σ ≥ 1`; stated in `ℕ`. PAPER ISSUE: none. -/
def primitiveNecklaceFactorStatement : Prop :=
  ∀ n σ : ℕ, 1 ≤ n → 1 ≤ σ →
    Nat.card (PrimWord n σ) = n * Nat.card (PrimNecklace n σ)

/-- **Remark 4.5(ii): the Moreau–Witt necklace count** (lines 467–468): the
number of primitive necklaces is `(1/n) ∑_{m∣n} μ(m) σ^{n/m}`.

Delta: `n ≥ 1`, `σ ≥ 1`; the division by `n` is cleared (`n · #necklaces =
∑ …`, in `ℤ`), which for `n ≥ 1` is equivalent to the quotient form and also
asserts that the division is exact. PAPER ISSUE: none. -/
def moreauWittNecklaceStatement : Prop :=
  ∀ n σ : ℕ, 1 ≤ n → 1 ≤ σ →
    (n : ℤ) * Nat.card (PrimNecklace n σ)
      = ∑ m ∈ n.divisors, ArithmeticFunction.moebius m * (σ : ℤ) ^ (n / m)

/-- **Remark 4.5(ii), necklace sentence**, the whole content as a conjunction. -/
def remark45NecklaceStatement : Prop :=
  nonPrimitiveIffRotationStatement ∧ primitiveWordCountStatement ∧
    primitiveNecklaceFactorStatement ∧ moreauWittNecklaceStatement

/- Non-vacuity: the hypotheses `1 ≤ n`, `1 ≤ σ` are satisfiable and the
types are inhabited at a small instance. -/
example : (1 : ℕ) ≤ 4 ∧ (1 : ℕ) ≤ 2 := ⟨by norm_num, by norm_num⟩
example : Nonempty (Config 4 1 (Fin 2)) := ⟨fun _ => 0⟩

end ShiftSym.P12
