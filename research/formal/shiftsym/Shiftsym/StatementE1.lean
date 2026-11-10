/- Main-paper relative-enumeration interface. Release extraction from the mixed
StatementE1 module: unused linear-CA definitions and targets are omitted.
The retained declarations are unchanged; the release fingerprint records this extraction. -/
import Shiftsym.Lemmas.Evaluate

open scoped Classical

namespace ShiftSym

open Module

variable {n d : ℕ}

/-- `Fix(H)` as a finset of configurations over an arbitrary finite
alphabet `A` (generalises `fixedByF σ`, the case `A = Fin σ`). -/
noncomputable def fixedByA (A : Type*) [Fintype A] [NeZero n]
    (H : AddSubgroup (Lat n d)) : Finset (Config n d A) :=
  Finset.univ.filter fun s => ∀ h ∈ H, shift h s = s

/-- The subgroup of the socle of `Z_n^d` attached to a tuple `U` of
subspaces `U p ≤ F_p^d` (one per prime `p ∣ n`): the join of their images
in the `p`-torsion subgroups. -/
noncomputable def socSub [NeZero n] (U : ModTuple n d) : AddSubgroup (Lat n d) :=
  Finset.univ.sup fun p : n.primeFactors =>
    ofMod (Nat.dvd_of_mem_primeFactors p.2) (U p)

/-- The Möbius coefficient `−μ(0, socSub U) = −∏_p spanSum (U p)`
(`= (−1)^{1+Σ_p rk U_p} ∏_p p^{C(rk U_p, 2)}`, see `mobiusCoeff_eq`). -/
noncomputable def mobiusCoeff (U : ModTuple n d) : ℤ :=
  -(∏ p : n.primeFactors, spanSum (U p))

/-- **Frozen target T1** (relative enumeration, E1): for every finite
alphabet `A` and every finset `X` of configurations,
`|X ∩ S| = Σ_U mobiusCoeff U · |X ∩ Fix(socSub U)| + |X|`. (The tuple
`U = 0` contributes `−|X|`, cancelling the final `+|X|`; so this is the
sum over nonzero socle subgroups.) No hypothesis beyond `n ≠ 0`. -/
def relativeEnumerationStatement (n d : ℕ) [NeZero n] (A : Type*) [Fintype A]
    (X : Finset (Config n d A)) : Prop :=
  ((X.filter IsShiftSymmetric).card : ℤ)
    = ∑ U : ModTuple n d,
        mobiusCoeff U * ((X ∩ fixedByA A (socSub U)).card : ℤ)
      + (X.card : ℤ)

end ShiftSym
