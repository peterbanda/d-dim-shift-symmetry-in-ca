/-
Phase H, group 07 (Dynamics), SUPPLEMENT of 2026-10-27 — the symmetry-breaking
clause of Corollary 8.2. FROZEN STATEMENTS, no proofs of them here (proofs:
`Shiftsym/Paper/Proofs/P07_Dynamics_SymmetryBreaking.lean`).

Paper: `shift_symmetry_d_dimensions.tex` (v6), Corollary 8.2 `cor:insolv`,
lines 790–804; the clause is lines 795–799.

Why a supplement. Group 07 (`S07_Dynamics.lean`, unchanged) was frozen against
the v3.1 text, which said the corollary covers "pattern recognition, and image
translation, exactly as in the two-dimensional discussion of [2019]"; that
sentence was filed as NON-MATHEMATICAL (informal task names). Paper v5 replaced
it, following the independent review of 2026-10-16 (finding 2), by "every
pattern-recognition or image-processing task whose required output breaks a
symmetry of some admissible input". The new qualifier is a precise mathematical
claim, and it is strictly more than the frozen `insolvGeneralStatement`, whose
hypothesis `RequiresLeavingS` demands a fully asymmetric output: asking the
constant input of `Z_4` to become the period-2 pattern `0101` breaks a symmetry
of the input although `0101` is itself shift-symmetric. Until this supplement
no frozen statement certified the clause (independent judgment of the
correspondence audit, 2026-10-27,
`research/formal/correspondence_audit/independent_judgment/JUDGMENT.md`).

Provenance, stated plainly: like the window-20 supplement, these statements
were frozen AFTER a proof of their content existed (the probe
`insolv_breaksSymmetry` of the judgment above, a few lines from Theorem 8.1 in
stabilizer form). Their fidelity to the paper was checked by three
fresh-context reviewers (literal comparison; exploit hunting; independent
reconstruction with exhaustive checks on small tori), all PASS, before the
`_proved` theorems were written; the docstrings then took the reviewers'
corrections (the PAPER ISSUE of `insolvSymBreakStatement` and wording), the
Props themselves did not change (research/experiments/README.md, Run 027;
artifacts in research/experiments/symbreak_fidelity/).

Frozen Props:
* `insolvSymBreakStatement` — no translation-equivariant map solves a task that,
                              on some admissible input, accepts only outputs
                              breaking a symmetry of that input
* `insolvFullStatement`     — Corollary 8.2 as stated in v5/v6:
                              `insolvStatement` and the Prop above
-/
import Shiftsym.Paper.S07_Dynamics

namespace ShiftSym.P07

/-- The hypothesis of the symmetry-breaking clause of Corollary 8.2: on some
admissible input `x`, every acceptable output `y` breaks a symmetry of `x`,
i.e. some translation fixing `x` does not fix `y` (`stab x ⊄ stab y`). This is
the notion of [2019] itself (arXiv:1703.09030v2, p. 2: a configuration is
unreachable "if a source configuration has a symmetry not contained in the
target"; p. 6: "sym-c to asym-f and sym-a to sym-b"). -/
def RequiresSymmetryBreaking {n d σ : ℕ} (T : Task n d σ) : Prop :=
  ∃ x ∈ T.admissible, ∀ y ∈ T.accept x, ¬ stab x ≤ stab y

/-- **Corollary 8.2, the symmetry-breaking clause** (`cor:insolv`, v6 lines
795–799).

Paper (verbatim): "This covers leader election (…) and, as in the
two-dimensional discussion of \cite{banda2019}, every pattern-recognition or
image-processing task whose required output breaks a symmetry of some
admissible input" (with the corollary's "Let $\sigma\ge2$ and $N>1$" and its
subject, unsolvability "by translation-equivariant CA on $\ZZ_n^d$", lines
791–793).

Formal: for every task `T` satisfying `RequiresSymmetryBreaking T` and every
translation-equivariant `Φ`, `Φ` does not solve `T`.

Delta: "task", "solvable" = `Task`, `Solves` of `S07_Dynamics.lean` (reaching an
acceptable output at SOME step — the weakest success notion, so this is the
strongest unsolvability). "Whose required output breaks a symmetry of some
admissible input" = `RequiresSymmetryBreaking`: one admissible input `x` such
that EVERY acceptable output for `x` (every output the task allows, hence
"required") lacks some translation fixing `x`; the broken translation may
depend on the output, which gives the largest class among the readings that
compare each output with its own input (the reading "one translation broken
by all acceptable outputs" is a special case; the weaker readings
"`stab y ≠ stab x`", "some acceptable output breaks a symmetry" and "the output
for one input breaks a symmetry of another input" make the clause false).
"Symmetry" = translation symmetry, the paper's only notion of configuration
symmetry (`stab`, Definition 2.1; a reflection reading would make the clause
false). "Pattern-recognition or image-processing" is not formalized:
the statement holds for EVERY task with this property, a generalization of
the paper's informal task class (those task names are not defined in the
paper or in [2019]). "Translation-equivariant CA" = any map with
`Equivariant Φ`, which includes every offset CA `caMap offs φ` of Definition
2.3 (`caMap_equivariant`). Standing hypotheses `n ≥ 2`, `d ≥ 1` and the
corollary's `σ ≥ 2`, `N > 1` (`1 < n ^ d`) are carried as in
`insolvGeneralStatement` (the implication does not use them).

PAPER ISSUE (imprecise wording): "This covers" presents the clause as an
instance of the corollary, but the task class is strictly larger than the
corollary's hypothesis (an asymmetric output of a symmetric input always breaks
a symmetry of it, not conversely; witness on `Z_4`: `0000 → 0101`, and [2019]'s
"sym-a to sym-b"), and the corollary's stated argument "no trajectory leaves
$S_{n^d}$" does not exclude it. The clause follows from the stabilizer form of
Theorem 8.1, `Stab(Φ s) ⊇ Stab(s)`, iterated along the trajectory. Frozen: the
unsolvability conclusion, which is what the clause and [2019] assert; it
strictly extends `insolvGeneralStatement`. Paper v7 rewords the sentence
accordingly ("More generally, since Stab can only grow along a trajectory
(Theorem 8.1), every … task whose required output breaks a symmetry of some
admissible input is unsolvable"). -/
def insolvSymBreakStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 < n ^ d →
    ∀ T : Task n d σ, RequiresSymmetryBreaking T →
      ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
        ¬ Solves Φ T

/-- **Corollary 8.2** (`cor:insolv`, v6 lines 790–804), as stated since v5: the
eight frozen parts of `insolvStatement` and the symmetry-breaking clause.
NON-MATHEMATICAL (not frozen): the reference to the specific cited
leader-election algorithms (as recorded at `insolvStatement`, whose docstring
discusses the v3.1 wording of the task sentence), the informal task names
"pattern-recognition or image-processing", and the attribution "as in the
two-dimensional discussion of [banda2019]". (`S07Statement`, the conjunction of
group 07, predates the clause and does not include it.) -/
def insolvFullStatement : Prop := insolvStatement ∧ insolvSymBreakStatement

end ShiftSym.P07
