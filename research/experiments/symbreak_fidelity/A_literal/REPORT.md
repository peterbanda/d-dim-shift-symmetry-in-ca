PASS (statements faithful, no weakening). One substantive docstring correction (F1) is requested before fingerprinting.

# Fidelity review A (literal comparison): the symmetry-breaking clause of Corollary 8.2

Reviewer A, fresh context, 2026-10-27.

Under review: `Shiftsym/Paper/S07_Dynamics_SymmetryBreaking.lean`, sha256 `dbe24aa3…7288` (equal to `../frozen_at_review.sha256`). Paper: `shift_symmetry_d_dimensions.tex` v6, sha256 `ff8d5610…e289`, identical to HEAD. The numbering (Definition 2.3, Remark 2.4, Theorem 8.1, Corollary 8.2) was checked against the `.aux` file.

Also read:
- `S07_Dynamics.lean` (`Task`, `Solves`, `RequiresLeavingS`, `insolvStatement` and its eight parts, `SS`) and `Definitions.lean`;
- the corollary text in git: v3.1 `ee9fb9f`, v4 `20d93ba`, v5 `b9df6bc`, v6 `f1d041a`;
- finding 2 of the independent review, and `JUDGMENT.md`;
- the 2019 paper (arXiv:1703.09030v2), pp. 2 and 6.

Probes: `probe_A.lean`, with output in `probe_A_output.txt`. Everything compiles, and the axioms are within {propext, Classical.choice, Quot.sound}. No probe proves `insolvSymBreakStatement` itself.

(The reviewer's harness does not allow subagents to write report files. The parent session saved this text verbatim from the reviewer's hand-back, after checking that the probe output has no errors and no `sorryAx`.)

## Checks

| # | Item | Verdict | Evidence |
|---|---|---|---|
| 1 | Hypotheses σ ≥ 2, N > 1, n ≥ 2, d ≥ 1 | OK | Line 791 and Definition 2.1 (lines 204–205). They are antecedents, exactly as in `insolvGeneralStatement`. `1 < n ^ d` is redundant but matches the paper's wording. None is extra relative to the paper. |
| 2 | "task" | OK | `Task` = admissible inputs plus, for each input, the acceptable outputs. The paper does not define "task", and this is the most general input/output specification. A CA with auxiliary states (a larger alphabet σ′ with a cellwise encoding ι and decoding π) is already covered by instantiating at σ′ (probe 7, `symBreak_aux_states`). |
| 3 | "required output" | OK | `∀ y ∈ T.accept x`: every output the task allows. This is the only true reading: if the task also allowed an output keeping all of x's symmetries, the identity map would solve it at k = 0. An empty `accept x` makes the hypothesis vacuous, which is harmless because such a task is trivially unsolvable. |
| 4 | "breaks a symmetry" | OK | `¬ stab x ≤ stab y`, i.e. ∃ v with τ_v x = x and τ_v y ≠ y. This is the 2019 paper's own notion (p. 2: "a configuration is unreachable (even if symmetric) if a source configuration has a symmetry not contained in the target"). Each of these readings implies it: "one translation broken by all outputs" (probe 5; strictly narrower, probe 5b on Z_2^2); Stab(y) ⊊ Stab(x); \|Stab y\| < \|Stab x\|; "x ∈ S, y ∉ S" (probe 2). |
| 5 | "some admissible input" | OK | `∃ x ∈ T.admissible`, and it is the same x whose outputs are constrained. The cross reading (the output for x′ breaks a symmetry of another input x) is false, so it is not a reasonable reading. Counterexample: admissible inputs {0…0, x′} with x′ asymmetric, and Φ mapping τ_v x′ ↦ τ_v y′ on the free orbit and acting as the identity elsewhere. |
| 6 | "symmetry" | OK (cosmetic C1) | Translations only (`stab`). A dihedral reading would make the clause false: for d = 1, n ≥ 3, the configuration δ_0 is reflection-symmetric, but its image under the offset CA max(s(u), s(u+1)) is not. |
| 7 | "unsolvable" | OK | `¬ Solves`, where `Solves` means every admissible input reaches an acceptable output at some k ≥ 0. This is the weakest notion of success, so `¬ Solves` is the strongest unsolvability. It matches 2019 Fig. 5 ("eventually reach"). |
| 8 | "translation-equivariant CA" | OK | Every Φ with `Equivariant Φ`, which covers every offset CA (probe 4, `symBreak_implies_CA`). On a finite torus every equivariant map is a CA with b = N, so nothing is lost in either direction. |
| 9 | Quantifier order and scope | OK | ∀ n d σ, hypotheses, ∀ T, `RequiresSymmetryBreaking T` → ∀ Φ, Equivariant → ¬ Solves. There is no hidden ∃. Putting T before Φ is equivalent to ∀Φ ∀T. |
| 10 | Deltas accurate and disclosed | PARTIAL | Every Delta of `insolvSymBreakStatement` is accurate. The "PAPER ISSUE: none" line is not (F1). Cosmetic items C1–C6 are listed below. |
| 11 | Verbatim quote and line numbers | OK | The quote matches lines 795–799 (with "(…)" standing for the leader parenthetical). Lines 790–804 and 791–793 are correct. "Def 2.1" is correct for Stab (line 210). |
| 12 | History ("Why a supplement") | OK | v3.1 and v4 both have the old "pattern recognition, and image translation, exactly as in …". v5 introduced the clause after review finding 2 (response row 2), and v6 is unchanged. The Z_4 example 0000 → 0101 is correct; probe 6 shows `RequiresSymmetryBreaking ∧ ¬RequiresLeavingS` with a nonempty accept set. |
| 13 | `insolvFullStatement` = "Cor 8.2 as stated since v5" | OK | Every other sentence of the v6 corollary is word for word the v3.1 text that the eight parts froze. The dropped "image translation" claim was never frozen. What remains outside is non-mathematical: citations, task names and the attribution. `insolvGeneralStatement` is now implied by the new Prop (probe 3); this is redundant but harmless. |
| 14 | Non-vacuity, strict extension | OK | Probe 6 (the Z_4 stripe task) and probe 2 (`RequiresLeavingS` → `RequiresSymmetryBreaking`) confirm the docstring's claim "strictly extends". |

## Weakening search: none found

These readings of the paper sentence are all implied by `insolvSymBreakStatement`:
- output asymmetric from a symmetric input (probe 2, then probe 3);
- one fixed broken translation (probe 5);
- strictly smaller stabilizer, by inclusion or by cardinality (either way, `stab x ≤ stab y` fails);
- a unique required output (`accept x = {f x}`), or a target set independent of the input (both are instances);
- outputs accepted up to translation (stab(τ_w y) = stab y);
- time-indexed acceptance, or reach-and-stay (both imply `Solves` for the union of the accept sets);
- auxiliary computation states with cellwise encode/decode (probe 7);
- literal offset CA (probe 4);
- dropping the "pattern-recognition or image-processing" restriction (the Prop holds for every task, a generalization).

The readings that are not implied are all false: the ∃-output reading (row 3), the cross-input reading (row 5) and the dihedral reading (row 6).

## Findings

**F1 (substantive, docstring only; the Prop does not change).** The `PAPER ISSUE: none` line, together with "covered by the corollary in the sense of its own justification (Theorem 8.1 along trajectories)", is inaccurate.

In the paper, "This covers …" follows a corollary whose hypothesis is "an output outside S_{n^d}" and whose stated argument is "no trajectory leaves S_{n^d}". Read as "these tasks are instances of the corollary", the clause is false:
- The Z_4 stripe task belongs to the class but does not satisfy the corollary's hypothesis.
- Neither does the 2019 paper's own example "sym-a to sym-b" (p. 6), which has a symmetric target.
- "No trajectory leaves S" excludes neither task. Only the stabilizer clause of Theorem 8.1, iterated, does.

The frozen Prop takes the correct reading at the level of the conclusion ("such tasks are unsolvable"), and the header already says the Prop is strictly more than `insolvGeneralStatement`. But the PAPER ISSUE line should say so too, following the project's practice for imprecise wording (the Phase H "imprecise" class; compare `levelSetInvariantLiteral`). Suggested replacement:

> PAPER ISSUE (imprecise wording): "This covers" presents the clause as an instance of the corollary, but the task class is strictly larger than the corollary's hypothesis (witness: on Z_4, 0000 → 0101; [2019]'s sym-a → sym-b), and the corollary's stated argument "no trajectory leaves S_{n^d}" does not exclude it; the clause follows from the stabilizer clause of Theorem 8.1, Stab(Φ(s)) ⊇ Stab(s), iterated along the trajectory. Frozen: the unsolvability conclusion, which is what [2019] asserts (p. 2). Suggested paper text: "… and, by the stabilizer form of Theorem 8.1, every … task whose required output breaks a symmetry of some admissible input is unsolvable as well".

Optionally, freeze the witness `∃ T, RequiresSymmetryBreaking T ∧ ¬ RequiresLeavingS T` (probe 6), as was done for `levelSetInvariantFalseStatement`, and add the issue to the paper-corrections ledger.

**Cosmetic.**
- **C1.** Replace "the paper's only notion" with "the paper's only notion of configuration symmetry", since the paper also uses "symmetric" for Gaussian binomials (line 1102). Optionally add that a reflection or rotation reading would make the clause false (row 6).
- **C2.** Replace "three lines from Theorem 8.1" with "a few lines from" (the probe is an induction plus three steps).
- **C3.** In `insolvFullStatement`, "as recorded at `insolvStatement`" is inaccurate: `insolvStatement` records the v3.1 names ("pattern recognition, and image translation"). Add the attribution "as in the two-dimensional discussion of [banda2019]" to the NON-MATHEMATICAL list. Note that `S07Statement` ("every claim of L725–800") does not include the v5 clause.
- **C4.** Add positive evidence to the Delta for `RequiresSymmetryBreaking`. The 2019 paper uses exactly this notion: p. 2, "has a symmetry not contained in the target"; p. 6, "pattern recognition or noise filtering (sym-c to asym-f and sym-a to sym-b)".
- **C5.** Replace "as large as possible" with "the largest class among readings that compare each output with its own input". The cross-input reading gives a larger class, but it is false.
- **C6.** The provenance paragraph cites Run 027, which `research/experiments/README.md` does not contain yet (it ends at Run 026). Log Run 027 before the commit.

## Process notes (out of scope, for the integrator)

- The file is not yet in `Shiftsym.lean`, `AuditPaper.lean` or `frozen_statements.sha256`.
- Both new Props end in `Statement`, so the audited count should go from 345 to 347, not to the 346 that `JUDGMENT.md` predicts. Check the §11 count.
- The frozen name is `insolvSymBreakStatement`, not the `insolvBreaksSymmetryStatement` proposed in `JUDGMENT.md`. Remap the `pattern` mapping accordingly.
