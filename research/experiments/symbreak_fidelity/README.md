# Fidelity reviews: the symmetry-breaking clause of Corollary 8.2 (2026-10-27, Run 027)

**Under review.** `research/formal/shiftsym/Shiftsym/Paper/S07_Dynamics_SymmetryBreaking.lean`, as frozen before the
reviews (sha256 in `frozen_at_review.sha256`). It defines `RequiresSymmetryBreaking`, `insolvSymBreakStatement` and
`insolvFullStatement`.

**Clause.** "every pattern-recognition or image-processing task whose required output breaks a symmetry of some
admissible input". It was added to Corollary 8.2 in paper v5, after finding 2 of the independent review, and no frozen
statement certified it (`research/formal/correspondence_audit/independent_judgment/JUDGMENT.md`).

**Process.** Three fresh-context reviewers worked independently before any `_proved` theorem was written. Lean runs
were serialized through one `flock` slot (memory). The reviewers' harness does not allow subagents to write report files,
so each `REPORT.md` was saved verbatim from the reviewer's hand-back. Its probe outputs and checksums were re-verified
before saving.

| Reviewer | Method | Verdict | Folder |
| --- | --- | --- | --- |
| A | literal comparison: every phrase of the paper sentence against the Props; history v3.1–v6; [2019] pp. 2, 6 | PASS, one substantive docstring finding (F1) | `A_literal/` |
| B | exploit hunting: name resolution, unfolding by `rfl`, non-vacuity, strictness, `Equivariant` = offset CA, alternative readings | PASS, no exploit | `B_exploits/` |
| C | independent reconstruction from the paper alone, then comparison; exhaustive checks on 9 small tori | PASS | `C_reconstruction/` |

**Main evidence.**
- **Same Prop.** B: the statement equals its fully unfolded form by `rfl`. C: it is `Iff.rfl` to C's own statement,
  which C wrote before opening the file.
- **Non-vacuous, and strictly stronger than `insolvGeneralStatement`.** On Z_4, `0000 → 0101` satisfies the new
  hypothesis with a nonempty acceptable set, but not `RequiresLeavingS`. C counts such symmetric-but-breaking pairs on
  every torus with composite N (Z3×Z3: 480) and none on Z2, Z3, Z5.
- **Equivariance does work.** B proves `Equivariant Φ ↔ ∃ offsets φ, Φ = caMap offsets φ`, so Φ ranges over exactly the
  paper's CA class. B and A also show that non-equivariant maps (a constant map; Remark 2.4's `locMap`) solve
  symmetry-breaking tasks.
- **Reading.** `¬ stab x ≤ stab y` is the largest true reading. These readings are false: `stab y ≠ stab x`, "some
  acceptable output breaks", cross-input, reflection. These readings are special cases: one broken translation for all
  outputs, strictly smaller stabilizer, asymmetric output.
- **Brute force (C).** 0 violations on Z2, Z3, Z4, Z2×Z2 (every equivariant map iterated), Z6, Z5, Z2³, Z3×Z3, Z2×Z4
  (orbit-exhaustive). The reachable set from x is exactly {y : Stab x ⊆ Stab y}. Every one of the 83,521 tasks on Z2 was
  run against every equivariant map.

**Findings and what was done.**

| Finding | Action |
| --- | --- |
| A F1: "PAPER ISSUE: none" is inaccurate. "This covers" presents the clause as an instance of the corollary, but the corollary's argument ("no trajectory leaves S") does not exclude these tasks; the stabilizer form of Theorem 8.1 does. C made the same point (optional paper prose). | Docstring now records PAPER ISSUE (imprecise wording). Paper v7 rewords the sentence: "More generally, since Stab can only grow along a trajectory (Theorem 8.1), … is unsolvable". |
| A C1–C5: notion "of configuration symmetry"; "a few lines"; NON-MATHEMATICAL list of `insolvFullStatement`; [2019] evidence for the notion; "largest class among readings that compare each output with its own input" | Applied to the docstrings. |
| B 3: say which weaker readings are false | Applied (Delta of `insolvSymBreakStatement`). |
| B 1, C 2: certify the non-vacuity and strictness witnesses | Added to the proof file as theorems (not paper claims): `requiresSymmetryBreaking_of_requiresLeavingS`, `stripeTask_requiresSymmetryBreaking_not_requiresLeavingS`. |
| A, C: Run 027 not yet logged; count 345 → 347, not 346 | Run 027 logged; §11 says 347. |
| B 2 (`equivariant_iff_caMap` as a library lemma), C 5 (offset-CA companion statement), A (freeze the strictness witness as a Statement) | Not done. They are optional, and the first two are covered by `caMap_equivariant` and the probe. |

**Props unchanged by the edits.** After the docstring edits, B's `rfl` probe (`probe0_names.lean`), C's `Iff.rfl` check
(`reconstruction_check.lean`) and B's `probe_ab.lean` were re-run against the edited file. All exit 0.
