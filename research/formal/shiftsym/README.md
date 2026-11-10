# shiftsym — Lean 4 formalization

Lean 4 + mathlib formalization of *Shift-Symmetric Configurations in d-Dimensional Cellular
Automata* (`../../../shift_symmetry_d_dimensions.pdf`, Section 11). Toolchain pinned in
`lean-toolchain`, mathlib in `lake-manifest.json`.

- `Shiftsym/Definitions.lean`, `Statement.lean`, `Lemmas/` — the core layer: the model from first
  principles and the two main theorems, `ShiftSym.enumeration_proved` (Theorem 4.4) and
  `ShiftSym.lowerBound_proved` (Theorem 6.1).
- `Shiftsym/Paper/` — the paper-wide layer: every other numbered statement frozen as a `Prop`
  (`S01_…` … `S12_…`, one file per part of the paper, each docstring quoting the passage it
  formalizes), proved in `Paper/Proofs/`. `AuditPaper.lean` fails the build unless each frozen
  statement has a theorem `<X>_proved` of exactly its type using only the standard axioms.
- `Shiftsym/StatementE1.lean`, `Lemmas/Relative.lean` — the relative enumeration theorem, used by
  the proofs of Theorem 5.1 and of Appendix A.
- `Shiftsym/Audit.lean` — prints the axiom set of the main declarations; `Experiments.lean` —
  `#eval` sanity checks against the reference values.
- The authors' working repository also holds layers for follow-up work (`StatementE2.lean`,
  `Lemmas/Linear.lean`, `Lemmas/Mismatch.lean`, `Ext/`, `AuditExt.lean`); they are not part of the
  public release of the paper's supplementary material.

Build and gates (from this directory; the mathlib cache is about 8 GB):

```
lake exe cache get
lake build                                 # must end green
lake env lean Shiftsym/Audit.lean          # axioms: propext, Classical.choice, Quot.sound only
python3 ../check_placeholders.py           # must print CLEAN
python3 ../check_frozen.py                 # frozen statements and their definition files unchanged
lake env lean ../frozen_deps.lean          # every file a statement unfolds to is fingerprinted
lake env lean ../kernel_replay.lean        # optional: full kernel replay; fails unless errors=0
```

Before trusting that a Lean name says what the paper says, read `../STATEMENT_PRESERVATION.md`
(representation choices and deltas, item by item).
