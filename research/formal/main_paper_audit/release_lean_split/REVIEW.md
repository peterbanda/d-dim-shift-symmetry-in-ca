# Main-paper release: relative-enumeration extraction

The release copy of `Shiftsym/StatementE1.lean` retains only `fixedByA`, `socSub`, `mobiusCoeff`, and `relativeEnumerationStatement`. The retained declarations are byte-identical to their original forms. The unused linear-CA definitions and two follow-up targets are omitted. The original mixed module remains available in the internal development.

The release's general audit omits checks of the removed declarations. Its frozen-file record explicitly records the extraction, the original module hash, and the new release hash. This is a documented scope change, not a silent replacement of a frozen target.

A fresh build into an empty project object directory compiled all **89 modules**, reusing only pinned external dependency objects. The paper audit passed **370/370 statements**. Dependency traversal passed **373 statements, 1,147 constants, 25 modules, zero unrecorded files**. Kernel replay passed **3,036 theorems and 804 safe definitions, zero errors**. Removing the unused definitions also removes six generated helper theorems; no main-paper theorem is removed.

The manuscript's replay totals and approximate companion-module line count are updated to describe this release. All 27 audited item hashes remain unchanged after refreshing the paper bundle. The original auditor event log is preserved.

The export script reproduces the extraction and documentation changes. The Lean statement and proof content of the main paper is unchanged, so these scope changes do not require repeating the correspondence audit. Frozen-file, placeholder, source-fingerprint and independent viewer reconstruction checks accompany the extraction.
