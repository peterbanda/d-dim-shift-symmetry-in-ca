# Tobi's final v11 audit — independent recheck, 2026-11-10

**PASS. V11-1, V11-2 and V11-3 are closed. No new mathematical or correspondence defect was found.**

Pulled `origin/main` with `git pull --ff-only`, advancing `8ddf7d6` to Tobi Lehman's
`c73bb7b42ee55d590557f4301393cb0f288d6e1e` (“done with audit v11”). The pre-existing untracked
`CA86.pdf` was preserved. This review also checks the fixes in `6ed8704` against the previous deep-review
baseline `dde222d`.

## What changed

Tobi's commit changes eight files: the viewer bundle, 126 appended audit events, and three generated report
pairs. There are **no manuscript, PDF, Lean, correspondence-definition, toolchain or frozen-fingerprint
changes in his commit**. The bundle differs from its parent only in build time, build Git revision and
the builder's local checkout path. Its items, hashes, mappings, source fingerprints and geometry are unchanged.

The earlier `6ed8704` commit implements the requested Miles–Ward wording and corrects the viewer delta about
the vector-space clause. These are the precise fixes requested by V11-2 and V11-3. The only manuscript
source change since `dde222d` is that literature sentence. All production Lean sources and frozen records
remain byte-identical to the deeply reviewed version. The intervening Markdown-formatting commit does
not change the mathematics or those Lean sources.

## Approval provenance

The old 3,524-event log is an exact byte prefix of the current 3,650-event log. Nothing was rewritten or
removed. The new log first withdraws four Theorem 4.7 mapping marks (`Gp`, `Fp`, `dp`, `rect.enum`) and six
Inversion Law marks (`whole`, `hyp`, `hyp.d`, `crit.d`, `ii.hyp`, `names`), along with their aggregate verdicts.
The latter six were withdrawn because the exact intermediate bundle of their old marks could not be recovered.

All ten links then receive fresh positive marks in the browser session. Theorem 4.7's final renewed approval
is at **2026-11-10 00:36:03.537 UTC**, and Proposition 10.2's is at **00:54:52.237 UTC**. Each verdict's item
hash exactly matches the current bundle. The browser session's PDF and TeX hashes also match the current
files. Intermediate negative/cleared marks remain in the history and have been superseded; there is no
outstanding negative or unset current mapping.

The verdicts have `auto: true` because the existing viewer aggregates the auditor's mapping marks into an
item verdict. They are not positional carry-forward events or approvals invented by this review. The other
25 item approvals remain valid against their unchanged hashes; this does not mean all their links were
reviewed again in the latest session.

An independent replay of the event sequence finds **27 current positive item verdicts, zero stale verdicts,
zero unjudged items, and 529 positive current mapping marks**. Recomputing the production report into a
temporary directory reproduces its rows, mapping marks, source checks, event digest, counts and session
statistics. The only differences from the last committed report are generation time and the bundle's build
time/Git metadata: Tobi generated that report before the final metadata-only bundle rebuild. The audited
content is identical, so this ordering does not invalidate the report or verdicts.

Evidence: [audit replay results](audit_verification.json). The existing carry-forward tool also reports
zero stale or unjudged items when run read-only.

## Independent reconstruction and mathematical baseline

The [bundle verifier](verify_bundle.py) reconstructs the content and hashes rather than accepting the
report's status alone. Its [results](bundle_verification.json) confirm:

- All **189 input fingerprints**, all **27 item hashes**, and **529 mappings** match the current source.
- A fresh instrumented TeX compilation has exactly the official PDF's word positions and auxiliary labels.
- All **577 highlights** and **68,268 glyph boxes** are reproduced across **28 pages**.
- All item approvals match those independently reconstructed hashes; none is stale or unjudged.
- The existing missing-anchor warning for one fixed-set hypothesis is unchanged and is not a new error.

The frozen-file check passes for all **38 recorded files**. No Lean rebuild or kernel replay was repeated:
the complete production Lean tree and its pins are unchanged, so the preceding independent clean public build
and replay remain applicable: **370/370 paper statements; 89 modules, 3,042 theorems and 809 safe definitions,
zero kernel errors**. Those are prior verification results preserved by source identity, not newly run tests.

The v11 supplement's natural scalar action, dimension equality, and relationship to the enumeration ranks
were substantively checked in the preceding deep review. Tobi's new audit closes the human-approval gap;
it does not substitute for or change that mathematical check. The Inversion Law, including its explicit
constant-20 supplement, likewise has no new statement or proof change.

## Closure and remaining release step

- **V11-1 closed:** the corrected Theorem 4.7 has a current approval, with its affected links freshly marked.
- **V11-2 closed:** the viewer delta now explicitly recognizes the frozen vector-space supplement.
- **V11-3 closed:** the manuscript uses the recommended narrower Miles–Ward description.

Only this review directory and the new entry in `independent_review.md` were written after the requested pull.
No production audit event, report, manuscript, PDF, Lean source or public checkout was modified, and nothing
was committed, pushed or published.
