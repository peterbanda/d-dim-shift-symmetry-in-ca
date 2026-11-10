# Independent verification of the v8 viewer rebuild

Reviewed commit: `baea4fa182aa30ebca8b5a54119701c1c02a2a97`, 2026-11-02. Baseline: `47ed8bc`.

**PASS: the current bundle mismatch reported as V8-1 is fixed.** The new bundle faithfully represents the current v8 manuscript and its correspondence mappings. The preventive source-hash preflight remains unimplemented, as the authors explicitly disclose. It is a remaining safeguard recommendation, not evidence of a mismatch in this rebuilt bundle.

The commit changes generated viewer data, documentation, and review records. No manuscript source, PDF, production Lean source or frozen fingerprint changed. All **281 files in the previous mathematical review's snapshot** still match their recorded hashes, and all artifacts listed in its final integrity record also match. Its mathematical conclusions and executed proof checks therefore remain applicable; I did not repeat Lean compilation or kernel replay for this data-only change.

## Independent checks

The saved [verification script](verify_bundle.py) performs read-only checks of production data, compiles an instrumented copy in a temporary directory, and prints [results](results.json).

| Check | Result |
| --- | --- |
| Input fingerprints | All 173 match: PDF, TeX, 73 Lean files, 25 mapping files, 73 exports |
| Bundle contents | 25 items, 476 mappings, 23 pages; current v8 numbering |
| New content | Lemma 4.2 included; Corollary 8.2 includes `insolvFullStatement` and the symmetry-breaking file |
| Fresh instrumented compilation | Three local pdfTeX passes; every extracted word and its coordinates match the committed PDF exactly |
| Auxiliary labels | Freshly compiled labels equal committed `paper.aux.json` |
| Highlight geometry | All 519 TeX anchors and their rectangles reproduced exactly; all 25 item rectangles reproduced |
| Glyph cache | All 51,954 boxes independently re-extracted and matched exactly |
| Content and verdict hashes | All 25 item texts, source ranges, resolved mappings and item hashes reproduced from current inputs |
| Existing verdicts | All 23 approvals are now stale; Lemmas 4.2 and A.2 remain unjudged |
| Anchor validation | Zero errors; the same disclosed fixed-set-family hypothesis warning |

The geometry check used the repository's marker/rectangle functions, with an independently executed **local** compilation rather than accepting the recorded Docker run. It did not overwrite the bundle. Glyph extraction used the cached PyMuPDF 2.1 package used by the current tooling environment. The system PyMuPDF 1.27.2.3 initially differed at nine zero-width combining-negation glyphs; using 2.1 reproduced the complete cache exactly. This is a renderer-version reproducibility detail, not a changed mathematical symbol. Tool versions and reviewed-file hashes are in [provenance.json](provenance.json).

The README's revised font recipe is consistent with the successful layout reproduction, and its explanation of `--check` versus a full rebuild is correct. Run 029 now accurately identifies the old bundle as v6 and explains why the previous stale flags did not detect working-tree changes.

## Remaining scope

The viewer still has no automatic startup/browser preflight against changed live sources. The documented manual fingerprint check is sufficient to establish that **this** bundle is current, but the same mismatch can recur after later edits unless the bundle is rebuilt or the proposed safeguard is implemented. The authors correctly disclose this deferral. Historical approvals remain attached to the same LaTeX-label IDs; this verification does not submit new auditor verdicts or clear their stale flags.

The response records an author decision to retain the abstract's novelty wording. That is an editorial disposition, not new evidence resolving the earlier independent attribution concern. No mathematical change or additional literature argument was included in this commit.

Only this verification and the summary appended to `independent_review.md` were written. No production files, audit events, author decisions or source mappings were changed; no commit or push was made.
