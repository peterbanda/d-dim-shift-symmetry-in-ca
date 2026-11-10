# Independent review of v8 and the commits of 2026-11-02

**Mathematical verdict: PASS for the changes reviewed.** I found no new false mathematical statement, missing mathematical hypothesis, or mismatch between the current main paper and its Lean formalization. The editorial corrections already made on top of John's version are justified. The newly committed Corollary 8.2 supplement faithfully states and proves the stronger symmetry-breaking claim.

**One verification-delivery issue remains:** the correspondence viewer combines the current v8 PDF with generated v6 data. Refresh it before using the viewer to sign off v8. This does not invalidate the mathematical results. The previously reported abstract-novelty concern also remains unresolved; it is not a new defect introduced by this merge.

Reviewed HEAD: `47ed8bc` (full hash in [manifest.json](manifest.json)). Baseline: `977f823`, immediately before today's three commits. Date: 2026-11-02. Main paper only; no semantic review of follow-up developments.

## Scope and provenance

| Commit | Reviewed content | Result |
| --- | --- | --- |
| `e868e8f` | v7 changes committed today: symmetry-breaking statement, proof, audit imports, fingerprints, manuscript wording, and supporting records | Mathematical/formalization PASS |
| `a7b87d6` | John's edits of v5 merged onto v7, editorial corrections 1–18, concordance, correspondence mappings, PDFs | Mathematical PASS; generated viewer bundle not refreshed |
| `47ed8bc` | Second pass, editorial corrections 19–30 and four correspondence anchors | PASS |

I inspected the complete manuscript diff and reconstructed the three-way merge independently, using v5 `b9df6bc`, v7 `e868e8f`, and the preserved `shift_symmetry_d_dim-V5-John.tex`. The merge exits successfully without conflicts. The [remaining diff against v8](editorial_diff.patch) is consistent with the editorial changes documented in `research/paper_edits/V8_EDITS.md`. This check distinguishes John's changes from subsequent corrections and confirms that the v6/v7 amendments were retained.

Across today's commits, the only Lean source changes are the two new symmetry-breaking files and their imports in `Shiftsym.lean` and `AuditPaper.lean`. Previously existing statements, definitions and proofs are unchanged. Neither v8 editorial commit changes Lean source. The review does not assume that this alone establishes correspondence: the changed prose, hypotheses, formula contexts, and references were checked against the existing definitions and proofs.

## Finding V8-1: the viewer's generated bundle is stale

**Medium priority; verification tooling, not a mathematical counterexample.**

`research/formal/correspondence_audit/data/audit_data.json` was built on 2026-10-22 at `f1d041a`. Its source hashes identify **v6**, not v7. It has 24 items and geometry for 21 pages. The current v8 paper has 25 theorem/lemma/proposition/corollary items and 23 pages. In particular:

- The bundle calls `lem:order` Lemma 3.1 and `lem:fix` Lemma 3.2, the reverse of v8.
- It calls the main theorem 4.3, not 4.4.
- It has no `lem:mobius2` item and does not include the new symmetry-breaking statement file in its displayed Lean-file list.
- Its stored PDF hash begins `fa91c65d…`; the current PDF is `3d5eb36a…`. The stored TeX hash begins `ff8d5610…`; the current source is `72bd9549…`.

See [the independently computed snapshot](viewer_snapshot.json).

The server serves `/repo/shift_symmetry_d_dimensions.pdf` from the current working tree while serving the old generated mappings and coordinates from `/data/audit_data.json`. Its startup checks only that the JSON exists. The browser's stale badge compares the saved verdict hash to the item's hash in that same generated JSON (`app/app.js:454–457`); it does not recompute the item from today's source. A verdict matching the old bundle can therefore remain visually current while the PDF has changed. The final audit report **does** compare live PDF/TeX hashes and disclose the mismatch (`tools/auditlog.py:175–225`), so that safeguard should not be overlooked.

Run 029 acknowledges that rebuilding was deferred, but its description at `research/experiments/README.md:574–576` is inaccurate in two respects: the bundle is v6, and the item stale flags are not automatically refreshed merely because files in the working tree changed. Regenerating the bundle is what changes the item hashes.

**Recommended correction:** rebuild the complete correspondence data, auxiliary labels and PDF-position artifacts against the committed v8 PDF with the supported TeX environment. Confirm 25 items, v8 numbering, the symmetry-breaking mappings, and matching live hashes. Add a startup or browser preflight that blocks review, or clearly flags a source mismatch, before showing historical highlights over a different PDF. Correct the Run 029 description. `tools/build.py --check` validates source anchors; its success is not evidence that the generated viewer bundle is current.

No viewer files or historical review verdicts were changed during this review.

## Mathematical correspondence of John's edits

### Model and preliminaries

The split of Definition 2.1 into Definitions 2.1 and 2.2 changes presentation, not the group action. Configurations are still functions on `(Z/nZ)^d`, translation still reads `s(u+v)`, and the stabilizer and fixed set retain the same carriers. Moving `Fix(H)` from the shift-symmetry definition does not change its meaning. The new fixed-set wording quantifies over every element of H, including zero; it does not restrict to generators or to a single shift.

Restoring the counting convention allowing `σ=1` matters: the fixed-set counts used by enumeration must cover the parameter range explicitly retained in Theorems 4.4 and 5.1. The restoration is correct. It does not extend the strict lower bound or logarithmic probability statements to `σ=1`; those retain their own `σ≥2` hypotheses.

The swap of the fixed-set and translation-order lemmas is safe. Writing `|A|/|H|` instead of `N/|H|` is exact because `|A|=N=n^d`. The order calculation still uses the least positive t annihilating every coordinate; neither the lcm/gcd formula nor its nonzero-vector hypothesis changed. The torsion lemma's three parts retain the field identification, nonzero-vector/order-p correspondence, line count, and generated-subgroup order. The multi-prime lemma still concerns the subgroup **generated** by the union, with order equal to the product of primary orders.

Two corrections to John's intermediate text were necessary and are now sound: positive prime-factor exponents make the listed primes actual divisors, and completeness must use **nontrivial** cyclic subgroups. Including the trivial subgroup would make its fixed set all configurations and would make the intermediate inclusion false.

### Split Lemmas 4.1 and 4.2

The old single lemma had three mathematical components. The new split preserves all three:

| v8 claim | Frozen statement / proof |
| --- | --- |
| Lemma 4.1: signed spanning-set sum equals the incidence Möbius function | `P03.lemMobiusFEqMuStatement` / `_proved` |
| Lemma 4.1: Möbius value is `(-1)^r p^(r choose 2)` | `P03.lemMobiusMuClosedFormStatement` / `_proved` |
| Lemma 4.2: signed rank-r sum is that value times the Gaussian binomial | `P03.lemMobiusCrStatement` / `_proved` |

I read the definitions and their bridges in `S03_MobiusCoefficients.lean` and `P03_MobiusCoefficients.lean`. `lines V` enumerates actual one-dimensional subspaces contained in V; `spanJ` is the submodule span of the union; the signed counts are finite sums over actual subsets, with integer signs. The Möbius function is mathlib's incidence-algebra function on the subspace lattice, not a definition chosen to equal the desired formula. The prime and dimension hypotheses remain the same, and `0≤r≤d` is retained. The rank-zero case includes the empty set of lines and gives 1 on both sides.

The proof route remains valid. Partitioning subsets by their span gives the sum over W≤V; it is 1 at the zero space and 0 otherwise. Both the Möbius function and the displayed closed form satisfy that recurrence. The new Lemma 4.2 groups each rank-r subset by its unique r-dimensional span. The repaired proof now says this explicitly. Its Lean counterpart `cr_eq_sum_f` performs that actual partition; `lemMobiusCr_proved` then uses the verified subspace count. The Gaussian-binomial recurrence used in Lean has an existing proved bridge to the paper's product formula.

The original conjunction remains unchanged and still contains all three components. Comparing the mapping JSON structurally showed that the only changes to Lean targets within v8 are the expected split of this lemma: seven coefficient mappings move to the new item, which also gets its own prime/dimension hypotheses. No mapping elsewhere silently changes its Lean target or classification. All 519 current TeX anchors locate successfully, and the 25 correspondence files contain 476 mappings.

Independent finite corroboration reconstructed projective lines and their spans over F2, F3 and F5, including dimension three over F2 and F3. It checked all **8,414 subsets** and **69 subspaces** across eight cases, both the individual signed sums and the rank grouping, including the zero-space recurrence. No project counting routine was imported. See [script](independent_checks.py) and [results](independent_checks.json).

### Enumeration, boundary cases, bounds and references

The main rank-vector formula, active-cell count, prime formulas, lower envelope, probability bounds, detection costs, and crossover criteria are unchanged. The prime corollary now states `d≥1, σ≥1` explicitly, matching the existing formal target. Its three displayed special cases retain the correct signs, powers, and coefficients.

The boundary remark keeps all previous cases; it distributes them across five parts. The necklace identification is now part (iii), and Section 11 points to it correctly. The restored E.20 citation matches the prime two-dimensional formula in the [2019 primary source](https://arxiv.org/pdf/1703.09030v2), p. 15. Replacing the suggestion that the paper corrects earlier higher-dimensional conjectures with a statement about naive generalizations is justified: the cited earlier discussion leaves extensions for future work (p. 4). This was an attribution repair, not a new theorem.

The Appendix A.1 reference correction is mathematically appropriate. On `T_j=(Z/nZ)^(d-j) × (Z/(n/p)Z)^j`, each earlier prime `p_i`, i≤m, divides both side lengths because `p_i≠p`. Its torsion therefore has dimension d, so fixed-set counting, torsion/line identification, completeness for the relevant primes, primary decomposition and the two signed-sum lemmas apply. The square-torus translation-order formula is not needed and is correctly excluded from the range. This preserves the rectangular-torus interpretation underlying the truncation argument.

I compiled v7 and v8 and compared their label tables. All changed numbers agree with the concordance: Definitions 2.3→2.4, Remark 2.4→2.5, Lemmas 3.1/3.2 exchanged, main theorem 4.3→4.4, prime corollary 4.4→4.5, and boundary remark 4.5→4.6. The new labels are Lemma 4.2, Definition 4.3 and Table 1. Existing equation numbers and the labels from Section 5 onward are unchanged. The references in the enumeration proof, alternative derivation, Section 11 and Appendix A.1 point to the appropriate new items.

### Disposition of the 30 documented editorial corrections

All 30 were checked against the reconstructed merge and final source. Entries 4, 5, 12, 16, 17, 19 and 22 are the ones with meaningful effects on hypotheses or proof readability; they are addressed above. Entries 8 and 10 correctly repair attribution. Entries 1–3, 6–7, 9, 11, 13–15, 18, 20–21 and 23–30 remove a mismatched environment, fix wording/typesetting, or clarify presentation without changing mathematical content. In particular, the new proof text does not revive a weakened hypothesis, omit a summand, reverse an inequality, or change a probability denominator.

## Corollary 8.2 supplement committed today

The new frozen hypothesis is

`∃ x ∈ admissible, ∀ y ∈ accept x, ¬ stab x ≤ stab y`.

This is the correct reading of a task whose required output breaks an input symmetry. The input is one admissible configuration; **all** acceptable outputs for that input must lose a symmetry. The lost translation may depend on the output. It is not enough that one permitted output loses symmetry, and it is not necessary that the output be completely asymmetric.

`Solves` requires each admissible input to reach an acceptable output at some nonnegative time; it permits the time to depend on the input. Proving impossibility for this permissive notion also rules out fixed-time, halting, or reach-and-stay success. Empty acceptable sets give trivially impossible tasks but are not the reason the result holds: the committed stripe example has an acceptable output, is still shift-symmetric, and nevertheless loses input symmetries.

The proof inductively obtains `stab x ≤ stab (Φ^[k] x)` from equivariance and the stabilizer form of Theorem 8.1. Any claimed successful time then contradicts the task hypothesis. The new whole-corollary conjunction retains the original eight parts. The supplement does not modify or weaken `insolvStatement` or the existing section conjunction; `AuditPaper` independently discovers both new targets. The provenance disclosure that these two statements were frozen after a probe proof existed is accurate and remains visible in Section 11.

As a direct check against abstraction mistakes, [LiteralChecks.lean](LiteralChecks.lean) proves a pointwise version using functions on `Fin d → ZMod n`, a nonzero translation v, equations `x(u+v)=x(u)` and a witness `y(u+v)≠y(u)`, and literal eventual acceptance along `Φ^[k]`. Its conclusion does not use the project's task/solvability/stabilizer predicates. It also proves that negated stabilizer inclusion is equivalent to loss of such an actual nonzero shift. Both probes compile with only standard axioms.

Independent exhaustive tests covered **131,344 binary full-neighborhood CA rules** on Z2, Z3, Z4 and Z2². They checked 2,099,264 one-step configuration/rule pairs and 5,844,264 trajectory visits through the first repeat. Every initial stabilizer is preserved. The checks include the nonempty Z4 stripe task and a Z2² task with three permitted stripe outputs: each loses some input symmetry, but no one nonzero translation is lost by all three. This specifically tests the output-dependent witness order. Finite checks corroborate the interpretation; the general conclusion rests on the proof and kernel replay.

## Validation actually executed

| Check | Result |
| --- | --- |
| Main audit build, then root `lake build Shiftsym` | Passed, with cache reuse and existing warnings |
| Direct paper audit | 347 statements, 0 failures; group 07 has 33 |
| Frozen files | 33 fingerprinted files pass |
| Definition dependency closure | 758 frozen statements, 2,064 constants, 31 modules, 0 unrecorded |
| Placeholder gate | CLEAN |
| Fresh kernel replay of main-paper imports | 72 modules; 2,739 theorems; 714 safe definitions; 0 errors |
| Independent literal Lean probes | Both passed; standard axioms only |
| Root inventory for Section 11 | 246 modules; 8,574 theorems; 1,999 safe definitions |
| Source correspondence check | 25 files, 476 mappings, 0 errors; existing missing-TeX-anchor warning for the fixed-set family's hypothesis |
| Anchor self-remap | 519 unchanged, 0 missing/moved/reworded |
| Independent combinatorial/dynamical checks | PASS, as detailed above |
| v7, v8 and mobile TeX builds | Three passes each, exit 0; no undefined references |
| Committed PDF versus rebuilt source | Extracted text matches exactly for both standard and mobile PDFs |
| Visual PDF inspection | Pages 7, 13 and 20: split lemmas, dynamics and Appendix A.1 readable, references correct |

The standard v8 PDF has the same minor 0.69986 pt overfull line in the chain proof already present in v7; mobile has no overfull box. Both builds retain two hyperref warnings about mathematical tokens in PDF strings. These do not prevent compilation or affect the displayed mathematical formulas.

The main replay rejects project axioms and opaque declarations as well as failed kernel checks. It reports five generated unsafe recursion helpers separately. Like the repository replay, it checks each project declaration against the loaded dependency environment; it is not a reconstruction of all of mathlib from an empty environment. The full-library numbers above were independently **counted**, not subjected to a fresh full-library replay in this review. The root build includes companion modules; their mathematical content remains outside scope.

Execution logs, [validation timings](validation.json), [document checks](document_checks.json), [mapping comparison](mapping_changes.json), and the source [manifest](manifest.json) are saved here. No manuscript, production Lean file, fingerprint, run log, or viewer data was modified, and no commit or push was made.

## Previously open matter

The abstract still says that all dynamical consequences are new (`shift_symmetry_d_dimensions.tex:68–69`). This was already flagged in the earlier independent review and acknowledged for author discussion. The 2019 paper itself discusses preservation and loss-of-symmetry obstructions, and the current paper's related-work paragraph acknowledges general stabilizer preservation. The soundness of the present proofs does not establish this broad novelty claim. Narrow it before publication; it should not be counted as resolved by accepting John's editorial merge.
