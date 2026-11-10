# Independent review of the v9 release and requested leader-election citations

> *Public release:* `internal_manifest.json` (it lists the working repository's unpublished files) and `workspace.json` (local paths) are not exported. This repository contains the paper and its supplementary material only; see the README at the repository root.

2026-11-05. Reviewed internal commit `444c7af` against the previously reviewed v8
(`baea4fa`), and the clean local public-release checkout at `e7caee2`. Also verified
the citation-only working-tree revision requested during this review. Main-paper
scope only: follow-up results are not assessed here.

**Verdict: the new applications and verification discussion are mathematically
sound within their stated scope, and I found no new paper–Lean correspondence gap.
The release is not yet ready for an unconditional “publish exactly as it stands”
sign-off.** The advertised repository is not anonymously accessible, the authors'
recorded hand-audit release gate remains open, and the public README has one
misleading mathematical heading. The requested citations are now incorporated and
validated. The pre-existing abstract novelty objection remains an author decision,
not a mathematical proof failure; see item 4 below.

This conclusion does not infer correspondence merely from successful compilation.
It combines the preceding semantic reviews with an exact comparison of the
unchanged statements, checks of the new prose and references, independent figure
computations, reconstruction of the viewer data, and a fresh build of every
exported project module followed by kernel replay.

1. **Public access and release synchronization — outstanding release action.**
   An unauthenticated HTTP request to
   [the advertised repository](https://github.com/peterbanda/d-dim-shift-symmetry)
   returned **404**. This agrees with Runs 030–031, which say it remains private.
   The GitHub connector could not retrieve it either. I could therefore audit the
   local release checkout and export, but cannot certify anonymous readers' access
   to the live repository. Before announcement, publish the intended repository
   and ensure it contains the final paper, matching viewer bundle and records.
   The citation update made during this review is local and has not been pushed.

2. **Historical hand approvals versus current item hashes — outstanding author gate,
   no discovered semantic regression.** All 25 items have historical positive
   verdicts. One current hash matches and 24 are stale. I independently verified
   that all 25 statement texts and their referenced Lean declarations are unchanged
   from v8, and every correspondence-file change is confined to `lines` fields.
   Five retained verdicts originated in the older v6 bundle: their exact verdict
   hashes match that bundle, and their statement/Lean/mapping content is likewise
   unchanged apart from line scopes. Thus the historical sentence “All 25 items
   were approved, and their statements are unchanged in this version” is supported.
   It should not be read as 25 current-hash approvals. Run 031 explicitly requires
   T. Lehman's reconfirmation or a reviewed change to line-sensitive hashing before
   posting. This review does not impersonate that approval. No audit event was
   added, removed or rewritten. The same 24 stale flags remain after adding the
   citations, whose effects are also confined to layout and line scopes.

3. **Public README heading — correction recommended before release.** At
   `research/public_release/overlay/README.md:52`, result 2 is headed “Bounds:
   primes minimize shift symmetry in every dimension”. The theorem underneath
   establishes equality in a side-dependent lower envelope exactly at primes;
   it does not establish that prime sides minimize probability among neighboring
   sizes. Observation 7.3 explicitly gives the opposite ordering at dimension 3:
   `P(5) > P(6)`, with logarithms approximately −28.61 and −31.67. The README's own
   result 4 also describes this inversion. Replace the heading with **“Bounds:
   a prime-tight lower bound and a probability upper bound”**. The displayed bounds
   are correct. This is a README wording issue; the manuscript's corresponding
   theorem and counterexample need no correction. The suggested one-line patch is
   in `recommended_readme.patch`; it was not applied as part of the citation edit.

4. **Abstract novelty — retained author decision, not endorsed by this review.**
   The abstract still says “all dynamical consequences” are new. The authors
   expressly retained this wording on 2026-11-02. The new references make the
   antecedents particularly clear: the 2015 paper discusses the one-dimensional
   symmetry obstruction, and the 2014 dissertation §6.1 contains both dimensions,
   including the two-dimensional preservation lemma and leader-election
   impossibility theorem. The general stabilizer principle also appears in the
   already cited Kornyak and Kaba–Ravanbakhsh discussions. The present paper's
   arbitrary-dimensional formulation, explicit formulas and refined rank results
   must be distinguished from novelty of the underlying preservation principle.
   Suggested wording remains “the explicit multi-prime closed form is new; we
   also derive dynamical consequences in arbitrary dimension.” I did not override
   the recorded author decision while adding citations.

**What was independently verified**

| Check | Result |
| --- | --- |
| v8 → committed v9 numbered environments | All **39** byte-identical, including definitions, remarks and computational observations |
| Production Lean source since v8 | Unchanged |
| Fresh standard export of committed internal state | **338/338 files** byte-identical to local public checkout `e7caee2` |
| Fresh public project compilation | **76/76 modules** compiled from source into an empty object directory, at most four processes |
| Main-paper audit against those fresh objects | **347/347** frozen statements; zero failures |
| Fresh kernel replay | **76 modules, 2,746 theorems, 716 definitions; zero errors** |
| Public fingerprint and placeholder gates | **25 fingerprinted files OK; CLEAN** |
| Fresh dependency closure | **352 frozen statements, 1,108 constants, 22 project modules; zero unrecorded files** |
| Committed v9 viewer reconstruction | **173 fingerprints, 25 items, 476 mappings, 519 highlights, 60,131 glyph boxes**, exact PDF word layout |
| Updated citation-version viewer reconstruction | Same item/mapping/highlight counts; **61,122 glyph boxes**, exact 26-page PDF word layout |
| Citation edit preservation | All **39** numbered environments, every Lean file, frozen hashes and auditor events unchanged |
| Bibliography after requested edit | **31** unique entries; no missing citation keys or unresolved cross-references |
| Minimal arXiv source package | Five files; three-pass clean-directory compilation reproduces the updated PDF's word coordinates |

The fresh project compilation used the pinned installed Lean toolchain and the
existing pinned mathlib/dependency cache; mathlib itself was not rebuilt from
source. No internal-only project object directory was on its Lean search path.
Every public project source was compiled anew. This strengthens the earlier
cached-object replay and avoids assuming the internal build cache corresponds to
its source files. The five `_unsafe_rec` entries reported separately by replay are
compiler-generated executable implementations, not additional proof axioms; the
theorem axiom gates admit only `propext`, `Classical.choice`, and `Quot.sound`.

The release keeps `StatementE1.lean` and `Lemmas/Relative.lean` because the main
paper needs the relative enumeration result. Two other E1 propositions remain
stated without proofs and are disclosed in the public README. They are not part
of the 347 paper statements or silently counted as established results. No
semantic review of these follow-up claims was performed.

**Application-by-application assessment**

- **Distributed computing:** a shared-offset CA on the torus is anonymous and
  translation-equivariant. A nonzero translation cannot fix a configuration with
  exactly one distinguished cell: it would have to fix that cell's position,
  impossible under the regular translation action. Stabilizer preservation thus
  excludes every symmetric input, so its exact uniform failure fraction is
  `|S|/σ^N`; this is a necessary obstruction, not a sufficiency theorem for the
  remaining inputs. The new citations correctly acknowledge earlier CA work.
- **Equivariant neural networks:** circular padding, stride one, shared weights
  and pointwise nonlinearities give equivariance under the stated full translation
  group. If `τv x = x`, then `τv F(x) = F(τv x) = F(x)`, independently of whether
  the feature alphabet is finite or continuous. The same argument allows different
  input/output channel spaces and composes through a stack. The Lean dynamics core
  already uses an arbitrary alphabet type, without finiteness assumptions. This
  is consistent with [Cohen–Welling](https://proceedings.mlr.press/v48/cohenc16.html)
  and [Kaba–Ravanbakhsh, Proposition 1](https://arxiv.org/html/2312.09016v2).
  The [neural-CA source](https://distill.pub/2020/growing-ca/) uses an asymmetric
  seed and stochastic cell updates, so it does not contradict deterministic
  synchronous insolvability.
- **Materials:** for an `n`-fold enlargement in each parent Bravais basis direction,
  atomic labelings are exactly maps from `Z_n^d` to the species alphabet. A shorter
  translational period is exactly a nontrivial stabilizer. Thus the enumeration
  applies to super-periodic labelings, and the binary fixed-composition count
  applies as stated. [Hart–Forcade, §III.B.5](https://arxiv.org/pdf/0804.3544)
  explicitly removes such labelings. The manuscript correctly distinguishes
  arbitrary Smith-normal-form quotients from the equal-sided case and does not
  claim to count inequivalent structures after rotations/species permutations.
- **Physics and numerical dynamics:** [Sandvik, §§4.1.3 and 4.4.1](https://physics.bu.edu/~sandvik/vietri/vietri.pdf)
  supports the momentum-compatibility and normalization statement for short-period
  computational basis configurations. The discussion does not identify these
  classical configurations with arbitrary quantum superpositions. The numerical
  claim is conditional on exact translation equivariance and exact arithmetic;
  loss of symmetry requires a perturbation or a violation of those assumptions.
- **Random initial states:** the uniform and fixed-active-cell probabilities use
  the correct sample-space sizes; the denominator at fixed `k` is
  `binom(N,k)(σ−1)^(N−k)`. The bound concerns membership in the invariant symmetric
  set, not a proof of pseudorandom quality or a claim that every asymmetric seed
  succeeds. [Wolfram's cited paper](https://www.sciencedirect.com/science/article/pii/019688588690028X)
  is relevant CA-generator background. The scope is appropriately limited.

These applications are justified mathematically but are not newly formalized Lean
models of neural networks, materials or quantum mechanics. Section 11 expressly
excludes the application discussion from its formalization claim.

**Figures and matcher claims**

I regenerated Figure 1 byte for byte, independently recomputed each plotted
configuration's stabilizer by multidimensional array shifts, and enumerated the
union of the fixed binary configurations of all seven prime-order subgroups of
`Z_6²`. This directly produced **801,064 distinct configurations**, without using
the closed count formula or inclusion–exclusion to obtain the union's size.
The plotted stabilizers are exactly `<(3,0)>`, `<(2,2)>`, `{0}`, and `<(0,2,2)>`.
The six active cells of the 3D example and the depicted generator arrows agree
with the caption. I visually inspected the new figures and updated application
and bibliography pages.

Figure 5 accurately separates proof checking from fidelity review. The viewer's
classification totals are 174 representation, 141 same, 85 definition, 57
hypothesis, 11 Lean-only, 3 citation, 3 paper-only and 2 generalization links;
none is classified weaker. That absence is not itself a completeness theorem.
The three paper-only links are an algorithm citation, big-O notation already
implied by the explicit detection bound, and the name of the historical
“composite advantage”; they do not expose a new omitted mathematical clause.
The symmetry-breaking clause of Corollary 8.2 is covered by its previously added
frozen statement. Reconstruction verified both item hashes and actual PDF
positions, not only the validator's success message. The existing missing-TeX-
anchor warning for `lem_fix.json:ii.hyp` is unchanged and disclosed.

**Requested references and resulting files**

The 2011 contribution is cited for evolved binary rules; its publisher confirms
LNCS **5778**, pages **310–317**, publication year **2011**, and
[DOI 10.1007/978-3-642-21314-4_39](https://link.springer.com/chapter/10.1007/978-3-642-21314-4_39).
ECAL 2009 is the conference name/date, not the chapter publication year.
The [2015 journal record](https://www.oldcitypublishing.com/journals/jca-home/jca-issue-contents/jca-volume-10-number-1-2-2015/jca-10-1-2-p-1-21/)
and the [2014 dissertation](https://peterbanda.net/Peter_Banda-Comenius_Dissertation-2014.pdf)
support the added historical attribution. No DOI was invented for the journal
article or thesis. These references do not become unproved assumptions in Lean.

Updated locally: the main TeX, its **26-page PDF**, the **54-page mobile PDF**, the
**26-page v8→v9 diff PDF**, the 24 correspondence files' line scopes, and the
viewer bundle/glyph data. No numbered statement, proof, audit verdict or frozen
fingerprint was changed. The v9 diff was regenerated from the reviewed v8 source
with `latexdiff --type=UNDERLINE`; additions are green and deletions red.
Hashes are in `updated_artifacts.json`. Original-commit evidence is retained
separately from the updated-artifact checks.

**arXiv packaging and remaining limitations**

`arxiv_source_v9_with_citations.zip` contains only the main TeX and its four
referenced graphics. The bibliography and TikZ diagram are inline; there are no
private absolute input paths or shell-escape requirements. It compiles from an
empty directory with no missing references and reproduces the updated paper's
word layout. There are no Type 3 fonts. Remaining warnings are the existing
0.70-point overfull line in Lemma A.3, underfull table/bibliography lines and two
hyperref bookmark warnings. The larger underlined diff-PDF boxes do not affect
the submission PDF.

Local compilation used TeX Live 2022. [arXiv currently supports 2023 and 2025,
with 2025 the default](https://info.arxiv.org/help/faq/texlive.html); this is therefore
not a claim to have run arXiv's own compiler. Use the prepared minimal package
and check the actual submission preview before submission, following
[arXiv's TeX instructions](https://info.arxiv.org/help/submit_tex.html).
A successful local build is not a prediction of moderation or endorsement.

No submission, repository-visibility change, commit or push was performed.
The user's pre-existing untracked `CA86.pdf` was left untouched. The historical
review artifacts and original public checkout were not modified.

Reproduction evidence: `internal_manifest.json`, `public_manifest.json`,
`export_comparison.json`, `statement_comparison.json`, `older_approvals.json`,
`fresh_build_results.json`, `fresh_kernel_replay.log`, `fresh_paper_audit.log`,
`fresh_dependencies.log`, `bundle_verification.json`,
`updated_bundle_verification.json`, `figure_verification.json`,
`citation_edit_checks.json`, `arxiv_updated_build.json` and the accompanying
scripts/logs in this directory. Temporary archive paths are in `workspace.json`;
recreate those snapshots from the recorded commits if the temporary directories
have been removed.

*Follow-up, 2026-11-05 (P. Banda's decisions after this review; record in Run 033 of
`research/experiments/README.md`):* the dissertation citation was dropped again. Its 1-D content is
covered by Banda–Caughman–Pospíchal (2015) and its 2-D content by Banda et al. (2019), both cited; the
leader-election application now cites the 2019 paper for two dimensions. The two remaining leader-election
sentences moved from the head of the related-work paragraph to follow the sentence on the 2019 paper.
Both arXiv zip packages were deleted: they predate the arXiv clean-up of the source (header comments,
date line), and no zip is kept: the cleaned source and its four figures are uploaded to arXiv directly. The
public README's heading for result 2 now reads "Bounds: a lower bound attained exactly at the primes".
