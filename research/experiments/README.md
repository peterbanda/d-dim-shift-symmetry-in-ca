# Experiments log

All computations use exact integer arithmetic (Python stdlib only, no floats in
any count; floats appear only in log10 displays for the extrema audit, computed
from big-int bit lengths).

## Run 001 — 2026-07-23 — independent three-level verifier

- Command: `python3 verify_bruteforce.py` (cwd: this directory)
- Environment: Python 3.10.12, Linux 6.8.0-124-generic x86_64, glibc 2.35
- Runtime: 7m37s
- Output: `verify_output.txt`
  sha256 `cbb95b794ab97e3fe5ecd172b7050fa569913d344a62d253d7c76613a1d4c8dc`
- Script: `verify_bruteforce.py`
  sha256 `5778619913ff226ddb0c7a81ec5ba03443e12f62c885b3ef1b1e12a5516226b7`

Levels (mutually independent implementations):
- L1: definition-level brute force over all $`\sigma^{n^d}`$ configurations and all
  nonzero shift vectors.
- L2: inclusion–exclusion over all subsets of prime-order generator
  representatives; generators found by brute-force order computation, subgroup
  joins by BFS closure, $`\lvert\mathrm{Fix}(H)\rvert = \sigma^{N/\lvert H\rvert}`$ via free coset action.
- L3: the draft's closed formula (Gaussian binomials).

Results:
- Section [1]: coefficient identity — exhaustive subsets-of-lines vs
  $`(-1)^{r+1} p^{\binom{r}{2}} \binom{d}{r}_p`$ for $`(p,d) \in \lbrace(2,2),(2,3),(2,4),(3,2),(3,3),(5,2),(7,2)\rbrace`$ — all match.
- Sections [2]–[4]: L1=L2=L3 on 41 cases ($`d=1`$ $`n\le14`$ $`\sigma\in\lbrace 2,3\rbrace`$; $`d=2`$ $`n\in\lbrace 2..6,8,9,10,12,15,30\rbrace`$;
  $`d=3`$ $`n\in\lbrace 2,3,4,6\rbrace`$; $`d=4`$ $`n\in\lbrace 2,4\rbrace`$; $`\sigma`$ up to 4); reference values 8/26/182/72/6398 confirmed.
- Section [5]: draft Thm 5.1 REFUTED — 20 violations; smallest $`n=2,d=3,\sigma=2`$ ($`72 < 100`$).
- Section [6]: extrema pattern holds at $`d=2`$ ($`n \le 40`$), FAILS at $`d=3,4`$ ($`n=5,6,10`$).
- Section [7]: irreversibility counterexample under draft's literal Def 2.2.

## Run 002 — 2026-07-23 — repaired lower-bound candidate (claim C009)

- Command: inline `python3 -c` scan importing `verify_bruteforce`
  (formula_count, r_d): $`F_d(n,\sigma) = \sum_{r=1}^{d} (-1)^{r+1} r_d(n,r) \sigma^{n^{d-r}}`$,
  tested $`F \le \lvert S\rvert`$ and equality-iff-prime over $`n=2..15`$, $`d=1..4`$, $`\sigma\in\lbrace 2,3\rbrace`$.
- Output: `lower_bound_candidate_test.txt` — 112 cases, 0 violations,
  0 composite equalities.

## Run 003 — 2026-07-24 — published 2D paper audit (arXiv:1703.09030v2)

- Command: `python3 verify_banda2d.py` (cwd: this directory; imports verify_bruteforce)
- Environment: Python 3.10.12, Linux 6.8.0-124-generic x86_64
- Runtime: 27 s
- Output: `verify_banda2d_output.txt`
  sha256 `0178b1575543be069e72996f0a8d705533e8e411c707dcce2725c85f55148998`
- Script: `verify_banda2d.py`
  sha256 `3bd51a89b41e16759133576d835bf84562ab7e3557a45bd63ff166d88ac534fa`

Results: every numbered statement tested is exact (E.17/18/19 $`n \le 60`$; E.20/E.21
$`n \le 200`$; A.21–A.24 statements $`n \le 100`$; E.22 + Eq. 23/24 $`n \le 100`$ $`\sigma \le 4`$;
E.29/E.30/E.32/A.34 all $`k`$, brute force $`n \le 4`$ + subgroup-IE $`n \in \lbrace 6,10,12\rbrace`$;
E.36 expectation model exact on full enumerations $`n \le 4`$; five spot values).
Findings: A.21 proof chain invalid at $`(n,m) \in \lbrace(6,1),(10,1),(14,1)\rbrace`$, A.22 at
$`n=6`$ — statements hold there by exact witness (see audits/audit-002-banda2d.md).
New reusable machinery: `ie_k_counts` (independent $`k`$-active-cell evaluator).

## Run 004 — 2026-07-24 — corroboration of the A.21/A.22 repair note

- Command: `python3 verify_fix_note.py` (cwd: this directory)
- Environment: Python 3.10.12, Linux 6.8.0-124-generic x86_64
- Runtime: 0.2 s
- Output: `verify_fix_note_output.txt`
  sha256 `f4be5259d5bd49d5fa144200955c61a61b776bf7b7657b880d020dda122943b9`
- Script: `verify_fix_note.py`
  sha256 `257aafead28c53d03ea71902e3255daba0327abe2f6213634e4efdeb27ae3575`

Results: original-chain failure sets confirmed complete (scan to $`n = 5000`$):
A.21 fails exactly at (6,1), (10,1), (14,1); A.22 exactly at (6,1). Union
bound $`0 \le q^m(1/p) \le \sum(p_i+1)\sigma^{A/p_i}`$, $`q^m(1/p^2) \ge 0`$, driver
$`\sigma^{A/2} \ge 2n/p+1`$, $`y_1+x_1+y_2 \ge 0`$, and $`0 \le x_2 \le y_1`$ all exact on 288 cases
(composite $`n \le 100`$, all $`m`$, $`\sigma \in \lbrace 2,3,5,7\rbrace`$). Supports the erratum draft
`../fix_note/banda2d_bounds_fix.tex` (PDF sha256 6801ff84…).

## Conventions

- Never report a float agreement as a verification; counts must match as ints.
- Every new run: record command, environment, runtime, output file, sha256.

## Run 005 — 2026-07-24 — round-3 proof-estimate validation (C009)

- Command: `python3 verify_ddim_lower_bound.py` (cwd: this directory)
- Environment: Python 3.10.12, Linux 6.8.0-124-generic x86_64
- Runtime: 0.8 s
- Output: `verify_ddim_lower_bound_output.txt` (sha256 below in git-free log: run `sha256sum`)

Results: all exact — (1) $`d`$-dim decomposition $`q^{m+1}-q^m = \sum(-1)^{j+1}r_d(p,j)B_j`$
(84 cases); (2) torus sandwich and union bound; (3) $`\binom{d}{j}_p \le 4p^{j(d-j)}`$ and
tail $`\le 4(d-1)p^{d(d-1)/2}`$ for $`d \le 8`$; (4) chain conditions (I)/(II) and the
chain itself; (5) base-case condition (M), $`q^1 > F_d`$ ($`d \in \lbrace 3,4\rbrace`$, $`n \le 30`$), and
the C009 statement to $`d = 5`$. Supports research/proofs/d_dim_proofs.tex Part II.

## Run 006 — 2026-07-24 — pre-publication validation of revised-paper claims

- Command: `python3 verify_paper_claims.py` (cwd: this directory)
- Environment: Python 3.10.12, Linux 6.8.0-124-generic x86_64
- Runtime: 2m21s
- Output: `verify_paper_claims_output.txt`

Results: [1] C017 $`k`$-active $`d`$-dim formula exact vs brute force ($`n=2`$, $`d\in\lbrace 3,4\rbrace`$,
$`\sigma\le3`$, all $`k`$) and vs independent subgroup-IE ($`n\le6`$ at $`d=3`$, $`n\le12`$ at $`d=2`$, all $`k`$),
$`\sum_k = \lvert S\rvert`$ consistent. [2] C023 upper bounds: union form, odd-prime term
lemma, and $`(2^d-1+2\log_2 n)\sigma^{N/2}`$ exact on $`n\le60`$, $`d\le4`$, $`\sigma\le4`$. [3] Detection
expectation model exact at (2,3,2),(2,3,3),(2,4,2); total-cells bound holds.
Gate for the round-4 paper revision.

## Run 007 — 2026-07-24 — dimension-insight charts 12–16

- Command: `python3 compute_dimension_insights.py` (cwd: project root)
- Environment: Python 3.10.12, matplotlib; 1.7 s
- Sanity gate: log-space evaluator asserted equal (<1e-9) to exact integer
  $`\log_{10}\lvert S\rvert`$ on 8 cases before any chart is drawn.
- Outputs: chart12_logP_vs_d.png, chart13_decay_rate_classes.png,
  chart14_pattern_flip.png, chart15_inversion_dimension.png,
  chart16_correction_crossover.png
- Measured inversion dimensions ($`\sigma=2`$): $`p=3`$: 1.00 (pred 1.00), $`p=5`$: 2.10
  (2.58), $`p=7`$: 4.00 (4.04), $`p=11`$: 6.37 (6.87), $`p=13`$: 8.03 (8.27).

## Run 008 — 2026-07-24 — crossover-law propositions (C024, C025)

- Command: `python3 verify_crossover_laws.py` (cwd: this directory); 0.4 s
- Output: `verify_crossover_laws_output.txt`
- Results: Prop A sandwich exact on 147×2 cases; Prop B conditions never
  contradicted, log signs = exact integer signs; $`P(3)=P(4)=\sigma^{-2}`$ at $`d=1`$ exact.
  Gate for the crossover-law additions to the paper (tex sha 68b446fb).

## Run 009 — 2026-08-04 — charts 12–16 regenerated (annotation fix)

- Command: `python3 compute_dimension_insights.py` (cwd: project root)
- Reason: chart13's in-image annotation cited a stale theorem number
  ("Thm 6.4(ii)"; the compiled paper numbers the upper bound 6.3). The
  annotation is now number-free ("forbidden by the upper bound").
  No data or computation changed; measured inversion dimensions
  reproduced identically ($`p=3`$: 1.00, $`p=5`$: 2.10, $`p=7`$: 4.00, $`p=11`$: 6.37,
  $`p=13`$: 8.03).
- Post-run sha256 of the three charts now embedded as paper figures:
  - chart13_decay_rate_classes.png 7223d6c0b4c96f6d32b1d8d741ab8ad2c0f29067eb3c3a690801a7ec212a31a7
  - chart14_pattern_flip.png       0485f5796e4027d4d478cedf5b19d994b858c56c4c820187299690346fece7df
  - chart15_inversion_dimension.png 091c5360426f04bb7aba2f70f35c39515e37e283c41d94a0cacdde8ed43c0cc5

## Runs 010–017

> *Public release:* Runs 010–017 (and the 2026-10-11 amendment of Run 016) record follow-up work and are omitted. This repository contains the paper and its supplementary material only; see the README at the repository root.

## Run 018 — 2026-10-16 — Phase H: chart 15 legend fix and paper v4

- Phase H formalization (every paper statement Lean-checked; research/formal/STATEMENT_PRESERVATION.md § "Phase H") found 32
  text defects; all are applied in paper v4 (research/formal/PAPER_CORRECTIONS_PROPOSAL.md, each backed by a proved theorem).
- Entry 25: chart 15's legend called $`p\ln 2`$ the asymptote of $`d_c(p)`$; the asymptote is $`p\ln2+\tfrac12\ln2-1`$
  (`ShiftSym.P11.figInversionAsymptote_proved`). `compute_dimension_insights.py` line 198 relabelled to "line $`p\thinspace \ln 2`$
  ($`d_c = p\ln 2 + O(1)`$)"; regenerated with `python3 -c "import compute_dimension_insights as m; m.chart15()"` (cwd: repo
  root; only chart 15; data unchanged). sha256 charts/chart15_inversion_dimension.png 66311403cafe4ea1… (was 091c5360426f04bb…).
- Paper v4: shift_symmetry_d_dimensions.tex aa9c0b7536785324…, .pdf 36f6dedc5faff9d6… (20 pp., pdflatex ×3, no undefined references).
  Review copy with the changes v3.1 → v4 marked (latexdiff 1.4.0, additions green, deletions red):
  shift_symmetry_d_dimensions_v4_diff.pdf ce408aa02cd81a85… (21 pp.).

## Run 019 — 2026-10-18 — response to the independent review: chart 14 title, paper v4 update

- Review and response: research/formal/main_paper_audit/ (independent_review.md; review and response in one file, timestamped).
- Chart 14: the embedded $`d = 2`$ title claimed prime dips "for all $`n \le 40`$", false at $`n = 3`$ ($`P(3^2) > P(4^2)`$).
  `compute_dimension_insights.py` line 140 now reads "every prime $`p \ge 5`$ is a local dip (a theorem; $`n = 3`$ is the exception:
  $`P(3) > P(4)`$)" (`ShiftSym.P11.compositeAdvantageD2_proved`); regenerated with
  `python3 -c "import compute_dimension_insights as m; m.chart14()"` (cwd: repo root; only chart 14; data unchanged).
  sha256 charts/chart14_pattern_flip.png 73856cfb2d8506e5… (was 0485f5796e4027d4…).
- Lean: group 12 (Remark 4.5 necklace identification), 5 statements proved; AuditPaper 342/342; kernel replay of all 242
  modules reachable from the root: 8553 theorems, 1990 definitions, 0 errors; check_frozen.py OK (19 files).
- Paper v4 (review fixes 1–6, 11): shift_symmetry_d_dimensions.tex 3a2051b898b0f82f…, .pdf 8ef31d0b7da762e2… (21 pp.); diff against v3.1
  (latexdiff 1.4.0, green added / red deleted): shift_symmetry_d_dimensions_v4_diff.pdf 916fe57220014307….

## Run 020 — 2026-10-19 — reply to the reviewer's verification: wording fix, dependency fingerprints, replay gate

- Verification and reply: research/formal/main_paper_audit/independent_review.md (sections of 2026-10-19).
- Paper (released as v5, Run 021): the sentence before Figure 2 now reads "shows the convergence in numerical evaluations of the exact formula"
  (was "in exact data"; chart 13 is a log-space evaluation). shift_symmetry_d_dimensions.tex 506534d98cfb4158…, .pdf 9d5f7a44b017a9ad…
  (21 pp., pdflatex ×3, no undefined references); diff against v3.1 (latexdiff 1.4.0): shift_symmetry_d_dimensions_v4_diff.pdf 103e1384eff1192c….
- Lean gates (cwd research/formal/shiftsym): `lake env lean ../frozen_deps.lean` (new) — 753 frozen statements, 2056
  constants, 29 Shiftsym modules in the dependency closure, 0 unrecorded after adding 10 files + toolchain/mathlib pins
  to frozen_statements.sha256 (dc7cea3468b326ef…, 31 files; each hash equal to main_paper_audit/source_manifest.json of 2026-10-16);
  `python3 ../check_frozen.py` OK (31 files); `lake env lean ../kernel_replay.lean` (now fails on errors or project
  axioms) — 242 modules, 8553 theorems, 1990 definitions, errors=0, exit 0; check_placeholders.py CLEAN.

## Run 021 — 2026-10-19 — paper v5

- v5 = v4 (commit 20d93ba) + the independent-review fixes of Runs 019–020 (Remark 4.5 necklace wording, Corollary 8.2 scope,
  Remark 9.3 fixed $`d`$, Table 2 detection row, figure captions and reproducibility paragraph, §11 counts for group 12 and the
  242-module replay, the sentence before Figure 2) + the date-line label v5. No theorem, lemma, proposition or corollary changed.
- shift_symmetry_d_dimensions.tex ee624497d3114686…, .pdf 132c2218576acca8… (21 pp., pdflatex ×3, no undefined references).
- Review copy v4 → v5 (latexdiff 1.4.0 --type=UNDERLINE against `git show 20d93ba:shift_symmetry_d_dimensions.tex`,
  additions green, deletions red): shift_symmetry_d_dimensions_v5_diff.pdf c4ee1b3cc8b3f8d8… (21 pp.).
  shift_symmetry_d_dimensions_v4_diff.pdf restored to its committed v3.1 → v4 version (20d93ba).

## Run 022 — 2026-10-19 — phone-sized renderings of paper v5 (light and dark)

- New wrappers that `\input` the unchanged v5 source (shift_symmetry_d_dimensions.tex ee624497d3114686…) and change only
  the layout through LaTeX hooks: a 4in × 7.1in page, `\sloppy`, line breaks after "/" and "_" in `\texttt`, link colours,
  and displays/tables wider than the column scaled down to it (`adjustbox`, max width only).
  shift_symmetry_d_dimensions_mobile.tex 4a805c30158dd8c6…; shift_symmetry_d_dimensions_mobile_darkmode.tex 0f2f7df4b3ec4887…
  (same layout, light text on RGB(30,32,36); the figures keep their white backgrounds).
- Build: pdflatex ×3 from the repository root, pdfTeX 1.40.29 (TeX Live 2026) in
  texlive/texlive@sha256:c451d81d69a3…; 0 errors, 0 undefined references, 0 overfull boxes in either log.
- shift_symmetry_d_dimensions_mobile.pdf 0ca51434484b6cfd… (42 pp.), shift_symmetry_d_dimensions_mobile_darkmode.pdf
  b30d7d1723e3eeaa… (42 pp.).

## Run 023 — 2026-10-20 — cited papers: arXiv sources and phone-sized renderings

- New `cited_papers/` with the arXiv sources (unchanged) and PDFs of the two Castillo-Ramirez papers cited in the paper:
  castillo-ramirez_gadouleau_2017/ (arXiv:1610.00532v2): paper.tex 211d1a31698bc268…, paper.pdf 9e5e2d03fce34562… (19 pp.);
  castillo-ramirez_sanchez-alvarez_2021/ (arXiv:2102.09524v2): paper.tex ccd83adbd7612a9d…, paper.pdf cec7f3839fa741f0… (8 pp.).
- Shared layout cited_papers/mobile_layout.tex 60beb7cfd10f15a6… (the Run 022 hooks, plus `align*` → one shrink-to-fit
  `aligned` block and `tikzpicture` fitted like `tabular`; both skipped in LR/math mode or when redefined).
  Wrappers: gadouleau paper_mobile.tex c9aa4ad76ff6ec70…, sanchez-alvarez paper_mobile.tex 65728ac5a10d2fe7…,
  paper_mobile_darkmode.tex dd58f8787c1d8f2f… (identical in both); slashbox.sty shim 30ba1c3bdb8bb38b… (loads diagbox).
- Build: pdflatex ×3 from each paper directory, pdfTeX 1.40.29 (TeX Live 2026) in texlive/texlive@sha256:c451d81d69a3…,
  with multirow, diagbox, tkz-graph, authblk (preprint bundle) and pict2e from CTAN (2026-10-20) on TEXMFHOME, as the
  medium scheme lacks them. The unchanged paper.tex also builds (0 errors). 0 errors, 0 undefined references,
  0 overfull boxes in all four mobile logs.
- castillo-ramirez_gadouleau_2017/paper_mobile.pdf 1b75e37657f149d0… (41 pp.), paper_mobile_darkmode.pdf 674bda977d8e5108… (41 pp.);
  castillo-ramirez_sanchez-alvarez_2021/paper_mobile.pdf 956db2465169aef6… (16 pp.), paper_mobile_darkmode.pdf 037365e15558f98e… (16 pp.).

## Run 024 — 2026-10-20 — dark-mode renderings removed

- Removed the dark-mode wrappers and PDFs of Runs 022–023 (shift_symmetry_d_dimensions_mobile_darkmode.tex/.pdf and
  cited_papers/*/paper_mobile_darkmode.tex/.pdf); the light renderings and their checksums above are unchanged.

## Run 025 — 2026-10-22 — Proposition 10.2: the window constant 20 frozen (group-09 supplement)

- New frozen file research/formal/shiftsym/Shiftsym/Paper/S09_CrossoverLaws_Window20.lean a5f160ec350eb027… with 3
  statements: `inversionExplicitWindow20Statement` and `inversionWindow20Statement` (the reviewed group-09 `∃ C` window
  bodies with `C := 20`, criteria and probability form) and `inversionLaw20Statement` (Proposition 10.2 as stated in v5).
  Frozen after the helper theorems `window_i`/`window_ii`, which supplied the paper's 20, existed; S09_CrossoverLaws.lean is
  unchanged (eb9baf4b5dcfbf9c…). Fingerprint in research/formal/frozen_statements.sha256 (65c15bc760a8dd91…; own dated
  section; 32 files).
- Fidelity: mechanical first (each window body equals the `∃ C` body with `C := 20` token for token; `fun h => ⟨20, h⟩`
  type-checks into both `∃ C` statements), then three fresh-context reviewers, all PASS: A literal comparison, B exploit
  hunting, C numerical reconstruction from the paper alone. Findings and what was done: research/experiments/window20_fidelity/
  README.md (1ae24ff566cefa93…). C: 1,260,654 grid points (302 primes 3–1999 × 6 alphabet sizes × every d ≤ ⌈d_c(p)⌉ + 60),
  0 disagreements between the paper and Lean readings, 0 violations; composite branch exact 35/35; prime branch proved at
  74,298 points by a log-space dominance bound (window20_fidelity/C_numerics/, SHA256SUMS c216a174f0821f40…).
- Proofs, written after the reviews: research/formal/shiftsym/Shiftsym/Paper/Proofs/P09_CrossoverLaws_Window20.lean
  ca15d051d029b5d5… (the three `_proved` theorems, from `window_i`/`window_ii` and the proved (i), (ii)), with
  `inversionWindow20_nonvacuous` (lower branch at p = 37 for exactly d ∈ {1, …, 4}; upper branch at p = 3 from d = 21 on)
  and `inversionWindow20_lower_empty` (no prime p ≤ 31 reaches the lower branch). Imported in Shiftsym.lean
  (e649485998a37929…) and Shiftsym/AuditPaper.lean (6ba4a4ef2bbbe38e…).
- Correspondence audit (research/formal/correspondence_audit): Proposition 10.2 now maps to `inversionLaw20Statement`, and
  the constant 20 is a `same` mapping.
- Not changed: the paper (v5). Its §11 figures (342 statements; 50 paper-layer modules; 242 modules, 8553 theorems and 1990
  definitions replayed) and its sentence that the constant 20 is certified only by auxiliary theorems describe the
  development before this run.

## Run 026 — 2026-10-23 — paper v6 and verification of the merged window-20 PR (#1)

- Paper v6 (from PR #1, commit f1d041a): §11 updated for the group-09 supplement (345 statements, 52 paper-layer modules,
  three statements frozen after their helper proofs existed, replay 244 modules / 8567 theorems / 1993 definitions) and the
  date-line label v6; nothing else changed. shift_symmetry_d_dimensions.tex ff8d56104ee1c07a…, .pdf fa91c65d6d8ab8d9…; review copy v5 → v6:
  shift_symmetry_d_dimensions_v6_diff.pdf 5fa22533a8eb626d….
- Verification after the merge (a066959), cwd research/formal/shiftsym: `lake build Shiftsym` green (the 64 modules
  invalidated by the Definitions.lean edit rebuilt in waves of at most 4 parallel jobs — an unthrottled build ran the
  20-core machine out of memory); AuditPaper 345/345, 0 failures (group 09: 24); AuditExt 389/401 proved, 12 listed
  stated-not-proved (unchanged); `lake env lean ../frozen_deps.lean` 756 frozen statements, 2061 constants, 30 modules,
  0 unrecorded; `lake env lean ../kernel_replay.lean` 244 modules, 8567 theorems, 1993 definitions, errors=0, exit 0
  (the figures stated in v6); check_placeholders.py CLEAN.
- `check_frozen.py` flagged Shiftsym/Definitions.lean (commit c909527: the deprecated alias `Set.mem_setOf_eq` replaced
  by its target `Set.mem_ofPred_eq` in the two proof fields of `stab`; diff 2+/2−, no definition or type changed).
  Re-recorded with a note in frozen_statements.sha256 (99c1315dec3d4671…); check_frozen.py now OK (32 files).

## Run 027 — 2026-10-27 — Corollary 8.2: the symmetry-breaking clause frozen (group-07 supplement); paper v7

- Trigger: an independent judgment of the two items left open by the correspondence audit (commit 977f823): Lemma A.2,
  never judged, and Corollary 8.2, whose verdict was stale (research/formal/correspondence_audit/independent_judgment/:
  JUDGMENT.md c3979aa96a25f4c3…, Probes.lean f1dd75578f5f0317…, probes.log 345354994ce580e5…, exit 0).
  - Lemma A.2 holds (15/15 mappings).
  - Corollary 8.2: the sentence added in v5 ("every pattern-recognition or image-processing task whose required output
    breaks a symmetry of some admissible input") had no frozen statement. It is strictly more than
    `insolvGeneralStatement`: on Z_4, 0000 → 0101 breaks a symmetry although 0101 is shift-symmetric.
- New frozen file research/formal/shiftsym/Shiftsym/Paper/S07_Dynamics_SymmetryBreaking.lean 936975cebac8504c… with
  `RequiresSymmetryBreaking` and 2 statements: `insolvSymBreakStatement` and `insolvFullStatement` (the corollary as
  stated since v5). It was frozen after a probe proof existed. S07_Dynamics.lean is unchanged. Fingerprint recorded in
  research/formal/frozen_statements.sha256 (57f77e572900524a…; own dated section; 33 files).
- Fidelity: three fresh-context reviewers, all PASS, before the proofs were written (research/experiments/symbreak_fidelity/,
  README.md d81a4653a8ddfd6a…; reviewed file hash dbe24aa3102d906e… in frozen_at_review.sha256). A did a literal
  comparison (REPORT 41d6a5cea75717c1…), B hunted for exploits (c467e306e12a049f…), and C did an independent
  reconstruction (19a6eb90fdfcfaac…).
  - C's brute force found 0 violations on Z2, Z3, Z4, Z2², Z6, Z5, Z2³, Z3², Z2×Z4. The reachable set from x is exactly
    {y : Stab x ⊆ Stab y}. SHA256SUMS is in C_reconstruction/.
  - A's finding F1 (the corollary's "This covers" is imprecise, since its argument "no trajectory leaves S" does not
    exclude these tasks) and the cosmetic items went into the docstrings only. B's `rfl` probe, C's `Iff.rfl` check and
    B's probe_ab were re-run against the edited file, all exit 0, so the Props are unchanged.
- Proofs, written after the reviews: research/formal/shiftsym/Shiftsym/Paper/Proofs/P07_Dynamics_SymmetryBreaking.lean
  6cc8fc54d0d973b8…. Theorem 8.1 in stabilizer form (`irrevStab_proved`) is iterated along the trajectory. The file also
  proves `requiresSymmetryBreaking_of_requiresLeavingS` and
  `stripeTask_requiresSymmetryBreaking_not_requiresLeavingS` (non-vacuity and strictness; not paper claims).
  Imported in Shiftsym.lean (a7580622ee92cc0a…) and Shiftsym/AuditPaper.lean (ee6019b65cadf5e3…).
- Gates (cwd research/formal/shiftsym):
  - `lake build` green; AuditPaper 347/347 (group 07: 33), 0 failures.
  - `lake env lean Shiftsym/Audit.lean` exit 0, no sorryAx.
  - check_placeholders.py CLEAN; check_frozen.py OK (33 files).
  - `lake env lean ../frozen_deps.lean`: 758 frozen statements, 2064 constants, 31 Shiftsym modules, 0 unrecorded.
  - `lake env lean ../kernel_replay.lean`: 246 modules, 8574 theorems, 1999 definitions, errors=0, exit 0
    (46 min, 18.1 GB peak RSS; +2 modules, +7 theorems, +6 definitions against Run 026).
- Paper v7: shift_symmetry_d_dimensions.tex 9ae81ae8537b6795…, .pdf 72ca4db4a61406d4… (21 pp.).
  - Corollary 8.2 reworded: "More generally, since Stab can only grow along a trajectory (Theorem 8.1), every … task
    whose required output breaks a symmetry of some admissible input is unsolvable, as in the two-dimensional
    discussion of [2019]".
  - §11: 347 statements, ≈24,000 lines in 54 modules, Section 8 group (33), "all but five", the five exceptions, and
    the replay figures above. Date-line label v7.
  - Review copy v6 → v7: shift_symmetry_d_dimensions_v7_diff.pdf 7dab740e652a0cf9…, made with latexdiff 1.3.1a
    (Ubuntu), `--type=UNDERLINE`, added text in green, legend in the date line.
  - Phone-sized rendering, rebuilt 2026-11-02 once the cm-super Type 1 fonts (needed by its microtype font expansion)
    were installed: shift_symmetry_d_dimensions_mobile.pdf a0611cbc0bfee938… (42 pp.; wrapper unchanged; pdflatex ×3
    from the repository root, pdfTeX 1.40.22, TeX Live 2022 Debian; 0 errors, 0 overfull boxes, no undefined
    references; the text carries the v7 date line, the reworded Cor 8.2 sentence and the §11 figures).
- Correspondence audit (research/formal/correspondence_audit):
  - cor_insolv.json (70a5ed596d60c36f…) changes: `pattern` now maps to `insolvSymBreakStatement` as a generalization;
    new mappings `pattern.hyp` (`RequiresSymmetryBreaking`), `pattern.why` (`irrevStabStatement`) and `full`
    (`insolvFullStatement`); one duplicated anchor pinned with `occ`.
  - TeX line-range scopes in six other mapping files were remapped onto v7 with build.py's `line_map`. Only the
    numbers changed.
  - Lean exports were added for the two new files. `build.py --check`: 24 files, 474 mappings, 0 errors.
  - data/audit_data.json is NOT rebuilt (the build needs the Docker image shiftsym-tex:jammy). After the rebuild, the
    tool will flag the verdicts on these seven items as stale, some of them only because line numbers moved.
- Docs: STATEMENT_PRESERVATION.md (row and totals), FORMALIZATION_PLAN.md (item 8), PAPER_CORRECTIONS_PROPOSAL.md
  (update to the "image translation" note), CLAUDE.md, README.md, and an addendum on finding 2 in
  research/formal/main_paper_audit/independent_review.md.

## Run 028 — 2026-11-02 — review of the contributor commits not covered by Runs 025–027

- Scope: the commits by T. Lehman on main up to 977f823 that no earlier run reviewed, with the Lean changes rechecked:
  d1a8d43, 779b5b6, a02114e, 2acc272, fb048a2, c909527, b83a7fb (f1d041a: Runs 025–026 and
  research/formal/main_paper_audit/pr1_window20/; 977f823: Run 027). origin/main = 977f823 at the time of the run.
- Lean, every file the commits touch:
  - Definitions.lean (c909527): `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` in the two proof fields of `stab`; no
    definition or statement changed (fingerprint re-recorded in Run 026).
  - S09_CrossoverLaws_Window20.lean (f1d041a): the two window bodies are the reviewed `∃ C` bodies of
    S09_CrossoverLaws.lean with `C := 20`, token for token; against paper v7 lines 985–1002, (i) and (ii) apply to every
    integer $`d \ge 1`$ with $`d \le d_c(p) - 20`$, resp. $`d \ge d_c(p) + 20`$, with the paper's hypotheses ($`p \ge 3`$ prime,
    $`\sigma \ge 2`$). The proofs (P09_CrossoverLaws_Window20.lean) are covered by AuditPaper 347/347 and the kernel
    replay of Run 027.
  - Shiftsym.lean, AuditPaper.lean, frozen_statements.sha256 (f1d041a): additions only (two imports, a docstring
    sentence, one fingerprint in a dated section); the audit check itself is unchanged.
  - correspondence_audit/tools/ExportInfo.lean (2acc272): an export tool, imported by no library module.
  - No gate (check_frozen.py, check_placeholders.py, frozen_deps.lean, kernel_replay.lean), lakefile, toolchain or
    manifest was touched by any of the commits.
- 779b5b6 and a02114e (Unicode math → LaTeX math in 35 resp. 22 Markdown files): formatting-only check
  research/experiments/format_check/format_check.py 48bd6668c851da17… (`python3 -I format_check.py <commit>`; compares
  each diff hunk after reducing both sides to a common skeleton). a02114e: 141 hunks, 0 differences
  (a02114e_output.txt 69377200985cd361…). 779b5b6: 983 hunks, 70 with residual differences (779b5b6_output.txt
  dc916954ac3dc685…), all inspected by hand and all notational: negated symbols (∤, ≢, ⊄ as `\nmid`, `\not\equiv`,
  `\not\subseteq`), the closing bar of `\lvert\lbrace…\rbrace\rvert` for `#{…}`, the paper macros `\ZZ`, `\gauss`,
  `\vv` replaced by `\mathbb{Z}`, `\binom`, `\mathbf{v}`, `p·ln 2` → `p \ln 2`, `r=1..d` → `\sum_{r=1}^{d}`, two
  displays set as `cases`, and one nested `C(r_p(H), 2)` → `\binom{r_p(H)}{2}`. Limitation: the check ignores grouping
  (brackets, extent of sub- and superscripts).
- Tooling (2acc272, b83a7fb): exercised, not read line by line (`build.py --check` 0 errors, Lean export, the citation
  data of Run 027); serve.py binds 127.0.0.1 and serves only app/, data/*.json, the paper source and .lean files under
  the Lean root (resolved-path checks). The auditor's 22 approvals were not re-judged; the two open items were (Run 027).
- fb048a2: shift_symmetry_d_dimensions_mobile.tex only changes layout through hooks and `\input`s the paper unchanged
  (its header still mentions the dark-mode wrapper removed in Run 024). Branch origin/mobile-dark-pdf (52a706e) is an
  earlier state of c909527; nothing to merge.
- c909527, cited_papers/: both arXiv records (1610.00532v2, 2102.09524v2) carry only the arXiv non-exclusive
  distribution licence (http://arxiv.org/licenses/nonexclusive-distrib/1.0/), which licenses arXiv, not third
  parties. Keep the copies only while the repository is private; replace them by links before it is made public.

## Run 029 — 2026-11-02 — paper v8: John Caughman's edits merged; correspondence audit carried to v8

- Source: J. Caughman's edit of paper v5 (b9df6bc), shift_symmetry_d_dim-V5-John.tex e7437322f79d69ea… (1697 lines;
  committed at the repository root as returned; it does not compile as is, see V8_EDITS.md entry 1). Three-way merge onto v7 (`git merge-file`, base v5, ours v7, theirs John): no conflicts, since v6
  and v7 touched only §11, Cor 8.2 and Prop 10.2's window sentence.
- Editorial changes on top of John's text, each with John's wording, the v8 wording and the reason:
  research/paper_edits/V8_EDITS.md ce9aaee29bcfdb90… (18 entries; decisions (a)–(e) and the renumbering approved by
  P. Banda). Among them: a stray `\end{remark}` that stopped compilation; the standing hypothesis of Definition 2.1
  restored to "(for counting statements, σ = 1 is also allowed)", without which Lemmas 3.1(i) and 3.2 would not
  cover the σ = 1 case that Theorems 4.4 and 5.1 use; four references that needed Lemma 4.2 after John's split of
  Lemma 4.1; §11's hard-coded "Definition 4.2" (now 4.3, via the new label `def:coef`) and its pointer to the
  necklace identification (Remark 4.6(iii), was 4.5(ii)).
- Renumbering: Definitions 2.1–2.3, Remark 2.4, Lemmas 3.1/3.2 (swapped), Lemma 4.1 (split into 4.1 and 4.2),
  Definition 4.2, Theorem 4.3, Corollary 4.4 and Remark 4.5 move; Sections 5 onward, equations and tables keep their
  numbers. Paper v3.1 to v7 share one numbering (all 51 labels compile to the same numbers; checked by compiling
  ee9fb9f). Concordance: research/formal/STATEMENT_PRESERVATION.md, section "Item numbers". Frozen Lean files and
  names keep the old numbers; CLAUDE.md, README.md and FOLLOW_UPS.md updated.
- Paper v8: shift_symmetry_d_dimensions.tex 3682affd0dc1a077…, .pdf 67e1d58629ce9e3c… (23 pp.; pdfTeX 1.40.22,
  TeX Live 2022 Debian, pdflatex ×3; 0 errors, no undefined references, one 0.7 pt overfull box in the proof of
  Lemma A.3, as in v7, where John's edits removed the other three). Date-line label v8.
  - Review copy v7 → v8: shift_symmetry_d_dimensions_v8_diff.pdf f2d59ef9dc5c19c3… (24 pp.), latexdiff 1.3.1a
    (Ubuntu), `--type=UNDERLINE`, added text in green, legend in the date line. In the diff only, latexdiff's doubled
    "translation-equivariant" in Definition 2.4 runs into the right margin.
  - Phone-sized rendering: shift_symmetry_d_dimensions_mobile.pdf 50d5334ad9a2c4b1… (46 pp.; wrapper unchanged;
    0 errors, 0 overfull boxes, no undefined references). John's `$$…$$` displays were converted to `\[…\]`, which
    the wrapper rescales.
- Correspondence audit (research/formal/correspondence_audit): 25 items (new: `lem:mobius2`), 476 mappings;
  `tools/build.py --check`: 0 errors, 1 warning (as before).
  - New tool tools/remap_anchors.py 93719fb947081aa6…: carries anchors from one paper version to the next by a line
    diff (`build.line_map`). v7 → v8 over 513 TeX anchors: 362 unchanged, 84 line scopes remapped, 20 moved (found
    once elsewhere, scope set there), 47 in reworded text. Self-test v8 → v8: 519 anchors, all unchanged.
  - The 47 reworded anchors were edited by hand, each against John's new wording; no mapping changed its kind. The
    mapping `cor_prime.json:hyp` now anchors to the corollary's own "integers d ≥ 1 and σ ≥ 1" (it pointed to
    Theorem 4.3's hypotheses), and the `sopf` anchor of thm_detect-worst.json points to the live definition (John left
    a commented-out copy before Theorem 6.3).
  - Lemma 4.1's mappings split: lem_mobius.json 2c8d3ac8b1999a80… keeps the chain f(V) = μ(0,V) = (−1)^r p^C(r,2)
    (`lemMobiusFEqMuStatement`, `lemMobiusMuClosedFormStatement`); lem_mobius2.json c4860b6665518282… takes eq. (cr)
    (`lemMobiusCrStatement`). The frozen conjunction `lemMobiusStatement` is unchanged.
  - Item numbers in the hand-written labels, notes and summaries follow v8 (e.g. Corollary 4.5, Definition 2.3 for
    S(v), Definition 2.4 for the CA); the README says 25 items and 23 pages.
  - Not rebuilt at first: data/audit_data.json and data/paper.aux.json (Docker image shiftsym-tex:jammy absent here).
    [Corrected after the independent v8 review, research/formal/main_paper_audit/v8_review/REVIEW.md, finding V8-1:
    this entry first said that until the rebuild the viewer "still shows v7" and that verdicts on changed items "will
    be flagged stale". Both were wrong. The bundle in the repository had been built at f1d041a from paper **v6**
    (TeX ff8d5610…, PDF fa91c65d…, 24 items, 21 pages); v7 never got a bundle. The viewer also flags a verdict as
    stale only against the item hashes stored in that bundle, so it flagged nothing. It showed the current v8 PDF with
    v6 item numbers and highlights. The bundle was rebuilt the same day; see the end of this entry.]
- Lean: no file changed. check_frozen.py: 33 files fingerprinted, OK; check_placeholders.py: CLEAN. No build or
  kernel replay needed (Run 027's figures stand).
- Second pass over John's edits (same day, after the push of a7b87d6; approved by P. Banda): V8_EDITS.md entries
  19–30 (V8_EDITS.md now ed91deba40ba7878…). One correction of substance: in the proof of Lemma A.1 the range
  "Lemmas 3.1–3.5" had come to include Lemma 3.2 (order of a translation) through John's swap of Lemmas 3.1 and 3.2.
  That lemma's formula holds only on the square torus, not on the rectangular tori T_j, so the range is now
  "Lemmas 3.1, 3.3–3.5, 4.1 and 4.2", as in v7. The rest is wording and typesetting:
  - the fixed-set formula of Definition 2.2, which printed "∀h ∈ H(τ_h s = s)";
  - the proofs of Lemmas 3.4 and 4.2;
  - "next section" in Remark 4.6(i), and "could" at the start of Section 4.3;
  - spacing after "et al.";
  - display-size Gaussian binomials in eq. (1) and Definition 4.3;
  - "Definition" in Theorem 8.1, with its clauses reordered to avoid a 19.5 pt overfull line (same meaning);
  - three section openings and one paragraph title.

  Entry 1's location is corrected to "after Definition 4.3". No line count changed.
  - Paper: shift_symmetry_d_dimensions.tex 72bd954993ea17ec…, .pdf 3d5eb36ae65f9fea… (23 pp.; pdflatex ×3; 0 errors,
    no undefined references, only the 0.7 pt overfull box in the proof of Lemma A.3, as in v7).
  - Review copy v7 → v8 rebuilt with the same recipe: shift_symmetry_d_dimensions_v8_diff.pdf e1b8d7a5188c4313…
    (24 pp.). In the diff only, struck-out inline formulas cannot break and run into the right margin (e.g. Lemma 3.2,
    Lemma 3.5, Theorem 8.1); all text stays on the page.
  - Phone-sized rendering: shift_symmetry_d_dimensions_mobile.pdf 9b44c8587c584540… (46 pp.; 0 errors, 0 overfull boxes).
  - Correspondence audit: tools/remap_anchors.py over the 519 TeX anchors gave 515 unchanged and 4 reworded. The four
    were updated by hand: lem_completeness.json:Fix and lem_fix.json:i.lhs (entry 20), and lem_mobius2.json:cr and
    cr.rhs (entry 26). New checksums: lem_completeness.json 530d2943b3274e1c…, lem_fix.json b00d60c92c5eb771…,
    lem_mobius2.json 5440ca42e6a79404…. `tools/build.py --check`: 0 errors, 1 warning (as before).
  - Lean: no file changed; check_frozen.py OK (33 files), check_placeholders.py CLEAN.
- Viewer bundle rebuilt against v8 (same day; independent v8 review, finding V8-1, approved by P. Banda):
  - Docker image shiftsym-tex:jammy built from the README recipe (image 09d8f6f613ba…, 578 MB; pdfTeX 1.40.22,
    TeX Live 2022/dev/Debian). The first attempt failed the layout check from the first word: the recipe lacked
    `cm-super`, so the container set the T1 text in bitmap Type 3 fonts, while the official v7/v8 PDFs, built on the
    authors' machine, use the scalable cm-super Type 1 fonts (SFRM, SFBX, …; Ubuntu cm-super 0.3.4-17). The v6 PDF
    (f1d041a) had been built in the container without cm-super; this is why the earlier builds passed. The recipe
    now installs `cm-super`, with a note on matching fonts (research/formal/correspondence_audit/README.md
    d06af8ceac0b209d…, which also says that `--check` does not refresh the bundle). The image was rebuilt from that
    recipe.
  - `tools/build.py` (full build): 25 correspondence files, 476 mappings, 0 errors, 1 warning (as before); 23 pages,
    51,954 glyph boxes; layout identical to the official PDF (every word at the same coordinates). The Lean exports
    (data/lean/) were not re-exported: no Lean file has changed since e868e8f, and all 73 Lean fingerprints match.
  - data/audit_data.json 6dc50324f6b393e4… (built at 47ed8bc; 25 items with v8 numbers, including Lemma 4.2;
    the symmetry-breaking statement file is listed; fingerprints match the committed PDF 3d5eb36a… and TeX 72bd9549…),
    data/paper.aux.json 85769167dc72e7ef…, data/pdf_chars.json 9ad8c729e1ada4bc….
  - Tobi Lehman's 23 verdicts in logs/events.jsonl (all 👍, given against v6) now show as stale, as intended:
    - line numbers only: Proposition 8.3, Theorem 9.1, Proposition 10.2, Lemmas A.3 and A.4;
    - mapping text only: Corollary 7.2, Lemma A.1;
    - mappings and summary: Theorem 4.4;
    - statement text changed: the other 15.

    Item IDs are LaTeX labels, so every verdict stays with its item through the renumbering. Not yet judged: Lemma 4.2
    (new) and Lemma A.2.

## Run 030 — 2026-11-03 — paper v9: Figure 1, verification-pipeline figure, applications and the correspondence audit

- Text added (no statement of Sections 2–10 or Appendix A changed; every label except the figures compiles to its v8
  number, checked by comparing the `.aux` files):
  - Abstract: one closing sentence (Lean verification of every numbered statement; hand audit of the correspondence of
    the 25 theorems, lemmas, propositions and corollaries with a purpose-built paper–Lean viewer).
  - Introduction: Figure 1 (`fig:examples`), referenced in the first sentence.
  - Section 11: Figures 1 and 5 and the applications of Section 12 declared not formalized; pointer to the hand audit;
    Figure 5 (`fig:pipeline`, TikZ; `\usepackage{tikz}` added).
  - Section 12 (now labelled `sec:conclusion`): "Applications" (distributed computing, machine learning, materials
    science, physics, random initial states) and "Verification and its audit". Subsection 4.4 labelled `sec:compver`.
  - Eight references: Angluin (STOC 1980), Yamashita–Kameda (IEEE TPDS 1996), Cohen–Welling (ICML 2016),
    Kaba–Ravanbakhsh (NeurReps 2023), Mordvintsev et al. (Distill 2020), Hart–Forcade (PRB 2008), Sandvik (AIP Conf.
    Proc. 2010, §§4.1.3, 4.4.1), Wolfram (Adv. Appl. Math. 1986). Each was checked at the source (publisher or
    proceedings page, arXiv, or the paper's text) before it was cited.
- Figure 1: compute_example_configs.py 93f552eea3034de2… (Python 3.10, matplotlib 3.10.8; fixed seeds 17001–17003,
  fixed cells for (d)) → charts/chart17_example_configs.pdf dcb9f5578a4ed8bc… (byte-identical on rerun; PDF metadata
  dates suppressed). The script computes every stabilizer by brute force over all translations and asserts:
  (a) {0, (3,0)}, (b) {0, (2,2), (4,4)}, (c) {0} on Z_6^2, (d) {0, (0,2,2)} on Z_4^3 (6 filled cells); and
  |S_{6^2}| = 801064 (σ = 2) both by the closed form of Theorem 4.4 (`formula_count`) and by inclusion–exclusion over
  the 7 prime-order cyclic subgroups. The count is also the frozen reference value `refValue62Statement`
  (Paper/S04_EnumerationCorollaries.lean).
- Independent hostile review of the additions (fresh context, own code; 2026-11-03): all eight citations correct;
  Figure 1 stabilizers and |S_{6^2}| reproduced independently (union of Fix⟨v⟩ over the 35 nonzero v; Möbius over the
  30 subgroups); 25 items, 476 links and 347 statements confirmed. Two errors and five warnings, all repaired before
  this entry:
  - "The audit approved all 25 items": at the time 5 verdicts were stale (line scopes only) and v9 moves every line
    scope. Now: "All 25 items were approved, and their statements are unchanged in this version."
  - Physics: "any deterministic update scheme … that treats all sites alike … preserves every translation symmetry"
    is false (counterexample: a red–black Gauss–Seidel sweep; also the sentence after Theorem 8.1). Now restricted to
    update maps that commute with the grid translations, in exact arithmetic.
  - The symmetry-breaking clause of Cor 8.2 was found by the separate check of 2026-10-27
    (correspondence_audit/independent_judgment/JUDGMENT.md), not by the hand audit; the text now says so.
  - The stale mechanism is described as implemented (item TeX, Lean source of its declarations, link data; after a
    rebuild); no link is of kind "weaker" (kinds: representation 174, same 141, definition 85, hypothesis 57,
    lean-only 11, citation 3, paper-only 3, generalization 2), and the text says so; neural CA drop determinism as well
    as synchrony; Theorem 5.1 gives the probability for a prescribed k, Corollary 7.2 for uniform k.
  - Nits adopted: Angluin and Yamashita–Kameda scoped; Figure 5's box and caption ("every frozen statement (currently
    347)", hand audit only for the 25 items); the Figure 1 count named as a machine-checked reference value; arrows
    and panel (d) described; "log kept under version control" instead of "append-only" (b83a7fb removed heartbeat
    events; the log also holds the scripted bulk-clear session of 2026-11-02).
- Paper v9: shift_symmetry_d_dimensions.tex 807c880603e5f0cd…, .pdf 02db9668739377ed… (25 pp.; pdfTeX 1.40.22,
  TeX Live 2022 Debian, pdflatex ×3; 0 errors, no undefined references; only warnings already in v8: the 0.7 pt
  overfull box in the proof of Lemma A.3, underfull lines in the summary table, two hyperref string warnings).
  - Review copy v8 → v9: shift_symmetry_d_dimensions_v9_diff.pdf c51a49f98ee7f6ef… (25 pp.), latexdiff 1.3.1a,
    `--type=UNDERLINE`, added text in green, legend in the date line. In the diff only, underlined additions cannot
    break and three lines run up to 17 pt into the margin.
  - Phone-sized rendering: shift_symmetry_d_dimensions_mobile.pdf c0734ae34ff0fd29… (53 pp.; 0 errors, 0 overfull
    boxes). The wrapper (bd8e29c073233a37…) now also scales `tikzpicture` to the line width, as it does `tabular`.
- Correspondence audit (research/formal/correspondence_audit):
  - Anchors carried v8 → v9 with tools/remap_anchors.py: 519 anchors, 397 unchanged, 122 line scopes renumbered
    (`\usepackage{tikz}` and Figure 1 shift every line after the preamble), 0 moved, 0 reworded; only `"lines"`
    values changed in data/corr. `build.py --check`: 0 errors, 1 warning (as before).
  - tools/build.py d924edb5fd99af5a…: the instrumented compile copied only charts/*.png into the container; it now
    copies *.pdf too (Figure 1 is a PDF). No other change.
  - Full rebuild (Docker shiftsym-tex:jammy, cm-super): layout identical to the official PDF (all words at the same
    coordinates, 25 pages, 59 842 glyph boxes); data/audit_data.json 9b0df1228098cee6…, paper.aux.json
    1a745590b657b241…, pdf_chars.json 0d83b45862ed8d8f…; fingerprints match the v9 PDF and TeX. Built from the
    working tree at 8109cf1 (the paper changes were not yet committed).
  - Verdicts: all 25 are 👍. Against the v9 bundle 1 is current (Lemma 4.1, whose correspondence file has no line
    scope) and 24 are stale. The statements' TeX, the Lean declarations and the mapping content are unchanged since
    the verdicts were given (v8, or v6 for Prop 8.3, Thm 9.1, Prop 10.2, Lemmas A.3 and A.4); only line numbers moved.
    The hand audit needs T. Lehman's re-confirmation for v9 before posting (or an item hash that ignores line
    scopes).
- Lean: no file changed; no build needed.

## Run 031 — 2026-11-04 — final release check of both repositories; chart scripts logged

- Own checks, all OK: both repositories clean and in sync with origin (internal 402c791, public 5814505); the public
  checkout is byte-identical to a fresh `export.py` run on internal HEAD (336 files, all tracked); every
  internal-only file and every public-side difference is an intended exclusion, overlay or transform; the paper
  rebuilds from `git archive HEAD` to the committed PDF's text; 28 citations ↔ 28 bibliography entries, 58 labels,
  no undefined or duplicate; every URL and DOI resolves (the repository URL answers 404 while private; the viewer link,
  then conformal.inc, answered 301 to functorial.inc) and all nine arXiv identifiers carry the titles the bibliography gives; the mobile
  and v8 → v9 diff PDFs are current; internal gates green (placeholders CLEAN, frozen 33 files OK, `lake build`
  no-op, no Lean change since 8109cf1); viewer fingerprints match in both repositories.
- Outside review, findings and what was done:
  - Hand-audit verdicts stale for v9 (24 of 25, line scopes only), while the paper says all 25 were approved:
    open; T. Lehman's re-confirmation (or an item hash without line scopes) is a release blocker.
  - Public viewer data built from the working tree: the export now drops the six entries of the omitted modules and
    sets `repo_abs` to null (app.js then omits the vscode:// links). Commit identifiers in records refer to the
    working repository (now said in the public README).
  - `verify_crossover_laws.py` imported from the absolute path of the working tree: now from the repository root
    computed from `__file__` (438d8e5187350ae9…); output identical to the committed one apart from the platform
    line, also when run from a copy outside the repository (0.6 s).
  - The paper's reproducibility paragraph said commands and checksums of all chart scripts are logged, but
    compute_charts.py, compute_criticality.py and compute_C_exploration.py had no run entry, and it named neither
    the script of Figure 1 nor Figure 2 as an output of compute_dimension_insights.py. The paragraph now lists all
    five scripts and their figures (same line count); the scripts are logged below.
  - Public README: "exact arithmetic" for the charts corrected (the exact formula evaluated in log space); the 2D
    composite advantage stated for the primes 5 ≤ p ≤ 40 by exact computation, not for p = 3 (re-verified now:
    P(p+1) > P(p) at d = 2 for every prime 5 ≤ p ≤ 40, false at p = 3; local minima at every prime 5 ≤ n ≤ 40 and
    maxima at every even 4 < n ≤ 40); r_d described as the Möbius numbers weighted by Gaussian binomials; the
    erratum labelled a draft; the viewer's internet need and its log side effect, the mathlib cache size, and a
    complete "Scope of this release" (omitted modules, filtered files, pointers to unpublished working files).
  - correspondence_audit/README.md: the history of the committed log (b83a7fb removed the heartbeat events; the
    scripted bulk-clear session of 2026-11-02, 68 events) and how to open the viewer without changing the log.
  - research/formal/shiftsym/README.md: the `lake new` template replaced by a description and the gates.
  - Export: links to absolute working-tree paths in two review records rewritten to repository links (`/path#Lnn`);
    the nested lake-template workflows (`shiftsym/.github/`) not exported; the two `../Riemann/…` pointers dropped
    (STATEMENT_PRESERVATION.md line 3, Audit.lean line 2); root-anchored LaTeX patterns in the public .gitignore.
- Chart scripts, run from the repository root (`python3 <script>.py`; Python 3.10.12, numpy 2.0.2, matplotlib
  3.10.8, mpmath 1.3.0, sympy 1.13.1, scipy 1.14.1, Linux 6.8.0-138 x86_64): compute_charts.py 81ab9a0a60c91c47…
  (1.4 s), compute_criticality.py d9bfde1c27acc92b… (1.5 s), compute_C_exploration.py 2688f07dfc5f8394… (2.2 s;
  C = 2.2060 / 2.5333 / 2.6541 at thresholds 0.1 / 0.05 / 0.01, as in Observation 10.4),
  compute_dimension_insights.py 821bb0f698338e8e… (2.6 s), compute_example_configs.py 93f552eea3034de2… (0.9 s).
  All 17 charts regenerated byte-identical to the committed ones (charts 1–16 PNG, chart 17 PDF dcb9f5578a4ed8bc…;
  chart 13 7223d6c0b4c96f6d…, chart 14 73856cfb2d8506e5…, chart 15 66311403cafe4ea1…); stdout deterministic (two
  runs), saved as research/experiments/chart_outputs/<script>_output.txt: compute_charts c7b666381eae638d…,
  compute_criticality bd7b93da9182144a…, compute_C_exploration 4f627f4abf941078…, compute_dimension_insights
  bbf848e056ef510a…, compute_example_configs 0469f3d4d51b5836….
- Paper: .tex b0c1cd13979af5c0… (1912 lines), .pdf 840bcbfff2b8212b… (25 pp.; 0 errors; same warnings); mobile .pdf
  9339bda7f518b3d2… (53 pp.; 0 errors, 0 overfull); v8 → v9 diff .pdf c8035272a464b953…. Audit bundle rebuilt:
  layout identical (25 pages, 60 131 glyph boxes); audit_data.json 27942e359d4c1cef…, paper.aux.json
  05870a98f0b4f1cf… (unchanged), pdf_chars.json ecb59be8d4d06893…; verdicts 1 current, 24 stale (line scopes only).
- Release tooling: export.py db5c26de0a9a9533…, overlay README 316a3f6064068f27…, overlay .gitignore
  88ed176560e0991d…; shiftsym/README.md 61c603906f3530c2…; correspondence_audit/README.md 864365a5d64e5b64….


## Run 032 — 2026-11-05 — independent v9 release review; earlier leader-election references

- Reviewed internal `444c7af` against reviewed v8 (`baea4fa`), and the clean public-release checkout `e7caee2`.
  Main paper only. Detailed report and executable evidence: `research/formal/main_paper_audit/v9_release/REVIEW.md`.
- Independently reproduced the committed public export: 338 files, all byte-identical. Compiled all 76 public Lean
  project modules from source into an empty object directory, with at most four compiler processes and the pinned
  dependency cache; no internal project objects on the search path. Fresh AuditPaper: 347/347, zero failures.
  Fresh kernel replay: 76 modules, 2746 theorems, 716 definitions, zero errors. Frozen files: 25 OK; placeholders:
  CLEAN; dependency gate: 352 frozen statements, 1108 constants, 22 project modules, zero unrecorded files.
- All 39 numbered environments and production Lean source are unchanged from v8. Independently reconstructed the
  committed viewer: 173 fingerprints, 25 items, 476 links, 519 highlights, 60131 glyph boxes; exact word layout.
  Historical approvals: 25 positive, 24 stale by line scopes only, one current. The five retained v6 verdicts were
  separately checked against their historical hashes and unchanged content. No auditor event changed.
- Figure 1: regenerated byte for byte; independent array-shift stabilizers agree with all four panels. Enumerating
  the union of fixed binary configurations under all seven prime-order subgroups gives 801064 distinct masks,
  independently of the closed count formula and without inclusion-exclusion to obtain the union size.
- Rebuilt main and mobile PDFs, v8→v9 diff, and viewer data with installed pdfTeX 1.40.22 (TeX Live 2022), three
  passes each. Only line scopes changed in the 24 correspondence files. Updated viewer reconstruction: all 519
  highlights and 61122 glyph boxes match exactly; 26 pages. The same 24 stale verdicts remain.
- Updated artifacts: main .tex 21357f73e3032c94…; main .pdf a40911ee5d55ae95… (26 pp.);
  mobile .pdf 72083bbdd4dd0ef2… (54 pp.); v8→v9 diff .pdf ca21e232ce7517b6… (26 pp.);
  audit_data.json 745cc1aaa1a91503…; pdf_chars.json a1c54a189b9e88a5….
  Full hashes: `v9_release/updated_artifacts.json`. Remaining main-PDF warnings are the prior 0.70 pt overfull
  line, underfull lines and two hyperref bookmark warnings; no new main-PDF overfull warning remains.
- Prepared `v9_release/arxiv_source_v9_with_citations.zip`: only the main TeX and four figures. Clean-directory
  compilation reproduces the updated PDF word layout. arXiv's own TeX Live 2023/2025 preview was not run.
- Addendum (review of this run, same day): the public README's result-2 heading is now “Bounds: a lower bound
  attained exactly at the primes” (the qualification the paper gives after Theorem 6.1); CLAUDE.md and README.md
  give 26 pp.; the correspondence-audit README says “every page” instead of a page count. `export.py`: the
  v9_release arXiv zips, `internal_manifest.json` (it lists the unpublished follow-up files) and `workspace.json`
  (a home-directory path) are not exported; the exported REVIEW.md carries a note saying so, and the zip link in
  independent_review.md becomes plain text. The export now fails if any exported text file contains a home-directory path.
  Test export with v9_release counted as tracked: 474 files, no home paths, and the only differences from the
  public checkout `e7caee2` are the intended ones (paper, viewer data, records, README heading, v9_release).
  Citations rechecked: DOI resolves to LNCS 5778 pp. 310–317 (2011); JCA 10(1–2) 1–21 lists Banda, Caughman,
  Pospíchal; the thesis link serves the 167-page PDF, whose §6.1 is “Symmetric Configurations” (pp. 91–116).


## Run 033 — 2026-11-05 — leader-election citations revised; arXiv zips deleted

- Paper: the dissertation citation (`banda2014thesis`) and its bibliography entry are removed. Its 1-D content is
  covered by Banda–Caughman–Pospíchal (2015) and its 2-D content by Banda et al. (2019), both cited; the 2019 paper
  discusses 2-D leader election and the probability of symmetric inputs (checked against arXiv:1703.09030v2). The
  related-work paragraph now opens with the 2019 paper, followed by one sentence on the earlier 1-D work (Banda
  2011; Banda–Caughman–Pospíchal 2015). In the distributed-computing application, two dimensions now cite Banda et
  al. (2019). Bibliography: 30 entries, all cited, no undefined references. No numbered statement changed.
- Rebuilt: .tex 0e81b5cf1b627fd8… (1932 lines, −10); .pdf c31d4f4039ccffcb… (26 pp.; pdfTeX 1.40.22, ×3; warnings as
  before: the 0.70 pt overfull box in Lemma A.3, two hyperref string warnings); mobile .pdf 173972b00eba98de… (54 pp.;
  0 overfull); v8 → v9 diff .pdf 3974c11caf68da2e… (26 pp.; latexdiff 1.3.1a `--type=UNDERLINE` against
  `git show 8109cf1:shift_symmetry_d_dimensions.tex`, added text green, legend in the date line).
- Correspondence audit: remap_anchors.py 519 anchors, 397 unchanged, 122 line scopes renumbered, 0 moved, 0 reworded;
  `build.py --check` 0 errors, 1 warning (as before); full rebuild (Docker shiftsym-tex:jammy): layout identical,
  26 pages, 60 849 glyph boxes; audit_data.json 3bf8936e0c195720…, pdf_chars.json a294eb00dff112d5…. Verdicts:
  1 current (lem:mobius), 24 stale by line scopes only, as before; the audit log is unchanged.
- Deleted `v9_release/arxiv_source_v9.zip` and `arxiv_source_v9_with_citations.zip` (they predate the arXiv
  clean-up of the source; no zip is kept: the cleaned source and its four figures are uploaded to arXiv directly;
  `v9_release/.gitignore` ignores `*.zip`). Follow-up notes added to independent_review.md and
  v9_release/REVIEW.md. export.py 2bcf2b49d0a0d8c6…: the zip handling of the Run 032 addendum is removed again;
  overlay README 835e69654fbeaec4….

## Run 034 — 2026-11-06 — enumeration on every finite abelian group: checks for Section 4.5 (paper v10)

- Command: `python3 verify_abelian.py > verify_abelian_output.txt` (cwd: this directory; the script was written in the
  follow-up folder and moved here when the result became Section 4.5 of paper v10, unchanged)
- Environment: Python 3.10.12, numpy 2.0.2; exact integer arithmetic; deterministic; ~4 min
- Checks (Theorem 4.7, Corollary 4.8 and Remark 4.9 of paper v10; first stated as follow-up A1): [1] closed formula in the divisor coding
  (as frozen in Lean) = vector coding on 8440 (group, σ) pairs; Gaussian binomials by product formula = q-Pascal;
  [2] definition-level brute force = full-subgroup-lattice evaluator (Möbius function of the whole lattice by
  recursion, no Hall values) = formula on all 84 rectangular groups with $`n_i \ge 2`$, at most 4 factors and
  $`\sigma^N \le 2^{20}`$ (σ = 2…5); [3] lattice evaluator = formula on 1605 (group, σ) pairs up to $`N = 343`$;
  [4] square tori $`n \le 30`$, $`d \le 4`$, $`\sigma \le 3`$ = Theorem 4.4, reference values; [5] Corollary (c) on 7 pairs
  of groups (equal order and ranks ⇒ equal counts, e.g. $`\mathbb{Z}_2\times\mathbb{Z}_8`$ and $`\mathbb{Z}_4\times\mathbb{Z}_4`$: 736);
  [6] $`N \mid \sigma^N - \lvert S_G\rvert`$ for $`N \le 60`$, σ = 2…5; [7] Corollary (d), $`k`$-active counts, brute
  force = formula for every $`k`$ on 525 (group, σ, k) triples; [8] at fixed $`N \le 1024`$ (σ = 2, 3), $`\lvert S_G\rvert`$ strictly
  increasing in the rank profile on all 3858 comparable pairs (Corollary 4.8(ii)).
  Result: ALL PASSED, exit 0.
- sha256: verify_abelian.py 4b405972bd96137ec4666179f69919d74bc54bce1d0f065b807782db051f5723;
  verify_abelian_output.txt e344ba008d84a5c0fc6e48a82150c8724798963d19a9766bf0ae8140ff266542
- Addendum (same day): [9] the identity behind Corollary 4.8(ii) (monotonicity in the ranks; proof by the q-Pascal
  rule, found by a v10 reviewer): raising one $`p`$-rank at fixed $`N`$ adds exactly $`p^{d_p}\,\mathrm{ac}(G'')`$ — exact and
  positive on all 6069 single rank steps with $`N \le 2000`$, σ ∈ {2, 3, 5}. ALL PASSED, exit 0. sha256: verify_abelian.py
  ac3fc99d5847d039492ff1792ea76de5fef8181f50fb77f4f752360856f84d63; verify_abelian_output.txt
  794c8020842762402e54120495890e8e79882ad79c859f67223d38b6fb38eb8d
- Reviews of the statement and proof (fresh context, own code): proof referee PASS with repairs (two MAJOR
  findings in the novelty statement, seven MINOR; all applied); independent numerical reconstruction CONFIRMED
  (about 300 000 exact comparisons).
- Moved to this directory with its output when the result became Section 4.5 of paper v10; docstring and the
  labels of [8], [9] now name Corollary 4.8(ii); rerun from here: ALL PASSED, exit 0. sha256: verify_abelian.py
  7a888fdade81ce36abd23d3af11c9fa7810d607dfcabb9c737e27eef425338d2; verify_abelian_output.txt
  73ff7fb669c3bff202bf054027d0a06ae8725fb9347e26373a40487adf172d9f
- Addendum (v10 final review): [10] Remark 4.9(i) by an independent route — the $`k`$-active counts from the full subgroup
  lattice of each group (its Möbius function by recursion, weights $`\lvert \mathrm{Fix}_k(H)\rvert`$) = the formula, for every $`k`$: 15278 (group, sigma, k) triples, N <= 64 (and four larger groups): lattice = formula. ALL PASSED, exit 0.
  sha256: verify_abelian.py 378513d772c3677b0cb0913a3d0faa42d3ab04bd4870457f14fb21356f76a8c7; verify_abelian_output.txt 3652ad9cfe42aec72eeb089aa938df730b71cc87290395c873b13d693adf114d

## Run 035 — 2026-11-06 — read model and Fourier detection: checks for Remark 9.4 (paper v10)

- Command: `python3 verify_fft_detection.py > verify_fft_detection_output.txt` (cwd: this directory)
- Environment: Python 3.10.12, numpy 2.0.2; seeded (`default_rng([2026, 11, 6, 3])`); ~11 s
- Checks (the remark, first staged as FOLLOW_UPS A3, became Remark 9.4 "Read complexity" of paper v10, with the Fourier route in the paragraph after it): [1] the stabilizer from one FFT per
  symbol present ($`m_s(v) = N - \sum_a (I_a \star I_a)(v)`$, rounding error asserted < 0.25) = the stabilizer by definition on
  1044 configurations over 58 tori ($`d = 1`$–4), σ ∈ {2, 3, 5}, half of them with a planted symmetry; [2] a configuration
  that differs from a constant in one cell has trivial stabilizer: all 2696 cases with $`N \le 64`$, σ ≤ 3; [3] for every
  proper subset $`U`$ of the cells ($`N \le 12`$, σ = 2; 7091 pairs) the constant on $`U`$ has a symmetric and an aperiodic
  completion; [4] exhaustive minimax over all deterministic adaptive algorithms: the least worst-case number of reads
  is exactly $`N`$ on 12 tori up to $`N = 9`$ (σ = 2, 3). Result: ALL PASSED, exit 0.
- sha256: verify_fft_detection.py 89f7176ddfa22a13b1ed5d9ec48230980f3dc92d4bea8711ea00afa5d57e83a7;
  verify_fft_detection_output.txt bb362b92965ba1289c4d4e43ee65b9cd501cf5ea7274dee162e08f4e9b7d46a0
- Docstring updated to name Remark 9.4 (no internal paths); rerun: ALL PASSED, exit 0. sha256: verify_fft_detection.py
  a71be684a71c4f63db895fe7a2b4240bba881ecd55c22f8193404f12ed9024c3; verify_fft_detection_output.txt bb362b92965ba1289c4d4e43ee65b9cd501cf5ea7274dee162e08f4e9b7d46a0

## Run 036 — 2026-11-06 — paper v10: Section 4.5, Remark 9.4, related-work corrections; reviews, Lean, viewer data

- Reviews (fresh-context agents; verdicts and repairs in the frozen files' docstrings and below): v10 related-work wording
  (7 agents: three changes × source/math lenses + completeness critic; Adamson's Theorem 3 found wrong as printed, open
  problem (2) as first reworded found not open — both repaired); Remark 9.4 supplement, three fidelity rounds (round 1:
  readLower too weak, bound unfrozen; round 2: an unfrozen lexicographic clause, since removed from the text; round 3:
  PASS) plus text checks (the speed-up claim conditioned, "streaming" dropped, [cg2017] Lemma 10 found); Section 4.5:
  fidelity rounds 1 (strict increase, free action, N = ∏ n_i unfrozen; repaired) and 2 (literal, exploit, numeric: PASS),
  a hostile referee of the section (existence of G'', notation; repaired), a final review of the whole v9 → v10 diff
  (math PASS, attribution PASS; audit-status wording, provenance sentences, Delsarte priority, the footnote's witness,
  the k-active evaluator — all repaired; check [10] added to Run 034).
- Literature check (two agents, web): Miles–Ward PAMS 137 (2009) is the relevant paper (Möbius inversion over finite-index
  subgroups, μ unevaluated; no closed form); their ETDS 38 (2018) paper concerns Lind's natural-boundary conjecture (FOLLOW_UPS
  section E corrected). Delsarte 1948 not read (paywall); nine citing works agree it treats Möbius inversion over subgroups
  of finite abelian groups (subgroup and homomorphism counts), not configurations; Hall (1936) and Weisner (1935) precede it.
  No prior closed form of Theorem 4.7 in the p-ranks or of Corollary 4.8(ii) found; Oh (2012) has the general Möbius form.
- Lean: extension groups A1 and A3 (frozen and proved earlier the same day) moved into the paper layer and deleted from the
  extension layer: group 13 `Paper/S13_AbelianGroups.lean` (16 statements; 11 from A1, 5 new, frozen before their proofs)
  with proofs `Paper/Proofs/P13_AbelianGroups*.lean` (8 modules, incl. the q-Pascal step identity, a torus with prescribed
  ranks, cyclic minimality by induction), and the group-08 supplement `Paper/S08_Detection_Reads.lean` (7 statements; read
  model as adaptive decision trees) with `Paper/Proofs/P08_Detection_Reads.lean`. Gates: `lake build` green; AuditPaper
  370 frozen paper statements, 0 failures (group 08: 32, group 13: 16); AuditExt 401 statements, 389 proved, 12 listed;
  check_placeholders CLEAN; check_frozen OK (35 files); frozen_deps 781 frozen statements, 0 unrecorded; Audit.lean no
  unexpected axiom; kernel replay (full) modules=257, theorems 8860, definitions 2091, errors=0; kernel replay of the
  released module set (exported root's imports): 85 modules + root + Audit = 87, 3032 theorems, 808 definitions, errors=0
  (the counts in Section 11).
- Correspondence audit: anchors restored to their v9 state and remapped v9 → v10 (440 unchanged, 137 line scopes renumbered,
  0 moved, 0 reworded across the final remaps); correspondence data drafted for Theorem 4.7 (28 links) and Corollary 4.8
  (25 links) by a fresh-context agent (S13 info trees exported with ExportInfo.lean); one anchor moved past a comma after the
  layout check caught a kerning change; `build.py --check` 27 files, 529 links, 0 errors, 1 warning (as before); full build
  (Docker shiftsym-tex:jammy): layout identical, 28 pages, 67 434 glyph boxes. Verdicts: 1 current (lem:mobius), 24 stale
  (line scopes only), 2 not yet audited (thm:abelian, cor:abelian-ranks).
- Export test (with the new untracked files included): 491 files + overlay; the scripts of Runs 034, 035, 037, 038 and the new
  Lean modules are exported; Runs 034–038 are not marked follow-up work and are exported; no home path.
- Builds: .tex 99498311d54fb1f875c30c434613ea13daf10e18bfa8167b0a1be4b125417f27 (2119 lines); .pdf c482a9e248599b030f4100336c09cf294491aaa7d67cae8efdae95d3b90428e3 (28 pp.; warnings
  as before: the 0.70 pt box in Lemma A.3, two hyperref string warnings); mobile .pdf 682426570118942cacbc2c157d8fda1b75e17368104ad5378eb988d90dba245d
  (60 pp., 0 overfull); audit_data.json c4026dd4d6b79dce94cc13f83a7343b63ae109e7237f9f988a000d86b229f311; pdf_chars.json
  b883ce53121e7081e87056cd5ea93fa054dcda310f02e29cf4b49f0d4d7cc9e3; S08_Detection_Reads.lean 856a1c2c6c0e65572bd1235246923fcd6efb8ba5416cce1ed6a38d8dd1ca326b;
  S13_AbelianGroups.lean 19db85b86f9f0705dc29934ea6b0eed6afd288ff41d854595f3ec237c3768961; frozen_statements.sha256
  535abdfe45ff64a91b23a4d50325cdee363500eceb79e85a012d3f789fde7c53.

## Run 037 — 2026-11-06 — the atranslational-necklace recursion of Adamson et al. checked against exhaustive counts

- Command: `python3 check_adamson_thm3.py > check_adamson_thm3_output.txt` (cwd: this directory)
- Environment: Python 3.10.12, numpy 2.0.2; exact integer and Fraction arithmetic; ~6 min on one core
- Source checked: D. Adamson, A. Deligkas, V. V. Gusev, I. Potapov, "Combinatorial algorithms for multidimensional
  necklaces", arXiv:2108.01990v2, Theorems 1–3 (formulas read from the v2 TeX source and checked against the PDF).
- Checks: on every ordered grid with all sides $`\ge 2`$ and $`N \le 16`$ (42 grids) for σ = 2, 3 (84 pairs), definition-level
  brute force (stabilizer of every word) gives the numbers of necklaces, Lyndon words, atranslational words and
  atranslational necklaces; the latter also equal $`(\sigma^N - \lvert S_G\rvert)/N`$ with $`\lvert S_G\rvert`$ from Theorem 4.7 on every pair.
  Their Theorems 1 and 2 match on all 84 pairs. Their Theorem 3 (a recursion across dimensions for the
  atranslational necklaces) matches under none of the 720 readings of the printed formula (best 66/84); with the exact counts of
  the smaller grids inserted, the smallest grid that fails under every reading is $`2 \times 4`$ with σ = 2 (28 instead of
  27); evaluated recursively the literal reading gives 27 there but fails on $`2 \times 2`$ (3 instead of 2). The output lists minimal witnesses
  for five defect classes (the excluded case $`l = 1`$; the displayed $`H`$ against the text; an untwisted base on the
  quotient, e.g. $`\mathbb{Z}_4`$ against $`\mathbb{Z}_2^2`$ on $`2 \times 4`$; a Möbius factor $`-\mu(4) = 0`$ on $`4 \times 4`$; period boxes outside the
  ansatz for $`d \ge 3`$). Paper v10 cites the recursion as stated there and notes the discrepancy in a footnote.
  Result: exit 0. (Script written by a fresh-context checking agent and adopted here unchanged except for its
  name and two references to Theorem 4.7.)
- sha256: check_adamson_thm3.py e1d7a667d299eed1c1f3d3988d0a1c6cf7a97a41b8f24739ca48724cb3444765; check_adamson_thm3_output.txt b7ad4d78a7dfca0e933af1ca08b4b71c285b74316c2189060240544340b30865

## Run 038 — 2026-11-06 — erratum to the 2019 Chaos paper rewritten (review of 2026-11-06 applied)

- Command: `python3 verify_erratum.py --fig9 <arXiv:1703.09030v2 PDF, sha256 214bb551a7475a0ac73140f300dec1b4aa16f9b7cd48afc9765771e3227604f0> > verify_erratum_output.txt`
  (cwd: `research/2d_fix_note/`, named `research/fix_note/` until later the same day); standard library only, PyMuPDF
  1.27.2 for [F4]
- Environment: Python 3.10.12, Linux 6.8.0-138-generic x86_64, glibc 2.35; 407 s
- Checks: [A] Eq. (19) = brute force (n≤4) = explicit-subgroup inclusion–exclusion (n≤30); [B] failures of Eqs. (21)–(24) only at
  n=1 or σ=1 (n≤40, σ≤4); Eq. (28)/E.29 brute force; [C] brute force n=6 (σ=2: k≤6, k≥30; σ=3: k≥32): printed Eqs. (32)–(33)
  36 vs 48; corrected (30)–(33) = inclusion–exclusion for all 0≤k≤n², n∈{6,10,12,14,15,30}; [D] E.21 prime-power branch and
  strict base step, composite n≤400; [E] chain failure sets (n≤5000, all prime orders); first A.22 step false 462/462 (n=6:
  4278 < 4280); Lemma R1 168 cases (19 brute force); R2/R3/sandwich 1245 cases; A.21–A.24, E.21, E.22 statements; [F]
  P^unif/P^dens main-text values, Fig. 7, Fig. 9 curve (≤0.0001 decades). Result: 66 checks, ALL PASSED, exit 0.
- The note (2 pp., article class; REVTeX is not installed here) was rewritten by a fresh-context agent after a hostile referee
  and a Chaos/AIP format check (both 2026-11-06): Chaos erratum title, the four original authors, numbered corrections.
  Supersedes the PDF checksum of Run 004.
- sha256: verify_erratum.py 52f2b529cd7bbc1527ec039019af6934c3e889637985f892f675cdbf88686833; verify_erratum_output.txt f1383a8149a0d53a26b7111079322d1202a77b222dbedbd6fa57d8a410671160;
  banda2d_bounds_fix.tex 22b29244488750c69911eadd888dbdb58f4c287df1dd1323997b7bb33fe942c9; banda2d_bounds_fix.pdf a6b947f6724e3df9dd62c77abbaefc5bb17edb11c94adca0aa7d16babb504b72

## Run 039 — 2026-11-06 — Castillo-Ramirez novelty check; credits in paper v10; the two-prime example of Corollary 4.8(i)

- **Literature check** (one workflow, 39 agents):
  - publication list (53 papers); one deep reader per relevant paper (18); an adversarial verifier per claimed
    overlap; a synthesis.
  - Record: `research/paper_edits/CASTILLO_RAMIREZ_CHECK.md` (533b7a2b0a3636d06842879724a948abf1bc76f1471feded68d47dfe6200bfa6).
  - Result: every novelty claim holds — the multi-prime closed forms, the k-active counts, Theorem 6.1 for d ≥ 2,
    Theorem 6.3(ii), the inversion law, Corollary 4.8(ii), detection, the dynamical consequences, E1 and E2.
  - Under-credited prior work, re-checked in the arXiv texts of [cg2017] (1610.00532v2) and [cgvn2017]
    (1701.02692v3):
    - Theorem 6.1 at d = 1 (noted after their Lemma 7);
    - the union bound of Theorem 6.3(i), which is a step of their Thm 5(ii);
    - the limit of Proposition 10.1, which follows from their Thm 5(ii);
    - the converse of the stabilizer inclusion (their Lemma 10 for distinct orbits; [cgvn2017] Thm 2(iii));
    - Theorem 4.7 for abelian p-groups (their Lemma 7(iii));
    - the orbit count of Remark 4.9(ii) (their Lemma 4).
- **Paper edits:**
  - A fresh-context referee checked every edit against the primary texts: PASS_WITH_FIXES (converse credit to their
    Lemma 10, Lemma 4 = orbit count, sentence order, "noted after", house style, a credit at Proposition 10.1); all
    applied.
  - No sentence quoted by a frozen Lean statement changed. `CLAUDE.md` and `FOLLOW_UPS.md` (A7) no longer call
    N | σ^N − |S| new.
- **Corollary 4.8(i) example:** Z2 × Z8 and Z4 × Z4 (both 2-groups, hence covered by [cg2017] Lemma 7(iii)) replaced by
  Z2 × Z24 and Z4 × Z12: N = 48, d_2 = 2, d_3 = 1, non-isomorphic (largest element orders 24 and 12).
  - `verify_abelian.py` check [11]: three independent routes give 50 388 256 (σ = 2) and 847 330 573 761 (σ = 3) for both
    groups. The routes are (U), the definition as a union over v ≠ 0 of Fix(⟨v⟩) by inclusion–exclusion over the 15
    and 19 nontrivial cyclic subgroups, cosets counted on the group; (L), the full subgroup lattice (22 and 30
    subgroups); and (F), Theorem 4.7. The value by hand from Theorem 4.7 is 3·2^24 + 2^16 − 2·2^12 − 3·2^8 + 2·2^4.
    Exhaustive enumeration is out of reach (2^48 configurations).
  - The whole verifier reruns: ALL PASSED, exit 0. verify_abelian.py 8d2720e071e6e7529ebb0185c89e07ee058ce859b14e59302b807804550563ce;
    output 4f97b2a6ed533f5f6e841938d62b88e9f2aaca1476bbfe8648f5aa98143f439d.
- **Lean:** in `Paper/S13_AbelianGroups.lean`, `card736Statement` was replaced by `cardTwoPrimeStatement`, statement only,
  and the docstring line numbers were corrected.
  - Three fresh-context fidelity reviewers (literal, exploit, numeric — the last recounting both groups with its own
    code) gave PASS, PASS, PASS. A repair round changed docstrings only: Deltas on the shared order and ranks, and a note
    on the inline display.
  - The fingerprint was then recorded (S13 aa1bac1375e407f617ed590ecb5500a8a9e9a01e4749aa37b6d193b5a9f8b0e0,
    2026-11-06T21:23+01:00), before the proof was written.
  - Proof: `cardTwoPrime_proved` via `abelianRHS_48` and `coeffA_two_three`. The `card736_*` lemmas were removed.
    P13_AbelianGroups_Rect.lean c76f2632f334b82bd048a12879f1db7aac60a82b3d6421a97d06c178522414df;
    P13_AbelianGroups.lean 103d0f0a808b57bcd97f1f3560d89dae5be89154511dd9a9e4e0b079e85b0e39.
  - Gates: `lake build` green (8955 jobs); AuditPaper 369 frozen paper statements, 0 failures (group 13: 16);
    check_placeholders CLEAN; check_frozen OK (35 files); frozen_deps 780, 0 unrecorded; Audit.lean only the three
    standard axioms. frozen_statements.sha256 6139075f647c34a3c6aa93703e533658280223bf6d9df6461c3cf8110879a5a8.
  - STATEMENT_PRESERVATION: the group-13 row now has the two-prime example; proof lines 8 (2315); totals 10010 / 47 (16708).
- **Correspondence audit:** the four links of `cor_abelian-ranks.json` that used the old example now point to the new
  text and to `cardTwoPrimeStatement` (not yet audited by T. Lehman).
- Kernel replay of the released module set after the new proof: 85 modules + root + Audit = 87, 3037 theorems,
  807 definitions, errors=0. Section 11 now says "(3037 theorems and 807 definitions)". The theorem count includes
  constants the elaborator generates for the new proofs. Full replay: see the addendum below.
- Builds:
  - .tex 18f3639f82f3843c6f2eb24da55786a9996f90c6ef2ea8e331c31069a36147d4 (2137 lines);
  - .pdf e3f75917193e149b17f6282293c3158ce4155c750248f9e38d4a465de204c7fd (28 pp.; only the 0.70 pt box);
  - mobile .pdf 4169fce9ca34c7d725f1f088e2b739c32d5c4293ab314a444bd0206d1f232898 (60 pp.);
  - v9 → v10 diff ad47559be369bff579eaf2e51c9e5537dff71fc9cd35ebf59705cce8c8eeae83 (29 pp.; 84 additions, 77 deletions).
- Addendum: full kernel replay (`kernel_replay.lean`) after the new proof: modules=257, theorems 8865, definitions 2090,
  errors=0, exit 0.
- Correspondence audit, final rebuild for this text:
  - Lean info trees re-exported (ExportInfo.lean) for S13, P13_AbelianGroups, P13_AbelianGroups_Rect, S08_Detection_Reads
    and P08_Detection_Reads: 0 errors.
  - Anchors remapped from the tex of the last viewer build (99498311, Run 036) to this one: 437 unchanged, 137 line
    scopes renumbered, 0 moved, 0 reworded. The three links of the new example were checked against the new text only.
  - `build.py --check`: 27 files, 529 links, 0 errors, 1 warning (as before).
  - Full build (Docker): 28 pages, 67 216 glyph boxes, layout identical to the official PDF.
  - Verdict replay: 1 current (lem:mobius), 24 stale (line scopes only), 2 not yet audited (thm:abelian,
    cor:abelian-ranks).
- Export test, through a temporary git index with every untracked file except CA86.pdf, so the real index is untouched:
  495 files + overlay; the export's home-path guard passed.
  - Exported: the new Lean modules, `verify_abelian.py`, the new audit data.
  - Excluded: FOLLOW_UPS_STATUS.md, research/abelian/, research/paper_edits/, CA86.pdf.
  - A scan for "/tmp/claude" finds only a generic lock-file path in two v7 files (symbreak_fidelity), already
    exported in v7.

## Run 040

> *Public release:* Run 040 records follow-up work and is omitted. This repository contains the paper and its supplementary material only; see the README at the repository root.

## Run 041

> *Public release:* Run 041 records follow-up work and is omitted. This repository contains the paper and its supplementary material only; see the README at the repository root.

## Run 042

> *Public release:* Run 042 records follow-up work and is omitted. This repository contains the paper and its supplementary material only; see the README at the repository root.

## Run 043

> *Public release:* Run 043 records follow-up work and is omitted. This repository contains the paper and its supplementary material only; see the README at the repository root.

## Run 044

> *Public release:* Run 044 records follow-up work and is omitted. This repository contains the paper and its supplementary material only; see the README at the repository root.

## Run 045 — 2026-11-07 — paper v10: viewer link updated; correspondence audit completed for v10 (Theorem 4.7, Corollary 4.8); public export

- **Audit staleness (before):** `tools/auditlog.py report` on the v10 bundle (built 2026-11-06 at 72b60b4): 25 up,
  0 down, 2 not judged (Theorem 4.7, Corollary 4.8, new in v10), and 24 of the 25 verdicts flagged stale.
  - Cause: the item hash covers the correspondence block, which stores TeX line numbers (`scope.lines`); the v9 front
    matter moved them (e.g. L216 → L292). Compared with the bundles the verdicts were given against (baea4fa for 19
    items, 977f823 for prop:rank, thm:detect-worst, prop:inversion, lem:chain, lem:base), every one of the 24 has the
    same TeX, the same Lean declarations and source text, and the same correspondence apart from line numbers and
    positions; no Lean file that an item uses changed.
- **Carry-forward:** new `correspondence_audit/tools/carry_forward.py`
  (014eb41d8f89f74688c15af2ca2967e70ba4f2bb2eb15f8098ff840d910c6970). For each stale verdict it finds the committed
  bundle with the verdict's hash and re-issues the verdict under the current hash only if the item's TeX and Lean
  source are identical, the correspondence file is identical with `lines` removed, and every mapping carries a mark
  equal to the verdict. Dry run: 24 to carry, 0 left. Negative control: lem:fix at 977f823 vs now (a mapping change of
  v6 → v8) is rejected. Applied: session `carry-forward-2026-11-08T00-33-44.837Z` (25 events, tool
  `claude-code:carry-forward-positional`; each verdict keeps `carried_from_hash`, `carried_from_bundle`,
  `carried_from_t`).
- **Audit of the new items:** T. Lehman in the viewer, session `2026-11-08T00-38-49-655Z-0j9na` (239 events, 59
  mapping marks): Theorem 4.7 👍 (2026-11-08T01:03:40Z), Corollary 4.8 👍 (2026-11-08T01:12:01Z).
- **Viewer data rebuilt** after the PDF (`tools/build.py`): 27 correspondence files, 529 mappings, 0 errors; layout of
  the instrumented copy identical to the official PDF (all words at the same coordinates). All 27 item hashes unchanged
  by the rebuild. audit_data.json 9085864456143922918fc65a7d6f936383064344907ee74ab0c6ca3058f70102; pdf_chars.json
  1f27754ba62dad2133e7f86696ce5d85df24c4ab52ce848905f67588121a3409.
- **Audit (after):** report `logs/audit_report_20261108T011442Z.md`
  (ee2801b0523789b29b5e9e0c49beb0613fc22b418302ff728475f53512d8cc11; .json 01103915…6bd0): 27 up, 0 down, 0 not
  judged; no stale verdict; PDF, TeX and every Lean file match the fingerprints of the build; all 529 mappings marked ✓.
  events.jsonl a8a9a15d298d44549106ea7d87d10e3ab177a5f3f5b2d3782c1433d630b5f3d0 (3511 events).
- **Public export** (`research/public_release/export.py`, run with PyMuPDF via `uv run --with pymupdf`) into a fresh
  clone of github.com/peterbanda/d-dim-shift-symmetry (HEAD 1e7f5d1). Two scope fixes first, since Runs 040–044 were
  committed after the last export:
  - Runs 040–044 (follow-up work) now carry "(follow-up work)" in their headings, so the export omits them like
    Runs 010–017.
  - `frozen_sha` now also drops the comment block directly above an omitted file's fingerprint (it records the
    freezes of that omitted file); the header block stays. export.py 2589aff84cb2cc772723b8dc3c2f8ce77dbcc7491f7a62f83f661f78141b7248.

## Run 046 — 2026-11-08 — review of the v10 correspondence audit; "an F_p-vector space" frozen and proved (group-13 supplement); paper v11; v10 → v11 diff; public export

- **Review of the audit (099e022).** Checked independently (own scripts, not `carry_forward.py`):
  - the 24 carried verdicts: for each, the bundle it was given against (baea4fa for 19, 977f823 for 5) and the current
    bundle have identical item TeX, summary, deltas, Lean declaration sources and links, apart from positions (PDF
    rectangles, TeX offsets and line numbers); every original verdict came from T. Lehman's browser sessions (viewer
    verdict after all links marked ✓); no Lean statement or definition file that existed at those bundles has changed
    (only new files were added; toolchain and mathlib pins unchanged); no definition, statement environment or the
    Model/Preliminaries text changed since baea4fa, and the changes since 977f823 (v8, J. Caughman) are wording only;
  - the log: 099e022 appended 264 lines and removed none;
  - the new items: Theorem 4.7 (28/28 links) and Corollary 4.8 (25/25) judged by T. Lehman in the viewer;
  - the `frozen_sha` change of export.py: on the current fingerprint file it drops exactly the 64 lines of the omitted
    extension files and their comment blocks and keeps the header and every paper-group comment.
  - Findings, all addressed below: Section 12 said "No link is of the kind 'weaker'", false since Theorem 4.7's link `Fp`
    ("an $`\mathbb{F}_p`$-vector space") is of that kind; the counts (476 links, 25 items) and "await the same audit" /
    "pending" were stale (Section 12, Figure 5 and its caption, Section 11, the abstract comment); two Run 030 sentences
    had been rewritten to "functorial.inc … answers 301 to functorial.inc", and Run 045 says those records were "left as
    written" (they were edited, as was `main_paper_audit/v9_release/paper_text.txt`); Run 045's affiliation addendum
    named the two follow-up drafts in a part of the run log that is exported.
- **Group-13 supplement** `Paper/S13_AbelianGroups_Torsion.lean` (namespace `ShiftSym.P13`): `pTorsion G p` (the
  subgroup `{g | p • g = 0}`) and `pTorsionVectorSpaceStatement`: for prime `p`, `G[p]` carries a `ZMod p`-module
  structure with the natural action `c • g = c.val • g`, and `Module.finrank (ZMod p) (pTorsion G p) = pRank G p` (the
  paper's "an $`\mathbb{F}_p`$-vector space, and let $`d_p=\dim_{\mathbb{F}_p}G[p]`$", L662–663 of ce43fba2…). Frozen before
  any proof, fingerprint 88f75c873b54b4a393c4372555742371901a1696ece1318049228039aeb35aa1.
  - Three fresh-context fidelity reviews (workflow, literal / exploit / numeric): PASS, PASS, PASS. The bound instance is
    the one the body uses (pp.explicit); the structure is unique (also without the action clause,
    `ZMod.instSubsingletonModule`); the numeric reviewer checked 930 groups (all products of cyclic groups with N ≤ 200
    and 25 larger ones; 2006 pairs (G, p) with p ∣ N, 11 881 with p ∤ N), against the exponent definition of `pRank`,
    the paper's $`d_p = |\{i : p \mid n_i\}|`$, a greedy basis and Gaussian elimination. MINOR items (AuditPaper import,
    preservation-table row, audit retarget) done; COSMETIC docstring items applied before the proof, comments only
    (comment-stripped text identical, 6c1c79f1…): fingerprint 7b575efa1854caca0ac7a1f224a728c6a163da16f923ae04aa348d5f26dd0028.
    Scratch `…/scratchpad/s13tors/review_{literal,exploit,numeric}/`.
  - Proof `Paper/Proofs/P13_AbelianGroups_Torsion.lean` (b8832b19…, 37 lines): `AddCommGroup.zmodModule` (the action
    clause by `rfl` after `p = n + 1`), then `Module.card_eq_pow_finrank` and the proved `pRankPowStatement`. Imported by
    `Shiftsym.lean` and `AuditPaper.lean` (docstring lists the supplement; 6719a325…).
  - Gates: `lake build` green (8975 jobs; log 783b9a69…): "group 13: 17 frozen statements, 0 failures", "370 frozen paper
    statements checked", "509 frozen extension statements, 482 proved, 27 stated-not-proved (listed)"; `Audit.lean`
    46 × [propext, Classical.choice, Quot.sound], 6 × [propext, Quot.sound]; `check_frozen.py` OK (38 files);
    placeholders CLEAN; `frozen_deps.lean` "889 frozen statements, 2334 constants visited, 36 Shiftsym modules in the
    closure, 0 unrecorded". Full kernel replay (20 GB cap): "modules=277 theorems ok=9663 defs ok=2282 errors=0", no
    axiom, 42 min 11 s, peak RSS 18 344 452 kB (log df168e48…). Released module set (the exported root's imports,
    `ReplayExport.lean` 7a0d7706…, as in Runs 036/039): "modules=87 theorems ok=3042 defs ok=809 errors=0", 39 s
    (log 9ced4120…); with root and Audit, 89 modules (the Section 11 figures).
  - frozen_statements.sha256: two dated entries (the record and the docstring-only re-record); cfa97387….
- **Paper v11** (date line "revised draft (v11, …)"; the version-history comment has a v11 entry): Section 12 — 529
  links for the 27 items, all 27 approved; each verdict was given against the version current at the time, those on
  Theorem 4.7 and Corollary 4.8 (added in v10) against v10 or later; a script carries a verdict over only where the
  item's TeX, the Lean source of its declarations and its links are unchanged apart from line numbers ("No link is of
  the kind 'weaker'" is true again). Figure 5: 370 statements, build audit 370/370, 27 items, 529 links; caption:
  "pending" removed. Section 11: 370 statements, 67 modules, Section 4.5: 17, "pending" removed, the replay of the
  released set (89 modules, 3042 theorems, 809 definitions). Abstract comment: the remaining release check (T. Lehman
  re-checks the changed links of Theorem 4.7). TeX 11178cbb8b42a73292f98c40d5327b4ff0666b506313240e25457b0f3c2ff2b7
  (2139 lines); PDF (Docker `shiftsym-tex:jammy`, pdflatex ×3; 28 pp., 0 errors, no undefined references, only the
  known 0.70 pt box) eb406edc3fa24d986a8e4bcfbc05d6660dc4469539054938427e4fa1154a9218 (intermediate; the committed
  paper is the one of Run 047).
- **v10 → v11 diff** `shift_symmetry_d_dimensions_v11_diff.pdf` d1075ddeeb318f0808b66bb7b0323d78d40c9ff081771f901a54fe9c9909556b
  (28 pp.; latexdiff 1.3.1a `--type=UNDERLINE` against `git show 099e022:shift_symmetry_d_dimensions.tex`, i.e. v10 with
  T. Lehman's two lines of 2026-11-07 (affiliation, viewer link), which are therefore not marked; added text green, legend
  in the date line; 12 additions and 14 deletions marked by latexdiff, and the three changed node texts of Figure 5
  marked by hand in the diff source, since latexdiff does not mark inside a TikZ picture; local pdflatex, 0 errors).
  The v9 → v10 copy is unchanged (as committed). Intermediate; the committed v10 → v11 copy is the one of Run 047.
- **Correspondence audit.** `data/corr/thm_abelian.json` (73a444a5…): `Fp` "weaker" → "same", anchored to the new
  statement; `dp` anchored to its finrank clause; `Gp` also to `pTorsion`; the two declarations added to the item's
  declaration list; summary and the p-rank delta updated. `tools/remap_anchors.py` (HEAD → current TeX): 561 anchors
  unchanged, 16 line scopes renumbered, 0 moved, 0 reworded. Lean info exported for the two new files (0 errors).
  `tools/build.py`: 27 correspondence files, 529 mappings, 0 errors; layout of the instrumented copy identical to the
  official PDF (final bundle: Run 047).
  - Carry-forward and the final report: see Run 047. (A carry-forward session of 19:14 UTC and two reports made
    during this run were on intermediate, uncommitted bundles; they were dropped before the commit, and Run 047
    carries the verdicts from the committed bundle 099e022 to the final one in a single session.)
  - **Open (T. Lehman):** re-check Theorem 4.7's links `Gp`, `Fp`, `dp` in the viewer and set its verdict again.
  - `correspondence_audit/README.md`: 27 items; the log history now records both carry-forward sessions and that five
    verdicts were stale at v8 only by line numbers.
- **Records.** Run 030: the two rewritten sentences now give the current link and the 2026-11-04 fact (conformal.inc
  answered 301 to functorial.inc); `v9_release/paper_text.txt` is left as 099e022 has it (the link is functorial.inc
  now; nothing references the file by hash). Run 045: its affiliation addendum regrouped so that the follow-up drafts
  are a "(follow-up work)" bullet; `export.py` (f6fd645b…) now drops such bullets inside exported runs. Also updated:
  STATEMENT_PRESERVATION.md (13-supplement row; totals 370, 48 proof modules), CLAUDE.md (370; module guide), the
  public README overlay (370).
- **Public export** (`uv run --no-project --with pymupdf python3 research/public_release/export.py ../d-dim-shift-symmetry`):
  514 files + overlay; follow-up runs appear only as omission notes; the only follow-up names in the exported run log
  are the exclusion list of Run 030, as before. Not committed in the public checkout.

## Run 047 — 2026-11-08 — paper v11: Corollary 4.8 and Remark 4.9 moved to a new Appendix B; final audit bundle; v10 → v11 diff

- **Paper** (`shift_symmetry_d_dimensions.tex`, still v11):
  - Corollary 4.8 with its proof and Remark 4.9 moved byte for byte (49 lines; same sha256 before and after) to the new
    Appendix B "Finite abelian groups: dependence on the ranks" (`app:abelian`, after Appendix A, opening "Notation is as
    in Section 4.5."): now Corollary B.1 and Remark B.2 (labels unchanged). Only these three labels change number
    (`.aux` comparison).
  - Connecting sentences: after Theorem 4.7 (for σ ≥ 2, the count depends only on N and the p-ranks and strictly
    increases with each p-rank, so the ring Z_N carries no more shift-symmetric configurations than any torus with N
    cells; Lean `onlyRanksStatement`, `stepStrictStatement`, `cyclicMinStatement`, `kActiveStatement`,
    `orbitCountStatement`); in open problem (2) ("For a fixed order alone, the minimum is attained by the cyclic group",
    `cyclicMinStatement`); in the conclusion ("The p-torsion carries all of this: …"; S02 `completenessStatement`, S08
    `completenessIffStatement` and the detector's `algorithmSpecStatement`, `scheduleCountStatement`,
    `detectCorrectStatement`, S07 `rankMonoStatement`, `rankTrajStatement`, and `onlyRanksStatement`).
  - Fresh-context review of the restructuring (workflow): PASS — the move verbatim, no reference broken (no undefined or
    multiply defined labels), every clause of the three sentences implied by a numbered result and covered by a frozen
    statement. One MINOR item (the bridge sentence relied on the standing σ ≥ 2 and said "grows"; now "for σ ≥ 2 … strictly
    increases") and four COSMETIC wording items applied, each with an unchanged line count. Scratch
    `…/scratchpad/s13tors/review_opt2/`.
  - TeX 051879945717a5d56f93c5107204c57184ff45df56390901ddcffc370e8fd1b1 (2156 lines); PDF (Docker `shiftsym-tex:jammy`,
    pdflatex ×3; 28 pp., 0 errors, no undefined references, only the known 0.70 pt box)
    ec0922254f551d7989e3f3a4fb82f6217b7fd1d4bfe70cacb72735bd6d003346.
- **Lean:** no frozen file changes (frozen docstrings keep the v10 numbers; concordance v10 → v11 added to
  `research/formal/STATEMENT_PRESERVATION.md`).
- **Correspondence audit:**
  - `tools/remap_anchors.py` (pre-move → final TeX): 530 anchors unchanged, 47 line scopes renumbered, 0 moved, 0 reworded.
    Theorem 4.7's correspondence: one note now names Corollary B.1 (the item is stale anyway). Corollary B.1's
    correspondence is unchanged, so its item hash is unchanged and its verdict stays current.
  - `tools/build.py`: 27 correspondence files, 529 mappings, 0 errors; layout identical to the official PDF;
    audit_data.json da04503102847c280ad18809291db93f5228c6538cd35985bc7578ea829d91c7, pdf_chars.json
    d6b956465a7e1992c9a6a2f3033247ae59ff0be42212e8ba5a862fdee5050c54 (after the "Appendices" heading; no item hash
    changed, carry-forward dry run 0).
  - The carry-forward session of Run 046 (19:14 UTC, 5 events) had been issued on an intermediate bundle that was never
    committed; the tool looks verdicts up in committed bundles only. Those 5 uncommitted lines were dropped (the log is
    then byte-identical to commit 099e022, 3511 events), and `tools/carry_forward.py --apply` ran once from 099e022 to the
    final bundle: session `carry-forward-2026-11-08T22-36-22.311Z` (13 events) re-issued 12 verdicts (Theorems 5.1, 6.1,
    Corollaries 7.1, 7.2, Theorem 9.1, Propositions 9.2, 10.1, 10.2, Lemmas A.1–A.4), each checked independently against
    the 099e022 bundle (item TeX, summary, deltas, Lean declaration sources and links identical apart from positions).
    Theorem 4.7 left stale. After the final wording fixes: carry-forward dry run 0, the same stale item.
  - Report `logs/audit_report_20261109T080402Z.md` (2de8812a…; .json be0ce022…): 27 up, 0 down, 0 not judged; stale:
    thm:abelian; sources match the build fingerprints. events.jsonl 63cbbaf0f30e402d0484e2cf8b0aa187e18ece5c7dcf75d3c9f894b86a6bd59a
    (3524 events). Intermediate reports of this run and of Run 046 were removed before the commit.
  - **Open (T. Lehman):** re-check Theorem 4.7's links `Gp`, `Fp`, `dp` and set its verdict again.
- **v10 → v11 diff** `shift_symmetry_d_dimensions_v11_diff.pdf` 436f33d5ef1bb8235581efeef434ffae079daecddf6638aed4b6ce6a0807ceb1
  (28 pp.; latexdiff 1.3.1a `--type=UNDERLINE`). Base: commit 099e022 (v10 with T. Lehman's two lines of 2026-11-07, which
  are therefore not marked), with Corollary 4.8 and Remark 4.9 relocated to Appendix B in the base copy, so the moved
  text is unmarked and two blue notes say where it moved from and to; added text green, legend in the date line; the
  three changed node texts of Figure 5 marked by hand (latexdiff does not mark inside a TikZ picture); 20 additions and
  18 deletions marked; local pdflatex, 0 errors.
- **Records:** STATEMENT_PRESERVATION.md (concordance v10 → v11 with the mapping of the three sentences; group-13 row);
  CLAUDE.md (v11 description, research/abelian pointers); FOLLOW_UPS_STATUS.md (item 1; release blockers for v11);
  research/abelian README and THEOREMS (A1.7); correspondence_audit/README.md (carry-forward history).

## Run 048 — 2026-11-09 — independent review of v10 and v11; V11-2 and V11-3 applied

- **Review received** (`research/formal/main_paper_audit/independent_review.md`, entry of 2026-11-09, and
  `main_paper_audit/v10_v11_review/`: REVIEW.md with its scripts, manifests and logs). It covers v9 `72b60b4`, v10
  `099e022`, v11 `dde222d` and the public checkout `6424a78`. Finding: no new mathematical error and no paper–Lean
  statement mismatch. Fresh verification by the reviewer: 89 public modules compiled from an empty object directory,
  paper audit 370/370, kernel replay 89 modules / 3042 theorems / 809 definitions / 0 errors; the public export
  rebuilt (519 files identical); all 189 viewer fingerprints, 27 item hashes, 529 mappings and 36 positional
  carry-forward events reconstructed or traced; an independent subgroup-poset evaluator and enumeration on 258
  group/alphabet cases; the 28-page layout reproduced from the TeX alone.
- **V11-1** (Theorem 4.7's stale verdict): open, T. Lehman's re-check.
- **V11-2** (viewer delta): `data/corr/thm_abelian.json` (6f25eff0…) — the "Not frozen" delta no longer lists "an
  F_p-vector space"; it names the group-13 supplement instead.
- **V11-3** (Miles–Ward wording): checked against the source first (arXiv:0706.3630v2, Lemma 2, p. 4, which bounds the
  Möbius value via Kratzer–Thévenaz: zero unless the quotient is a product of elementary abelian groups, else at most
  ∏ p_i^{n_i(n_i−1)/2}); the related-work sentence (L250–251) now ends "without reducing them to the explicit
  rank-indexed formula used here". Same source lines, so no anchor moved and no item hash changed.
- Paper (v11): TeX 4fa670ab187426f5ad7f78f9efe4d0e4b0bf5e3b086274a1a151ded92a4e7071; PDF (Docker `shiftsym-tex:jammy`,
  pdflatex ×3; 28 pp., 0 errors, no undefined references, only the known 0.70 pt box)
  0562c670f488d6cb543c3d45aff1ee29c15befd5917cf2dc9a161dec9c9a009c.
- Audit: `tools/build.py` 27 files, 529 mappings, 0 errors, layout identical; audit_data.json
  a662f88b09afedb5113acb44da094ff8bad74f8b0da8424e74909a7e029c1542, pdf_chars.json
  2c2da6cdfb7b77bda2a2619e5c16b31362b23242f99002c283c92fbf435ca74d; carry-forward dry run 0; report
  `logs/audit_report_20261109T085105Z.md` (c7788eda…; .json ab4e80bd…): 27 up, 0 down, 0 not judged; stale: thm:abelian.
- v10 → v11 diff regenerated as in Run 047 (now also marking the Miles–Ward wording):
  841224d178f998bf69df01b52f2f228a39fd2206fbaf29fb349358be6e468c73 (28 pp.).
- `research/public_release/export.py`: `v10_v11_review/workspace.json` (temporary build locations) is not exported, and
  the exported REVIEW.md says so, as for `v9_release/`. The review's `.log` files are committed with `git add -f`
  (the `*.log` rule of .gitignore), as for `v9_release/`.
- Response appended to `independent_review.md`.

## Run 049 — 2026-11-10 — audit of the clean release repository d-dim-shift-symmetry-in-ca; release fixes

- Audited `github.com/peterbanda/d-dim-shift-symmetry-in-ca` (single commit fcb0613, 657 files) against internal d58c4f3:
  byte-identical to a fresh export except 11 `release_lean_split/` evidence files (compile logs with local paths, build
  trees) that had been left out by hand; no home paths, follow-up material or CA86.pdf. Its Lean tree built from scratch
  (only the pinned mathlib reused; from-scratch parallel builds need more than 10 GB): 89 modules, paper audit 370/370
  (group 13: 17), frozen_deps 373 statements / 0 unrecorded, kernel replay modules=89 theorems 3036 defs 804 errors=0, no
  axiom or sorry; check_frozen and placeholders pass. Audit: 27/27 approved and current; T. Lehman's re-check of
  Theorem 4.7 (session 2026-11-10T00-28-31-841Z, links Gp, Fp, dp marked) in c73bb7b. Paper rebuilds to the committed text.
- Fixes: the erratum's repository link now names d-dim-shift-symmetry-in-ca (PDF rebuilt, 2 pp.); export.py excludes the
  11 `release_lean_split/` files, so the release is reproducible from HEAD; the release-check comment under the abstract
  removed (two comment lines blanked, no line moved); CLAUDE.md points to the new repository and checkout.
- Docker image `shiftsym-tex:jammy` had disappeared from this machine; rebuilt from the recipe in
  `correspondence_audit/README.md` (image 3fe202ca1060, pdfTeX 1.40.22); `tools/build.py` with it: 27 files, 529 mappings,
  0 errors, layout identical to the official PDF; carry-forward 0, nothing stale; report audit_report_20261110T155655Z.md (efb7e9dc…).
- Addendum (2026-11-11): arXiv readiness — `\pdfoutput=1` (line 2) and PDF title/author metadata (hyperref line); the release build also blanks the version-history and venue comments of the source; a minimal arXiv-style build (main TeX + 4 figures, 616 KB) reproduces the 28-page word layout. Internal diff since v11: `shift_symmetry_d_dimensions_post_v11_diff.pdf` (latexdiff against dde222d).
- Addendum (2026-11-11): contact email of P. Banda (peter.banda@protonmail.com) as a footnote on the author line (`\thanks`, same wording as the erratum; the only email in the paper); same line count, only page 1 changes (pages 2–28 text-identical), 0 errors, 28 pp.; viewer data rebuilt (layout identical), audit 27/27 current; post-v11 diff regenerated with the footnote marked by hand.
- Addendum (2026-11-11): AI-use statement — an unnumbered Acknowledgments section before the references, one sentence ("AI assistants, including but not limited to Claude (Anthropic) and Codex (OpenAI), were used in developing and reviewing the proofs, the Lean formalization, and the verification scripts, and in editing the text; the authors take full responsibility for the content."); 3 lines added after every audited item (line 1940), 28 pp., 0 errors; viewer data rebuilt (layout identical), audit 27/27 current; post-v11 diff regenerated (29 pp.); arxiv_submission/ refreshed. Then moved before the appendices (after the open problems of Section 13): remap_anchors 561 OK / 16 REMAP (Appendix A line scopes), carry_forward re-issued 4 verdicts (lem:dtorus, lem:chain, lem:base, lem:coef; nothing left stale), 28 pp., 0 errors, layout identical, audit 27/27 current.
