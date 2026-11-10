# Main-paper mathematical and formalization audit

| | Timestamp | By |
|---|---|---|
| Review | 2026-10-16 18:21 +0200 | independent reviewer (the text below, unchanged up to the Response section) |
| Response | 2026-10-18 13:38 +0200 | authors ([Response](#response-2026-10-18)) |
| Verification of the response | 2026-10-19 09:42 +0200 | independent reviewer ([Verification](#independent-verification-of-the-response-2026-10-19)) |
| Reply to the verification | 2026-10-19 10:22 +0200 | authors ([Reply](#reply-to-the-verification-2026-10-19)) |
| Verification of PR #1 (window 20) | 2026-10-23 | independent reviewer ([PR #1](#independent-verification-of-tobis-merged-pr-1-2026-10-23)) |
| Addendum on finding 2 | 2026-10-27 | authors ([Addendum](#addendum-on-finding-2-2026-10-27)) |
| Independent review of v8 and today's commits | 2026-11-02 | independent reviewer ([v8 review](#independent-review-of-v8-and-the-commits-of-2026-11-02)) |
| Response to the v8 review | 2026-11-02 22:11 +0100 | authors ([Response](#response-to-the-v8-review-2026-11-02)) |

Audit date: 2026-10-16. Repository HEAD: `20d93bade666a6ec3d55743032df11e4d19ba532`.

**Verdict.** I found no material weakening of the principal enumeration, lower-bound, active-cell, symmetry-preservation, or detection theorems in their Lean statements. Their definitions describe the intended mathematical objects, and the formal conclusions have the required scope. The mathematical core looks solid. However, a successful build does not justify an unqualified claim that every mathematical assertion in the manuscript has been formalized. There is an actual unformalized necklace identification, an overbroad application sentence, an ambiguity in the dimension quantifiers, a misleading complexity summary, a false embedded figure annotation, and inaccurate plot-arithmetic descriptions.

These findings have different consequences. None supplies a counterexample to the principal counting theorems. Several do supply counterexamples to natural readings of the surrounding prose. The report separates those from the theorems that actually passed scrutiny.

**Scope and method.** I examined the main manuscript `shift_symmetry_d_dimensions.tex`, its included figures, the core Lean definitions/statements, all eleven paper statement groups, the audit machinery, and relevant proof implementations and representation bridges. Follow-up papers are excluded. Companion results imported by main-paper proofs were considered as dependencies, not as an audit of those follow-ups. I checked particularly for changed quantifiers, assumptions hidden in definitions, vacuous premises, cardinalities defined by the desired answer, truncated natural-number arithmetic, missing equivalences, substituted probability models, and costs disconnected from the implemented detector. This was a semantic review of the statements and supporting constructions, not a line-by-line manual reproof of every Lean proof term or a comprehensive novelty review.

## Findings requiring correction or explicit qualification

### 1. The necklace interpretation is not certified by the word-count theorems

**Classification: concrete coverage gap; the mathematics is correct.**

The manuscript identifies the number of primitive words as $`n`$ times the number of primitive necklaces in [Remark 4.5](/shift_symmetry_d_dimensions.tex#L462). Lean proves the Möbius complement formula for actual words: see [the word-count statements](/research/formal/shiftsym/Shiftsym/Paper/S04_EnumerationCorollaries.lean#L373), especially `remark45d1CountStatement` and `classicalNonprimitiveCountStatement` at lines 396 and 435. Those are meaningful counting theorems, not merely identities between two formulas.

But the development has no corresponding primitive-necklace quotient and no theorem identifying its cardinality with the word count divided by $`n`$. The missing step is that the rotation action on primitive words is free, so every orbit has exactly $`n`$ words. The existing word-period bridge does not itself establish a necklace-count statement.

The [earlier correction proposal](/research/formal/PAPER_CORRECTIONS_PROPOSAL.md#L145) explicitly acknowledges this and treats it as a bibliographic exception. The manuscript's [formalization scope](/shift_symmetry_d_dimensions.tex#L1123) excludes “bibliographic” sentences generally. That may explain the author's intention, but the factor-$`n`$ identification is mathematical content, not merely an attribution. A reader expecting every precise assertion to have a Lean counterpart will not find one here.

**Correction:** either add the rotation quotient and free-orbit cardinality theorem, or explicitly state that the classical necklace identification is outside the formalization. The existing nonprimitive-word theorem needs no repair.

### 2. The insolvability application needs a defined task, especially for image translation

**Classification: overbroad prose; the conditional theorem and leader-election instance are sound.**

[Corollary 8.2](/shift_symmetry_d_dimensions.tex#L789) correctly rules out a task if some admissible symmetric input requires an asymmetric output. It then says this covers pattern recognition and image translation. Neither task is defined sufficiently to establish that premise.

Lean accurately formalizes `Task`, `Solves`, and `RequiresLeavingS`, and proves the conditional result in [S07](/research/formal/shiftsym/Shiftsym/Paper/S07_Dynamics.lean#L261). Leader election has a separate definition and proof. However, [the documentation for `insolvStatement`](/research/formal/shiftsym/Shiftsym/Paper/S07_Dynamics.lean#L491) explicitly excludes the two other task names as undefined informal language. Thus those applications are not consequences established by the formalized conjunction.

A literal translation task is a counterexample to the broad reading. Fix an offset $`w`$, require output $`s(\cdot+w)`$, and use the one-offset local rule that copies that cell. This map is equivariant and solves the task in one step for every input, symmetric inputs included. The new [Lean probe](/research/formal/main_paper_audit/semantic_probes.lean#L16) proves this using the production `Task`, `Solves`, `caMap`, and `Equivariant` definitions.

The cited [2019 paper, Figure 5](https://arxiv.org/pdf/1703.09030) concerns particular image-processing transformations between illustrated input and output configurations. Referring to that discussion does not make arbitrary image translation impossible.

**Correction:** state that the corollary covers those pattern-recognition or image-processing tasks whose admissible input/output relation requires symmetry breaking. Define any particular intended application. Keep the separately proved leader-election example.

### 3. The smooth-factor polylogarithmic claim fixes dimension; the text should say so

**Classification: important quantifier ambiguity, not a failed fixed-dimension theorem.**

The [detection section](/shift_symmetry_d_dimensions.tex#L833) says $`d`$ is part of the input. [Remark 9.3](/shift_symmetry_d_dimensions.tex#L896) then says that in every dimension the bound is polylogarithmic when all prime factors are polylogarithmically small.

The actual quantifiers in [remPolylogSmoothStatement](/research/formal/shiftsym/Shiftsym/Paper/S08_Detection.lean#L589) are

```math
\forall d\ge1\;\forall c\;\exists C,k\;\forall n:\quad
  \bigl[\forall p\mid n,\ p\le(\log n)^c\bigr]
  \Longrightarrow \sum_{p\mid n}p^d\le C(\log(n^d))^k.
```

The exponent may depend on $`d`$; the proof uses $`k=cd+1`$. This is a correct statement for each fixed dimension. It is not a uniform polylogarithmic bound when dimension grows as part of the input.

For an explicit obstruction, set $`n=2^t`$, $`d=t`$, $`t\ge3`$. The only prime factor is $`2\le\log n`$, yet

```math
N=2^{t^2},\qquad \sum_{p\mid n}p^d=2^t.
```

No constants $`C,k`$ independent of $`t`$ bound $`2^t`$ by $`C(t^2\log2)^k`$. Thus the variable-dimension interpretation is false even on this very smooth family.

**Correction:** add “for each fixed dimension $`d`$” and disclose dependence of the polynomial degree on $`d`$. The natural-density statement should likewise be presented with $`d`$ fixed. No change to the existing fixed-dimension Lean theorem is needed.

### 4. The conclusion table blurs an upper bound with the actual detector cost

**Classification: misleading complexity summary; the average-read theorem is sound.**

The [conclusion table](/shift_symmetry_d_dimensions.tex#L1278) puts “polylog only on a set of $`n`$ of density 0” in the detection average-case row. Section 9 more carefully says **this bound**, namely $`B(n,d)=\sum_{p\mid n}p^d`$, is non-polylogarithmic for almost all $`n`$. A loose upper bound being large cannot prove that the actual expected read count is large. The Lean density-zero result concerns $`B`$, not a matching lower bound on early-stop reads.

There is a strong counterexample to reading the table as a claim about actual cost. In dimension one there is one order-$`p`$ subgroup for each prime divisor. With first-mismatch stopping and alphabet size $`\sigma\ge2`$, the expected reads in a single $`p`$-cell orbit are

```math
1+\sum_{j=0}^{p-2}\sigma^{-j}\le3.
```

Each orbit passes with probability $`Q=\sigma^{1-p}\le1/2`$, so a standalone subgroup test visits at most two orbits in expectation. Independence of distinct orbit contents therefore bounds expected reads by $`6`$ per subgroup. Summing standalone costs bounds the full detector, giving at most $`6\omega(n)\le6\log_2 n`$ for **every** $`n\ge2`$ in dimension one. No independence between different subgroup tests is required.

For binary input and prime $`n=p`$, the single orbit is the entire lattice. The exact expectation is $`3-2^{2-p} < 3`$, whereas $`B(p,1)=p`$. The independent checker enumerated this expectation for primes through 13. The existing [Lean statement documentation](/research/formal/shiftsym/Shiftsym/Paper/S08_Detection.lean#L538) already recognizes the early-stopping distinction.

**Correction:** write “the displayed upper bound is polylogarithmic only on a density-zero set, for fixed $`d`$; early stopping can have smaller actual cost.” The summary table is expressly excluded from the formalization, but remains part of the mathematical exposition.

### 5. Figure 1 still contains a false all-primes title

**Classification: definite presentation error, contradicting the corrected caption and Lean.**

The embedded [chart14 image](/charts/chart14_pattern_flip.png) says that primes are local dips in dimension two, “audited: holds for all $`n \le 40`$.” The title is generated at [compute_dimension_insights.py:140](/compute_dimension_insights.py#L140).

The $`n=3`$ exception is real:

```math
P_{3^2}=26/512=0.05078125,
\qquad P_{4^2}=736/65536=0.01123046875.
```

Thus $`n=3`$ is not a strict local minimum. The manuscript's [observation](/shift_symmetry_d_dimensions.tex#L724) and [caption](/shift_symmetry_d_dimensions.tex#L759) have been corrected; `captionDipsD2Statement` correctly assumes prime $`p\ge5`$, and `extremaBoundaryStatement` records the exception. The image title has escaped those corrections.

**Correction:** regenerate the image with a title explicitly limited to primes $`5\le p\le40`$, and mention the $`p=3`$ exception. Certifying a caption does not certify text embedded in a PNG.

### 6. The plots are not evaluated entirely with exact arithmetic

**Classification: reproducibility/provenance error; not a failure of the numerical Lean certificates.**

The figure captions call the plots “exact arithmetic,” and the [reproducibility paragraph](/shift_symmetry_d_dimensions.tex#L1105) says all computations use exact integers. But [log10_S](/compute_dimension_insights.py#L38) evaluates the enumeration formula using floating logarithms and signed log-sum-exp, omitting terms whose relative base-10 logarithm is at most $`-300`$. Crossing locations also use floating interpolation. Exact integer coefficients are not the same as exact evaluation of the count or a rigorous interval enclosure of the plotted value.

The script header describes its method more accurately and says it is compared against exact evaluation where feasible. Separately, the certified numerical statements use exact certificates and analytic bounds; those proofs do not trust this plotting code. I found no evidence here that the certified displayed numerical intervals are false.

**Correction:** distinguish exact counts/certified numerical intervals from floating evaluation used to render the figures. Describe the plots as numerical evaluation of the exact formula, unless they are regenerated from rigorous interval calculations.

## What the formal statements actually establish

The following checks are affirmative findings, not inferences from the number of passing proofs.

| Paper component | Formal counterpart and fidelity assessment |
|---|---|
| Model and shift symmetry | `Definitions.lean`, S01: lattice is `Fin d → ZMod n`; configurations are functions on it; symmetry means an actual nonzero translation fixes the configuration. `numSS` is a subtype cardinality, not the enumeration formula in disguise. |
| Order, fixed sets, torsion, completeness, multi-prime joins | S02's five lemma groups describe actual element orders, subgroup-fixed configurations, torsion subspaces and joins. The completeness equivalence connects arbitrary nonzero stabilizers to the prime-order tests used in counting and detection. |
| Möbius coefficients and Gaussian counts | S03 and S02: genuine subspace counts/Möbius identities and product/recurrence bridges. The composite-base Gaussian polynomial used in the lower envelope is also bridged to the paper's formula; it is not treated as a finite field of composite size. |
| Main enumeration theorem | `enumerationStatement` counts actual symmetric configurations for every $`n\ge2,d\ge1,\sigma\ge1`$. S04 proves reindexing from divisors to rank vectors. Signed sums live in integers. Divisibility establishes that natural-number division in exponents is exact. |
| Prime case, boundary cases, second derivation | S04 gives actual prime counts, $`d=1`$ nonprimitive-word counts, and $`d=2`$ specialization. The second derivation uses subgroup Möbius/Hall machinery without invoking `enumeration_proved`; it shares lower-level mathematical infrastructure. Necklace qualification: finding 1. |
| $`k`$-active enumeration | S05 counts configurations with a specified number of occurrences of an actual distinguished symbol. The divisibility restriction on $`k`$, exponents, binomial coefficients, and $`0^0`$ cases are represented explicitly. It does not silently assume the problematic divisions are exact. |
| Density-uniform probability | S05 constructs a genuine probability mass function: uniform choice of $`k`$, followed by a uniform configuration in that active-count class. The desired probability formula is proved from that distribution. |
| Lower bound and equality iff prime | Core `lowerBoundStatement` is the actual-cardinality inequality with both directions of equality iff primality, uniformly for $`n\ge2,d\ge1,\sigma\ge2`$. It is not merely a prime-case equality or a conditional composite result. |
| Upper bounds and uniform probability | S06 connects subgroup counts to configuration counts and probability. The asymptotic lower bound on decay rate has explicit uniform quantifiers in $`n,d,\sigma`$ as $`N\to\infty`$. |
| Irreversibility and rank monotonicity | S07 preserves each stabilizer, hence all prime torsion ranks simultaneously and along trajectories. Rank is linked to intrinsic finite dimension, not an unrelated numerical surrogate. Absorbing superlevel sets are proved; arbitrary exact-rank strata are not incorrectly asserted invariant. |
| Insolvability and leader election | S07 proves the conditional obstruction and a separately defined unique-leader task. The additional informal application names are excluded: finding 2. |
| Detector correctness and worst/average reads | S08 defines an actual recursive detector with a read counter. Statements cover all valid subgroup schedules and traversal orders, with existence of valid inputs proved. Both early-stop and completed-walk variants are handled. The exact geometric expectation is for a standalone subgroup test, and full-algorithm cost is bounded above by their sum. |
| Complexity qualifications | Fixed-dimension smooth-factor/density claims are formalized. Exact improvement factors are restricted to completed walks as disclosed in the current manuscript. Findings 3–4 concern stronger readings of the prose/table. |
| Decay-rate and inversion laws | S09 proves fixed-$`(n,\sigma)`$ convergence as $`d\to\infty`$, the probability comparisons, sign threshold, and linear asymptotics of the crossing scale. The explicit constant 20 really is proved in helper theorems `window_i` and `window_ii`; its presence is not lost merely because a frozen aggregate statement existentially quantifies a constant. |
| Numerical observations | S11 formalizes exact integer comparisons and rigorous intervals for rounded values. Inversion deepening is quantified over all applicable primes, alphabets, and dimensions, not only the plotted sample. Auxiliary explicit witnesses support claims whose frozen surface statement is shorter, including the $`n=10`$ nonmaximum. Fitted empirical constants are expressly excluded. |
| Appendix lower-bound argument | S10's rectangular torus is an actual product of cyclic groups; its union interpretation has a cardinality bridge. The coefficient estimates, monotone chain, base cases, low-dimensional cases, and strictness feed into the full lower-bound theorem. |

For the most consequential representation bridge, [semantic_probes.lean:9](/research/formal/main_paper_audit/semantic_probes.lean#L9) proves directly that the cardinality of configurations admitting a nonzero fixing translation equals the paper's rank-vector formula. This makes the endpoints of the main counting result visible without relying on theorem names or documentation.

## Additional wording and interpretation notes

“Equivariance is necessary” should mean that the hypothesis cannot simply be dropped from the general theorem. It is not a necessary condition for an individual map to preserve every stabilizer. The map copying the value at one fixed absolute cell to all cells preserves every stabilizer, since its outputs are constant, but is not equivariant. [The probe](/research/formal/main_paper_audit/semantic_probes.lean#L37) proves both facts on the binary two-cell lattice. The existing theorem proves the appropriate sufficient condition and counterexamples to dropping it; no converse should be inferred from the remark title.

The abstract's [claim that all dynamical consequences are new](/shift_symmetry_d_dimensions.tex#L70) should be narrowed. The general stabilizer inclusion under equivariant cellular automata is already explicit in the proof of Lemma 3 of [Castillo-Ramirez and Gadouleau](https://arxiv.org/pdf/1610.00532). This is an attribution concern, not a mathematical counterexample or a comprehensive assessment of novelty of the enumeration formula.

The algorithmic certificates concern **cell reads**. They do not establish the same bound for all implementation work, such as constructing schedules, checking list membership, or factoring $`n`$. Section 9 correctly states this cost model. Preserve that precision in the abstract and summaries.

The shaded region in the decay-rate figure should be understood asymptotically, as the corrected caption says. It is not a finite-$`N`$ prohibition of rates below $`1/2`$; for example $`c(2,2)=1/4`$.

## Validation and reproducibility

The following commands completed successfully from the indicated locations:

```bash
# research/formal/shiftsym
lake build
lake env lean Shiftsym/AuditPaper.lean
lake env lean Shiftsym/Audit.lean
lake env lean ../main_paper_audit/semantic_probes.lean

# repository root
python3 research/formal/check_placeholders.py
python3 research/formal/main_paper_audit/independent_checks.py
```

`lake build` completed successfully with 8,938 jobs reported. It reused existing build artifacts; this is not a claim of a fresh independent kernel replay of every imported module. The targeted paper audit found **337 statements and zero failures**, with group counts matching the manuscript: 31, 20, 22, 48, 31, 41, 31, 25, 21, 33, 34. The placeholder check was clean. Core theorem axiom audits and the new probes use only the allowed standard axioms `propext`, `Classical.choice`, and `Quot.sound` (some probes use fewer).

The independent Python checker imports no project calculation functions. It uses the rational-product Gaussian formula rather than copying Lean's recurrence, and compares:

- exhaustive nonzero-shift tests over **377,838 configurations** in 52 parameter triples, including active-cell histograms;
- explicit subgroup-join inclusion–exclusion against the formula in 27 triples, including multiple distinct primes and non-elementary cyclic factors;
- the lower and upper bounds, including equality iff prime, in 276 triples;
- actual early-stop read expectations in the binary prime-size one-dimensional examples above.

All passed. These finite checks are independent corroboration and useful counterexample searches, not substitutes for the universally quantified Lean results.

Saved artifacts: [independent checker](independent_checks.py), [result JSON](independent_checks.json), [Lean probes](semantic_probes.lean), [probe output](semantic_probes.log), [paper audit output](paper_audit.log), and [source hashes](source_manifest.json). The source manifest records the reviewed source state, including the main paper, included charts, core sources and paper-layer sources. No manuscript, production proof, or figure was changed by this audit.

## What passing the audit does—and does not—mean

[AuditPaper.lean](/research/formal/shiftsym/Shiftsym/AuditPaper.lean#L66) does a useful structural check: it discovers statement definitions in the intended modules, requires a corresponding theorem of the exact statement shape, verifies proof-module provenance, and rejects unexpected axioms. This prevents an apparent certificate that merely proves some other proposition or adds an extra hypothesis at the proof declaration.

It cannot decide whether the statement translates the manuscript faithfully. It also does not enforce an immutable historical set or hash of statements: weakening or deleting a statement can escape a correspondence check if the remaining definitions/proofs remain well formed. I found no evidence of such an exploit here. The practical improvement is to maintain a manuscript-to-statement ledger that includes explicit exclusions, quantifier order, exact helper theorem names when needed, and versioned hashes. In particular, embedded image text and application claims need to be part of that ledger.

The appropriate conclusion is that the main mathematical results have substantial and credible formal support, while the remaining claims of complete coverage and a few expository assertions need the targeted corrections above.

---

## Response (2026-10-18)

*Authors' response, 2026-10-18 13:38 +0200.* Every finding was checked against the paper, the chart
script, the Lean development and the cited Castillo-Ramirez–Gadouleau paper
before a decision was taken; all six numbered findings were confirmed. None
affects a theorem, lemma, proposition, corollary or Lean proof.


---

## Independent verification of the response (2026-10-19)

**Verdict:** the substantive fixes to findings 1–5 check out. Finding 6 is substantially addressed, with one leftover sentence identified below. I found no new mismatch between the main-paper mathematical claims and the new necklace formalization. The novelty concern remains open, as the response acknowledges. The new verification tools are useful, with the limitations below.

This recheck examined the actual manuscript diff, the regenerated chart, both new Lean files, the updated audit, and the fingerprint/replay scripts. It did not treat the response's reported prior reviews as evidence in place of inspection. Follow-up papers remain outside the semantic review scope.

**Confirmed fixes.**

- **1 — Closed.** `PrimNecklace` is an actual quotient of primitive configurations by rotation, not a count defined using the desired formula. The proof establishes that the relation is an equivalence, rotations preserve primitivity, and the action is free. The explicit bijection `PrimNecklace n σ × Lat n 1 ≃ PrimWord n σ` supplies the factor `n`. The set-level proper-power/rotation equivalence connects this definition to the classical notion of a primitive word. The cleared-denominator Moreau–Witt statement has the correct hypotheses, including `n ≥ 1`, so it is equivalent to the quotient formula. See [S12](/research/formal/shiftsym/Shiftsym/Paper/S12_Necklaces.lean#L44) and [P12](/research/formal/shiftsym/Shiftsym/Paper/Proofs/P12_Necklaces.lean#L111).
- **2 — Closed.** The application now explicitly requires an output that breaks an input symmetry. This is supported by stabilizer preservation and no longer asserts generic image-translation insolvability.
- **3 — Closed.** The smooth-factor assertion now fixes dimension and discloses dependence of the degree on dimension.
- **4 — Closed.** The conclusion table now explicitly qualifies the displayed bound, rather than purporting to characterize actual early-stop cost.
- **5 — Closed.** I inspected the regenerated image. Its title includes the `n = 3` exception. The stronger all-primes-`p ≥ 5` wording is supported: `compositeAdvantageD2Statement` compares a prime with **both** adjacent composite integers, for every alphabet size at least two. It is not merely a finite scan or a comparison with the successor alone.

**Remaining items.**

1. **One arithmetic-provenance sentence remains (minor).** Although the captions and reproducibility paragraph are corrected, [the sentence introducing the decay-rate figure](/shift_symmetry_d_dimensions.tex#L962) still says the figure shows convergence “in exact data.” Its generator still uses floating log-space evaluation. Replace this with “in numerical evaluations of the exact formula.” This is a residual wording issue, not a numerical theorem failure.

2. **The novelty claim remains unresolved.** [The abstract](/shift_symmetry_d_dimensions.tex#L67) still says that all dynamical consequences are new. The response agrees with the factual concern and labels it “TO DISCUSS”; it therefore should not be counted as closed. The original recommendation to narrow the claim and distinguish the new results from established stabilizer preservation still stands.

3. **The new tools should not be described as a complete automatic protection against semantic drift.** The fingerprint gate checks the listed statement files and `Paper/Common.lean`, but omits the main core [Statement.lean](/research/formal/shiftsym/Shiftsym/Statement.lean) and [Definitions.lean](/research/formal/shiftsym/Shiftsym/Definitions.lean). Changes to these can change a statement's meaning without changing its fingerprinted paper-layer wrapper. Include these files, and preferably the other relevant definition dependencies, if protection of the whole mathematical contract is intended. Separately, [kernel_replay.lean](/research/formal/kernel_replay.lean#L27) collects kernel errors but only prints the result; it does not throw an error when the collected list is nonempty. Its header correctly tells a human to inspect `errors=0`, but a zero process exit status alone is not a reliable automated success signal. Add a final `throwError` on a nonempty error list before using it as an automated gate. Neither observation establishes a defect in a current proof.

**Validation performed in this recheck.** The targeted build succeeded (8,764 jobs reported, with cache reuse). I also ran Lean directly on `P12_Necklaces.lean` and `AuditPaper.lean`: the new proof file passed, and the audit reported **342 statements, zero failures**, including all five new statements. The fingerprint gate passed for 19 files, and the placeholder check was clean. Comparison against the original independent audit's SHA-256 manifest found no changes to the previously reviewed main statement files, `Common.lean`, or the core `Definitions.lean`/`Statement.lean`. Thus the added necklace formalization has not silently replaced the original statements.

I additionally performed a fresh kernel replay restricted to the project modules imported by `Shiftsym.AuditPaper`: **68 modules, 2,718 theorems and 705 safe definitions, zero errors**. The replay reported five generated unsafe recursion helpers separately; no project axiom or opaque declaration was reported. This rechecks declarations against the loaded dependency environment, not a reconstruction of mathlib from an empty environment. The [saved runner](response_main_kernel_replay.lean) follows the supplied replay implementation, restricts imports to the main-paper audit, and throws an error if any declaration fails. [Output](response_main_kernel_replay.log) is saved alongside it. I stopped the initially started whole-library replay when restricting this check to the requested main-paper scope; the response's full-library counts are not independently reconfirmed here.

No production proof, manuscript, figure, or authors' response was edited during this recheck. Only this appended verification and its replay artifacts were added.

---

## Reply to the verification (2026-10-19)

*Authors' reply, 2026-10-19 10:22 +0200.* All three remaining items were checked against the paper and the
Lean development; all three are confirmed.

| # | Item | Decision | What was done |
|---|---|---|---|
| R1 | "in exact data" before the decay-rate figure | **FIX** | Replaced by the reviewer's wording: "Figure 2 shows the convergence in numerical evaluations of the exact formula." The two other "exact" passages of §10 were rechecked and kept: the measured row of Remark 10.3 ("in exact data") states values of the exact quantity, certified to two decimals in Lean (`ShiftSym.P11.measuredRow_proved`), and the §10 preamble's "computational findings with exact arithmetic" refers to discrete claims that are Lean-checked. Released with fixes 1–6 as paper v5 (21 pp.); all changes since v4 are marked in `shift_symmetry_d_dimensions_v5_diff.pdf`. |
| R2 | Novelty claim of the abstract | **TO DISCUSS** | Unchanged and still open: a decision for the authors (item 7). |
| R3a | Fingerprints omit `Statement.lean`, `Definitions.lean` and other definition dependencies | **FIX** | New gate `research/formal/frozen_deps.lean`: it computes from the environment the dependency closure of all 753 frozen statements (core, paper-wide and extension layers; types of every constant reached and bodies of definitions; theorems are skipped, since by proof irrelevance a proof cannot change a statement's meaning) and fails unless every Shiftsym file in the closure is fingerprinted. Its first run found 10 unrecorded files: `Definitions.lean`, `Statement.lean`, `StatementE1.lean`, `StatementE2.lean`, and six lemma files that hold definitions statements unfold to (`Lemmas/Assembly`: a `Fintype` instance; `Bridge`: `ofMod` and an instance; `Evaluate`: `ModTuple`; `Linear`: `quotRule`; `MobiusSum`: `linesF`, `spanSum`; `Torsion`: the torsion subgroups and their equivalences). These ten, plus `lean-toolchain` and `lake-manifest.json` (the mathlib pin), are now in `frozen_statements.sha256` (31 files). Each hash equals the one in this folder's `source_manifest.json`, i.e. the state reviewed on 2026-10-16. `check_frozen.py` now also flags an unrecorded `Statement*.lean` or `Definitions.lean`. |
| R3b | `kernel_replay.lean` exits 0 even with errors | **FIX** | It now throws (nonzero exit) on a nonempty error list and on any axiom declared in a Shiftsym module. |

**Validation.** `lake env lean ../kernel_replay.lean` (new version, whole library): 242 modules, 8553 theorems, 1990
definitions, 0 errors, no project axiom, exit status 0 (the numbers stated in §11 of the paper). `python3 research/formal/check_frozen.py`: 31 files, all unchanged.
`lake env lean ../frozen_deps.lean`: 753 statements, 2056 constants, 29 Shiftsym modules, 0 unrecorded.
`check_placeholders.py`: CLEAN. No file of the Lean package changed (the two scripts sit outside it), so the build
and AuditPaper results of the verification stand. The reviewer's restricted replay runner and its log are kept in this
folder.


---

## Independent verification of Tobi's merged PR #1 (2026-10-23)

**PASS for the merged change and its statement/proof correspondence.** Reviewed HEAD: `df7e8e110c1b53863023bf000e978add7518570a`; PR commit `f1d041a`, merged as `a066959`. The [detailed report](pr1_window20/REVIEW.md) records the mathematical analysis, appendix recheck, source hashes, independent checks, and execution evidence.

Tobi correctly identified that the old frozen Proposition 10.2 window statements only asserted existence of a constant. The constant 20 was already proved by auxiliary theorems, as the earlier review observed. The supplement now exposes the literal 20 in audited criteria and probability statements, and includes both in the whole-proposition target. I verified the full parameter ranges, inclusive window endpoints, strict probability comparisons, actual configuration-cardinality definitions, the `d ≥ 1` convention, non-vacuity at `p = 37`, and the exact upper endpoint at `p = 3, d = 21`. The new proofs establish the paper's claims without weakening the old statements.

The four appendix lemmas remain faithful. The PR changes their correspondence annotations, not their statements or proofs. An additional Lean probe establishes Lemma A.2's printed coefficient bound even for ranks above the dimension, where the product is zero. The `Definitions.lean` re-record is justified: exactly two deprecated-alias replacements reproduce the current file byte for byte, with no other change. The pinned mathlib source confirms the alias relation.

Independent validation: full build passed with cache reuse; paper audit **345/345**, zero failures; dependency gate **756 statements, 30 modules, zero unrecorded**; fingerprint gate **32 files**, passed; placeholders clean. The fresh full kernel replay completed in about 34 minutes: **244 modules, 8,567 theorems, 1,993 safe definitions, zero errors**, exactly matching v6 and Run 026. Independent literal Lean probes, 284,598 exact prime/dimension checks, 24 exact count comparisons, and 38 probability-sign certificates valid for every alphabet size at least two also passed. All 259 snapshotted source/artifact hashes remained unchanged during validation.

No new mathematical or formalization defect was found. The older abstract-novelty concern remains outside this PR. No production proof, manuscript, figure, fingerprint, or run log was changed during this review; only review artifacts were added. No commit, push, or GitHub comment was made.


---

## Addendum on finding 2 (2026-10-27)

*Authors.* The v5 fix for finding 2 narrowed Corollary 8.2's application sentence to "every pattern-recognition or
image-processing task whose required output breaks a symmetry of some admissible input", and the verification closed it
as "supported by stabilizer preservation". An independent judgment of the paper ↔ Lean correspondence audit
(`../correspondence_audit/independent_judgment/JUDGMENT.md`) then found that no frozen statement certified this clause.
The clause is strictly more than the frozen `insolvGeneralStatement`: on Z_4, 0000 → 0101 breaks a symmetry of the input,
although 0101 is itself shift-symmetric.

The clause is now frozen in the group-07 supplement `Shiftsym/Paper/S07_Dynamics_SymmetryBreaking.lean`
(`insolvSymBreakStatement`, `insolvFullStatement`). Three fresh-context fidelity reviews passed before the proofs were
written (`research/experiments/symbreak_fidelity/`). The proofs are in `Paper/Proofs/P07_Dynamics_SymmetryBreaking.lean`,
which uses the stabilizer form of Theorem 8.1 iterated along the trajectory.

The literal review found that "This covers" was imprecise: the corollary's stated argument, "no trajectory leaves
S_{n^d}", does not exclude these tasks. Paper v7 therefore rewords the sentence: "More generally, since Stab can only grow
along a trajectory (Theorem 8.1), every … task whose required output breaks a symmetry of some admissible input is
unsolvable". AuditPaper now checks 347 statements (Run 027 in `research/experiments/README.md`).

---

## Independent review of v8 and the commits of 2026-11-02

**Mathematical PASS for the changes reviewed; one correspondence-viewer issue remains.** Reviewed
`e868e8f`, `a7b87d6` and `47ed8bc`, with `977f823` as the baseline. The [detailed report](v8_review/REVIEW.md)
records the complete scope, mathematical analysis, finding, independent probes and execution evidence.
Follow-up papers remain outside the semantic review.

John's edits and all 30 documented editorial corrections preserve the mathematics. I independently reconstructed
the v5/John/v7 merge, inspected the manuscript diffs, checked the split Möbius lemmas against their literal sum,
subspace and incidence-Möbius definitions, verified the counting hypotheses and corrected Appendix A.1 references,
and compiled both versions to verify the renumbering. The standard and mobile PDFs rebuild successfully and their
extracted text matches the committed PDFs exactly.

The symmetry-breaking supplement committed today also passes. Its quantifiers correctly require one admissible
input for which every acceptable output loses an input symmetry; the lost translation may depend on the output.
The proof iterates stabilizer inclusion. Separate Lean probes establish the corresponding claim directly in cell
values and nonzero translations, without using task or stabilizer predicates in the conclusion. Exhaustive
independent checks cover 8,414 subsets of projective lines and 131,344 binary CA rules on four small tori, including
nonempty symmetry-breaking tasks and an example that distinguishes the witness quantifier order.

**V8-1 — Refresh the generated correspondence viewer before using it to sign off v8.** The source mappings are
updated, but `data/audit_data.json` is still from **v6**, with 24 items and 21-page geometry. The server displays
the current v8 PDF (25 items, 23 pages) with those old mappings. The browser's stale indicator compares verdicts
with the old generated item hashes, so it does not automatically detect today's source changes. The final audit
report does disclose PDF/TeX hash mismatches. Run 029's description that the UI shows v7 and flags changed items
stale is therefore inaccurate. Rebuild the complete bundle and add a source-hash preflight; the detailed report
contains precise evidence and the affected code locations. This is a tooling problem, not a counterexample to a theorem.

Independent validation: main and root builds passed; paper audit **347/347**, zero failures; fingerprint gate
**33 files**, passed; dependency closure **758 statements, 31 modules, zero unrecorded**; placeholders clean.
A fresh main-paper kernel replay passed for **72 modules, 2,739 theorems and 714 safe definitions, zero errors**.
The full-root inventory matches Section 11's **246 / 8,574 / 1,999** counts; this inventory check is not a fresh
full-library replay. Source-anchor validation passed for **25 files and 476 mappings**, with the existing warning.

The previously open abstract claim that all dynamical consequences are new remains unresolved and was not
introduced by this merge. No production proof, manuscript, viewer data, fingerprint or run log was changed during
this review. Only review artifacts were added; no commit or push was made.

## Response to the v8 review (2026-11-02)

*Authors.* We thank the reviewer. Details and checksums are in Run 029 of `research/experiments/README.md`.

**V8-1: accepted and fixed.** The finding is correct. `data/audit_data.json` had been built at `f1d041a` from paper
**v6** (TeX `ff8d5610…`, PDF `fa91c65d…`, 24 items, 21 pages); v7 never had a bundle. Run 029 said that the viewer
"still shows v7" and that changed items "will be flagged stale". Both statements were wrong, and they are corrected in
place, marked as a correction.

- **Rebuilt.** A full `tools/build.py` run against v8 passes: 25 correspondence files, 476 mappings, 0 errors; 23
  pages, layout identical to the official PDF. The bundle is built at `47ed8bc`. Its fingerprints match the committed
  PDF (`3d5eb36a…`) and TeX (`72bd9549…`). It has 25 items with v8 numbers, Lemma 4.2 among them, and lists the
  symmetry-breaking statement file. No Lean file has changed since `e868e8f`, and all 73 Lean fingerprints match.
- **A second cause, found during the rebuild.** The README's Docker recipe did not install `cm-super`. The v6 PDF had
  been built inside that container, with bitmap Type 3 fonts. v7 and v8 were built on the authors' machine with the
  scalable cm-super Type 1 fonts. The container therefore could not reproduce the official PDF, and the layout check
  failed from the first word. The recipe now installs `cm-super` and explains why the fonts must match, and the image
  was rebuilt from it.
- **Effect on the recorded audit.** All 23 verdicts in `logs/events.jsonl` (all 👍, given against v6) now show as
  stale, as intended:
  - five only because line numbers moved: Proposition 8.3, Theorem 9.1, Proposition 10.2, Lemmas A.3 and A.4;
  - three because mapping text or the summary changed: Theorem 4.4, Corollary 7.2, Lemma A.1;
  - fifteen because the statement text changed.

  Lemma 4.2 (new) and Lemma A.2 have never been judged. Item IDs are LaTeX labels, so every verdict stays with its item
  through the renumbering. Re-judging is for the auditor.
- **Preflight check: not implemented.** The viewer is maintained by Tobi Lehman, and we pass the recommendation to him.
  Meanwhile, the audit README states three things: `--check` does not refresh the bundle; the stale flag compares only
  against the item hashes stored in the bundle; and the bundle's fingerprints (or the "sources unchanged" line of the
  audit report) must match the current PDF and TeX before anyone relies on the viewer.


## Independent verification of the v8 viewer rebuild (2026-11-02)

**PASS for commit `baea4fa`: the current V8-1 bundle mismatch is fixed.** The [verification report](v8_viewer_recheck/REVIEW.md)
and its executable checks confirm that all 173 input fingerprints match, the viewer has 25 correctly numbered v8
items and 476 mappings, and the new Möbius lemma and symmetry-breaking statement are included. A fresh instrumented
compilation reproduced the official PDF's word layout exactly, all 519 anchor highlights, all item rectangles and
the auxiliary labels. All 51,954 glyph boxes and all 25 item hashes were independently reproduced.

All 23 historical approvals now compare stale against the new item hashes; Lemmas 4.2 and A.2 remain unjudged.
No auditor verdict was submitted or changed. The automatic source-hash preflight remains deferred, as the response
explicitly states, so the preventive recommendation remains open even though the present bundle is correct.


**Note (2026-11-04).** This recheck describes the bundle of `baea4fa`. T. Lehman has since audited all 25 items
against that bundle (`8109cf1`: all 25 approved), and paper v9 moved every line, so the bundle was rebuilt for v9
(Run 030): 1 verdict is current and 24 are stale by line scopes only, pending his re-confirmation.
`v8_viewer_recheck/verify_bundle.py` asserts the `baea4fa` state and stops at its first fingerprint check against
the current bundle; it is kept as the record of that check.

## Independent review of v9 and its public release (2026-11-05)

**No new mathematical or paper–Lean correspondence defect found; release actions remain.** The
[detailed review and evidence](v9_release/REVIEW.md) cover internal `444c7af`, the public-release checkout
`e7caee2`, and the leader-election citations P. Banda requested during this review. Follow-up results were excluded.

- All 39 numbered environments and all production Lean sources are unchanged from reviewed v8. The standard
  export reproduces all 338 files of the public checkout byte for byte.
- A fresh compilation into an empty project object directory passed for all 76 exported modules, using the pinned
  mathlib/dependency cache. The fresh paper audit is **347/347**; fresh kernel replay is **76 modules, 2,746
  theorems, 716 definitions, zero errors**. Fingerprints, placeholders and dependency closure also pass.
- The application statements hold with their stated qualifications. Figure 1's stabilizers were independently
  recomputed; direct enumeration of the union of fixed configurations gives **801,064**, without using the count
  formula to obtain that union size. Figure 5 and the viewer discussion accurately separate proof checking from
  correspondence review.
- Reconstructed the committed viewer's 173 fingerprints, all 25 items, 476 links, 519 highlights and 60,131 glyph
  boxes. All historical approvals are positive; 24 remain stale solely because of line scopes. Five older v6
  approvals were also traced to their exact historical hashes. Run 031's requirement for T. Lehman's reconfirmation
  or a reviewed hashing change remains open; no verdict was submitted or altered.
- The advertised public GitHub URL returns **404 anonymously**. The local release is verifiable, but readers need
  access to the final synchronized repository before announcement. No visibility change or push was performed.
- The public README heading “primes minimize shift symmetry in every dimension” overstates the prime-tight
  lower-bound theorem and conflicts with Observation 7.3. A one-line replacement is supplied in
  [recommended_readme.patch](v9_release/recommended_readme.patch). The manuscript's theorem is correct.

added Banda (2011), Banda–Caughman–Pospíchal (2015), and Banda's dissertation (2014) to
the related work and leader-election application, with the verified 2011 DOI and a thesis download link. All 39
numbered environments, Lean files and frozen hashes remain unchanged. Rebuilt the main PDF (26 pages), mobile
PDF (54 pages), v8→v9 diff (26 pages), line scopes and viewer data. Independent reconstruction of the updated
viewer reproduces all 519 highlights and 61,122 glyph boxes exactly; all 31 bibliography entries resolve in TeX.

The minimal arXiv source package (`v9_release/arxiv_source_v9_with_citations.zip`, deleted since; see the
follow-up note below) contains the main TeX and four
figures and compiles in isolation to the updated PDF's word layout. Local TeX Live is 2022, so arXiv's own
2023/2025 preview still needs checking. The earlier abstract novelty objection remains recorded as an author
decision; the new citations strengthen the historical attribution but do not establish novelty of the underlying
symmetry-preservation principle. No numbered mathematical statement or Lean proof needed correction.

*Follow-up, 2026-11-05 (P. Banda's decisions after this review; record in Run 033 of
`research/experiments/README.md`):* the dissertation citation was dropped again. Its 1-D content is
covered by Banda–Caughman–Pospíchal (2015) and its 2-D content by Banda et al. (2019), both cited; the
leader-election application now cites the 2019 paper for two dimensions. The two remaining leader-election
sentences moved from the head of the related-work paragraph to follow the sentence on the 2019 paper.
Both arXiv zip packages were deleted: they predate the arXiv clean-up of the source (header comments,
date line), and no zip is kept: the cleaned source and its four figures are uploaded to arXiv directly. The
public README's heading for result 2 now reads "Bounds: a lower bound attained exactly at the primes".

## Independent review of v10 and v11, including results promoted from follow-ups (2026-11-09)

**No new mathematical error or paper–Lean statement mismatch found.** The
[detailed review and reproducible evidence](v10_v11_review/REVIEW.md) cover final v9 `72b60b4`, final v10
`099e022`, v11 `dde222d`, and public checkout `6424a78`. Promoted results are included as main-paper content;
the remaining follow-ups are excluded. All 2,983 lines of new statement/proof modules were read against the
paper, including definitions, quantifiers, representation changes and dependencies.

The finite-abelian-group enumeration, rectangular specialization, strict rank increment and cyclic minimum,
fixed-population extension, free-orbit count, adaptive deterministic read lower bound, and v11 natural
torsion-vector-space/dimension statement are faithfully formalized. Corollary 4.8 with its proof and Remark 4.9
moved byte for byte to Appendix B. Previously existing paper-layer Lean files and the existing core definitions,
statements and lemma files are unchanged from final v9. The Fourier operation-count paragraph is correctly
separated from the formalized claims; its exact implementation requires suitable NTT roots and moduli.

Four remaining items are recorded in the detailed review:

- **V11-1 — final auditor action:** Theorem 4.7 is the only stale approval. Its `Gp`, `Fp`, and `dp` mappings
  changed substantively with the v11 supplement, so T. Lehman must re-check it and issue the current verdict.
  The new formal statement is correct; this is the already disclosed release-record gate, not a proof defect.
- **V11-2 — viewer documentation:** `data/corr/thm_abelian.json:87` still says “an F_p-vector space” is unfrozen,
  contradicting the new supplement and mapping. Correct that delta before the final approval; the frozen old
  S13 file need not change.
- **V11-3 — small manuscript attribution clarification:** the description of Miles–Ward as working “without
  evaluating the Möbius function” is too broad: their Lemma 2 already uses its elementary-abelian support and
  coefficient bound. Say instead that they do not reduce the counts to the explicit rank-indexed formula used
  here. See [their primary paper, Lemma 2](https://arxiv.org/pdf/0706.3630). No mathematical change is needed.
- **V11-4 — public access:** the advertised GitHub URL still returns anonymous **404**. The local public
  checkout matches a fresh export exactly, but reader access must be enabled before advertising it as public.

Fresh verification, independent of the authors' reported runs:

- Compiled all **89 public project modules** into an empty project object directory, reusing only pinned
  external dependencies. Paper audit: **370/370**, zero failures. Fresh kernel replay: **89 modules, 3,042
  theorems, 809 safe definitions, zero errors**. Frozen files, dependency closure and placeholder gates pass.
- Rebuilt the public export: **519 files identical** to the public checkout. Reconstructed all **189 viewer
  input fingerprints, 27 item hashes, 529 mappings, 577 highlights and 68,243 glyph boxes**. Word positions and
  auxiliary labels match. All **36 positional carry-forward events** were independently traced to their
  historical bundles; no inappropriate carry-forward was found.
- An independent subgroup-poset evaluator and direct enumeration passed **258 group/alphabet cases, 5,973
  fixed-k cases, 127,588 configurations and 958 strict rank steps**, including trivial and mixed-prime groups.
  Both order-48 examples give **50,388,256** binary symmetric configurations. The separate FFT/read experiment
  also passes. The full Adamson 84-case/720-reading rerun reproduces the carefully qualified footnote.
- Compiling only the main TeX and four figures reproduces the official **28-page** word layout, with no
  unresolved references or Type 3 fonts. The new theorem, read-complexity and Appendix B pages render correctly.
  No ZIP was created; arXiv's own upload preview was not run.

Only this review entry and `v10_v11_review/` were written. The manuscript, PDFs, production Lean files,
fingerprints, auditor events and public checkout were not modified. No commit, push or publication was made.

**Response (2026-11-09, Run 048 of `research/experiments/README.md`).**

- **V11-1:** open. T. Lehman re-checks Theorem 4.7's links `Gp`, `Fp`, `dp`; it is the only stale verdict.
- **V11-2:** fixed. The delta in `data/corr/thm_abelian.json` now says that "an F_p-vector space", listed as not
  frozen in the S13 docstring, is frozen in the group-13 supplement (`pTorsionVectorSpaceStatement`). Theorem 4.7
  was stale already, so its re-check covers this change.
- **V11-3:** applied, after reading Miles–Ward's Lemma 2 (arXiv:0706.3630v2, p. 4): by Kratzer–Thévenaz, the Möbius
  value vanishes unless the quotient is a product of elementary abelian groups and is bounded by
  $`\prod_i p_i^{n_i(n_i-1)/2}`$. The related-work sentence now ends "without reducing them to the explicit
  rank-indexed formula used here" (same source lines; no audit item changes).
- The review folder is committed with its `.log` evidence (force-added past the `*.log` rule, as for
  `v9_release/`); its `workspace.json` (temporary build locations) is not exported to the public repository.

## Independent recheck of Tobi's final v11 audit (2026-11-10)

**PASS: V11-1, V11-2 and V11-3 are closed.** Pulled `origin/main` by fast-forward from `8ddf7d6` to
Tobi Lehman's `c73bb7b` (“done with audit v11”). The [detailed review](tobi_v11_recheck/REVIEW.md),
[audit replay](tobi_v11_recheck/audit_verification.json), and
[bundle reconstruction](tobi_v11_recheck/bundle_verification.json) record the checks.

- Tobi changed only audit artifacts. His bundle differs from its parent only in build time, Git revision and
  local checkout path; no item, mapping, source fingerprint, manuscript or Lean statement changed.
- The old 3,524-event log is preserved byte for byte, with 126 events appended. Four Theorem 4.7 links and six
  older Proposition 10.2 links were cleared and freshly approved in the browser. The renewed verdicts match
  the current hashes: Theorem 4.7 at 00:36:03.537 UTC and Proposition 10.2 at 00:54:52.237 UTC on November 10.
  The viewer's automatic aggregate verdicts follow the auditor's mapping marks; these are not positional
  carry-forwards. Intermediate negative/cleared marks remain visible and are superseded.
- Independent event replay finds **27 current positive approvals, zero stale or unjudged items, and all 529
  mapping marks positive**. Recomputing the final report reproduces its substantive contents; only generation
  and bundle-build metadata differ because the report preceded the final metadata-only rebuild.
- Independently reproduced **189 source fingerprints, 27 item hashes, 529 mappings, 577 highlights and 68,268
  glyph boxes**. Fresh instrumented compilation reproduces the current 28-page PDF's word layout and labels.
- Verified the preceding `6ed8704` fixes: the viewer no longer calls the vector-space clause unfrozen, and the
  manuscript uses the recommended narrower Miles–Ward description. No further manuscript correction is needed
  for these findings.
- All production Lean sources, pins and frozen records are unchanged from the deep review; the 38-file frozen
  gate passes. The previous **370/370 statement audit and 89-module kernel replay** therefore remain applicable.
  They were not unnecessarily rerun for this audit-only commit.


## Release-content scope inspection (2026-11-10)



This was a read-only inspection of the release checkout. Only internal review records were written; no release
files, commits, pushes, visibility settings or Git history were changed.

## Release extraction of the required relative-enumeration interface (2026-11-10)

The release working tree now omits the two unused linear-CA targets and their supporting definitions from
`StatementE1.lean`; the internal mixed module and follow-up proofs remain intact. The required relative-enumeration
declarations are retained verbatim. General-audit checks of the removed names are omitted, and the release freeze
explicitly records the extraction and original hash. See [verification evidence](release_lean_split/REVIEW.md).

A fresh source build passes all **89 modules** and **370/370 paper statements**. Dependency traversal covers
**373 statements and 1,147 constants**, with no unrecorded dependency. Kernel replay passes **3,036 theorems
and 804 safe definitions, zero errors**. The manuscript/PDF replay totals and approximate companion-module size
were updated accordingly. The reduced theorem count includes six generated helper theorems belonging to the
removed definitions, not main-paper results.

Independent viewer reconstruction reproduces **27 unchanged item hashes, 529 mappings, 577 highlights and
68,268 glyph boxes**; all 27 approvals remain current. The original auditor event log is unchanged. No repeat
of Tobi's correspondence audit is required. All changes are uncommitted; no push or history rewrite was made.
