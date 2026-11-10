# Independent review of the merged constant-20 PR

Review date: 2026-10-23. Reviewed repository HEAD: `df7e8e110c1b53863023bf000e978add7518570a`.
PR commit: `f1d041a10032f4e8772c37848862b8a26d3daf4e`; merge commit: `a066959`.

**Verdict: PASS. The change is correct and closes the discrepancy in the frozen statement.** The new statements express the literal constant 20, and the proofs establish them for the paper's full parameter range. I found no new missing hypothesis, weakened conclusion, vacuous substitute, or incorrect definition. The four appendix lemmas also remain faithful to the manuscript. The full kernel replay passed with exactly the inventory reported in v6. The execution record below identifies the validation actually performed.

## What Tobi fixed

Tobi is right that the original frozen window statements were weaker than the explicit sentence in Proposition 10.2. An assertion of the form `∃ C, window_property C` does not, by itself, give `window_property 20`. Even a proof that constructs the witness 20 leaves only the existential proposition exposed by the theorem's type.

However, the constant 20 was already proved by the helper theorems `window_i` and `window_ii`. The previous independent review's conclusion that 20 was machine-checked was correct, and the paper disclosed that it relied on these helpers. The PR improves the statement/proof correspondence: the exact quantitative claim is now a named, frozen target covered directly by the paper audit. It does not repair a false mathematical theorem or introduce the first proof of the constant.

The supplement adds two substantive formulations and an aggregate:

| New target | What its type guarantees |
|---|---|
| `inversionExplicitWindow20Statement` | Below `dc p - 20`, criterion (i) holds; above `dc p + 20`, criterion (ii) holds. |
| `inversionWindow20Statement` | The actual uniform symmetry probabilities have the corresponding strict ordering on both sides. |
| `inversionLaw20Statement` | All the old parts of Proposition 10.2, together with both explicit-20 formulations. |

The source is [S09_CrossoverLaws_Window20.lean](/research/formal/shiftsym/Shiftsym/Paper/S09_CrossoverLaws_Window20.lean#L73), and the proof is [P09_CrossoverLaws_Window20.lean](/research/formal/shiftsym/Shiftsym/Paper/Proofs/P09_CrossoverLaws_Window20.lean#L18). The old `S09_CrossoverLaws.lean` is byte-identical to the October 16 audit state. Nothing was weakened to accommodate the new proofs.

## Exact correspondence with Proposition 10.2

I compared the source, the rendered v6 PDF (pages 13–14), the statement definitions, the proof bodies, and the underlying definitions. The proposition itself is unchanged by this PR; v6 updates the date line and Section 11's description of the formalization.

The following details were checked explicitly:

- **Uniformity:** the new statements quantify over every prime `p ≥ 3`, every natural alphabet size `σ ≥ 2`, and every natural dimension `d ≥ 1`. The constant 20 is a literal real numeral, independent of all three parameters.
- **Endpoints:** both window comparisons are inclusive (`≤`), and the conclusions are strict. There is no loss of the boundary cases through replacement by a strict window condition.
- **Direction:** the lower branch proves `P(p,d,σ) < P(p+1,d,σ)`; the upper branch proves the reverse inequality. The negative sign on the upper logarithmic threshold has the paper's scope.
- **Dimension:** the additional shared `d ≥ 1` antecedent does not weaken the upper-window sentence, where the paper does not repeat it. The condition `d ≥ dc(p)+20`, together with `dc(p) ≥ 0`, already implies it. The lower branch explicitly requires positive dimension in the paper.
- **Arithmetic:** `p`, `σ`, and `d` are cast to reals in logarithms and comparisons. The exponent `d-1` uses natural subtraction only under `d ≥ 1`. `phi` uses real powers, and the existing `phi_natCast` theorem identifies its value at an integer dimension with the ordinary powers printed in the paper.
- **Logarithms:** the bases are greater than one and the arguments are positive. The numerator and denominator in `dc(p)` are positive for `p ≥ 3`. No totalized `log 0`, division by zero, or negative-argument convention is being exploited.
- **Probability:** `probUnif` is the cardinality of the configurations fixed by some nonzero translation divided by `σ^(n^d)`. It is not defined to satisfy the desired inversion inequality.
- **Whole proposition:** the aggregate retains (i), (ii), the unique real zero and sign pattern of `phi`, and the `p ln 2 + O(1)` assertion. Keeping the old existential window conjuncts is harmless redundancy: the new explicit claims imply them by taking `C = 20`.
- **Audit inclusion:** both the library root and `AuditPaper.lean` import the supplement. Its namespace, module prefix, and theorem names meet the actual discovery rules. The three new targets are counted, their proof types match, and their axiom dependencies pass the audit.

[LiteralChecks.lean](LiteralChecks.lean) independently restates the logarithmic criteria using `Real.log` quotients and the probabilities using a raw subtype cardinality of functions on `Fin d → ZMod n`. It then derives those statements from the new certified targets. This checks the semantic endpoints rather than merely asking Lean whether a declaration with the expected name exists. All five named probes compiled with only `propext`, `Classical.choice`, and `Quot.sound`.

## Why the constant-20 proof works

I traced the new wrappers through the old helpers instead of treating them as an unexplained black box. Set

\[
q=1+1/p,\quad c=d_c(p),\quad a=1-1/p.
\]

The core identity is

\[
\varphi(d)=a p^d\bigl(1-q^{d-c}\bigr),\qquad q^c=2-2/p.
\]

For either relevant integer (m), the logarithmic threshold satisfies

\[
\log_\sigma\bigl(2\log_2(m)m^{d-1}\bigr)
\le 1+d\log_2(m),\qquad \sigma\ge2.
\]

Below the window, (d\le c-20) gives (q^{d-c}\le q^{-20}\le p/(p+20)) by Bernoulli's inequality. The existing center estimate (c\le(p+1)\ln2), together with (d\ge1), also forces (p\ge29). The helper handles (d=1) separately, using \(\varphi(1)=(p-3)/2\). For (d\ge2), it bounds the positive main factor strongly enough that

\[
\varphi(d)\ge (20/3)p^{d-1}
\quad\text{while the logarithmic threshold is at most }3p^{d-1}.
\]

Above the window, (q^{d-c}\ge q^{20}\ge1+20/p). Thus

\[
-\varphi(d)\ge(40/3)p^{d-1},
\]

again exceeding the threshold, which is bounded by (3p^{d-1}). This branch's window hypothesis already forces (d\ge2). These are inequalities with substantial slack; 20 is not a numerically fitted cutoff.

The conversion from the criteria to actual probabilities uses the proved log-ratio sandwich

\[
\varphi(d)-L_p\le
\log_\sigma\frac{P_{(p+1)^d}}{P_{p^d}}
\le\varphi(d)+L_{p+1},
\]

where (L_m=\log_\sigma(2\log_2(m)m^{d-1})). The smallest prime factor of (p+1) is two because (p\ge3) is prime. Positivity of both probabilities is proved before logarithmic monotonicity is used. There is no assumption of the desired comparison in this argument.

## Boundary and vacuity checks

The lower window is empty for small primes. This is a genuine feature of the conservative constant 20, not a defect hidden in the proof:

- (d_c(3)=1); the upper-window equality case is exactly (d=21).
- (d_c(31)<21), and no prime (p\le31) admits a positive integer dimension in the lower window.
- (24\le d_c(37)<25); at the first applicable prime (p=37), the lower window contains exactly (d=1,2,3,4).

The new file proves these facts. The independent Lean probes go further than checking that the antecedents can hold: they derive the actual probability comparisons at ((p,d)=(37,4)) and ((3,21)), for **every** alphabet size at least two.

The statement does not assert a unique zero of the actual probability difference or a nonempty composite-advantage phase for every prime. The unique-zero assertion is about the real function `phi`; the probability window establishes the two strict orderings outside the undecided band. This is the appropriate reading of the quantified sentence in Proposition 10.2.

## The four appendix lemmas

The PR changes the correspondence annotations for Lemmas A.1–A.4, not their Lean statements or proofs. I rechecked those annotations against the actual definitions and conclusions rather than assuming the mappings were authoritative.

| Lemma | Review result |
|---|---|
| A.1, rectangular-torus union interpretation | The two displayed inequalities have the correct ranges and exponents. The actual union-count identity is a separate proved auxiliary statement; it is not silently substituted for an assumed interpretation. The torus is the real product of `d-j` copies of `ZMod n` and `j` copies of `ZMod (n/p)`. Divisibility and the valuation identity justify the quotients. The prime indexing is increasing and correctly translated from one-based to zero-based indices. |
| A.2, coefficient estimates | All three bounds are proved for real `q ≥ 2`, not merely prime or integral `q`. The dimension-one empty tail is handled. The first frozen part includes `j ≤ d`, the usual rank range. I additionally proved the printed product-formula bound for **all** natural `j`, using signed integer powers: when `j>d`, the factor at `i=d` makes the product zero. Thus this range restriction hides no counterexample. See [AppendixChecks.lean](AppendixChecks.lean). |
| A.3, monotone chain | `qm` is the actual alternating truncation, and its union-cardinality bridge makes monotonicity a genuine set-inclusion argument. The assumptions are exactly composite `n`, at least two distinct prime factors, positive dimension, alphabet size at least two, and `1 ≤ m < k`. Prime powers are not lost from the lower-bound theorem: they need no chain step and are handled by the base bound. |
| A.4, strict base case | The conclusion is strictly `F_d < q^1` for all composite `n`, all `σ ≥ 2`, and all `d ≥ 3`, including composite prime powers. The Gaussian binomial at the composite base `n` is connected to the paper's product formula by a proved bridge; it is not treated as a nonexistent field of order `n`. The proof's envelope estimate is independently available in the core inequality development. |

The Lean proofs need not follow every line of the paper's proof. In particular, the union interpretation provides a shorter monotone-chain argument. That is not a statement mismatch. The manuscript's analytic intermediate inequalities also have their own certified statements.

## Independent arithmetic checks

[independent_checks.py](independent_checks.py) imports only Python's standard library and reconstructs the relevant formulas independently of the project's calculation functions or the PR's prior review scripts.

Window membership is tested with **exact integer inequalities**, not rounded logarithms. For example,

\[
d\le d_c(p)-20
\iff (p+1)^{d+20}\le2(p-1)p^{d+19}.
\]

The script checked 284,598 prime/dimension pairs, using every prime from 3 through 1999 and every (1\le d\le p+25). There were 185,749 lower-window hits and 86,872 upper-window hits. At every hit, exact integer bounds establish the required strict criterion uniformly for all (\sigma\ge2). The first nonempty lower window was at (p=37), and the exact (p=3,d=21) endpoint was checked.

Separately, the script reconstructs each symmetry probability as a finite Laurent polynomial in the alphabet size, using the product formula for Gaussian coefficients. It proves the sign of 38 selected probability differences through an exact leading-term/tail inequality. If (A\sigma^E) is the leading term and the remaining absolute coefficient sum is (T), with exponent gap (g), the certificate verifies (A2^g>T). This implies the claimed sign for every (\sigma\ge2), without constructing astronomically large counts. These include high-dimensional upper-window cases.

There are also 24 direct exact-rational comparisons of the full enumeration formulas at lower-window cases (p\in\{37,41,43,47\}), (d\in\{1,2\}), (\sigma\in\{2,3,5\}). All checks passed. These finite certificates corroborate the universal Lean results; they are not a substitute for them.

## Fingerprints, merge provenance, and v6

I verified the re-recorded `Definitions.lean` fingerprint independently. Replacing exactly the two occurrences of `Set.mem_setOf_eq` in the original October 16 file with `Set.mem_ofPred_eq` reproduces the current file **byte for byte**. The pinned mathlib source explicitly declares the former as a deprecated alias of the latter. Both changes occur in proof fields of `stab`; the carrier predicate and all statement types are unchanged. Re-recording the hash with the retained explanation and old fingerprint is justified.

The dependency gate now covers the core definitions and statement dependencies previously identified as missing. It reports 756 frozen statements, 2,061 visited constants, 30 project modules in the dependency closure, and zero unrecorded modules. The fingerprint record contains 32 files, including the toolchain/dependency pins. It passes. The replay script now raises an error on kernel failures and project axioms, addressing the earlier automation concern.

The merged tree at `a066959` is identical to the PR tree at `f1d041a`. The subsequent commit `df7e8e1` contains the fingerprint re-record and Run 026. These two changes are already committed in the reviewed checkout; the quoted internal discussion about whether to commit them describes an earlier state.

Run 026's recorded checksum prefixes match the current files:

- TeX: `ff8d56104ee1c07a…`
- Main PDF: `fa91c65d6d8ab8d9…`
- v5-to-v6 diff PDF: `5fa22533a8eb626d…`
- Fingerprint record: `99c1315dec3d4671…`

All 73 source/PDF fingerprints in the correspondence application's built data match the current files. Its `git_head` records the pre-commit HEAD used while building the data, but the individual file hashes are current; I found no stale content behind the proposition mapping.

The GitHub connector returned 404 for the private PR. This review therefore relies on the complete local PR commit, merge commit, and current files, rather than remote PR comments or GitHub status badges. No GitHub review, comment, commit, or push was made.

## Execution record

The full library build completed successfully, reporting 8,942 jobs with cache reuse. This is not a claim that all sources were freshly recompiled. The fresh paper audit reported **345 statements, zero failures** (group 09: 24; group 10: 33). The frozen-dependency gate and fingerprint check passed, and the placeholder check was clean. Both independent Lean probe files compiled successfully with the allowed standard axioms.

The **full-library kernel replay completed successfully** in 2,014.61 seconds (about 34 minutes), with exit code zero:

```text
KERNEL REPLAY: modules=244 theorems ok=8567 defs ok=1993 errors=0 []
```

These figures exactly match v6 and Run 026. The additional output lists generated unsafe recursion helpers separately; it reports no project axiom or opaque declaration. As documented by the replay implementation, this checks every project theorem and safe definition against the loaded dependency environment; it is not a rebuild of all mathlib declarations from an empty environment. Companion modules are included in this execution check, while the semantic sign-off remains restricted to the main paper.

The source and artifact hashes in [manifest.json](manifest.json) were checked again after completion: all 259 recorded files were unchanged during validation. Saved execution evidence includes [the full replay output](kernel_replay.log), [command results and timings](results.json), [the paper audit](paper_audit.log), [dependency closure](frozen_deps.log), [literal-probe axiom checks](literal_checks.log), [the appendix probe](appendix_checks.log), and [independent arithmetic results](independent_checks.json). The build log is saved as `build.log`.

## Scope of the conclusion

I find no reason to revert the PR or the fingerprint update. The new target is stronger, correctly proved, and properly connected to the paper and audit. The main-paper appendix correspondence also passes this recheck.

This is not a blanket resolution of unrelated editorial findings from the earlier review. In particular, the abstract still says that all dynamical consequences are new; the previously acknowledged attribution concern is outside this PR and remains open. Nothing about this merge establishes that novelty claim.
