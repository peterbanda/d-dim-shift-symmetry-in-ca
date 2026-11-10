# Independent review of v10 and v11 — 2026-11-09

> *Public release:* `workspace.json` (temporary build locations) is not exported. This repository contains the paper and its supplementary material only; see the README at the repository root.

**Verdict: no new mathematical error or paper–Lean statement mismatch found in the promoted results. The current release still has one stale hand-audit approval and two small documentation issues. The advertised repository also remains inaccessible anonymously.**

The finite-abelian-group enumeration, strict rank monotonicity, fixed-population extension, free-orbit count, deterministic read lower bound, and v11 torsion-vector-space supplement withstand this review. They are not accepted merely because Lean compiles: their types, definitions, quantifiers, representation changes, and proof dependencies were read against the manuscript, and the new counts were checked independently.

Scope: final v9 `72b60b4` → final v10 `099e022` → v11 `dde222d`; the main v10 addition is commit `140e362`. Public checkout: `6424a78`. Results originally developed as follow-ups are included wherever promoted into the main paper or imported by its proofs. The remaining follow-ups are excluded. Earlier reviews remain the baseline for unchanged mathematics. This review changes only review records and artifacts; no manuscript, PDF, production Lean file, fingerprint record, auditor event, release checkout, commit, push, or repository visibility was changed.

## Findings and remaining actions

### V11-1 — Theorem 4.7 still requires the auditor's current approval

**Priority: release-record action, not a mathematical defect.**

The current viewer bundle is correct, but the latest recorded positive verdict for `thm:abelian` is stale. Its declarations and correspondence changed when v11 added the formal vector-space/dimension supplement. This is not a positional change. The other 26 items have current positive verdicts; no item is unjudged.

`tools/carry_forward.py` in dry-run mode correctly refuses to carry this verdict: “Lean declarations changed; correspondence changed beyond line numbers.” Runs 046–047 already disclose the pending check of `Gp`, `Fp`, and `dp`. The new Lean statement really does cover the intended natural scalar action and dimension; I found no residual semantic gap in those links.

**Action:** after correcting V11-2, rebuild the bundle and have T. Lehman re-check and approve Theorem 4.7 against that bundle. Do not copy its old approval or represent this independent review as his verdict. Section 12, lines 1688–1693, is defensible as a historical description of approvals, but it should not be read as evidence that all 27 approvals cover the final bundle until this is done. If publishing before that recheck, disclose the pending item in the rendered paper rather than only the run log.

Evidence: [bundle reconstruction](bundle_verification.json), [carry-forward history](carry_history.json), current `logs/events.jsonl`, and `data/corr/thm_abelian.json`.

### V11-2 — A viewer explanation still says the newly covered clause is unfrozen

**Priority: low; audit documentation.**

`research/formal/correspondence_audit/data/corr/thm_abelian.json:87`, the last `statement.deltas` entry, still lists “an F_p-vector space” among the unfrozen material. This contradicts the updated summary, earlier delta, actual `Fp` mapping, and new `pTorsionVectorSpaceStatement`.

**Action:** remove that clause from the list of uncovered material, or explicitly state that the historical S13 header is superseded by `S13_AbelianGroups_Torsion`. The old frozen S13 file itself need not change. Make this correction before V11-1's final approval, since correspondence edits change the item hash.

### V11-3 — Narrow the description of Miles and Ward

**Priority: low; manuscript literature wording.**

`shift_symmetry_d_dimensions.tex:250` says Miles and Ward study the counts “without evaluating the Möbius function.” Their Lemma 2 already invokes its elementary-abelian-product support and the product of prime-power coefficients to obtain a bound. The useful distinction is that they do not present this paper's explicit rank-indexed finite-group count, not that they avoid the classical evaluation altogether. See [Miles–Ward, Lemma 2, printed page 4](https://arxiv.org/pdf/0706.3630).

Suggested replacement for the end of that sentence: **“and study the growth of these counts, without reducing them to the explicit rank-indexed formula used here.”** This is an attribution clarification; it changes no theorem, proof, or claimed formula. I have not edited the manuscript.

### V11-4 — Public access remains unresolved

**Priority: release action carried forward from the v9 review.**


**Action:** ensure anonymous access to the final synchronized repository before announcing it as public supplementary material. No visibility change or push was attempted. Evidence: [access check](release_access.json), [export comparison](export_comparison.json).

## Mathematical correspondence review

### Theorem 4.7 and its setting

Read all three new statement files and the ten new proof files, including the arbitrary-weight regrouping, divisor evaluation, quotient counts, rectangular specialization, orbit counts, rank-step algebra, and positivity/existence argument. These total 2,983 added Lean source lines. Every previously existing paper-layer Lean source is byte-identical to final v9; the existing core definitions, statements and lemma files are also unchanged.

The model is substantive: `IsShiftSymmetricG s` means that a nonzero group element fixes the configuration at every cell. `G` is an arbitrary finite additive commutative group, not a supplied torus or a group satisfying the conclusion as an assumption. The alphabet `Fin σ` represents any finite alphabet up to relabeling. The main theorem assumes `σ ≥ 1`, as the manuscript does.

The paper sums over rank vectors. Lean sums over nonunit divisors of `R = ∏ p^{d_p}`. This is a faithful representation: unique prime factorization gives the bijection `v ↔ ∏ p^{v_p}`; deleting divisor 1 removes precisely the zero vector; `bigOmega` gives the sum of exponents; omitted zero coordinates contribute coefficient 1. For actual group ranks, `p^{d_p}=|G[p]|` divides `|G|`; the prime powers are coprime, so `R | N`. Consequently the natural-number quotients used as exponents are exact. The generic vector-to-divisor bridge is not separately frozen as a proposition; the correspondence file discloses that, and the representation was checked here rather than presumed from a green audit.

The proof establishes completeness via prime-order subgroups, identifies their fixed configurations with labelings of quotient cosets, applies inclusion–exclusion, and groups prime-order subgroups by the subspaces they span. The cross-prime subgroup order is proved through an injective summation homomorphism. The Gaussian spanning-set coefficients are evaluated by existing certified results, and the arbitrary-weight identity is specialized to ordinary and fixed-population counts. There is no circular assumption of the enumeration theorem in the final proof: helpers that take it as a hypothesis are instantiated with its proved form.

V11 adds precisely the missing explicit bridge between the numerical rank encoding and the paper's vector-space definition. `pTorsionVectorSpaceStatement` asserts a `Module (ZMod p)` structure on the actual subgroup `{g | p • g = 0}`, specifies `c • g = c.val • g` in the ambient group, and equates its `finrank` with `pRank G p`. Thus it cannot be satisfied merely by choosing an unrelated vector space of the right size. Finiteness makes the dimension meaningful, and primality makes `ZMod p` a field. The proof constructs the natural action and compares the two cardinality powers. This covers every prime, including primes not dividing the group order.

Rectangular specialization includes factors of size 1 and the empty product, but excludes `ZMod 0`, which would be infinite. The original symmetry predicate and cubic enumeration formula are linked by `bridgeStatement` and `squareStatement`. For the trivial group the nonzero-vector sum is empty and the symmetric count is zero, as required; `σ = 1` behaves correctly as well.

### Corollary B.1: the rank increment is genuinely strict

The type correspondence covers all parts:

| Paper claim | Frozen statements |
| --- | --- |
| Dependence only on order and prime ranks | `onlyRanksStatement` |
| The two order-48 examples | `cardTwoPrimeStatement` |
| Exact increment `p^{d_p} ac(G'')` and positive complement | `monotoneStatement` |
| Strictness without having to supply `G''` | `stepStrictStatement` |
| Cyclic group minimizes the count | `cyclicMinStatement` |

The signed q-Pascal identity has the correct exponent and sign. Subtracting the complement sums and shifting the selected coordinate divides the group order by `p`. The proof does not leave `G''` as a potentially nonexistent witness: admissible rank profiles are realized by products of cyclic prime-power groups, and a rank increase at fixed order ensures enough p-power remains after division. Positivity comes from an actual singleton-defect configuration. The trivial-group complement is handled rather than silently assuming another nonzero element.

The paper does not assert uniqueness of the cyclic minimizer in the frozen conclusion; Lean proves the stated non-strict minimum and separately the strict single-rank step. No stronger manuscript assertion has been replaced by a weaker inequality.

### Remark B.2: fixed-population counts and free orbits

`kActiveStatement` counts configurations with exactly `k` occurrences of the distinguished symbol, with `k ≤ N`. Its divisibility filter enforces `h | k`; then the number of fixed configurations is the binomial choice of marked cosets times the choices of other symbols. Under the hypotheses, the natural subtractions and divisions match the paper's integers. The endpoint cases `k=0`, `k=N`, and `σ=1` were checked.

`freeActionStatement` includes preservation of aperiodicity under translation and triviality of each stabilizer. `orbitCountStatement` counts actual sets of translates of aperiodic configurations and proves their count times `N` equals the aperiodic population. The divisibility statement follows. It is not a claim only about all configuration orbits or an arbitrary quotient of the right cardinality.

### Remark 9.4: adaptive read complexity

The six new statements cover reading every cell once, at most `N` reads, at least `N` reads on every constant input, the worst-case lower bound, the one-defect lemma, and the correlation identity.

`ReadTree` branches on the value actually returned by each read. Its path and cost depend on the input; repeated reads are charged again. Correctness is required on every configuration. This captures total deterministic adaptive algorithms in the stated query model; finite input and alphabet sets allow their finite executions to be unfolded into a finite tree. The proof is not restricted to a fixed read order or an algorithm without memory.

If a correct algorithm omits a cell on a constant input, changing only that cell preserves the entire observed path but changes the correct answer. The formal argument proves this indistinguishability, rather than merely displaying two inputs with different symmetry. The upper bound uses an explicit enumeration of all cells and a decision at the leaf. It promises a read bound, not a bound on computation between reads.

The stabilizer/correlation statement uses the original `stab`, natural-number indicator sums, and an equivalence, not just a sufficient condition. Summing over all alphabet symbols counts exactly the matching cells.

### Fourier paragraph and applications

The autocorrelation computation and stated asymptotic comparisons are correct in the arithmetic-operation model. Transforming indicators and inverse-transforming their frequency products computes all correlations; absent symbols contribute zero and at most `min(σ,N)` symbols occur. Separating the `d` transforms along coordinate axes gives the `N log N` factor. The prime-side and growing-dimension comparisons, and the cheaper orbit-walk regimes, have the claimed asymptotic orders.

An exact NTT requires suitable roots of unity and a modulus large enough to recover counts in `[0,N]` (or sufficient CRT moduli). Field setup and bit complexity are not covered by the arithmetic-operation claim. The cited [Pollard paper, §§1 and 3(ii)](https://luca-giuzzi.unibs.it/corsi/Support/papers-cryptography/2004932.pdf) makes these conditions explicit. The Lean header also records the modulus requirement. This paragraph is explicitly excluded from formalization in §11; the numerical FFT check uses floating point with a checked rounding margin, and is not a kernel-certified NTT implementation.

The new materials application correctly uses the finite lattice quotient of a Bravais supercell and Smith normal form to obtain a product of three cyclic factors. A nontrivial translation stabilizer is exactly the extra translational periodicity being counted. Fixed binary composition is covered by Remark B.2(i). The new conclusion sentences restate certified completeness, detection, dynamical rank monotonicity, and dependence on prime ranks. The revised open problem no longer presents rectangular enumeration as unsolved.

## Version, literature and audit-history checks

- Corollary 4.8 with its proof and Remark 4.9 were moved **byte for byte** from final v10 to Appendix B, becoming B.1 and B.2. Their labels persist; the surrounding definition of `ac`, group setting and hypotheses survive the move. The v11 diff explicitly marks the relocation with a note rather than depicting it as deleted mathematics. The v10 diff predates the later affiliation/link edit, as the run log discloses. See [move/source checks](moves_and_existing_sources.json).
- The new attribution to Castillo-Ramirez–Gadouleau is supported by the cited local primary source: Lemma 7(iii) covers abelian p-groups after counting subspaces of the p-torsion; the union-bound proof is in Theorem 5(ii); the proofs of Lemmas 3 and 10 give stabilizer equality/inclusion. Those acknowledgments materially improve v9's presentation.
- The Adamson footnote was checked against the actual [v2 PDF, Theorem 3](https://arxiv.org/pdf/2108.01990v2), including the printed formula visually. Downloaded SHA-256: `be25bb9b34dbd84b13e2523c1cf7be18bf630b5b542cdfebdb3ba1f030cd5212`, identical to Run 037's source. Re-running the full 84-case, 720-reading experiment reproduces zero universally successful readings and a best score of 66/84. Direct subgroup checks here independently support the replacement count. The footnote carefully limits its assertion to readings tried; it does not claim every conceivable repair was excluded. Logs and structured results: [rerun](adamson_rerun.log), [JSON](adamson_rerun.json).
- The new Oh citation has the correct author, title, journal, year and pages in the [publisher record](https://link.springer.com/article/10.1007/s10801-011-0307-3), and its abstract supports the stated general necklace-polynomial context. The full subscription article was not available in this review, so this is not a certification that no equivalent formula appears anywhere in that literature. Delsarte's reference matches the [journal issue record](https://www.jstor.org/stable/i307235), including its printed author initial. General novelty remains a literature judgment, not a consequence of a Lean build.
- Independently reconstructed **all 36 positional carry-forward events** from their historical Git bundles. Each has a matching preceding verdict, identical item TeX, identical declaration text, correspondence identical after removing line positions, and approved current mapping marks. Existing non-extension frozen definitions are unchanged across both carry-forward intervals. The script does not itself protect against arbitrary future changes in surrounding definitions or live sources; source/fingerprint validation remains necessary. No actual inappropriate carry-forward was found in this release. See [checker](check_history.py) and [results](carry_history.json).

## Fresh verification evidence

| Check | Result |
| --- | --- |
| Public source build into an empty project object directory, at most four workers | **89/89 modules compiled** |
| Paper statement/proof/type/axiom audit on those fresh objects | **370/370; zero failures** |
| Kernel replay of the freshly built public root | **89 modules; 3,042 theorems; 809 safe definitions; zero errors** |
| Frozen-statement dependency traversal | **375 statements; 1,171 visited constants; 25 project modules; zero unrecorded** |
| Public frozen-file gate | **28 files; unchanged, complete** |
| Internal frozen-file gate | **38 files; unchanged, complete** (hash check only, not a review of excluded follow-ups) |
| Public placeholder/bypass scan | **Clean** |
| Fresh public export vs. public checkout | **519/519 files identical** |
| Viewer input fingerprints | **189/189 match** |
| Viewer reconstruction | **27 items; 529 mappings; all hashes reproduced** |
| PDF anchoring reconstruction | **577 highlights; 68,243 glyph boxes; word positions and auxiliary labels identical** |
| Minimal source compilation | **TeX + four figures; 28 pages; same word layout as official PDF; no undefined references or Type 3 fonts** |

The source build reuses only the pinned external mathlib/dependency objects; no previously built project object is on the project search path. The replay's listed unsafe implementation companions are compiler-generated executable functions, not unverified theorems; the reported safe definitions and theorem bodies are kernel-replayed. The statement audit checks the allowed axioms. The paper-wide module total is 66 files under `Paper/` plus `AuditPaper.lean`, i.e. **67 modules and 26,955 lines**, consistent with §11.

The independent mathematical checker imports no project evaluator. It enumerates actual subgroup sets and inverts their inclusion poset, then compares with a separately coded Gaussian-product formula. It passed on **86 group presentations**, **258 group/alphabet cases**, **5,973 fixed-k cases**, **127,588 directly enumerated configurations**, **1,905 single defects**, and **958 strict rank steps**. The groups include the trivial group, factors of size 1, mixed prime orders, nonisomorphic groups with equal rank profiles, and elementary abelian rank six. Both order-48 groups give **50,388,256** binary symmetric configurations despite having different subgroup lattices. See [independent checker](check_new_math.py) and [results](independent_math.json). These finite tests supplement the universal proof review; they are not its substitute.

The repository's separate FFT/read experiment also passes on rerun: 1,044 Fourier/definition comparisons, 2,696 one-defect cases, 7,091 proper-read-set cases, and exact adaptive minimax checks through nine binary cells. See [log](fft_detection_rerun.log).

The clean source compile was performed in a temporary directory, without creating a ZIP or changing the official PDF. New theorem, read-complexity and Appendix B pages were visually inspected. The remaining TeX warnings are underfull boxes, bookmark sanitization, and the already recorded 0.70-point overfull box; no new material layout problem was found. This is a local TeX Live check, not a run of arXiv's upload service.

Files in this directory preserve the tested commits and main-paper input hashes, executable checks, and detailed logs. `workspace.json` identifies temporary build locations; recreate those snapshots before rerunning checks that use them. The report does not silently refresh or approve the production audit data.
