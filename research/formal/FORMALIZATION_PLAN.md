# Lean formalization plan — shift-symmetry paper

Date: 2026-07-24. Toolchain: Lean 4 v4.33.0-rc1 + mathlib (7.8 GB cache,
20-core box; full build of our library $`\approx`$ 30 s incremental). Project:
`research/formal/shiftsym/`. Certification commands (all passing):
`lake build`, `lake build Shiftsym`, `lake env lean Shiftsym/Audit.lean`;
`grep sorry/admit/axiom` clean.

## Phase A — DONE (this session)

Definitions, frozen `Prop` targets, and 6 machine-checked theorems: the
dynamics core (irreversibility in three forms + offset-CA equivariance +
subgroup-level rank monotonicity + symmetric-input existence) and the
fixed-count lemma $`\lvert \mathrm{Fix}(H)\rvert = \lvert A\rvert^{[G:H]} = \lvert A\rvert^{N/\lvert H\rvert}`$.

## Phase B — preliminaries toward the enumeration theorem (est. days)

1. DONE (2026-07-24) — `dvd_pow_of_mem_divisors_rad` (Statement.lean).
2. DONE (2026-07-24) — `isShiftSymmetric_iff_prime_order`
   (Lemmas/Completeness.lean), via `nsmul_self_lat`/`addOrderOf_lat_dvd`
   and an explicit `minFac` construction. Also machine-checked beyond
   plan: trajectory insolvability `iterate_ne_of_not_isShiftSymmetric`
   (C018).
3. DONE (2026-07-24) — `latTorsionEquiv` ($`p`$-torsion $`\simeq_+ (\mathbb{Z}/p\mathbb{Z})^d`$, via the
   elementary embedding $`y \mapsto y.\mathrm{val}\cdot(n/p)`$ at ZMod level; Lemmas/Torsion.lean),
   `card_latTorsion` (= $`p^d`$), `card_addOrderOf_eq_prime` (= $`p^d - 1`$).
   Sub-item 3b DONE (2026-07-24, increment 3): `card_orderP_subgroups`
   = gaussBinom p d 1 (Lemmas/Lines.lean; fiber partition via
   Equiv.sigmaFiberEquiv + Nat.card_sigma; `gaussBinom_geom` /
   `sub_one_mul_gaussBinom` in Statement.lean).
4. DONE (2026-07-24) — `latPrimarySplit` via `ZMod.prodEquivPi` (k-ary CRT
   found in mathlib, Data/ZMod/QuotientRing) + `ZMod.ringEquivCongr`
   (Lemmas/Crt.lean); `prod_primePow_eq`, `primePow_pairwise_coprime`,
   cardinality sanity `card_latPrimarySplit`.

## Phase C — the combinatorial heart (est. 1–2 weeks; main library risk)

5. DONE (2026-07-24, increment 4) — `card_submodule_finrank` = gaussBinom
   p d r (Lemmas/GaussCount.lean): mathlib `card_linearIndependent` +
   span-fibering (`spanMap`/`spanFiberEquiv`, same sigmaFiber pattern as
   the line count) + the $`\mathbb{Z}`$-side identity `gaussBinom_mul_prod_int`
   (double induction, `prod_split` reindexing, closed by
   `linear_combination`) transferred to $`\mathbb{N}`$ (`gaussBinom_mul_prod`) with a
   `gaussBinom_eq_zero_of_lt` guard. Generic form
   `card_finrank_submodule_generic` proved over any finite field. THE
   MAIN LIBRARY-GAP RISK OF THE PLAN IS RETIRED.
6. DONE (2026-07-24, increment 5) — `spanSum_eq_mobius` (Lemmas/
   MobiusSum.lean): $`f(W) = (-1)^{\dim W} q^{\binom{\dim W}{2}}`$, via
   `sum_spanSum_le` (partition recursion over powersets of `linesF`),
   `alt_sum_le` (alternating subspace identity from `card_finrank_le` =
   subLeEquiv + Grassmannian count), `gaussBinom_alt_sum` ($`q`$-binomial
   theorem at $`-1`$ by telescoping), and strong induction on rank. Green on
   first full build after pre-emptive fixes.
7. DONE (2026-07-24, increments 6–7 — Phase D): increment 6 delivered
   the certified IE skeleton `card_shiftSymmetric_IE` (Lemmas/
   Assembly.lean) plus `spanSum_rank_classified`; increment 7 (Phase D2)
   evaluated it. New files: Lemmas/Primary.lean (torsion arithmetic;
   $`\mathbb{Z}`$-Bézout coprime-torsion separation; `card_univ_sup_of_torsion`
   $`\lvert \bigsqcup_i L_i\rvert = \prod_i \lvert L_i\rvert`$ via the summation-hom range/injectivity — no
   primary-decomposition machinery needed), Lemmas/Bridge.lean (the
   `ofMod`/`toMod` dictionary through `AddSubgroup.toZModSubmodule` +
   `latTorsionEquiv` + `MapSubtype`; order/join/⊥/card preservation;
   line ↔ order-p matching; `spanSum_transport`), Lemmas/Evaluate.lean
   (the regrouping chain: empty-set peel → powerset ≃ per-prime tuples
   of powersets via `Finset.sum_nbij'` → fiber over tuples of per-prime
   joins — this tuple-fibering ELIMINATES the projection-uniqueness
   lemma — → `Finset.prod_univ_sum` factorization → fiber over
   `hOf U = ∏ p^{rk}` into the divisor set → factorization bookkeeping
   onto `coeffOf`).

## Phase D — main theorem assembly — DONE (2026-07-24)

8. DONE: **`enumeration_proved : ∀ n d σ, enumerationStatement n d σ`**
   (Lemmas/Evaluate.lean) — the paper's main theorem, machine-checked
   for ALL $`n \ge 2`$, $`d \ge 1`$, $`\sigma \ge 1`$ (every composite $`n`$, every dimension).
   Axioms: propext, Classical.choice, Quot.sound. C001 MACHINE_CHECKED.

## Phase E — lower bound — DONE (2026-08-04)

9. DONE: **`lowerBound_proved : ∀ n d σ, lowerBoundStatement n d σ`**
   (Lemmas/LowerBound.lean) — $`F_d(n,\sigma) \le \lvert S\rvert`$ with equality iff $`n`$ prime,
   for all $`n \ge 2`$, $`d \ge 1`$, $`\sigma \ge 2`$. The formal route is SHORTER than the
   informal one and needs no rectangular tori: with the enumeration
   theorem certified, the prime case is a divisor reindexing
   (Lemmas/PrimeCase.lean: divisors($`p^d`$) $`\leftrightarrow`$ Icc 1 d, coeffOf($`p^r`$) =
   $`(-1)^{r+1} r_d(p,r)`$), and the composite case is the arithmetic chain
   $`F_d \le K\cdot\sigma^{n^{d-1}} < \sigma^{2n^{d-1}} \le \sigma^{n^d/p_1} \le \lvert S\rvert`$ with
   $`K = \binom{d}{1}_n + (d-2)2^d n^{\binom{d}{2}} < 2^{n^{d-1}}`$ (Lemmas/Ineq.lean:
   $`q`$-Pascal bound $`\binom{d}{r}_q \le 2^d q^{r(d-r)}`$, the choose-2 splitting
   identity, $`n^2 \le 2^n`$ and a squared-exponent comparison; the last
   fixed-set inequality reuses `card_fixedByF` + completeness). The
   erratum-repaired published-E.21 import is thereby absent from the
   certified chain.

## STATUS: THE FORMALIZATION PROGRAM IS COMPLETE

Both frozen targets are theorems on the approved axioms
(propext, Classical.choice, Quot.sound; no sorry):
- `enumeration_proved  : ∀ n d σ, enumerationStatement n d σ` (C001)
- `lowerBound_proved   : ∀ n d σ, lowerBoundStatement n d σ`  (C009)

## Policy

- No `sorry`/`admit`/new axioms ever committed; `Audit.lean` prints axiom
  sets and is part of the default build.
- The frozen targets in `Statement.lean` are `def … : Prop` — they assert
  nothing until proved.
- Statement-preservation table updated with every new declaration.
- Priorities follow the two hostile referees' nominated targets
  (round-report-003 addendum); the load-bearing novel step for Part II is
  the rectangular-torus union lemma.
- Realistic total for `enumerationStatement`: 2–6 focused weeks depending
  on the Phase-C library gaps; `lowerBoundStatement` comparable on top.

## Phases F and G (2026-10-10/11)

Phase F certified, among results of follow-up work, the relative enumeration theorem
(`Shiftsym/StatementE1.lean`, `Shiftsym/Lemmas/Relative.lean`), which the paper-wide layer uses
(Theorem 5.1, Appendix A).

> *Public release:* the descriptions of Phases F and G and of the Phase H extension layer concern follow-up work and are omitted. This repository contains the paper and its supplementary material only; see the README at the repository root.

## Phase H — every statement of the paper (2026-10-15/16) — DONE

Goal: Lean coverage of everything the paper states, no shortcuts,
adversarial review after the proofs, and a triple check that every proof is
about the statement it claims. Mapping and procedure:
STATEMENT_PRESERVATION.md § "Phase H".

1. DONE — Scope: all 37 statement environments plus the checkable prose
   claims, split into 11 groups by paper section (`Shiftsym/Paper/Sxx_*.lean`,
   namespaces `ShiftSym.P01` … `ShiftSym.P11`; shared notation in
   `Paper/Common.lean`: `numSS`, `sopfD`, `probUnif`).
2. DONE — Freeze with triple fidelity review (literal / exploit / numeric),
   repair loop until all three reviewers pass; 337 frozen statements; sha256
   recorded before any proof.
3. DONE — Proofs (`Paper/Proofs/Pxx_*.lean`, 35 modules, 13 884 lines). Notable:
   Hall's evaluation of the subgroup-lattice Möbius function on abelian
   $`p`$-groups and the Castillo-Ramirez–Gadouleau formula (§4.3) via mathlib's
   `IncidenceAlgebra.mu`; the §9 detector as an executable Lean function with
   exact worst-case and average-case read counts; the inversion law with
   $`d_c(p) = p \ln 2 + O(1)`$ and an explicit window; Appendix A with real-$`q`$
   Gaussian binomials; the §10 observations as kernel computations (no
   `native_decide`; `maxRecDepth` raised in P11 and P07 caption checks).
4. DONE — Adversarial layer: mechanical gate + hostile proof referee per group
   (all PASS), three fresh paper-to-Lean fidelity reviewers per group (all
   PASS), build-failing environment audit `Shiftsym/AuditPaper.lean`
   (337/337), a kernel replay of the 73 modules present before the extension
   layer (core plus paper layer; 0 errors); the extension layer has not been
   kernel-replayed.
5. Paper-text defects found by the freezing: consolidated in
   `research/formal/PAPER_CORRECTIONS_PROPOSAL.md` (each correction backed by a
   proved theorem; the literal false claims are refuted in Lean).

6. DONE (2026-10-18) — independent review of the Phase H result
   (`research/formal/main_paper_audit/independent_review.md`, response at its end): group 12
   added (`Paper/S12_Necklaces.lean`, the necklace identification of Remark
   4.5, frozen after two review rounds, proved, refereed, triple fidelity
   PASS); statement fingerprints committed (`frozen_statements.sha256`,
   checked by `check_frozen.py`); kernel replay committed
   (`kernel_replay.lean`). After the reviewer's verification of the response
   (2026-10-19): the fingerprints also cover every file a frozen statement
   unfolds to (Definitions.lean, Statement*.lean, six lemma files, toolchain and
   mathlib pins; 31 files), `frozen_deps.lean` computes that closure and fails
   on an unrecorded file, and `kernel_replay.lean` fails on any kernel error or
   project axiom.

7. DONE (2026-10-22) — the window constant 20 of Proposition 10.2 frozen:
   supplement `Paper/S09_CrossoverLaws_Window20.lean` (criteria form,
   probability form, and the proposition as stated in v5; 3 statements), frozen
   after the helpers `window_i`/`window_ii` existed, three fresh fidelity
   reviews PASS (`research/experiments/window20_fidelity/`), then proved in
   `Paper/Proofs/P09_CrossoverLaws_Window20.lean` with non-vacuity witnesses;
   `S09_CrossoverLaws.lean` unchanged; AuditPaper 345/345 (Run 025).

8. DONE (2026-10-27) — the symmetry-breaking clause of Corollary 8.2 frozen:
   the independent judgment of the two open correspondence-audit items
   (`correspondence_audit/independent_judgment/JUDGMENT.md`) found that the
   sentence added in paper v5 ("every … task whose required output breaks a
   symmetry of some admissible input") had no frozen statement and is strictly
   more than `insolvGeneralStatement`. Supplement
   `Paper/S07_Dynamics_SymmetryBreaking.lean` (`RequiresSymmetryBreaking`,
   `insolvSymBreakStatement`, `insolvFullStatement`; 2 statements), frozen after
   a probe proof existed, three fresh fidelity reviews PASS
   (`research/experiments/symbreak_fidelity/`; docstring corrections only
   afterwards, among them the PAPER ISSUE "imprecise wording"), then proved in
   `Paper/Proofs/P07_Dynamics_SymmetryBreaking.lean` with non-vacuity and
   strictness witnesses; `S07_Dynamics.lean` unchanged; paper v7 rewords the
   sentence; AuditPaper 347/347 (Run 027).

Gates now: `lake build` (includes AuditPaper and AuditExt), `lake env lean
Shiftsym/Audit.lean`, `python3 research/formal/check_frozen.py`, `lake env lean ../frozen_deps.lean`, and `python3 research/formal/check_placeholders.py`
(comment-aware replacement for the bare grep, which would match docstring
words such as "admits").
