# Statement-preservation table (informal ↔ Lean)

The formal statements
must not silently gain or lose hypotheses. Project: `shiftsym/` (Lean 4
v4.33.0-rc1 + mathlib master, pinned by `lean-toolchain` +
`lake-manifest.json`). Date: 2026-07-24.

| Informal (paper / problem.md) | Lean (`ShiftSym.*`) | Notes / deltas |
| --- | --- | --- |
| Lattice $`\mathbb{Z}_n^d`$ | `Lat n d := Fin d → ZMod n` | `n = 0` gives the infinite `ℤ^d` — every cardinality lemma carries `[NeZero n]`; contract excludes $`n = 0`$ anyway ($`n \ge 2`$) |
| Configuration $`s:\mathbb{Z}_n^d\to\Sigma`$ | `Config n d A := Lat n d → A` | alphabet is an arbitrary type `A`; statements use `Fin σ` (WLOG: only $`\lvert\Sigma\rvert`$ enters informally) |
| $`\tau_v s (u) = s(u+v)`$ | `shift v s u = s (u + v)` | identical |
| $`\mathrm{Stab}(s)`$ | `stab s : AddSubgroup (Lat n d)` | carrier = $`\lbrace v \mid \mathrm{shift}\ v\ s = s\rbrace`$; subgroup laws proved, not assumed |
| shift-symmetric ($`\exists v \ne 0`$ fixing $`s`$) | `IsShiftSymmetric` | identical quantifier structure |
| $`\mathrm{Fix}(H)`$ | `fixedBy A H` | identical |
| equivariance $`\Phi\tau_v=\tau_v\Phi`$ | `Equivariant Φ` | identical; `caMap_equivariant` proves the offsets model satisfies it |
| $`\lvert S_{n^d}\rvert`$ | `Nat.card {s : Config n d (Fin σ) // IsShiftSymmetric s}` | `Nat.card` of the subtype; finite for $`\sigma \ge 1`$, $`n \ge 1`$ |
| $`\sum`$ over rank vectors $`0 \prec v \le d`$ | $`\sum`$ over `h ∈ ((rad n)^d).divisors.erase 1` | **reindexing**: bijection $`h = \prod p_i^{v_i} \leftrightarrow (v_i)`$; $`h`$ ranges over divisors of $`\mathrm{rad}(n)^d`$ except 1 $`\Longleftrightarrow`$ $`0 \le v_i \le d`$, $`v \ne 0`$. `coeffOf` recovers $`(-1)^{1+\lvert v\rvert}\prod r_d`$ via `h.factorization`; must be justified once in the eventual proof |
| exponent $`n^d\prod p_i^{-v_i}`$ (exact) | `n ^ d / h` ($`\mathbb{N}`$-division) | exact: `dvd_pow_of_mem_divisors_rad` is now MACHINE_CHECKED, so no truncation can hide (caveat CLOSED 2026-07-24) |
| $`r_d(p,v)=p^{\binom v2}\binom{d}{v}_p`$ | `rdCoeff p v d` with recursive `gaussBinom` | product formula ↔ $`q`$-Pascal recurrence: equivalence is standard; sanity-checked by `rfl` at 7 values and by `#eval` matches of full RHS at 6 reference points |
| $`F_d(n,\sigma)`$ ($`q = n`$ composite allowed) | `lowerEnvelope n dd σ` | same reindexing-free sum over $`r \in [1, d]`$ |
| hypotheses $`n \ge 2`$, $`d \ge 1`$, $`\sigma \ge 1`$ ($`\sigma \ge 2`$ for bounds) | explicit `2 ≤ n → 1 ≤ dd → …` antecedents in the `Prop`s | no hidden strengthening; statements are `def … : Prop`, NOT axioms |

## Item numbers: paper v3.1–v7 versus v8 (2026-11-02)

The frozen Lean files, their docstrings and declaration names (for example `cor44Statement`), this
table and the dated reports cite the item numbers of the paper they were written against. Paper
v3.1 to v7 share one numbering (all 51 labels compile to the same numbers). Paper v8 merged John
Caughman's edits (`research/paper_edits/V8_EDITS.md`), which split two items and swapped two
lemmas. Frozen files are never edited, so read old numbers through this table. Items not listed
keep their numbers, including everything from Section 5 on.

| v3.1–v7 | v8 | Label | Change |
| --- | --- | --- | --- |
| Definition 2.1 (Lattice and configurations) | Definitions 2.1 and 2.2 | — | split: the translation $`\tau_v`$, $`\mathrm{Stab}`$ and (moved from 2.2) $`\mathrm{Fix}(H)`$ form the new Definition 2.2 (Translations acting on configurations) |
| Definition 2.2 (Shift-symmetry) | Definition 2.3 | — | renumbered; $`\mathrm{Fix}(H)`$ moved to Definition 2.2 |
| Definition 2.3 (Equivariant cellular automaton) | Definition 2.4 | `def:ca` | renumbered |
| Remark 2.4 (Equivariance is necessary) | Remark 2.5 | `rem:equivariance-needed` | renumbered |
| Lemma 3.1 (Order of a translation) | Lemma 3.2 | `lem:order` | swapped with the next |
| Lemma 3.2 (Fixed counts and joins) | Lemma 3.1 (Fixed sets and generated subgroups) | `lem:fix` | swapped; retitled |
| Lemma 3.5 (Multi-prime joins) | Lemma 3.5 (Multi-prime generated subgroups) | `lem:joins` | retitled only |
| Lemma 4.1 | Lemmas 4.1 and 4.2 | `lem:mobius`, `lem:mobius2` | split: 4.1 is the chain $`f(V)=\mu(0,V)=(-1)^r p^{\binom r2}`$, 4.2 is eq. (cr) for $`c_r(p)`$ (`lemMobiusCrStatement`; `lemMobiusStatement` is still the conjunction of both) |
| Definition 4.2 (Coefficient function) | Definition 4.3 | `def:coef` (new) | renumbered |
| Theorem 4.3 (Enumeration in $`d`$ dimensions) | Theorem 4.4 | `thm:main-enum` | renumbered |
| Corollary 4.4 (Prime lattices) | Corollary 4.5 | `cor:prime` | renumbered; now states $`d\ge1`$, $`\sigma\ge1`$ itself |
| Remark 4.5 (Attribution and boundary checks), parts (i)–(iii) | Remark 4.6, parts (i)–(v) | `rem:boundary` | renumbered; old (ii) split into new (ii) $`n=1`$ and $`\sigma=1`$, (iii) $`d=1`$ (the necklace identification of group 12), (iv) $`d=2`$; old (iii) is new (v) |
| Lemma 3.3 (Torsion and lines) | Lemma 3.3, parts (i)–(iii) | `lem:torsion` | itemized, same content |

Equation numbers, section numbers and Table 1 are unchanged. The correspondence audit
(`correspondence_audit/data/corr/`) follows v8: `lem_mobius2.json` is the new item.

## Figure numbers: paper v8 versus v9 (2026-11-03)

Paper v9 adds an illustrative Figure 1 in the Introduction and a diagram of the verification
pipeline in Section 11; neither is formalized (Section 11 says so). The three formalized captions
move up by one. Frozen docstrings keep the numbers of the version they were written against (and
some of them already disagree with each other, e.g. `S07_Dynamics.lean` calls `fig:pattern-flip`
"Figure 2", `S11_Numerics.lean` "Figure 1"); identify figures by label. Every other label compiles
to the same number as in v8 (checked by comparing the `.aux` files).

| v8 | v9 | Label | Change |
| --- | --- | --- | --- |
| — | Figure 1 | `fig:examples` | new, illustrative (stabilizers checked by exact computation, Run 030) |
| Figure 1 | Figure 2 | `fig:pattern-flip` | renumbered |
| Figure 2 | Figure 3 | `fig:rate-classes` | renumbered |
| Figure 3 | Figure 4 | `fig:inversion` | renumbered |
| — | Figure 5 | `fig:pipeline` | new, illustrative (verification pipeline) |

## Item numbers: paper v10 versus v11 (2026-11-08)


| v10 | v11 | Label | Change |
| --- | --- | --- | --- |
| — | Appendix B | `app:abelian` | new appendix "Finite abelian groups: dependence on the ranks" |
| Corollary 4.8 | Corollary B.1 | `cor:abelian-ranks` | moved verbatim |
| Remark 4.9 | Remark B.2 | `rem:abelian` | moved verbatim |

Three connecting sentences were added; each restates frozen, proved statements and adds no claim:
after Theorem 4.7 (`onlyRanksStatement`, `stepStrictStatement`, and `cyclicMinStatement` for the
ring versus any torus with the same number of cells), in open problem (2) (`cyclicMinStatement`),
and in the conclusion (S02 `completenessStatement`, S08 `completenessIffStatement` and the detector's
`algorithmSpecStatement`, `scheduleCountStatement`, `detectCorrectStatement`, S07 `rankMonoStatement`,
`rankTrajStatement`, and `onlyRanksStatement`). The sentence after Theorem 4.7 also uses `kActiveStatement` and
`orbitCountStatement` (Remark B.2) and states σ ≥ 2, the hypothesis of `stepStrictStatement` and `cyclicMinStatement`.

## Certified so far (axioms: propext, Classical.choice, Quot.sound only; no sorryAx)

| Lean declaration | Paper result | Claim |
| --- | --- | --- |
| `stab_le_stab_apply` | Thm 8.1 (irreversibility, stabilizer form) | C004 |
| `shift_apply_eq_of_shift_eq` | Thm 8.1 per-vector form | C004 |
| `isShiftSymmetric_apply` | Thm 8.1 set form | C004 |
| `caMap_equivariant` | Def 2.3 (offset CA are equivariant) | C004 hypothesis link |
| `stab_inf_mono` | Prop 8.3, subgroup form | C015 (dimension form still informal) |
| `isShiftSymmetric_const` | Cor 8.2 input-existence half | C018 (half) |
| `card_fixedBy`, `card_fixedBy_div` | Lemma 3.2(i) ($`\lvert\mathrm{Fix}(H)\rvert = \sigma^{N/\lvert H\rvert}`$) | C002/C005 interface |
| `isShiftSymmetric_iff_prime_order` (+ `nsmul_self_lat`, `addOrderOf_lat_dvd`) | Lemma 3.4 (completeness, element form) | C005 (first half) |
| `isShiftSymmetric_iterate` | trajectory preservation | C004/C018 |
| `iterate_ne_of_not_isShiftSymmetric` | Cor 8.2 (insolvability core) | C018 → MACHINE_CHECKED |
| `dvd_pow_of_mem_divisors_rad` | exponent integrality of the frozen statement | closes the $`\mathbb{N}`$-division caveat above |
| `latTorsionEquiv`, `card_latTorsion` | Lemma 3.3 core ($`p`$-torsion $`\cong \mathbb{F}_p^d`$, cardinality $`p^d`$) | C005 (torsion half) |
| `card_addOrderOf_eq_prime` | Lemma 3.3 (order-$`p`$ elements = $`p^d - 1`$) | C005 |
| `latPrimarySplit`, `card_latPrimarySplit` | Lemma 3.5 infrastructure (primary decomposition) | C006 interface |
| `card_orderP_subgroups`, `gaussBinom_geom`, `sub_one_mul_gaussBinom` | Lemma 3.3 line count ($`\binom{d}{1}_p`$ subgroups of order $`p`$) | C005 (completes it → MACHINE_CHECKED) |
| `card_submodule_finrank` (+ generic form, `gaussBinom_mul_prod`, `gaussBinom_eq_zero_of_lt`) | $`\binom{d}{r}_p`$ = #($`r`$-dim subspaces), the Gaussian-binomial interface of Lemma 4.1 | C007 ingredient |
| `spanSum_eq_mobius` (+ `sum_spanSum_le`, `alt_sum_le`, `card_finrank_le`, `gaussBinom_alt_sum`) | Lemma 4.1, the signed spanning-set count (referees' #1 target) | C007 per-subspace form |
| `spanSum_rank_classified` | Lemma 4.1 classified: $`\sum_{\text{rank } r} f(W) = (-1)^r q^{\binom{r}{2}} \binom{n}{r}_q`$ | C007 (span-grouped form) |
| `card_shiftSymmetric_IE` (+ `isShiftSymmetric_iff_mem_biUnion`, `inf'_fixedByF`, `card_fixedByF`, `natCard_shiftSymmetric_eq_filterCard`) | Thm 4.3 proof skeleton: $`\lvert S\rvert`$ as alternating sum over prime-order-subgroup sets | C001 (IE step certified) |
| `latTorsion_mono`, `latTorsion_inf_coprime`, `le_torsion_of_card_prime`, `card_univ_sup_of_torsion` | Lemma 3.5: coprime torsion separation, $`\lvert\bigsqcup_i L_i\rvert = \prod_i\lvert L_i\rvert`$ ($`\mathbb{Z}`$-Bézout) | C006 |
| `ofMod`/`toMod` dictionary (+ inverses, mono, sup/⊥/card preservation), `spanSum_transport` | subgroups $`\le`$ $`p`$-torsion $`\cong`$ submodules of $`\mathbb{F}_p^d`$; Lemma 4.1 transported to the ambient lattice | C005/C007 bridge |
| **`enumeration_proved`** | **Theorem 4.3 (main enumeration), all $`n \ge 2`$, $`d \ge 1`$, $`\sigma \ge 1`$** | **C001 → MACHINE_CHECKED** |
| `gaussBinom_le_pow`, `choose_two_split`, `rdCoeff_le`, `envelope_coeff_lt_two_pow` | coefficient estimates of §6 (sharper $`2^d`$-form of $`\binom{d}{j}_q \le 4q^{j(d-j)}`$) | C009 ingredients |
| `enumerationRHS_prime`, `coeffOf_prime_pow`, `rad_prime` | §6: at prime $`n`$ the formula IS the envelope (divisor reindexing) | C009 (equality half) |
| `card_SS_ge_fix`, `exists_orderP_subgroup`, `lowerEnvelope_le_K`, `lowerEnvelope_lt_card` | §6: one order-$`p_1`$ fixed-set beats the envelope at composite $`n`$ | C009 (strict half) |
| **`lowerBound_proved`** | **Theorem 6.1 (tight lower bound, equality iff prime), all $`n \ge 2`$, $`d \ge 1`$, $`\sigma \ge 2`$** | **C009 → MACHINE_CHECKED** |

Both frozen targets are **PROVED**: `enumerationStatement`
(`enumeration_proved`, 2026-07-24) and `lowerBoundStatement`
(`lowerBound_proved`, 2026-08-04). Delta note for the lower bound: the
formal composite-case proof replaces the informal rectangular-torus
union chain by a direct arithmetic comparison — the STATEMENT proved is
the frozen one, unchanged; only the proof route differs (and eliminates
the published-E.21 import from the certified chain). `Experiments.lean` `#eval`s are display-only
sanity (no axioms): RHS reproduces 8/26/182/72/6398/801064 and
$`F_3(6,2) = 2954937483568`$ — the latter catching a hand-arithmetic typo in a
round-1 note (Python and Lean agree; only a comment was wrong).

## Companion development used by the paper: relative enumeration (2026-10-10)

Frozen in `Shiftsym/StatementE1.lean`, proved in `Shiftsym/Lemmas/Relative.lean`; axioms propext,
Classical.choice, Quot.sound only. The proof of Theorem 5.1 uses the relative enumeration theorem and
proofs in Appendix A use the weight-generic regrouping lemma. The release extracts only this required
interface from the mixed original module; unrelated linear-CA declarations are omitted.

| Informal | Lean (`ShiftSym.*`) | Notes / deltas |
| --- | --- | --- |
| arbitrary finite alphabet $`\Sigma`$, arbitrary subset $`X \subseteq \Sigma^G`$ | `A : Type*` with `[Fintype A]`, `X : Finset (Config n d A)` | strictly more general than the paper's `Fin σ`; `fixedByA A H` is `fixedByF σ H` for `A = Fin σ` |
| $`\mathrm{Fix}(H)`$ as a set of configurations | `fixedByA A H : Finset (Config n d A)` (`Finset.univ.filter (∀ h ∈ H, shift h s = s)`) | `mem_fixedByA : s ∈ fixedByA A H ↔ H ≤ stab s` |
| elementary abelian $`H \le \mathrm{soc}(G)=\bigoplus_p G[p]`$, rank vector $`(r_p)`$ | tuple `U : ModTuple n d` (one subspace `U p ≤ F_p^d` per `p ∈ n.primeFactors`), subgroup `socSub U := ⨆_p ofMod (U p)` | **representation choice**: socle subgroups are indexed by their per-prime components; `U ↦ socSub U` is a bijection onto the elementary abelian subgroups (injective by `ofMod_injective` + coprime torsion separation, `card_univ_sup_of_torsion`); the ranks are `finrank (ZMod p) (U p)` |
| $`c(H) = -\mu(0,H) = (-1)^{1+\sum_p r_p}\prod_p p^{\binom{r_p}{2}}`$ | `mobiusCoeff U := -(∏ p, spanSum (U p))`; closed form `mobiusCoeff_eq` | the definition is the signed spanning-set count (the certified Lemma 4.1 object); Hall's evaluation is the THEOREM `mobiusCoeff_eq`, not an assumption |
| T1a: $`\lvert X\cap S\rvert = \sum_{\emptyset\ne J\subseteq\mathcal L}(-1)^{\lvert J\rvert+1}\lvert X\cap\mathrm{Fix}\langle J\rangle\rvert`$ | `card_filter_shiftSymmetric_IE` | sum over `t : (primeOrderSubs n d).powerset.filter (·.Nonempty)` with `t.1.sup id` for $`\langle J\rangle`$; identical to the certified `card_shiftSymmetric_IE` with `X ∩ ·` |
| T1b: $`\lvert X\cap S\rvert = \sum_{0\ne H\le\mathrm{soc}} c(H)\thinspace \lvert X\cap\mathrm{Fix}(H)\rvert`$ | `relativeEnumerationStatement n d A X` := `((X.filter IsShiftSymmetric).card : ℤ) = ∑ U : ModTuple n d, mobiusCoeff U * ((X ∩ fixedByA A (socSub U)).card : ℤ) + (X.card : ℤ)`; proved by `relativeEnumeration_proved` | **reindexing**: the sum runs over ALL tuples including `U = 0` (which contributes `−\|X\|`, since `socSub 0 = ⊥`, `fixedByA A ⊥ = univ`), compensated by `+ \|X\|`; hypotheses: only `[NeZero n]` (the statement is true for $`n = 1`$ and $`d = 0`$ as well — no `2 ≤ n`, `1 ≤ d` antecedents were needed, a harmless strengthening) |
| weight-generic regrouping | `relative_regroup (w : AddSubgroup (Lat n d) → ℤ)` : `∑_{t nonempty} (−1)^{\|t\|+1} w (t.sup id) = ∑ U, mobiusCoeff U * w (socSub U) + w ⊥` | the Theorem-4.3 chain of Evaluate.lean re-proved once for an arbitrary weight; `card_shiftSymmetric_eq_tuple_sum` is its full-shift instance (consistency with `enumeration_proved`, not a re-proof) |

> *Public release:* the rows of this table for linear cellular automata, the section on extension E2, and the Phase H extension layer (E1/E2) concern follow-up work and are omitted. This repository contains the paper and its supplementary material only; see the README at the repository root.

## Phase H (2026-10-15/16): every statement of the paper


**Scope.** Every theorem, lemma, proposition and corollary of
`shift_symmetry_d_dimensions.tex` (v3.1), every mathematical claim inside its
definitions, remarks and observations (including the exact computations of
§10), the checkable claims of the running text (e.g. the prefactor
comparisons after Theorem 6.3, the polynomiality remark before Theorem 6.1,
the definition of $`\mathrm{sopf}_d`$), the second derivation of §4.3 (Castillo-Ramirez–
Gadouleau Lemma 7(i), multiplicativity of the subgroup-lattice Möbius
function, Hall's evaluation on abelian $`p`$-groups), and the four Appendix A
lemmas of the informal lower-bound proof. Not formalised, by nature: pure
attributions ("is Lemma 7(iv) of [cg2017]"), statistical summaries (the fitted
constant $`C \approx 2.2`$–$`2.65`$ of Observation 10.4), and interpretive sentences — each
is listed as NON-MATHEMATICAL, with its reason, in the header of the frozen
file of its group.

**How the mapping is recorded.** The per-statement table of this document is
replaced, for Phase H, by the frozen statement files themselves: every
`def <X>Statement : Prop` carries a docstring with the paper label and line
numbers, the paper sentence quoted (verbatim in most cases), every
representation choice under "Delta:", and every defect of the paper text under
"PAPER ISSUE:" (in which case the evidently intended corrected claim is frozen
and, where the literal claim is false, its negation is frozen and proved too).
The proof of `<X>Statement` is the theorem `<X>_proved` (same namespace) with
type literally `∀ params, <X>Statement params`.

| Group | Paper range | Frozen statements | Statements | Proof modules (lines) |
| --- | --- | --- | --- | --- |
| 01 Model | Defs 2.1–2.3, Remark 2.4 | `Paper/S01_Model.lean` | 31 | 1 (455) |
| 02 Lattice lemmas | Lemmas 3.1–3.5 | `Paper/S02_LatticeLemmas.lean` | 20 | 1 (501) |
| 03 Möbius, coefficients | Lemma 4.1 (incl. $`\mu(0,V)`$ as mathlib's incidence-algebra Möbius function), Def 4.2, Table 1, Remark "Duality" | `Paper/S03_MobiusCoefficients.lean` | 22 | 1 (362) |
| 04 Enumeration corollaries | Thm 4.3 integrality in rank-vector form, the rank-vector ↔ divisor bridge, Cor 4.4, Remark 4.5, §4.3 second derivation, §4.4 reference values | `Paper/S04_EnumerationCorollaries.lean` | 48 | 6 (2055) |
| 05 k-active | Thm 5.1 with the §5 conventions, $`\sum_k`$ identity, Cor 7.2 (density-uniform distribution as a PMF) | `Paper/S05_KActive.lean` | 31 | 4 (1215) |
| 06 Bounds, probability | Remark 6.2, Thm 6.3 (i),(ii), the prose comparisons, polynomiality, $`\mathrm{sopf}_d`$, Cor 7.1 (with an explicit $`\varepsilon`$–$`M`$ form of the $`o(1)`$) | `Paper/S06_BoundsProbability.lean` | 41 | 4 (1539) |
| 07 Dynamics | Thm 8.1, Cor 8.2 (task/solvability made precise; leader election), Prop 8.3 ($`p`$-rank as an $`\mathbb{F}_p`$-dimension) and its prose | `Paper/S07_Dynamics.lean` | 31 | 2 (524) |
| 08 Detection | the §9 algorithm as a Lean function with read counting; Thm 9.1, Prop 9.2, Remark 9.3 | `Paper/S08_Detection.lean` | 25 | 3 (2070) |
| 09 Crossover laws | Prop 10.1 (bounds, rate, limits), Prop 10.2 (i),(ii), sign/zero of $`\varphi`$, $`d_c = p \ln 2 + O(1)`$, the window | `Paper/S09_CrossoverLaws.lean` | 21 | 2 (816) |
| 10 Appendix A | truncations $`q^m(c)`$, Lemmas A.1–A.4, the $`d \le 2`$ base case | `Paper/S10_AppendixLemmas.lean` | 33 | 5 (1806) |
| 11 Numerics | Obs 7.3, Remark 10.3, Obs 10.4, Obs 10.5 (kernel computations, no `native_decide`) | `Paper/S11_Numerics.lean` | 34 | 6 (2541) |
| 12 Necklaces (2026-10-18) | Remark 4.5(ii): proper powers = words fixed by a nontrivial rotation (set level), primitive-word count, the factor $`n`$ to primitive necklaces, the Moreau–Witt count | `Paper/S12_Necklaces.lean` | 5 | 1 (156) |
| 09 supplement (2026-10-22) | Prop 10.2: the window with the explicit constant 20 (criteria and probability form), and the proposition as stated in v5. Frozen after its helper proof existed; three fidelity reviews PASS (`research/experiments/window20_fidelity/`) | `Paper/S09_CrossoverLaws_Window20.lean` | 3 | 1 (93) |
| 07 supplement (2026-10-27) | Cor 8.2: the symmetry-breaking clause added in v5 ("every … task whose required output breaks a symmetry of some admissible input", in stabilizer form; strictly more than `insolvGeneralStatement`), and the corollary as stated since v5. Frozen after a probe proof existed; three fidelity reviews PASS (`research/experiments/symbreak_fidelity/`) | `Paper/S07_Dynamics_SymmetryBreaking.lean` | 2 | 1 (71) |
| 08 supplement (2026-11-06) | Remark 9.4 (Read complexity, paper v10) and the paragraph after it: with memory for all cells, $`N`$ reads suffice (every cell read once) and, for $`N \ge 2`$, $`\sigma \ge 2`$, are necessary in the worst case — every correct deterministic algorithm, modelled as an adaptive decision tree `ReadTree`, makes at least $`N`$ reads on every constant configuration; the one-defect lemma; the indicator identity for $`\mathrm{Stab}`$. Not frozen: the cited operation counts of the FFT/NTT route and the comparison with Theorem 9.1 that rests on them. Five statements were first frozen and reviewed in the extension layer (group A3, deleted when the remark entered the paper); three fidelity rounds of this file, and a re-review after the text was aligned with the statements as first frozen (Run 036) | `Paper/S08_Detection_Reads.lean` | 6 | 1 (189) |
| 13 Finite abelian groups (2026-11-06) | Section 4.5 (paper v10; in v11 Section 4.5 and Appendix B): the setting (p-ranks, rectangular tori and their order), Theorem 4.7 in divisor form for every finite abelian group and on rectangular tori (`rectEnum`, `rectRank`, `rectCard`), the square torus = Theorem 4.4 (`square`, `bridge`), Corollary 4.8 (only N and the ranks matter, the two-prime example $`\mathbb{Z}_2\times\mathbb{Z}_{24}`$, $`\mathbb{Z}_4\times\mathbb{Z}_{12}`$: 50 388 256 — `cardTwoPrime`, which replaced the 736 example on 2026-11-06, re-frozen before its proof after three fidelity reviews, Run 039 —, the rank-step identity, strict increase, the cyclic group has the fewest), Remark 4.9 (k-active counts, free action, N ∣ σ^N − |S_G|, orbit count); `pRankPow` certifies the p-rank coding. Eleven statements were first frozen, reviewed and proved as extension group A1 (deleted when the section entered the paper); five frozen before their proofs; two fidelity rounds (Run 036) | `Paper/S13_AbelianGroups.lean` | 16 | 8 (2315) |
| 13 supplement (2026-11-08) | Section 4.5, the setting sentence "$`G[p]=\{g\in G: pg=0\}`$, an $`\mathbb{F}_p`$-vector space, and let $`d_p=\dim_{\mathbb{F}_p}G[p]`$": `G[p]` (`pTorsion`) carries the natural `ZMod p`-module structure ($`c \cdot g = c.\mathrm{val} \cdot g`$) and its `finrank` is `pRank G p`. It closes the only link of kind "weaker" in the v10 correspondence audit (Theorem 4.7, mapping `Fp`) and supersedes the "Not frozen" entry for this phrase in group 13's header (that file is unchanged). Frozen before its proof; three fresh-context fidelity reviews (literal, exploit, numeric) PASS; docstring-only re-record afterwards (Run 046) | `Paper/S13_AbelianGroups_Torsion.lean` | 1 | 1 (37) |
| total | | 10083 lines incl. `Paper/Common.lean` | **370** | 48 (16745) |

Line numbers in the docstrings of `Paper/S08_Detection_Reads.lean` and `Paper/S13_AbelianGroups.lean` were corrected
when the two files were re-frozen on 2026-11-06 (Run 036 addendum, Run 039); later edits of the paper may shift them
again. The files are fingerprinted, so the numbers are corrected only at a deliberate re-freeze. The files are fingerprinted, so the
numbers are corrected only at a deliberate re-freeze.

The two main theorems keep their original frozen statements
(`enumerationStatement`, `lowerBoundStatement`); Phase H adds the bridge
`P04.rankVectorReindexStatement` (the paper's rank-vector sum equals the
divisor-indexed `enumerationRHS`), so Theorem 4.3 is now certified in the
paper's own indexing as well.

**Procedure (all four layers of the full suite).**
1. Freeze: one drafter per group wrote the Props before any proof existed,
   with Python brute-force sanity checks; three independent hostile fidelity
   reviewers per group (literal comparison; exploit hunting with concrete
   demonstrations; independent numerical reconstruction from the paper alone)
   rejected and re-reviewed until all three passed (1–4 rounds per group).
   The existing core statements (`Definitions.lean`, `Statement.lean`) and the
   E1/E2 statements were re-reviewed the same way.
2. Prove: proofs in `Paper/Proofs/Pxx_*.lean`; the frozen files are
   sha256-locked (unchanged since freezing).
3. Attack: per group an independent mechanical gate (frozen file unchanged; no
   forbidden token — `sorry`, `admit`, `native_decide`, `axiom`,
   `debug.skipKernelTC`, `run_cmd`, custom `elab`/`macro`, `unsafe`,
   `implemented_by`, `extern`; every module builds; every statement has its
   `_proved` theorem with the exact type; axioms $`\subseteq`$ {propext, Classical.choice,
   Quot.sound}) and a hostile proof referee; then three fresh post-proof
   fidelity reviewers per group working from the paper to the Lean theorems.
   All 11 groups: gate PASS, referee PASS, fidelity 3 × PASS.
4. Whole-development checks: `Shiftsym/AuditPaper.lean` (part of the default
   build) discovers every frozen paper statement from the environment and
   fails the build unless each has its `_proved` theorem with the exact type
   and approved axioms (337/337); a kernel replay re-sent every theorem and
   definition of the 73 `Shiftsym.*` modules present before the extension
   layer (core plus paper layer) to the kernel under fresh names
   (2783 theorems, 717 definitions, 0 errors); the extension layer has not
   been kernel-replayed.

**Paper issues.** The freezing surfaced defects in the paper text (7 FALSE,
6 ILL-POSED, 13 IMPRECISE, plus records and citation details). Each is
recorded at its statement and certified in corrected form; the consolidated,
adversarially checked corrections proposal is
`research/formal/PAPER_CORRECTIONS_PROPOSAL.md`.
