<!-- Applied in paper v4 (2026-10-16): all 32 entries, the new §11, the deletion of Open Problem (3), the title tag and the
introduction sentence; NOT applied: the optional abstract/conclusion sentences and the optional Open Problem (1) rewording. Produced 2026-10-16 from the
Phase H formalization (research/formal/STATEMENT_PRESERVATION.md, section "Phase H"); every corrected
claim is a proved Lean theorem named in its entry. -->

# Corrections proposal for `shift_symmetry_d_dimensions.tex` (v3.1), based on the Phase H formalization

## Summary table

Revision 4 (2026-10-16). Three rounds of independent checker reports (two reports per round) returned FAIL. All findings of round 1 were applied in Revision 2, and all findings of round 2 in Revision 3. All findings of round 3 are applied in Revision 4, and none is rejected. Where the adopted wording differs from a checker's suggestion, a "Checker note" or the Revision 4 table gives the reason (entries 24, 28 and 31, the helper-lemma disclosure, and the title tag). The longer title tag kept in Revision 3 is replaced by the fallback both checkers offered. See "Revision 4", "Revision 3" and "Revision 2" below. Severity legend and conservativeness rule follow the table. "Lean theorem" names the main certificate of the corrected text (fully qualified; see each entry's part (d) for the complete list, helpers and refutations).

| Entry | Severity | Paper line(s) | Lean theorem |
|---|---|---|---|
| 1. Rem. 2.4 — "same from $`n=4`$ on" fails at every prime $`n`$ ($`d=1`$) | FALSE | 245–250 | `ShiftSym.P01.locIff_proved` (refutation `ShiftSym.P01.locFromFourRefuted_proved`) |
| 2. Rem. 4.5(ii) — "words with nontrivial period"; Moreau–Witt counts necklaces | ILL-POSED | 457–459 | `ShiftSym.P04.classicalNonprimitiveCount_proved`, `ShiftSym.P04.remark45d1Count_proved` |
| 3. §4.3 — CG Lemma 7(i) is stated for order $`N\ge2`$ | CITATION | 468–469 | `ShiftSym.P04.cgLemma7i_proved` |
| 4. §4.4 — "41 parameter triples" (29 L1 / 44 in all) | RECORD | 491–495 | none (run log; the formula is `ShiftSym.enumeration_proved`) |
| 5. §4.4 — reference values hold for $`\sigma=2`$ only | IMPRECISE | 496 | `ShiftSym.P04.referenceValues_proved` |
| 6. §5 — scope of the binomial convention breaks Thm 6.1 | ILL-POSED | 523–527 | `ShiftSym.P05.kActive_proved`, `ShiftSym.P05.noFractionalExponent_proved` (refutation `ShiftSym.P05.conventionScopeLiteral_proved`) |
| 7. §5 — 2019 Eq. (29) overstated; Eqs. (32)–(33) misprinted | CITATION | 527–528 | `ShiftSym.P05.banda2019Convention_proved`, `ShiftSym.P05.banda2019Eq29Standard_proved` (refutation `ShiftSym.P05.banda2019Eq32PrintedFalse_proved`) |
| 8. Rem. 6.2 — naive bound is not "the first two terms" | IMPRECISE | 601–603 | `ShiftSym.P06.naiveCoincide_proved` |
| 9. §6.2 — "the prefactor" ambiguous | IMPRECISE | 662–664 | `ShiftSym.P06.evenImprove_proved` |
| 10. §6.2 — restriction $`n\ge4`$ unnecessary (no change) | IMPRECISE | 666–667 | `ShiftSym.P06.e22Sharpen_proved` |
| 11. Cor. 7.2 — $`P^{\mathrm{dens}}`$ never defined in words | IMPRECISE | 694–696 | `ShiftSym.P05.density_proved` |
| 12. Obs. 7.3 — "the same failure" at $`n=10`$ | IMPRECISE | 717 | `ShiftSym.P11.extremaN10_proved` |
| 13. Obs. 7.3 — "state-space effect … once $`d\ge3`$" | ILL-POSED | 719–723 | `ShiftSym.P11.extremaBreaks_proved`, `ShiftSym.P11.inversionD3Scope_proved`, `ShiftSym.P11.compositeAdvantageD2_proved` |
| 14. §8 — "fully $`p`$-periodic" | ILL-POSED | 790 | `ShiftSym.P07.rankFull_proved` |
| 15. §8 — "each level set is an irreversible attractor" | FALSE | 790–791 | `ShiftSym.P07.superlevelInvariant_proved` (refutation `ShiftSym.P07.levelSetInvariantFalse_proved`) |
| 16. §9 — traversal order; early stop unspecified | IMPRECISE | 809, 820–823 | `ShiftSym.P08.detectCorrect_proved` (all variants); `ShiftSym.P08.remPolylogFactorConservative_proved` (the exception) |
| 17. Prop. 9.2 — "orbits visited" for a single subgroup | IMPRECISE | 838–840 | `ShiftSym.P08.detectAvgOrbits_proved` |
| 18. §9 — alphabet of the 2D checks | RECORD | 858–860 | `ShiftSym.P08.avgOrbitsChecked_proved` |
| 19. Rem. 9.3 — polylog figures "hold" for random $`n`$ | FALSE | 864–868 (+130–132) | `ShiftSym.P08.remPolylogRandomN_proved`, `ShiftSym.P08.remPolylogSmooth_proved` |
| 20. Rem. 9.3 — improvement factor exact only for completed walks | IMPRECISE | 868–870 | `ShiftSym.P08.remPolylogFactor_proved`, `ShiftSym.P08.remPolylogFactorConservative_proved` |
| 21. Prop. 10.2 — "unique zero" needs real $`d`$ | ILL-POSED | 945–946 | `ShiftSym.P09.phiSign_proved` |
| 22. Prop. 10.2 — "explicitly bounded window" never explicit | IMPRECISE | 951–953 (+965) | `ShiftSym.P09.inversionExplicitWindow_proved` (the constant 20: helpers `ShiftSym.P09.window_i`, `ShiftSym.P09.window_ii`) |
| 23. Rem. 10.3 — "interpolated" unspecified | IMPRECISE | 969–970 | `ShiftSym.P11.measuredRow_proved` |
| 24. Rem. 10.3 — causal "because" (interpolation claim for $`p\ge5`$ only) | FALSE | 981–982 | `ShiftSym.P11.measuredGapCause_proved`, `ShiftSym.P11.coefficientsFavorPrime_proved` |
| 25. Fig. 3 caption — $`p\ln2`$ is not the linear asymptote (and chart 15's legend: mandatory regeneration) | FALSE | 1000 | `ShiftSym.P11.figInversionAsymptote_proved`, `ShiftSym.P11.dcOffsetLimit_proved` |
| 26. Obs. 10.4 — "least $`d`$" gives $`d^{\ast}=1`$ | ILL-POSED | 1007 | `ShiftSym.P11.dstarClaim_proved` (refutation `ShiftSym.P11.dstarLiteralDegenerate_proved`) |
| 27. Obs. 10.4 — "three unclamped points"; undefined fractional $`d^{\ast}`$ | RECORD | 1013–1015 | `ShiftSym.P11.dstarUnclampedByTheta_proved` (the $`C`$ values are not Lean-checkable) |
| 28. Obs. 10.5(a) — fails at $`(3,4)`$; nearest-prime reading fails; now a theorem | FALSE | 1021–1022 (+884–886, 1004; 1023 recommended) | `ShiftSym.P11.compositeAdvantageD2_proved` (exception `ShiftSym.P11.extremaBoundary_proved`) |
| 29. Obs. 10.5(b) — "for small $`n`$" overstates; $`(p,p-1)`$ never inverts | IMPRECISE | 1022–1023 | `ShiftSym.P11.inversionD3Scope_proved` |
| 30. Rem. (Duality) — "symmetry types" undefined | IMPRECISE | 1029–1030 | `ShiftSym.P03.dualityLattice_proved`, `ShiftSym.P03.dualitySubspace_proved` |
| 31. Table 2 — "typical $`n`$" (consequential to 19) | FALSE | 1130–1131 | `ShiftSym.P08.remPolylogRandomN_proved`, `ShiftSym.P08.remPolylogSmooth_proved` |
| 32. App. A — imported base step; source case split omits prime powers | CITATION | 1325–1327 | `ShiftSym.P10.baseD2_proved` |
| §11 — new Formal-verification section | new text | 1055–1105 | `ShiftSym.enumeration_proved`, `ShiftSym.lowerBound_proved`; `Shiftsym/AuditPaper.lean` (337/337 `X_proved`) |
| Open Problem (3) — resolved, delete | new text | 1161–1165 | `ShiftSym.P05.kActive_proved`, `ShiftSym.P06.upperBounds_proved` |
| Open Problem (1) — partly resolved (optional) | new text | 1157–1158 | `ShiftSym.P11.compositeAdvantageD2_proved`, `ShiftSym.P11.extremaBreaks_proved` |
| Title (fallback wording), introduction, abstract (optional) | new text | 47; 147–151; 84–87 | as §11 |
| Introduction, contribution (iv) (consequential to 19; text under entry 19) | IMPRECISE | 130–132 | `ShiftSym.P08.remPolylogRandomN_proved` |
| Table 2 row "Prime local minima of $`P`$" (optional; consequential to 13 and 28; text under entry 28) | IMPRECISE | 1134–1136 | `ShiftSym.P11.compositeAdvantageD2_proved`, `ShiftSym.P11.extremaBreaks_proved`, `ShiftSym.P11.inversionDeepens56_proved` |

Totals: 7 FALSE, 6 ILL-POSED, 13 IMPRECISE, 3 RECORD, 3 CITATION (32 numbered entries; the rows after entry 32 are new or consequential text and are not counted). Entries 31 and 32 lie partly outside the formalized line ranges (§§2–10 and Appendix A were formalized; Table 2 was not). They are included because they repeat, or depend on, a certified correction.

### Revision 4 (2026-10-16): response to the third pair of checker reports

Checker A (mathematics lens) and checker B (fidelity lens) checked Revision 3 and both returned FAIL, each with one blocking finding: entry 31 for A, and the consequential edits of entry 28 for B. Apart from their findings, both confirmed the proposal. A ran `#check` and `#print axioms` on every cited name (all 97 `_proved` theorems use only the three standard axioms), re-checked the frozen-file checksums, and reproduced the numerical claims with an independent evaluator. B confirmed all 111 cited Lean names and all 127 quoted lines (verbatim, with correct line numbers), and compiled a copy of the paper with every edit applied (20 pages, no errors, no undefined references). Every finding is applied, and none is rejected. Each changed entry has a "Revised after the third checker reports" bullet.

| Finding | Checker | Blocking | Action |
|---|---|---|---|
| 31: "polylog only for polylog-smooth $`n`$" asserts necessity and identifies the exceptional set. Neither is frozen, and the Revision 3 Checker note under entry 19 rejected the same content for contribution (iv) | A, B | A: yes | applied: "polylog only on a set of $`n`$ of density $`0`$ (e.g.\ polylog-smooth $`n`$)". This is A's wording plus B's example, which is the certified sufficiency direction |
| 28: the mandatory edits of line 1004 and the §10 preamble named "one exception". But the deepening of the inversion in Obs. 10.5 is also a universal theorem (`inversionDeepens_proved`), and so are the $`p=3`$ boundary case of Rem. 10.3 (`boundaryCase_proved`) and the corrected Fig. 3 asymptote. The Duality remark after line 1004 is a standard identity, not a computational observation | B (A non-blocking) | B: yes | applied: no exceptions are counted. The computational label now covers only "the observations" (A), and a general clause says that exact claims stated for all parameters are theorems, with named examples (B). A pointer inside Obs. 10.5 states the deepening claim with its quantifiers (recommended). Checker note under entry 28 |
| 25: chart 15 still carries the legend "asymptote $`d_c\approx p\ln2`$" (`compute_dimension_insights.py`, line 198) | B | no | applied: regenerating chart 15 and logging the Run with SHA-256 are now a mandatory part of entry 25 |
| 24: "for $`p\ge5`$" reads as a claim about all primes, but `measuredGapCause_proved` covers only $`p\in\lbrace5,7,11,13\rbrace`$ | A, B | no | applied: "for $`p=5,7,11,13`$" (B's wording). Both checkers found the general claim true numerically (A: every prime $`p < 20000`$; B: every prime $`p\le3000`$), but no theorem certifies it |
| 22: now that the width is the constant 20, "which grows linearly in the prime" can be read as saying that the window grows | A | no | applied: "a dimension that grows linearly in the prime". The docstring of `inversionExplicitWindowStatement` reads "which" as the location $`d_c(p)`$ |
| 6: $`h`$ is used before it is defined | A | no | applied: $`h=h(\mathbf{v})`$ in Theorem 5.1, $`h=\lvert H\rvert`$ in its proof, $`h=1`$ in Corollary 7.2 |
| 2: "$`n`$ times the Moreau–Witt count of primitive necklaces" is not Lean-certified and was not a listed exception; the letter $`m`$ is used twice in one sentence | A, B | no | applied: listed as a bibliographic exception in the conservativeness rule; $`u^j`$, $`j\ge2`$ |
| 1, 12: two added claims are certified only by unfrozen helper lemmas (`const_of_stab_prime`, `p10_lt_p9_d3`) | B | no | applied: disclosed in the conservativeness rule, and one sentence of §11 says so. While applying this, the constant 20 of entry 22 was found to be in the same position (helpers `window_i`/`window_ii`; `inversionExplicitWindowStatement` is $`\exists C`$) and is disclosed too. Entry 13 now also cites the frozen `inversionDeepens56_proved` for $`P(6^d) < P(5^d)`$, $`d\ge3`$, and entry 28 cites the frozen `boundaryCase_proved` for the all-$`\sigma`$ exception $`(3,4)`$ |
| §11: "are proved by exact integer arithmetic checked by the Lean kernel" suggests that the kernel evaluated $`\sigma^{14^9}`$ | A | no | applied: exact integer certificates combined with proved analytic bounds; "no compiled code or floating-point arithmetic is trusted" |
| §11: the audit-module sentence overstates. `AuditPaper.lean` scans only `ShiftSym.P01`–`P11`, and `Audit.lean` lists core, E1 and E2 declarations and never fails the build | B | no | applied (B's wording, slightly adapted) |
| §11 and preconditions 1, 3: if `Shiftsym/Ext/` (statements without proofs, matched by the `Shiftsym.+` glob) is committed, "Every frozen statement X has a theorem X_proved" becomes false | B | no | applied: the sentence is restricted to the core and paper-wide layers, and preconditions 1 and 3 now keep `Ext/` out of the committed library until it is proved. While applying this, the naming was made exact (`XStatement` / `X_proved`) |
| §11 first sentence and title tag: "every numbered statement of this paper" also covers the summary Table 2 (§12), which is not formalized. The title tag lacks "statistical summaries aside" | A, B | no | applied: §11 now speaks of the numbered statements of Sections 2–10 and Appendix A and lists the summary table among the unformalized items. The title tag uses the fallback "post-audit, formally verified in Lean~4". The introduction and the optional abstract sentence are aligned |
| Table 2 row "Prime local minima of $`P`$" is slightly stale after entries 13 and 28 | B | no (optional) | applied as an optional consequential edit under entry 28 |
| Style: "cf.\ " spacing in entry 28; §11's last paragraph omits `Shiftsym/AuditPaper.lean` | B | no | applied |

Adopted with a wording different from the checkers' suggestions (reasons in the entries):
- **Entry 28.** B's line-1004 wording ("The remaining items are computational observations; …") still covers the Duality remark (A's finding), so the adopted text says "observations". Both of B's wordings cite "the first and third claims" of Obs. 10.5; the adopted text names the claims instead, because the ordinal depends on how the corrected sentence is split.
- **Entries 1 and 12.** B offered two options: freeze the helpers in a supplementary statement file, or disclose them. Freezing is not possible within this proposal, which edits no Lean file, so they are disclosed.
- **Title tag.** A's first option ("… all numbered statements (statistical summaries aside) …") would still include the summary Table 2 (B's finding). The fallback that both checkers offered is adopted.

### Revision 3 (2026-10-16): response to the second pair of checker reports

Checker A (mathematics lens) and checker B (fidelity lens) checked Revision 2 and both returned FAIL. A raised two blocking findings and B raised two (entries 24 and 13+29 for A; entries 13 and 28 for B), plus non-blocking ones. Every finding is applied. Two are applied with a different wording than the checker suggested, and the reasons are recorded in "Checker note" bullets. Each changed entry has a "Revised after the second checker reports" bullet.

| Finding | Checker | Blocking | Action |
|---|---|---|---|
| 24: "already gives a zero below $`d_c(p)`$" is false at $`p=3`$ (the interpolated zero equals $`d_c(3)=1`$); `measuredGapCause_proved` covers only $`p\in\lbrace5,7,11,13\rbrace`$ | A, B | A: yes | applied: "for $`p\ge5`$ (at $`p=3`$ both equal $`1`$)" |
| 13, 29: "yet" implies that the pairs $`(p,p-1)`$ invert later, but they never do | A, B | A: yes | applied: "yet" dropped in both places |
| 13: the new text described the window of Prop. 10.2 backwards relative to entry 22 | B | yes | applied: the window clause is removed. B's suggested wording was not used (Checker note under entry 13) |
| 28: Obs. 10.5(a) is now a universal, machine-checked theorem, but line 1004 and the §10 preamble (lines 884–886) still call it empirical | B (A non-blocking) | B: yes | applied: pointer to Section 11 added inside Obs. 10.5(a); the edits to line 1004 and lines 884–886 are now **mandatory** |
| 13: "($`\sigma=2`$)" missing on $`P(5^d) > P(6^d)`$; "Apart from two machine-checked statements" suggests the rest is not machine-checked | A, B | no | applied: B's wording ("two statements that hold for all … — … — these are exact finite computations (all machine-checked …)") |
| 12, 13: notation $`P(n)`$ (fixed $`d`$) mixed with $`P(9^3)`$ in one paragraph | B | no | applied: $`P^{\mathrm{unif}}_{n^d}`$ throughout the inserted sentences |
| 29: alphabet of the $`d=3`$ clause unstated after "for every $`\sigma\ge2`$" | B | no | applied: "($`\sigma=2`$)" |
| 2: Moreau–Witt counts primitive necklaces, not primitive words | A | no | applied: the explicit formula, with "$`n`$ times the Moreau–Witt count of primitive necklaces" |
| 8: "only for $`d\le2`$" needs $`\sigma\ge2`$ | A | no | applied: "($`\sigma\ge2`$)" |
| 19: contribution (iv) of the introduction still says "restated under their actual hypotheses" | B | no | applied, with a narrower wording than B's suggestion (Checker note under entry 19) |
| 15, 19: symbol $`k`$ already means $`\omega(n)`$ and the active-cell count | B | no | applied: $`r`$ in entry 15, $`j`$ in entry 19 (not $`m`$, which is $`N/p`$ in Prop. 9.2 right before Rem. 9.3) |
| §11: "73 modules imported by the root" (the root imports 72; the 73 include the root) | A | no | applied: "the 73 modules reachable from the library's root module (the root included)" |
| §11: replay skipped 6 unsafe compiler auxiliaries | A | no | applied: "every theorem and every safe definition"; detail in the notes |
| §11: "whose type is literally X" for parameterized statements | A | no | applied: "literally X, or $`\forall`$ params, X params"; same fix in the status paragraph and facts table |
| §11: group labels omit the Fig. 1/2/3 captions and the §3-preamble sentence | A, B | no | applied |
| §11: "proof-internal claims are formalized only where the text asserts them" overstates; S06 freezes no proof step of Thm 6.3(ii) | B | no | applied: "(non-proof) prose"; "selected proof-internal claims"; "formalized only selectively" |
| §11: Appendix A uses `relative_regroup`, not `relativeEnumeration_proved` | B | no | applied: theorem for Thm 5.1, regrouping lemma for Appendix A |
| §11: "the text above states the corrected claim" over-reaches (two optional items not adopted) | B | no | applied: restricted to "a mathematical claim" (both items are classified non-mathematical in S06/S07) |
| Introduction: "every mathematical claim of the other numbered statements" claims more than §11 | A | no | applied: "the mathematical content of the other numbered statements (statistical summaries aside)"; the abstract sentence aligned the same way |

Not adopted as suggested (with Checker notes):
- **Entry 13, B's replacement wording for the window** ("its explicit criteria (i) and (ii) apply only for $`d\le d_c(p)-20`$ resp. $`d\ge d_c(p)+20`$, so for small $`p`$ they decide nothing at $`d=3`$"). It would be false. Criterion (ii) of Prop. 10.2 does hold at $`(p,d)=(5,3)`$ for every $`\sigma\ge2`$ (hand check by checker B in round 1 and checker A in round 2: $`\varphi(3)=-8 < -\log_2(72\log_2 6)\approx-7.54`$). The certified window gives *sufficient* conditions for (i) and (ii), and says nothing about where they fail. The clause was removed instead; "consistent with" plus $`d_c(5)\approx2.58`$ carries the content.
- **Introduction contribution (iv), B's wording** ("the bound is polylogarithmic only for $`n`$ with polylogarithmically small prime factors, a set of density zero"). The adopted wording states only the density-zero fact of `remPolylogRandomN_proved`. B's version adds a necessity claim and identifies the exceptional set, and no frozen statement certifies either.
- **Title tag** (line 47): kept as in Revision 2. It is shorthand for the first sentence of the new §11, which is followed there by the statistical-summary exception. A's finding concerned the introduction text, which is aligned. If the authors prefer, the tag can be shortened to "post-audit, formally verified in Lean~4". (Superseded in Revision 4: the shortened tag is now the proposal.)

### Revision 2 (2026-10-16): response to the first pair of checker reports

Checker A (mathematics lens) and checker B (fidelity lens) both returned FAIL. Every finding was applied; none was rejected. Each changed entry has a "Revised after the checker reports" bullet.

| Finding | Checker | Action |
|---|---|---|
| 13: uncertified causal "reason"; "smallest pair"; $`(9,10)`$ omitted; $`(p,p+1)`$ vs $`(p,p\pm1)`$; all-$`d`$ claim before "exact computations, not asymptotic" | A, B | applied: "consistent with", the window described as stated, $`(9,10)`$ added, next sentence rewritten |
| 28: "(at $`p=3`$ the reverse holds)" false, since $`P(2^2) > P(3^2)`$ | A, B | applied: names the exceptional pair $`(3,4)`$; "for every $`\sigma\ge2`$" added; consequential note on line 1004 |
| 7: Eq. (29) also needs annihilation at $`k > n^2`$ | A, B | applied: "needs it only at $`\sigma=1`$" |
| 19: clause about the 2019 figures not certified | A, B | applied: bound-level statement only, with a checked citation link |
| 2: "cyclic words" (necklaces) ambiguous | A | applied |
| 24: "zero of $`\varphi`$ itself below $`d_c`$" contradicts itself | B | applied: the interpolated zero of the bare $`\varphi`$; Prop. 10.1 parenthetical neutralized |
| 27: symbol $`d^{\ast}`$ reused; interpolated quantity unnamed | B | applied |
| 30: hypothesis $`p\mid n`$ missing | B | applied |
| §11: E1 modules uncounted; "73 modules of the library"; walk-variant exception; "one strengthening"; "quotes verbatim"; "Eleven"; `Shiftsym.lean` precondition | A, B | applied (facts table, text, notes, preconditions) |
| Title/introduction/abstract overclaim | A, B | applied: "mathematical content of / every mathematical claim of" |

Not adopted (optional suggestions, not findings): checker B's hand check that criterion (ii) of Prop. 10.2 holds at $`(5,3)`$. It is not frozen in Lean (Checker note under entry 13). Found while applying the reports: the $`d=2`$ prime-dip theorem (`compositeAdvantageD2_proved`) also makes Obs. 7.3's "we know of no proof of either pattern" (entry 13) and Open Problem (1) partly out of date (new optional section below).

Status: proposal only. Neither the paper nor any Lean file has been edited.
Prepared 2026-10-16 from:

- the "PAPER ISSUE" notes in the docstrings of the frozen statement files (the "none" notes are skipped),
- the frozen statement files `research/formal/shiftsym/Shiftsym/Paper/S01_Model.lean` … `S11_Numerics.lean`. Their SHA-256 values were recorded at freezing time and re-verified with `sha256sum -c`.
- the proofs in `research/formal/shiftsym/Shiftsym/Paper/Proofs/`. All 11 group gates PASS (`reports/mygate_01..11.txt`). There are 337/337 statements, each with a `<X>_proved` theorem of type literally `<X>Statement`, or `∀ params, <X>Statement params` for a parameterized statement (the shape `AuditPaper` checks). The axioms are within {propext, Classical.choice, Quot.sound}. The audit module `Shiftsym/AuditPaper.lean` builds. The kernel replay (`reports/kernel_replay.txt`) re-checked all 73 modules reachable from the root module `Shiftsym.lean` (working copy; the root imports 72 modules, and the 73 include the root itself): 2783 theorems and 717 definitions, 0 errors. Six compiler-generated `*._unsafe_rec` auxiliaries were skipped as non-safe; they play no role in soundness.

Line numbers refer to the current `shift_symmetry_d_dimensions.tex` (1456 lines). Lean names are fully qualified. The `ShiftSym.Pxx.<X>_proved` theorems are the gate-audited certificates. A few *helper* theorems are cited where the certificate needed for an exact constant or witness lives one level down. Their axioms are audited through the `_proved` theorem that uses them. Three of them carry details of the replacement texts that no frozen statement covers; they are listed under the conservativeness rule.

Severity legend: **FALSE** means a mathematical claim is false as written. **ILL-POSED** means the text is undefined or ambiguous, so that some reading is false. **IMPRECISE** means the text is true under the evident reading but misleading. **RECORD** marks a factual record of a computation. **CITATION** marks a claim about another paper.

Conservativeness rule applied throughout: every proposed replacement asserts only what a proved Lean theorem certifies. There are a few clearly marked exceptions:
- pure provenance records (entries 4, 18, 27), checked against the repository's run logs;
- two statements about the 2019 source, checked against the 2019 paper (arXiv:1703.09030v2): a verbatim quotation (entry 32), and the statement that the 2019 polylogarithmic figures rest on $`\mathrm{sopf}(n)`$ and $`\mathrm{sopf}_2(n)`$ (entry 19);
- one classical identification attached to a citation (entry 2): the number of primitive words of length $`n`$ is $`n`$ times the Moreau–Witt count $`\frac1n\sum_{m\mid n}\mu(m)\sigma^{n/m}`$ of primitive necklaces. The Lean development has no necklace object. What is certified is the complement formula $`\sigma^n-\sum_{m\mid n}\mu(m)\sigma^{n/m}`$ for the non-primitive words (`ShiftSym.P04.remark45d1Count_proved`). The factor $`n`$ is classical: each primitive necklace of length $`n`$ has exactly $`n`$ distinct rotations (added after the third checker reports, checker A).

Kernel-checked but not frozen (disclosed after the third checker reports, checker B). Three details of the replacement texts are certified by auxiliary theorems of the proof modules, not by frozen statements. They are kernel-checked, and their axioms are audited through the `_proved` theorems that use them. But their statements were not frozen before their proofs were written:
- entry 1: "on $`\mathbb{Z}_p`$, $`p`$ prime, every shift-symmetric configuration is constant" (`ShiftSym.P01.const_of_stab_prime`). The consequence the remark draws, that every location-selecting map on $`\mathbb{Z}_p`$ satisfies Theorem 8.1, is the frozen `ShiftSym.P01.locPrimeThm81_proved`;
- entries 12 and 13: the witness $`P^{\mathrm{unif}}_{9^3} > P^{\mathrm{unif}}_{10^3}`$ (`ShiftSym.P11.p10_lt_p9_d3`). The frozen `extremaN10Statement` says only that $`10`$ is not a local maximum (strict and non-strict), and its docstring deliberately leaves the witness unfrozen;
- entry 22: the explicit constant $`20`$ (`ShiftSym.P09.window_i`, `ShiftSym.P09.window_ii`). The frozen `inversionExplicitWindowStatement` asserts only $`\exists C`$.

Two other details cited from helpers are also covered by frozen statements: $`P^{\mathrm{unif}}_{6^d} < P^{\mathrm{unif}}_{5^d}`$ for all $`d\ge3`$ ($`\sigma=2`$) by the first conjunct of `inversionDeepens56_proved` (entry 13), and $`P^{\mathrm{unif}}_{4^2} < P^{\mathrm{unif}}_{3^2}`$ for every $`\sigma\ge2`$ by `boundaryCase_proved` (entry 28). The new §11 says in one sentence that a few details rest on auxiliary theorems. Freezing the three helpers in a supplementary statement file would be a small addition to the development. It is not done here, because this proposal edits no Lean file.

*Update 2026-10-22:* the constant 20 of entry 22 is now frozen, in the supplementary statement file `Shiftsym/Paper/S09_CrossoverLaws_Window20.lean` (`inversionExplicitWindow20Statement`, `inversionWindow20Statement`, and `inversionLaw20Statement` for Proposition 10.2 as stated in v5). It was frozen after the helpers existed and passed three fresh fidelity reviews; see research/experiments/README.md, Run 025. The helpers of entries 1 and 12–13 are still not frozen.

No replacement text makes a causal claim ("because", "the reason is") unless a theorem certifies it. The one causal phrase that remains, "mainly because of the interpolation itself" (entry 24), is the certified gap decomposition of `measuredGapCause_proved` (the interpolation accounts for at least three quarters of every gap). Entries 13 and 24 were revised for this reason.

Numbers or claims that appear in the frozen docstrings only as Python evidence were deliberately left out of the replacement texts, e.g. Dickman's `ln 2` proportion, `C = 4` for the window, and the fit constants `3.43/2.68/2.61`.

---

### 1. Remark 2.4 — "the conclusion is the same from $`n=4`$ on" (lines 245–250)

- **(a) Severity:** FALSE.
- **(b) Current:**
```latex
245: configuration $(1,1)$ maps to $(1,0)$, which is not shift-symmetric. If
246: one insists that $\eta$ only select \emph{locations} (each cell reads
247: actual cells, just not translation-uniform ones), the conclusion is the
248: same from $n=4$ on: with $d=1$, $n=4$, $\phi=\mathrm{id}$, let every cell
249: read itself except that cell $2$ reads cell $1$; then $(0,1,0,1)$, fixed
250: by the shift $2$, maps to $(0,1,1,1)$, which is not. The two-dimensional
```
- **(c) Proposed** (replace lines 245–250):
```latex
configuration $(1,1)$ maps to $(1,0)$, which is not shift-symmetric. If
one insists that $\eta$ only select \emph{locations} (each cell reads
actual cells, just not translation-uniform ones), equivariance can still
fail on every $\A$, and some location-selecting map breaks irreversibility
exactly when $|\A|=n^d$ is not prime (on $\ZZ_p$, $p$ prime, every
shift-symmetric configuration is constant and is mapped to a constant
one). In $d=1$ the smallest case is $n=4$: with $\phi=\mathrm{id}$, let every cell
read itself except that cell $2$ reads cell $1$; then $(0,1,0,1)$, fixed
by the shift $2$, maps to $(0,1,1,1)$, which is not. The two-dimensional
```
- **(d) Lean:**
  - Corrected text: `ShiftSym.P01.locIff_proved`, which gives the exact range under every reading of "location-selecting" and of "does not support". Also certified:
    - `ShiftSym.P01.locNotEquivariantFromTwo_proved` (equivariance fails on every $`\mathbb{Z}_n^d`$, $`n\ge2`$);
    - `ShiftSym.P01.locPrimeThm81_proved` (full Thm 8.1 on prime cycles; helper `ShiftSym.P01.const_of_stab_prime`);
    - `ShiftSym.P01.locLeastFour_proved` ($`n=4`$ is least in $`d=1`$);
    - `ShiftSym.P01.locExample_proved` (the example).
  - Refutation of the old text: `ShiftSym.P01.locFromFourRefuted_proved` ($`\neg\thinspace \forall n\ge4`$, in its weakest form).
- **(e) Justification:** On $`\mathbb{Z}_5`$, and on every prime cycle, location-selecting maps satisfy the whole of Theorem 8.1. So "from $`n=4`$ on" is false at $`n=5`$. The phenomenon occurs exactly when $`\neg(d=1\wedge n\text{ prime})`$.

### 2. Remark 4.5(ii) — "words with nontrivial period" (lines 457–459)

- **(a) Severity:** ILL-POSED.
- **(b) Current:**
```latex
457: recovers \cite[Thm.~E.19]{banda2019} exactly. $d=1$ recovers the classical
458: count of words with nontrivial period (Moreau--Witt complement
459: \cite{moreau1872,witt1937}).
```
- **(c) Proposed** (replace lines 457–459):
```latex
recovers \cite[Thm.~E.19]{banda2019} exactly. $d=1$ recovers the classical
count of non-primitive words (proper powers $u^j$, $j\ge2$; equivalently,
words, i.e.\ configurations on $\ZZ_n$, fixed by a nontrivial cyclic
rotation), the complement $\sigma^n-\sum_{m\mid n}\mu(m)\,\sigma^{n/m}$
($\mu$ the number-theoretic M\"obius function) of the number of
primitive words, which is $n$ times the Moreau--Witt count of primitive
necklaces \cite{moreau1872,witt1937}.
```
- **(d) Lean:**
  - Corrected text: `ShiftSym.P04.classicalNonprimitiveCount_proved`, `ShiftSym.P04.remark45d1Count_proved`, `ShiftSym.P04.remark45d1Formula_proved`.
  - Refutation of the alternative reading: not formalized. It is hand-checkable: over $`\lbrace a,b\rbrace`$ at $`n=3`$, the words with a period $`t < n`$ in the Lothaire/Fine–Wilf sense are $`aaa,bbb,aba,bab`$ (4), against 2 non-primitive words.
- **(e) Justification:** In combinatorics on words a "period" need not divide $`n`$, and under that standard meaning the count differs from the Moreau–Witt complement (e.g. 4 vs 2 at $`n=3`$, $`\sigma=2`$). Only the parenthetical fixed the intended meaning.
- **Revised after the checker reports:** the gloss no longer says "cyclic words". In combinatorics on words a cyclic word is usually a conjugacy class (necklace), and non-primitive necklaces are counted differently: 3 classes against $`\lvert S_4\rvert=4`$ words at $`n=4`$, $`\sigma=2`$. The Lean object (`numSS n 1 σ`) counts words on $`\mathbb{Z}_n`$, which is what the new gloss says.
- **Revised after the second checker reports:** checker A pointed out that the Moreau (1872) and Witt (1937) formula $`\frac1n\sum_{m\mid n}\mu(m)\sigma^{n/m}`$ counts primitive *necklaces* (Lyndon words), while the number of primitive *words* is $`n`$ times that. So "the complement of the Moreau–Witt count of primitive words" assigned the wrong object to Moreau–Witt. The new text writes the complement explicitly, $`\sigma^n-\sum_{m\mid n}\mu(m)\sigma^{n/m}`$. This is literally `moreauWittComplement n σ` in `remark45d1CountStatement` (S04, line 373), and the text relates it to the Moreau–Witt necklace count correctly. Checker A's brute force confirms 4 vs 2 at $`n=3`$ and 3 necklaces vs 4 words at $`n=4`$. The symbol $`\mu`$ is glossed because the paper otherwise uses $`\mu`$ for lattice Möbius functions $`\mu(\cdot,\cdot)`$ (lines 358, 471).
- **Revised after the third checker reports:** the exponent of the proper powers is now $`j`$ (checker B), because $`m`$ is the summation index of the Möbius sum in the same sentence. Checker A noted that "$`n`$ times the Moreau–Witt count of primitive necklaces" is true (classical) but not Lean-certified, since S04 has no necklace object. It is now listed as a bibliographic exception in the conservativeness rule.

### 3. §4.3 — scope of the cited CG Lemma 7(i) (lines 468–469)

- **(a) Severity:** CITATION.
- **(b) Current:**
```latex
468: Castillo-Ramirez and Gadouleau \cite[Lemma~7(i)]{cg2017} show that for any
469: finite group $G$ of order $N$ and $|A|=q\ge2$, the number of aperiodic
```
- **(c) Proposed** (line 469):
```latex
finite group $G$ of order $N\ge2$ (for $N=1$ the formula is trivial) and $|A|=q\ge2$, the number of aperiodic
```
- **(d) Lean:** `ShiftSym.P04.cgLemma7i_proved` (proved for every finite group, including $`N=1`$).
- **(e) Justification:** Castillo-Ramirez–Gadouleau state Lemma 7 for groups of order $`\ge2`$. The paper's broader attribution is true but is not what they prove.

### 4. §4.4 — record of the verification run, "41 parameter triples" (lines 491–495)

- **(a) Severity:** RECORD.
- **(b) Current:**
```latex
491: against (L1) definition-level brute force over all $\sigma^{n^d}$
492: configurations and all nonzero shifts, and (L2) an independent
493: inclusion--exclusion over all subsets of brute-force-discovered prime-order
494: subgroups with BFS subgroup closures, on 41 parameter triples covering
495: $d\le4$, $n\le60$ (including the multi-prime $n=6,10,12,15,30,60$ and
```
- **(c) Proposed** (replace lines 491–495):
```latex
against (L1) definition-level brute force over all $\sigma^{n^d}$
configurations and all nonzero shifts, on 29 parameter triples (all with
$n^d\le16$), and (L2) an independent
inclusion--exclusion over all subsets of brute-force-discovered prime-order
subgroups with BFS subgroup closures, on these and 15 further triples
(44 in all), covering
$d\le4$, $n\le60$ (including the multi-prime $n=6,10,12,15,30,60$ and
```
- **(d) Lean:** No theorem certifies a run log. The formula itself is the certified `ShiftSym.enumeration_proved`, which makes the record pure provenance. Source of the record: `research/experiments/verify_output.txt` (Run 001, sha256 `cbb95b79…`). Section [2] holds 29 L1=L2=L3 triples, all with $`n^d\le16`$. Section [3] holds 18 L2=L3 triples, 3 of them repeats, so 15 are new: 44 distinct in all. I re-counted this today.
- **(e) Justification:** The log does not support "41 triples, each checked by L1 and L2": L1 ran on 29 triples, and the union is 44. Consequential: the Run 001 entry of `research/experiments/README.md` ("L1=L2=L3 on 41 cases") needs the same correction.

### 5. §4.4 — reference values without alphabet size (line 496)

- **(a) Severity:** IMPRECISE.
- **(b) Current:**
```latex
496: prime powers $4,8,9$), and $\sigma\le4$; reference values include
```
- **(c) Proposed:**
```latex
prime powers $4,8,9$), and $\sigma\le4$; reference values ($\sigma=2$) include
```
- **(d) Lean:** `ShiftSym.P04.referenceValues_proved` (all six values at $`\sigma=2`$; e.g. `ShiftSym.P04.refValue22_proved`).
- **(e) Justification:** The values hold only for $`\sigma=2`$. For example $`\lvert S_{2^2}\rvert=21`$ at $`\sigma=3`$ (`verify_output.txt`, L1).

### 6. §5 preamble — scope of the binomial convention (lines 523–527)

- **(a) Severity:** ILL-POSED.
- **(b) Current:**
```latex
522: Fix a state $a\in\Sigma$ and let $S^a_{n^d,k}$ be the set of
523: shift-symmetric configurations with exactly $k$ cells in state $a$. Here
524: and below, $\binom xy:=0$ whenever $y$ is not an integer in
525: $\{0,\dots,x\}$; a vanishing binomial annihilates its whole summand (so
526: the accompanying factor with fractional exponent never occurs), and
527: $0^0:=1$ (relevant only at $\sigma=1$, $k=N$). This convention is also
```
- **(c) Proposed.** In lines 523–527, replace the fragment from "Here and below," up to "(relevant only at $`\sigma=1`$, $`k=N`$)." with:
```latex
In Theorem~\ref{thm:kactive}, its proof, and
Corollary~\ref{cor:dens} (with $h=h(\vv)$ in Theorem~\ref{thm:kactive},
$h=|H|$ in its proof, and $h=1$ in Corollary~\ref{cor:dens}),
$\binom{N/h}{k/h}:=0$ whenever
$k/h$ is not an integer in $\{0,\dots,N/h\}$, and such a vanishing
binomial annihilates its
whole summand (so the accompanying factor with fractional exponent never
occurs); all other binomial coefficients are the ordinary ones, and
$0^0:=1$ (relevant only at $\sigma=1$, $k=N$).
```
- **(d) Lean:**
  - Corrected text: `ShiftSym.P05.noFractionalExponent_proved`, `ShiftSym.P05.fractionalExponentArises_proved`, `ShiftSym.P05.zeroPowRelevance_proved`, `ShiftSym.P05.fixKCount_proved` and `ShiftSym.P05.kActive_proved`. All of these encode exactly this scope. The intended $`F_d`$ is `ShiftSym.lowerBound_proved`.
  - Refutation of the literal scope: `ShiftSym.P05.conventionScopeLiteral_proved`. Read with "Here and below", $`\binom12=0`$ annihilates the $`r=1`$ summand of $`F_d`$, the envelope drops strictly below $`\lvert S\rvert`$ at every prime, and Theorem 6.1 becomes false (e.g. $`F^{\mathrm{lit}}_1=0 < 2=\lvert S_2\rvert`$).
- **(e) Justification:** As worded, the annihilation clause also governs $`n^{\binom r2}`$ in Theorem 6.1, Lemma A.2 and the Möbius values. There it makes Theorem 6.1 false (certified). It would also wipe out the $`r=1`$ summand behind "$`d=2`$ is Lemma E.21" and the $`r_d(p,1)\ge1`$ step of Lemma A.3. Restricting the scope removes this and changes nothing inside Theorem 5.1 or Corollary 7.2.
- **Revised after the third checker reports:** the scope sentence used $`h`$ before defining it (checker A). It now says what $`h`$ is in each of the three places: $`h(\mathbf{v})`$ in Theorem 5.1, $`\lvert H\rvert`$ in its proof, and $`1`$ in Corollary 7.2, whose formula has $`\binom Nk`$. Checker A also confirmed the mathematics, including that the literal old scope breaks Theorem 6.1, and even the factor $`r_d(p,1)`$ of Theorem 5.1, through $`\binom12=0`$.

### 7. §5 preamble — what Eqs. (29)–(33) of [banda2019] require (lines 527–528)

- **(a) Severity:** CITATION. Eqs. (32)–(33) of the 2019 paper are false as printed.
- **(b) Current:** the sentence "This convention is also implicitly required by Eqs.~(29)--(33) of \cite{banda2019}." in
```latex
527: $0^0:=1$ (relevant only at $\sigma=1$, $k=N$). This convention is also
528: implicitly required by Eqs.~(29)--(33) of \cite{banda2019}.
```
- **(c) Proposed** (replace that sentence):
```latex
This convention is also implicitly required by Eqs.~(30)--(33) of
\cite{banda2019} (Eq.~(29) needs it only at $\sigma=1$); in
Eqs.~(32)--(33) there, the factors $r(i)$ must be built from the primes
$r_i$ of $\gcd(k,n)$ rather than from the primes $p_i$ of $n$ (as printed,
with the primes in increasing order, both equations give $36$ at $n=6$,
$k=3$, $\sigma=2$, whereas $|S^a_{6^2,3}|=48$).
```
- **(d) Lean:**
  - What is required: `ShiftSym.P05.banda2019Needs_proved`, `ShiftSym.P05.banda2019Eq29Needs_proved` and `ShiftSym.P05.banda2019Eq29Standard_proved`. The last shows that for $`\sigma\ge2`$, Eq. (29) needs no part of the convention.
  - Corrected Eqs.: `ShiftSym.P05.banda2019Valid_proved`, including `ShiftSym.P05.banda2019Eq32Valid_proved` and `ShiftSym.P05.banda2019Eq33Valid_proved`.
  - Refutation as printed: `ShiftSym.P05.banda2019Eq32PrintedFalse_proved` and `ShiftSym.P05.banda2019Eq33PrintedFalse_proved`. Both are robust over every labelling of the primes; the witness is $`n=6`$, $`\sigma=2`$, with values $`36`$ vs $`48`$ via `numKActive_6_3`.
  - Whole sentence: `ShiftSym.P05.banda2019Convention_proved`.
- **(e) Justification:** Eq. (29) assumes $`\lvert\langle v\rangle\rvert\mid k`$, so it never meets a non-integer index. It invokes the convention only at $`\sigma=1`$, in two ways: through $`0^0:=1`$ at $`k=n^2`$, and, because it is stated for every $`k\in\mathbb N`$, through the annihilation of $`0`$ raised to a negative power at $`k > n^2`$. Both are recorded in the docstrings of `banda2019Eq29NeedsStatement` and of `banda2019ConventionStatement` (PAPER ISSUE 1). For $`\sigma\ge2`$ it needs nothing (`banda2019Eq29Standard_proved`). Eqs. (32)–(33), the 2019 Thm E.32, use the wrong primes and are false as printed, so the paper should not vouch for them unqualified.
- **Revised after the checker reports:** the earlier parenthetical "(Eq.~(29) needs only $`0^0:=1`$, at $`\sigma=1`$)" left out the $`k > n^2`$ case and so overstated what is certified. The new wording, "needs it only at $`\sigma=1`$", is exactly `banda2019Eq29Needs_proved` plus `banda2019Eq29Standard_proved`.
- **Consequential notes:**
  - Table 2 row "$`k`$-active counts & Thm.~E.32" (line 1122) may add "(with $`r(i)`$ as corrected in Section~\ref{sec:kactive})".
  - The misprint, and the 2019 range typo "$`k\le n`$" for "$`k\le n^2`$" in Eq. (30)/Thm E.32 (`ShiftSym.P05.banda2019Eq30Valid_proved` is stated for $`k\le n^2`$), are not yet in the companion erratum `research/2d_fix_note/banda2d_bounds_fix.tex`.

### 8. Remark 6.2 — "not its first two terms" (lines 601–603)

- **(a) Severity:** IMPRECISE.
- **(b) Current:**
```latex
601: $|S_{2^3}|\ge100$, while $|S_{2^3}|=72$. For prime $n$ the true count is
602: the full alternating sum of Corollary~\ref{cor:prime}, not its first two
603: terms; only for $d\le2$ do the two coincide.
```
- **(c) Proposed** (replace lines 601–603):
```latex
$|S_{2^3}|\ge100$, while $|S_{2^3}|=72$. For prime $n$ the true count is
the full $d$-term alternating sum of Corollary~\ref{cor:prime}, which
agrees with the naive two-term expression only for $d\le2$ ($\sigma\ge2$).
```
- **(d) Lean:** `ShiftSym.P06.naiveCoincide_proved`, `ShiftSym.P06.primeCountFullSum_proved`, `ShiftSym.P06.naiveCounterexample_proved`. The other reading (sum vs its two-term truncation) is also certified: `ShiftSym.P06.truncationCoincide_proved`.
- **(e) Justification:** The naive bound's second term is $`-\sigma(\binom{d}{1}_p-1)`$, not the $`r=2`$ term $`-p\binom{d}{2}_p\sigma^{p^{d-2}}`$, so "its first two terms" misdescribes it. Both coincidence statements are true.
- **Revised after the second checker reports:** "($`\sigma\ge2`$)" added (checker A). At $`\sigma=1`$ both sides equal $`1`$ for every $`d`$, and `naiveCoincideStatement` assumes `2 ≤ σ`.

### 9. §6.2 comparison — "improves the prefactor further" (lines 662–664)

- **(a) Severity:** IMPRECISE.
- **(b) Current:**
```latex
662: ties $N-1$, and for $n\in\{3,4\}$ the two are comparable); for even
663: $n\ge4$ and $d\ge2$, the closed form (ii) improves the prefactor further
664: to $2^d-1+2\log_2 n$. (For odd $n$ the exponent $N/p_1\le N/3$ of (i) is
```
- **(c) Proposed:** replace "the closed form (ii) improves the prefactor further to $`2^d-1+2\log_2 n`$" with
```latex
the closed form (ii) improves the prefactor $2\log_2(n)\,n^{d-1}$
further to $2^d-1+2\log_2 n$
```
- **(d) Lean:** `ShiftSym.P06.evenImprove_proved` (strictly below both $`2\log_2(n)n^{d-1}`$ and $`N-1`$, with $`p_1=2`$).
- **(e) Justification:** The preceding clause names the union prefactor $`\mathrm{sopf}_d`$, and against that prefactor the claim is false (e.g. $`\mathrm{sopf}_d(4)=2^d-1 < 2^d+3`$, hand-checkable), so the comparison must be named.

### 10. §6.2 comparison — "For $`d=2`$ and $`n\ge4`$, (ii) also slightly sharpens …" (lines 666–667)

- **(a) Severity:** IMPRECISE (misleading, not false).
- **(b) Current:**
```latex
666: For $d=2$ and $n\ge4$, (ii) also slightly sharpens the
667: $6\log_2(n)\sigma^{n^2/2}$ of \cite[Lemma~E.22]{banda2019}.
```
- **(c) Proposed:** **no change.** The sentence is certified as written. Dropping "$`n\ge4`$" would be true, since $`3+2\log_2 n < 6\log_2 n`$ for $`n > 2^{3/4}`$, but it is not certified as a strict inequality for $`n\in\lbrace2,3\rbrace`$. The helper `ShiftSym.P06.closed_le_e22` is only non-strict for $`n\ge2`$.
- **(d) Lean:** `ShiftSym.P06.e22Sharpen_proved` (as written) and `ShiftSym.P06.e22Bound_proved`.
- **(e) Justification:** Recorded so that the authors know the restriction is unnecessary; a certified change would need one more small lemma.

### 11. Corollary 7.2 — $`P^{\mathrm{dens}}`$ never defined (lines 694–696)

- **(a) Severity:** IMPRECISE.
- **(b) Current:**
```latex
694: Let $\sigma\ge2$. Under the density-uniform distribution (first draw
695: $k\in\{0,\dots,N\}$ uniformly, then a configuration with exactly $k$
696: cells in state $a$ uniformly),
697: \[
698:     P^{\mathrm{dens}}_{n^d} \;=\; \frac{1}{N+1}\sum_{k=0}^{N}
```
- **(c) Proposed** (line 696):
```latex
cells in state $a$ uniformly), the probability that the drawn configuration lies in $S_{n^d}$ is
```
- **(d) Lean:** `ShiftSym.P05.density_proved`, `ShiftSym.P05.densityClosed_proved` (the distribution is a mathlib `PMF`; $`P^{\mathrm{dens}}`$ is the probability of $`S_{n^d}`$).
- **(e) Justification:** The formula is correct, but the quantity it computes was only implicit.

### 12. Observation 7.3 — "the same failure occurs at $`n=10`$" (line 717)

- **(a) Severity:** IMPRECISE.
- **(b) Current:**
```latex
716: so the prime $5$ is not a local minimum and the composite $6$ is not a
717: local maximum; the same failure occurs at $n=10$ and persists at $d=4$.
```
- **(c) Proposed** (line 717):
```latex
local maximum; likewise the even $n=10$ is not a local maximum
($P^{\mathrm{unif}}_{9^3}>P^{\mathrm{unif}}_{10^3}$), and all three
failures persist at $d=4$.
```
- **(d) Lean:** `ShiftSym.P11.extremaN10_proved` (helper witness `ShiftSym.P11.p10_lt_p9_d3`; the witness is kernel-checked but not frozen, see the conservativeness rule) and `ShiftSym.P11.extremaD4_proved`.
- **(e) Justification:** 10 is composite, so "the same failure" can only be the "even $`n`$ is not a local maximum" half, and its witness is $`P(9^3) > P(10^3)`$. Read as "a prime fails to be a local minimum", it would be mis-stated.
- **Revised after the second checker reports:** the paragraph writes $`P(n)`$ at fixed $`d`$ ($`P(3)=26/2^9`$, $`\log_{10}P(5)`$), under which "$`P(9^3)`$" would mean $`n=729`$ (checker B). The inserted sentences of entries 12 and 13 now use the paper's standard notation $`P^{\mathrm{unif}}_{n^d}`$ throughout.

### 13. Observation 7.3 — "The reason is the state-space effect …" (lines 719–723)

- **(a) Severity:** ILL-POSED. It names no precise comparison, and read as a statement about the pattern's composites, "once $`d\ge3`$" is false.
- **(b) Current:**
```latex
719: The reason is the state-space effect: relative to lattices with the same
720: cell count, the composite's extra symmetric configurations are
721: exponentially outweighed once $d\ge3$. These are exact computations, not
722: asymptotic claims; we know of no proof of either pattern as a theorem for
723: general $n$.
```
- **(c) Proposed** (replace lines 719–723; this relies on entry 28 for Observation 10.5):
```latex
This is consistent with the inversion law
(Proposition~\ref{prop:inversion}): for the pair $(5,6)$ of the pattern,
$d_c(5)\approx2.58$, and indeed
$P^{\mathrm{unif}}_{5^d}>P^{\mathrm{unif}}_{6^d}$ for every $d\ge3$
($\sigma=2$), which already breaks the pattern (as does
$P^{\mathrm{unif}}_{9^3}>P^{\mathrm{unif}}_{10^3}$), while at $d=3$
($\sigma=2$) no pair $(p,p\pm1)$ with $7\le p\le23$ is inverted. Apart
from two statements that hold for all $d\ge3$ ($\sigma=2$), resp.\ for
all primes $p\ge5$ and all $\sigma\ge2$ --- the inequality
$P^{\mathrm{unif}}_{5^d}>P^{\mathrm{unif}}_{6^d}$ above, and, at $d=2$,
$P^{\mathrm{unif}}_{p^2}<P^{\mathrm{unif}}_{(p\pm1)^2}$
(Observation~\ref{obs:inversion}) --- these are exact finite computations
(all machine-checked, Section~\ref{sec:formal}), not asymptotic claims;
we know of no proof of the even-peak pattern as a theorem for general $n$.
```
- **(d) Lean:**
  - `ShiftSym.P11.dcRow_proved` ($`d_c(5)`$ rounds to $`2.58`$).
  - `ShiftSym.P11.extremaBreaks_proved` (helper `ShiftSym.P11.p6_lt_p5_all`: $`P(6^d) < P(5^d)`$ for all $`d\ge3`$, $`\sigma=2`$). The inequality is also frozen, as the first conjunct of `ShiftSym.P11.inversionDeepens56_proved`.
  - `ShiftSym.P11.extremaN10_proved` (helper `ShiftSym.P11.p10_lt_p9_d3`: $`P(10^3) < P(9^3)`$; the witness is kernel-checked but not frozen, see the conservativeness rule).
  - `ShiftSym.P11.inversionD3Scope_proved` (at $`d=3`$, $`\sigma=2`$, only $`(3,4)`$ and $`(5,6)`$ are inverted among the pairs $`(p,p\pm1)`$ with $`3\le p\le23`$).
  - The other claims of Obs. 7.3 ("all machine-checked"): `ShiftSym.P11.extremaD2_proved`, `ShiftSym.P11.extremaD3Values_proved`, `ShiftSym.P11.extremaD4_proved`, `ShiftSym.P11.extremaBoundary_proved` (with `extremaN10_proved` above).
  - `ShiftSym.P11.compositeAdvantageD2_proved` ($`d=2`$: $`P(p^2) < P(c^2)`$ for every prime $`p\ge5`$, composite $`c=p\pm1`$, $`\sigma\ge2`$).
  - "Consistent with": the sign of $`\varphi`$ (`ShiftSym.P09.phiSign_proved`, negative for real $`d > d_c(p)`$) and the inequality above go in the same direction. Nothing more is claimed.
  - No causal statement is certified. Neither the old "state-space effect" nor a causal link to Proposition 10.2 is frozen (the `obsExtremaStatement` docstring classifies the "reason" sentence as a PAPER ISSUE and leaves it out), so the replacement says "consistent with", not "the reason".
- **(e) Justification:** The lattices compared ($`p^d`$ vs $`(p\pm1)^d`$) do not have equal cell counts. At $`d=3`$ every prime $`7\le p\le23`$ is still below both composite neighbours, so the pattern breaks through $`(5,6)`$ and through the composite pair $`(9,10)`$, not through a general loss of the composite advantage. The certified window of Proposition 10.2 (`ShiftSym.P09.inversionExplicitWindow_proved`, constant 20) does not reach $`d=3`$: for every $`p\le31`$, $`d=3`$ lies strictly inside $`(d_c(p)-20,\thinspace d_c(p)+20)`$, so the new text does not mention the window. For $`p\ge5`$ the pairs $`(p,p-1)`$ never invert, at any $`d\ge1`$ and $`\sigma\ge2`$, because $`P^{\mathrm{unif}}_{(p-1)^d}\ge\sigma^{-(p-1)^d/2} > \binom{d}{1}_p\thinspace \sigma^{p^{d-1}-p^d}\ge P^{\mathrm{unif}}_{p^d}`$ (one order-2 subgroup on the left, the union bound over the $`\binom{d}{1}_p`$ order-$`p`$ subgroups on the right; recorded in the `inversionDeepensStatement` docstring, not frozen as a theorem). So the text says "is inverted", not "is yet inverted". The last sentence must change as well. Read after this entry and entry 28, the old "exact computations, not asymptotic claims; we know of no proof of either pattern" would contradict two certified statements for all $`d`$, resp. all $`p`$, that the corrected paper itself makes.
- **Revised after the checker reports:** both checkers rejected the earlier replacement ("The reason is the inversion law …: a prime–even pair loses its composite advantage only inside the window …"). It made an uncertified causal claim, called $`(5,6)`$ "the smallest pair" although $`(3,4)`$ is smaller, left out the $`(9,10)`$ failure, mixed $`(p,p+1)`$ with $`(p,p\pm1)`$, and put an all-$`d`$ theorem directly in front of the unchanged "These are exact computations, not asymptotic claims". All five points are fixed above.
- **Revised after the second checker reports:**
  - *Window described backwards* (checker B, blocking). The Revision 2 text said that the window "covers only $`d\le d_c(p)-20`$ and $`d\ge d_c(p)+20`$". Entry 22 defines the window as the band $`(d_c-20,\thinspace d_c+20)`$ in which the inversion happens, and criteria (i)/(ii) are guaranteed outside it. The clause is removed (see the Checker note below for why B's replacement wording was not used).
  - *"yet"* (checker A, blocking; checker B, non-blocking). The word presupposed that the pairs $`(p,p-1)`$ invert at some larger $`d`$, which is false (see (e)). It was dropped.
  - *Alphabet and "machine-checked"* (checkers A and B). "($`\sigma=2`$)" now qualifies the all-$`d`$ statement and the $`d=3`$ clause. The "Apart from" clause now uses B's wording, so it no longer suggests that the finite computations are uncertified.
  - *Notation* (checker B): $`P^{\mathrm{unif}}_{n^d}`$ throughout (see entry 12).
- **Checker note (round 2, B's suggested window wording not adopted):** checker B proposed "although its explicit criteria (i) and (ii) apply only for $`d\le d_c(p)-20`$ resp. $`d\ge d_c(p)+20`$, so for small $`p`$ they decide nothing at $`d=3`$". This would be false. Criterion (ii) holds at $`(p,d)=(5,3)`$ for every $`\sigma\ge2`$: $`\varphi(3)=\tfrac45\cdot125-\tfrac{216}2=-8 < -\log_2(72\log_2 6)\approx-7.54`$, which is the hand check made by checker B in round 1 and by checker A in round 2. `inversionExplicitWindow_proved` says only that the criteria hold *outside* the band, so it gives sufficient conditions and is silent about where the criteria fail. Any short wording of the window risks the same misreading, and the window adds nothing at $`d=3`$, so the clause was removed rather than reworded.
- **Checker note (optional suggestion not adopted):** checker B remarks that criterion (ii) of Proposition 10.2 already holds at $`(p,d)=(5,3)`$ for every $`\sigma\ge2`$ ($`\varphi(3)=-8 < -\log_2(72\log_2 6)\approx-7.54`$, by hand). No Lean statement freezes that instance, so under the conservativeness rule it is not used in the replacement. It would be a one-line addition to S09 if the authors want to cite it.
- **Revised after the third checker reports:** the text is unchanged. Part (d) now cites the frozen `inversionDeepens56_proved` for $`P(6^d) < P(5^d)`$, $`d\ge3`$ (checker B), and marks the witness $`P(9^3) > P(10^3)`$ as certified by a helper only.

### 14. §8 prose — "$`\mathrm{rk}_p=d`$ configurations are fully $`p`$-periodic" (line 790)

- **(a) Severity:** ILL-POSED. Under the standard reading "period $`p`$ along every axis" it is false.
- **(b) Current:**
```latex
788: all of them are monotone. Geometrically, $\rk_p=1$ configurations are
789: periodic along one direction of the $p$-torsion (``stripes''/``slabs''),
790: $\rk_p=d$ configurations are fully $p$-periodic; each level set is an
791: irreversible attractor by Proposition~\ref{prop:rank}. Kornyak's
```
- **(c) Proposed:** replace "$`\mathrm{rk}_p=d`$ configurations are fully $`p`$-periodic" with
```latex
$\rk_p=d$ configurations are exactly those fixed by the whole $p$-torsion
$\A[p]=(\tfrac np\ZZ/n\ZZ)^d$
```
- **(d) Lean:**
  - Corrected text: `ShiftSym.P07.rankFull_proved` ($`\mathrm{rk}_p(s)=d\iff\mathcal{A}[p]\le\mathrm{Stab}(s)`$) and `ShiftSym.P02.torsionEq_proved` ($`\mathcal{A}[p]=(\tfrac np\mathbb{Z}/n\mathbb{Z})^d`$).
  - Refutation of the standard reading: the kernel-checked `example` (by `decide`) in `Shiftsym/Paper/S07_Dynamics.lean` (no named theorem). On $`\mathbb{Z}_6`$, $`s=(0,1,0,1,0,1)`$ has $`\mathcal{A}[3]\le\mathrm{Stab}(s)`$, so $`\mathrm{rk}_3=1=d`$, but $`s`$ has no period $`3`$.
- **(e) Justification:** Translations by $`p\thinspace \mathbf e_i`$ have order $`n/p`$, not $`p`$. The two readings agree only for $`n=p^2`$.

### 15. §8 prose — "each level set is an irreversible attractor" (lines 790–791)

- **(a) Severity:** FALSE.
- **(b) Current:** see entry 14 (lines 788–791).
- **(c) Proposed:** replace "each level set is an irreversible attractor by Proposition~\ref{prop:rank}" with
```latex
each superlevel set $\{\rk_p\ge r\}$ is absorbing (no trajectory leaves
it) by Proposition~\ref{prop:rank}
```
  Lines 788–791 after entries 14 and 15:
```latex
all of them are monotone. Geometrically, $\rk_p=1$ configurations are
periodic along one direction of the $p$-torsion (``stripes''/``slabs''),
$\rk_p=d$ configurations are exactly those fixed by the whole $p$-torsion
$\A[p]=(\tfrac np\ZZ/n\ZZ)^d$; each superlevel set $\{\rk_p\ge r\}$ is
absorbing (no trajectory leaves it) by Proposition~\ref{prop:rank}. Kornyak's
```
- **(d) Lean:** corrected text `ShiftSym.P07.superlevelInvariant_proved`; refutation `ShiftSym.P07.levelSetInvariantFalse_proved`.
- **(e) Justification:** A constant CA maps the asymmetric $`s=(0,1)`$ on $`\mathbb{Z}_2`$ ($`\mathrm{rk}_2=0`$) to a constant ($`\mathrm{rk}_2=1`$), so level sets below the top are not invariant. Only "$`\mathrm{rk}_p`$ never drops" follows from Proposition 8.3.
- **Revised after the second checker reports:** the threshold is now written $`r`$, not $`k`$ (checker B), because $`k`$ already denotes $`\omega(n)`$ (§3, "Throughout") and the active-cell count (§5). The letter $`r`$ is the paper's rank variable.

### 16. §9 algorithm and cost model — order of traversal; early stop (lines 809, 820–823)

- **(a) Severity:** IMPRECISE. The traversal order may or may not depend on the subgroup, and a failing walk may or may not stop at its first mismatch.
- **(b) Current:**
```latex
809: Lemma~\ref{lem:torsion}): traverse the cells in a fixed order; for each
810: yet-unvisited cell, walk its $C$-orbit ($p$ cells) checking equality;
811: abort the subgroup at the first failing orbit. Report ``symmetric'' at
```
```latex
820: Throughout this section we charge one read per visited cell: the first
821: cell of an orbit walk (the \emph{anchor}) is read once and its value
822: cached, and each subsequent cell of the orbit is read once and compared
823: to the cached value.
```
- **(c) Proposed:**
  - In line 809, replace "traverse the cells in a fixed order;" with "traverse the cells in a fixed order (which may depend on the subgroup);".
  - At the end of line 823, after "compared to the cached value.", append:
```latex
A failing orbit walk may stop at its first mismatch or be completed; all
results of this section hold in both variants, except the exact factor in
Remark~\ref{rem:polylog}, which refers to completed walks.
```
- **(d) Lean:**
  - Every algorithmic statement is quantified over all subgroup enumerations, per-subgroup traversal orders and both variants: `ShiftSym.P08.detectCorrect_proved`, `ShiftSym.P08.detectWorst_proved`, `ShiftSym.P08.thmDetectWorst_proved`, `ShiftSym.P08.propDetectAvg_proved`, and the `remPolylog*_proved` theorems.
  - The only exception, for completed walks only: `ShiftSym.P08.remPolylogFactorConservative_proved`.
- **(e) Justification:** The two readings give different algorithms. Every claim of §9 was certified for both, except the exact factor, which holds only for completed walks (entry 20).

### 17. Proposition 9.2 — "the expected number of orbits visited" (lines 838–840)

- **(a) Severity:** IMPRECISE.
- **(b) Current:**
```latex
838: For $\ssb$ uniform on $\Sigma^{n^d}$ and any single order-$p$ subgroup,
839: the expected number of orbits visited is exactly
840: $\frac{1-Q^{m}}{1-Q}$ with $Q=\sigma^{1-p}$ and $m=N/p$; consequently the
```
- **(c) Proposed** (replace lines 838–840):
```latex
For $\ssb$ uniform on $\Sigma^{n^d}$, the test of any single order-$p$
subgroup, run on its own, visits in expectation exactly
$\frac{1-Q^{m}}{1-Q}$ orbits, with $Q=\sigma^{1-p}$ and $m=N/p$; consequently the
```
- **(d) Lean:** `ShiftSym.P08.detectAvgOrbits_proved` (stand-alone test; every generator, order and variant).
- **(e) Justification:** Inside the full algorithm a subgroup is skipped once an earlier one passes, which changes the expectation. The proof (lines 852–854) computes the stand-alone test.

### 18. §9 — alphabet of the two-dimensional checks (lines 858–860)

- **(a) Severity:** RECORD.
- **(b) Current:**
```latex
858: The per-generator expectation was confirmed to match full-enumeration
859: averages \emph{exactly} for $(n,d,\sigma)\in\{(2,3,2),(2,3,3),(2,4,2)\}$
860: and, in two dimensions, for $n\le4$.
```
- **(c) Proposed** (line 860):
```latex
and, in two dimensions, for $n\le4$ with $\sigma=2$ and for $(n,\sigma)=(3,3)$.
```
- **(d) Lean:** `ShiftSym.P08.avgOrbitsChecked_proved` (exactly these seven instances). It is subsumed by `ShiftSym.P08.detectAvgOrbits_proved` for all parameters. Run-log source: `verify_banda2d_output.txt` §[7] (Run 003) and `verify_paper_claims_output.txt` §[3] (Run 006).
- **(e) Justification:** The 2D instances actually enumerated were $`(n,\sigma)\in\lbrace(2,2),(3,2),(3,3),(4,2)\rbrace`$.

### 19. Remark 9.3 — polylogarithmic figures "hold … for randomly chosen $`n`$" (lines 864–868)

- **(a) Severity:** FALSE.
- **(b) Current:**
```latex
864: prime $n$ it equals $n^d=N$. The polylogarithmic figures quoted in
865: \cite[Sec.~V--VI]{banda2019} for $d=2$ hold, as that paper states, for
866: \emph{randomly chosen} $n$ (whose prime factors are typically small), not
867: in the worst case over $n$; the same conditioning is required in every
868: dimension. Note also that for prime $n$ the average case
```
- **(c) Proposed** (replace lines 864–868; the tail of line 868, "Note also that for prime $`n`$ the average case", is unchanged here and is treated in entry 20):
```latex
prime $n$ it equals $n^d=N$. The polylogarithmic figures quoted in
\cite[Sec.~V--VI]{banda2019} for $d=2$ are stated there for
\emph{randomly chosen} $n$ and rest on $\sum_{p\mid n}p$ and
$\sum_{p\mid n}p^2$ being polylogarithmic; but in every dimension,
$\sum_{p\mid n}p^d$ is polylogarithmic in $N$ when all prime factors of $n$
are polylogarithmically small, whereas for any fixed $C$ and $j$ the $n$
with $\sum_{p\mid n}p^d\le C\log^j N$ have natural density zero, so this
bound is not polylogarithmic for almost all $n$. Note also that for prime $n$ the average case
```
- **(d) Lean:**
  - Corrected text: `ShiftSym.P08.remPolylogSmooth_proved`, `ShiftSym.P08.remPolylogRandomN_proved` (density zero for every $`d`$, $`C`$ and exponent $`j`$; the Lean statement calls the exponent `k`) and `ShiftSym.P08.remPolylogNotPolylog_proved`.
  - Refutation of the old text: `ShiftSym.P08.remPolylogRandomN_proved` itself, since its $`d=1`$ and $`d=2`$ instances refute "$`\mathrm{sopf}(n)`$, resp. $`\mathrm{sopf}_2(n)`$, is polylogarithmic for random $`n`$", on which the 2019 figures rest.
  - Citation part ("rest on"): checked against the 2019 text (arXiv:1703.09030v2, Sec. V: "The function $`\mathrm{sopf}(n)`$, which plays a crucial role in both O formulas, is of a logarithmic nature in “most of the cases,” … However, for randomly chosen $`n`$ the expected time complexities drop to just $`O(\log(n)n^2)`$ and $`O(\log^2(n))`$"; appendix: average case $`O(\mathrm{sopf}_2(n)+\mathrm{sopf}(n))`$). The same reading is recorded in the `remPolylogRandomNStatement` docstring. This is the one citation exception besides entry 32 (see the conservativeness rule).
- **(e) Justification:** $`\mathrm{sopf}(n)`$ and $`\mathrm{sopf}_2(n)`$ are polylogarithmic only on a density-zero set. The attribution "as that paper states" is accurate, but the paper asserted the figures in its own voice. The parenthetical "typically small" cannot mean polylogarithmically small, because such $`n`$ have density zero. Speaking of the bound $`\sum_{p\mid n}p^d`$ also resolves the ambiguity of "the same conditioning is required in every dimension". For the actual cost of early-stopping walks, the S08 docstring's exact evidence shows that no conditioning is needed at $`d=1`$, so the claim is only right for the bound. The replacement therefore says nothing about when the 2019 figures themselves hold. No Lean theorem bounds the actual cost from below for general composite $`n`$. Polylog-smoothness is also not sufficient for the figure $`O(\log^2 n)`$: if the prime factors of $`n`$ have size $`(\log n)^c`$ with $`c > 1`$, then $`\mathrm{sopf}_2(n)`$ is not $`O(\log^2 n)`$.
- **Revised after the checker reports:** both checkers flagged the earlier main clause, "but they hold only for $`n`$ whose prime factors are all polylogarithmically small", as a claim about the 2019 running-time figures that no theorem certifies (the certificates concern only the bound $`\sum_{p\mid n}p^d`$), and one that invites a false converse. The new text states only the bound-level facts and links them to the 2019 figures by a checked citation.
- **Revised after the second checker reports:**
  - The exponent is now $`j`$ (checker B), because $`k`$ already denotes $`\omega(n)`$ and the active-cell count. Checker B suggested $`m`$, but $`m=N/p`$ in Proposition 9.2, two paragraphs earlier in the same section, and §9 uses $`j`$ nowhere.
  - *Consequential, mandatory* (checker B). Contribution (iv) of the introduction, lines 130–132, still says that the average-case claims are "restated under their actual hypotheses", but this entry deliberately stops saying when the 2019 figures hold. Current:
```latex
130:     analysis (Section~\ref{sec:detection}), with the average-case
131:     ``polylogarithmic'' claims of the two-dimensional literature restated
132:     under their actual hypotheses.
```
    Proposed (replace lines 131–132):
```latex
    ``polylogarithmic'' claims of the two-dimensional literature corrected:
    the average-case bound $O(\sum_{p\mid n}p^d)$ is polylogarithmic in
    $N$ only on a set of $n$ of natural density zero.
```
    Lean: `ShiftSym.P08.remPolylogRandomN_proved`. Any set of $`n`$ on which the bound is at most $`C\log^j N`$ for fixed $`C,j`$ lies inside a set of density zero.
  - **Checker note (round 2, B's wording for (iv) narrowed):** checker B suggested "the bound is polylogarithmic only for $`n`$ with polylogarithmically small prime factors, a set of density zero". The "only for" direction is elementary, since each $`p^d`$ is at most the sum, but neither it nor the identification of the exceptional set with the polylog-smooth $`n`$ is frozen. The adopted wording states only what `remPolylogRandomN_proved` certifies.

### 20. Remark 9.3 — "improves the worst case … by a factor $`n^{d-1}`$" (lines 868–870)

- **(a) Severity:** IMPRECISE.
- **(b) Current:**
```latex
868: dimension. Note also that for prime $n$ the average case
869: $O(N)$ still improves the worst case $O(N\cdot n^{d-1})$ by a factor
870: $n^{d-1}$.
```
- **(c) Proposed** (replace from "Note also" to the end of line 870):
```latex
Note also that for prime $n$ the average case
$O(N)$ still improves the worst case, which is of exact order
$N\cdot n^{d-1}$, by a factor of at least order $n^{d-1}$ (of exact order
$n^{d-1}$ when every failing orbit walk is completed, as in the proofs of
Theorem~\ref{thm:detect-worst} and Proposition~\ref{prop:detect-avg}).
```
- **(d) Lean:**
  - Average case $`O(N)`$: `ShiftSym.P08.remPolylogAvgPrime_proved`.
  - Worst case: upper bound `ShiftSym.P08.remPolylogWorstPrime_proved`, attained by `ShiftSym.P08.remPolylogWorstLower_proved`.
  - Factor: at least order $`n^{d-1}`$, both variants, `ShiftSym.P08.remPolylogFactor_proved`; exact order for completed walks, `ShiftSym.P08.remPolylogFactorConservative_proved`.
- **(e) Justification:** The exact-order statement is certified only for completed walks. For walks that stop at the first mismatch, only "at least order $`n^{d-1}`$" is certified; the docstring's exact evidence indicates order $`n^d`$ there.

### 21. Proposition 10.2 — "unique zero" of $`\varphi`$ (lines 945–946)

- **(a) Severity:** ILL-POSED. $`\varphi`$ is defined on integer dimensions, where it generally has no zero (e.g. $`d_c(5)\approx2.58`$).
- **(b) Current:**
```latex
945: The function $\varphi$ is positive below and negative above its unique
946: zero
```
- **(c) Proposed** (replace lines 945–946):
```latex
The function $\varphi$, regarded as a function of real $d$, is positive
below and negative above its unique zero
```
- **(d) Lean:** `ShiftSym.P09.phiSign_proved` (on all of $`\mathbb R`$).
- **(e) Justification:** The proof's monotonicity argument already treats $`d`$ as real.

### 22. Proposition 10.2 — "an explicitly bounded window" (lines 951–953)

- **(a) Severity:** IMPRECISE (the window is never stated).
- **(b) Current:**
```latex
951: so the two-dimensional ``composite advantage'' inverts within an
952: explicitly bounded window around $d_c(p)$, which grows \emph{linearly} in
953: the prime.
```
- **(c) Proposed:**
  - Replace lines 951–953 with:
```latex
so the two-dimensional ``composite advantage'' inverts within an
explicitly bounded window around $d_c(p)$, a dimension that grows
\emph{linearly} in the prime: (i) applies to every integer $d\ge1$ with
$d\le d_c(p)-20$, and (ii) to every integer $d\ge d_c(p)+20$.
```
  - At the end of the proof (line 965, after "by expanding both logarithms."), add: "The window bound follows by elementary estimates of $`\varphi`$ and of the thresholds in (i) and (ii); it is machine-checked (Section~\ref{sec:formal}), and the constant $`20`$ is not optimized."
- **(d) Lean:** `ShiftSym.P09.inversionExplicitWindow_proved` (instantiated with $`C=20`$ via `ShiftSym.P09.window_i` and `ShiftSym.P09.window_ii`; the frozen statement asserts $`\exists C`$, so the value $`20`$ is certified by these two kernel-checked helpers rather than by a frozen statement, see the conservativeness rule), `ShiftSym.P09.inversionWindow_proved` (probability form) and `ShiftSym.P09.dcAsymptotic_proved`. *Update 2026-10-22:* the 20 is now frozen as well, `ShiftSym.P09.inversionExplicitWindow20_proved` and `ShiftSym.P09.inversionWindow20_proved` (supplement `S09_CrossoverLaws_Window20.lean`, Run 025).
- **(e) Justification:** The certificate fixes the explicit width 20, uniform in $`p\ge3`$ and $`\sigma\ge2`$. The smaller constant 4 that the docstring suggests is backed only by Python, so it is not proposed.
- **Revised after the third checker reports:** with the explicit width $`20`$, "which grows linearly in the prime" could be read as saying that the window grows (checker A). Only its location $`d_c(p)`$ grows. This is also how the `inversionExplicitWindowStatement` docstring reads the clause ("the window's location `d_c(p)`", frozen as `dcAsymptoticStatement`). The text now says "a dimension that grows linearly in the prime".

### 23. Remark 10.3 — "Interpolated sign changes" (lines 969–970)

- **(a) Severity:** IMPRECISE.
- **(b) Current:**
```latex
969: Interpolated sign changes of $\log_{10}[P_{(p+1)^d}/P_{p^d}]$ in exact
970: data ($\sigma=2$) against $d_c(p)$:
```
- **(c) Proposed** (replace lines 969–970):
```latex
Linearly interpolated zeros of $d\mapsto\log_{10}[P_{(p+1)^d}/P_{p^d}]$
between the consecutive integer dimensions at its first sign change, in
exact data ($\sigma=2$), against $d_c(p)$:
```
- **(d) Lean:** `ShiftSym.P11.measuredRow_proved` (all five entries under exactly this procedure, including $`p=11,13`$ on lattices up to $`14^9`$ cells) and `ShiftSym.P11.dcRow_proved`.
- **(e) Justification:** This is the procedure that reproduces all five tabulated values.

### 24. Remark 10.3 — "Measured values sit at or slightly below $`d_c`$ because …" (lines 981–982)

- **(a) Severity:** FALSE (causal attribution).
- **(b) Current:**
```latex
981: Measured values sit at or slightly below $d_c$ because the coefficient
982: corrections in Proposition~\ref{prop:rate} favor the prime side. At
```
- **(c) Proposed** (replace lines 981–982 up to "At"):
```latex
Measured values sit at or below $d_c$, mainly because of the
interpolation itself: interpolating the bare exponent $\varphi$ (without
coefficient corrections) linearly between $\lfloor d_c\rfloor$ and
$\lfloor d_c\rfloor+1$ already gives a zero below $d_c(p)$ for
$p=5,7,11,13$ (at $p=3$ both equal $1$); the coefficient corrections (the factors $|S_{n^d}|/\sigma^{N/p_1}$, which
Proposition~\ref{prop:rate} bounds on both sides) favor the prime side but
account for at most a quarter of the gap (at most $10^{-3}$ of it for
$p=11,13$). At
```
- **(d) Lean:**
  - "At or below": `ShiftSym.P11.measuredAtOrBelow_proved`.
  - "Favor the prime side": `ShiftSym.P11.coefficientsFavorPrime_proved`.
  - Cause and shares: `ShiftSym.P11.measuredGapCause_proved`, stated for $`p\in\lbrace5,7,11,13\rbrace`$, the tabulated primes $`\ge5`$. The interpolated zero $`y`$ of the bare $`\varphi`$ satisfies $`y < d_c`$, $`\lfloor x\rfloor=\lfloor y\rfloor=\lfloor d_c\rfloor`$ and $`4(y-x)\le d_c-x`$, and $`1000(y-x)\le d_c-x`$ for $`p\ge11`$.
  - $`p=3`$: $`\varphi(1)=\tfrac23\cdot3-\tfrac42=0`$ and $`d_c(3)=\ln(4/3)/\ln(4/3)=1`$, so the interpolated zero is $`1=d_c(3)`$ (hand-checkable; checker A also proved it in Lean in a scratch file, which is not part of the development). The measured value is exactly $`1=d_c(3)`$ (`ShiftSym.P11.boundaryCase_proved`), and the paper's next sentence treats $`p=3`$ as the exact boundary case.
- **(e) Justification:** The gap is mainly a chord-versus-curve artefact of the interpolation; the coefficient corrections account for $`\le 25`$% of it, and $`\le 0.1`$% at $`p\ge11`$ (certified bounds). "Slightly" also understated gaps of about half a dimension at $`p=5,11`$, as the certified rounding intervals of the two table rows show. The direction "favor the prime side" comes from the exact leading coefficients of Theorem 4.3 ($`\binom{d}{1}_p`$ order-$`p`$ subgroups against $`2^d-1`$ order-2 subgroups), not from Proposition 10.1, whose bounds are two-sided on both sides of the comparison (S11 PAPER ISSUE at `measuredAtOrBelowStatement`). The parenthetical therefore cites Proposition 10.1 only to identify the corrections, not as the source of their direction.
- **Revised after the checker reports:** the earlier wording "places the zero of $`\varphi`$ itself below $`d_c(p)`$" contradicted itself, since by Proposition 10.2 the zero of $`\varphi`$ *is* $`d_c(p)`$. What is certified is that the linearly interpolated zero $`y`$ of $`\varphi`$ satisfies $`y < d_c(p)`$, and the new wording says exactly that. The parenthetical "(the prefactors bounded in Proposition~\ref{prop:rate})" was also made neutral about where the direction comes from, which answers checker B's remark that the S11 note was only softened.
- **Revised after the second checker reports:** the clause "already gives a zero below $`d_c(p)`$" is now limited to $`p\ge5`$ (checker A, blocking; checker B, non-blocking). Unrestricted, it covered all five tabulated primes and was false at $`p=3`$, where the interpolated zero equals $`d_c(3)=1`$. `measuredGapCause_proved` covers only $`p\in\lbrace5,7,11,13\rbrace`$. The rest of the sentence ("at most a quarter of the gap", "$`10^{-3}`$ for $`p=11,13`$") is unchanged. At $`p=3`$ the gap is zero, so the bound holds trivially there: `ShiftSym.P11.boundaryCase_proved` certifies that the measured sign change is exactly $`1`$ and that $`d_c(3)=1`$.
- **Revised after the third checker reports:** "for $`p\ge5`$" became "for $`p=5,7,11,13`$" (checker B; checker A suggested "for the tabulated $`p\ge5`$"). Read as a claim about all primes, the old clause said more than `measuredGapCause_proved` certifies, since it covers only these four. Both checkers found the general claim true by exact or high-precision computation (A: every prime $`5\le p < 20000`$; B: every prime $`5\le p\le3000`$), but no theorem certifies it. The explicit list is the shortest wording that matches the certificate.

### 25. Figure 3 caption — "its linear asymptote $`p\ln2`$" (line 1000)

- **(a) Severity:** FALSE.
- **(b) Current:**
```latex
999: inversion dimensions against the prediction
1000: $d_c(p)=\ln(2-2/p)/\ln(1+1/p)$ and its linear asymptote $p\ln2$.}
```
- **(c) Proposed** (line 1000):
```latex
$d_c(p)=\ln(2-2/p)/\ln(1+1/p)$ and the line $p\ln2$ ($d_c(p)=p\ln2+O(1)$;
the linear asymptote itself is $p\ln2+\tfrac12\ln2-1$).}
```
- **(d) Lean:**
  - Corrected text: `ShiftSym.P11.figInversionAsymptote_proved` (slope $`\ln2`$, bounded offset) and `ShiftSym.P11.dcOffsetLimit_proved`, first conjunct (true asymptote; helper `ShiftSym.P11.dc_linear_asymptote`).
  - Refutation: `ShiftSym.P11.dcOffsetLimit_proved`, second conjunct (helper `ShiftSym.P11.dc_not_asymptote_zero`).
- **(e) Justification:** $`d_c(p)-p\ln2\to\tfrac12\ln2-1\approx-0.653\neq0`$, so $`p\ln2`$ is only the asymptotic slope.
- **Consequential, mandatory (part of this entry):** the right panel of `charts/chart15_inversion_dimension.png` has the legend "asymptote $`d_c\approx p\ln2`$" (`compute_dimension_insights.py`, line 198). That is exactly the claim this entry refutes, so fixing only the caption would leave the figure contradicting it. The legend must be relabelled (e.g. "slope $`p\ln2`$"), or the curve must be the true asymptote $`p\ln2+\tfrac12\ln2-1`$. Then the chart must be regenerated (script run from the project root) and the new output logged as a new Run with SHA-256 in `research/experiments/README.md`, as the CLAUDE.md verification discipline requires for regenerated charts.
- **Revised after the third checker reports:** the chart fix was only a recommendation ("should be relabelled"). Checker B pointed out that the image would still assert the refuted asymptote, so relabelling, regeneration and the Run log entry are now mandatory.

### 26. Observation 10.4 — "the least $`d`$" (line 1007)

- **(a) Severity:** ILL-POSED. Read literally, the claim is false.
- **(b) Current:**
```latex
1006: \begin{observation}[Single-term crossover dimension]\label{obs:dstar}
1007: For prime $n=p$, define $d^*(p;\theta)$ as the least $d$ at which the
1008: second term of Corollary~\ref{cor:prime} falls below a fraction $\theta$
```
- **(c) Proposed** (line 1007):
```latex
For prime $n=p$, define $d^*(p;\theta)$ as the least $d\ge2$ at which the
```
- **(d) Lean:**
  - Corrected text: `ShiftSym.P11.dstarClaim_proved` and `ShiftSym.P11.t2t1Formula_proved` (stated for $`d\ge2`$). Optional strengthening, certified: `ShiftSym.P11.dstarAllPrimes_proved` (the $`\theta=0.05`$ statement holds for *all* primes).
  - Refutation of the literal reading: `ShiftSym.P11.dstarLiteralDegenerate_proved` ($`d^{\ast}=1`$ for every $`p`$, $`\sigma`$, $`\theta`$).
- **(e) Justification:** $`T_2=0`$ at $`d=1`$, and the displayed exponent $`p^{d-2}(p-1)`$ is not an integer there. The script `compute_C_exploration.py` already starts at $`d=2`$.

### 27. Observation 10.4 — fit and "only three unclamped data points" (lines 1013–1015)

- **(a) Severity:** RECORD. The count depends on $`\theta`$, and the quoted $`C`$ range comes from a fractional $`d^{\ast}`$ that the paper never defines.
- **(b) Current:**
```latex
1012: ($\sigma=2$): only $p\in\{2,3,5\}$ have $d^*>2$ at $\theta=0.05$; a fit
1013: $d^*\approx1+C/\ln p$ gives $C\approx2.2$--$2.65$ depending on $\theta$
1014: (about $2.5\pm0.3$), but with only three unclamped data points and
1015: systematic residuals this is an indicative, threshold-dependent summary,
1016: not an estimate of a universal constant. The driver is the
```
- **(c) Proposed** (replace lines 1013–1015):
```latex
$d^*\approx1+C/\ln p$ to a fractional version of $d^*$ (interpolating
$\log|T_2/T_1|$ linearly between consecutive integer dimensions) gives
$C\approx2.2$--$2.65$ depending on $\theta$
(about $2.5\pm0.3$), but with only two to four unclamped data points per
threshold (for the integer $d^*$: four, three, and two at
$\theta=0.01,0.05,0.10$) and
systematic residuals this is an indicative, threshold-dependent summary,
```
- **(d) Lean:** `ShiftSym.P11.dstarUnclamped_proved` (three at $`\theta=0.05`$) and `ShiftSym.P11.dstarUnclampedByTheta_proved` ($`\lbrace2,3,5,7\rbrace`$, $`\lbrace2,3,5\rbrace`$, $`\lbrace2,3\rbrace`$). The $`C`$ values themselves are a statistical summary and not Lean-checkable. Record source: `compute_C_exploration.py` (log-linear fractional $`d^{\ast}`$, clamp mask $`d^{\ast} > 2.01`$, leaving 4/2/2 points with $`C=2.654/2.533/2.206`$), as documented in the `dstarUnclampedStatement` docstring and the S11 reviews.
- **(e) Justification:** As written, "three points" holds only at $`\theta=0.05`$ and for the integer $`d^{\ast}`$. The quoted fit uses a different, undefined $`d^{\ast}`$. The replacement states the method, and states only certified counts: "two to four" covers both the 4/3/2 and the 4/2/2 counts.
- **Revised after the checker reports:** the earlier "to $`d^{\ast}`$ interpolated log-linearly between consecutive integers" reused the symbol $`d^{\ast}`$, which entry 26 defines as an integer, for an undefined second quantity, and did not say what is interpolated. The new text calls it a fractional version of $`d^{\ast}`$ and names the interpolated quantity, $`\log\lvert T_2/T_1\rvert`$, as computed by `compute_C_exploration.py` (`log10_correction_ratio`, linear interpolation in $`d`$ between $`d-1`$ and $`d`$).

### 28. Observation 10.5(a) — "composites have higher $`P^{\mathrm{unif}}`$ than neighboring primes" (lines 1021–1022)

- **(a) Severity:** FALSE at the pair $`(3,4)`$, for every $`\sigma`$. Under the "nearest prime" reading it fails more widely.
- **(b) Current:**
```latex
1020: \begin{observation}[Prime--composite gap inversion]\label{obs:inversion}
1021: At $d=2$ composites have higher $P^{\mathrm{unif}}$ than neighboring
1022: primes; by $d=3$ this inverts for small $n$
1023: (Observation~\ref{obs:extrema}), and the inversion deepens with $d$
```
- **(c) Proposed:** replace "At $`d=2`$ composites have higher $`P^{\mathrm{unif}}`$ than neighboring primes;" with
```latex
At $d=2$, for every $\sigma\ge2$, every prime $p\ge5$ has smaller
$P^{\mathrm{unif}}$ than both adjacent integers $p\pm1$ (a theorem,
machine-checked in Section~\ref{sec:formal}; the pair $(3,4)$
is the exception: $P^{\mathrm{unif}}_{4^2}<P^{\mathrm{unif}}_{3^2}$;
cf.\ Observation~\ref{obs:extrema});
```
- **(d) Lean:**
  - Corrected text: `ShiftSym.P11.compositeAdvantageD2_proved` (every $`\sigma\ge2`$, adjacency reading, $`(3,4)`$ excluded).
  - The exception, and refutation of the old text: `ShiftSym.P11.extremaBoundary_proved` ($`P(4^2) < P(3^2)`$ at $`\sigma=2`$). For every $`\sigma\ge2`$ the exception follows from the frozen `ShiftSym.P11.boundaryCase_proved`: its last conjunct, an interpolated sign change at exactly $`1`$ for every $`\sigma\ge2`$, forces `inversionLogRatio σ 3 2 < 0`. The proof goes through the helper `ShiftSym.P11.ilr3_two_neg`.
  - Refutation of the nearest-prime reading: `ShiftSym.P11.compositeNearestPrimeFail_proved` ($`P(9^2),P(10^2) < P(7^2)`$, $`P(35^2) < P(31^2)`$).
- **(e) Justification:** The paper itself records $`P(3) > P(4)`$ in Obs. 7.3. Odd composites have no prime at distance 1, so only the adjacency statement about primes $`p\ge5`$ is both meaningful and true. "For every $`\sigma\ge2`$" makes explicit the alphabet range that `compositeAdvantageD2_proved` covers. The observation fixes no alphabet, and its example in part (c) is at $`\sigma=2`$.
- **Revised after the checker reports:** both checkers showed that the earlier parenthetical "(at $`p=3`$ the reverse holds, …)" is false. The reverse of "smaller than both neighbours" is "larger than both", but $`P(2^2)=1/2 > 26/2^9=P(3^2)`$ at $`\sigma=2`$, and in general $`P(2^2)/P(3^2)=\sigma^5(3\sigma-2)/(4\sigma^2-3) > 1`$. Only $`P(4^2) < P(3^2)`$ holds, and that is all the certificates cover. The new parenthetical names exactly the exceptional pair.
- **Revised after the second checker reports:** checker B (blocking) and checker A (non-blocking) pointed out that the Revision 2 edit makes Obs. 10.5(a) a universal theorem that is supported only in Lean, while line 1004 and the §10 preamble still call it empirical. The proposal made the line-1004 fix optional and did not mention the preamble. Now Obs. 10.5(a) carries the pointer "(a theorem, machine-checked in Section~\ref{sec:formal}; …)", and both consequential edits are mandatory (below).
- **Consequential, mandatory (both are needed once the corrected Obs. 10.5(a) is adopted):** the corrected Obs. 10.5(a) is a theorem for all primes $`p\ge5`$ and all $`\sigma\ge2`$, machine-checked but not proved in the paper. Two sentences still call everything after Prop. 10.2 empirical, and would be false for it. The replacements count no exceptions, because several items after Prop. 10.2 contain exact claims for all parameters, all of them machine-checked:
    - Obs. 10.5(a) (`compositeAdvantageD2_proved`);
    - the deepening of the inversion in Obs. 10.5 (`inversionDeepens_proved`, every prime $`p\ge3`$, every $`\sigma\ge2`$, every $`d\ge1`$);
    - the $`p=3`$ boundary case of Rem. 10.3 (`boundaryCase_proved`, every $`\sigma`$);
    - the corrected Fig. 3 asymptote (`figInversionAsymptote_proved`, `dcOffsetLimit_proved`);
    - the $`\lvert T_2/T_1\rvert`$ formula of Obs. 10.4 (`t2t1Formula_proved`);
    - the Duality identity (`dualityGauss_proved`).
  - Line 1004. Current:
```latex
1004: The remaining items are empirical.
```
    Proposed:
```latex
The remaining observations are computational, except for exact claims
stated for all parameters (such as the composite advantage at $d=2$ and
the deepening of the inversion in Observation~\ref{obs:inversion}),
which are theorems (machine-checked, Section~\ref{sec:formal}).
```
  - §10 preamble, lines 884–886. Current:
```latex
884: We first prove two crossover laws that organize everything this section
885: observes; the items after them are computational findings with exact
886: arithmetic, labeled as such.
```
    Proposed (replace lines 885–886):
```latex
observes; the observations after them are computational findings with
exact arithmetic, labeled as such. Where an item after the two laws
states an exact claim for all parameters (such as the composite
advantage at $d=2$ and the deepening of the inversion in
Observation~\ref{obs:inversion}), that claim is a theorem,
machine-checked in Section~\ref{sec:formal}.
```
  - Obs. 10.5, deepening clause, lines 1023–1024 (recommended, checker B). Under the frozen reading the clause "and the inversion deepens with $`d`$" is a universal claim, and both edits above call it a theorem. So its quantifiers should be stated. Replace "and the inversion deepens with $`d`$ (e.g.," with
```latex
and the inversion deepens with $d$: for every prime $p\ge3$ and every
$\sigma\ge2$, once $P^{\mathrm{unif}}_{(p+1)^d}<P^{\mathrm{unif}}_{p^d}$,
the ratio $P^{\mathrm{unif}}_{(p+1)^d}/P^{\mathrm{unif}}_{p^d}$ decreases
strictly with every further dimension (a theorem, machine-checked in
Section~\ref{sec:formal}; e.g.,
```
    The rest of the sentence ("$`P(6)/P(5)`$ falls from …, $`\sigma=2`$).") is unchanged and closes the parenthesis. Lean: `ShiftSym.P11.inversionDeepens_proved` (a negative log-ratio at $`d`$ implies a strictly smaller one at $`d+1`$; by induction it stays negative and keeps decreasing) and, for the example pair, `ShiftSym.P11.inversionDeepens56_proved`. The claim concerns the pairs $`(p,p+1)`$; the pairs $`(p,p-1)`$ never invert (entry 13 (e)).
  - Table 2 row "Prime local minima of $`P`$", lines 1134–1136 (optional, checker B). Current:
```latex
1134: Prime local minima of $P$ & yes (empirical) & \textbf{fails for }$d\ge3$;
1135: inversion at $d_c(p)\approx p\ln2$
1136: (Proposition~\ref{prop:inversion}, Observation~\ref{obs:extrema}) \\
```
    Proposed:
```latex
Prime local minima of $P$ & yes for $p\ge5$ (empirical there; a theorem
here, Observation~\ref{obs:inversion}) & \textbf{fails for }$d\ge3$
(at $p=5$, $\sigma=2$); inversion of $(p,p{+}1)$ around
$d_c(p)\approx p\ln2$
(Proposition~\ref{prop:inversion}, Observation~\ref{obs:extrema}) \\
```
    Lean: `compositeAdvantageD2_proved` (2D column: every prime $`p\ge5`$ is a strict local minimum, for every $`\sigma\ge2`$); `extremaBreaks_proved` and `inversionDeepens56_proved` (failure at every $`d\ge3`$, $`\sigma=2`$, through $`(5,6)`$); Proposition 10.2 for where the inversion happens. Nothing in the current row is false. "Fails for $`d\ge3`$" is true through $`p=5`$, but it reads more broadly than corrected Obs. 7.3, by which no pair $`(p,p\pm1)`$ with $`7\le p\le23`$ is inverted at $`d=3`$.
  - Alternative to the pointers (the authors' choice): add the short proof recorded in the `compositeAdvantageD2Statement` docstring. One order-2 subgroup gives $`P(c^2)\ge\sigma^{-c^2/2}`$, while $`P(p^2) < (p+1)\sigma^{p-p^2}`$. This leaves only $`(\sigma,p,c)=(2,5,6)`$, which is settled by exact computation. The environment name "Computational Observation" can stay, because the pointer inside Obs. 10.5(a) marks the exception.
  - See also entry 13 and Open Problem (1) below.
- **Revised after the third checker reports:** checker B (blocking) showed that the Revision 3 replacements for line 1004 and the §10 preamble, which named "one exception", were false. The deepening of the inversion in Obs. 10.5 is frozen as the universal `inversionDeepensStatement` (every $`\sigma\ge2`$, every prime $`p\ge3`$, every $`d\ge1`$) and certified by `inversionDeepens_proved`. The $`p=3`$ boundary case of Rem. 10.3 holds for every $`\sigma`$ (`boundaryCaseStatement`). Checker A (non-blocking) added that the Duality remark after line 1004 is a standard identity, not a computational observation, and that the corrected Fig. 3 asymptote is also a theorem. The replacements now count no exceptions: the computational label applies to "the observations", and the general rule is stated with named examples. The pointer in the deepening clause is recommended, so that the claim the two edits call a theorem is stated with its quantifiers. "cf.\ " now has inter-word spacing (checker B). The Table 2 row is an optional addition (checker B).
- **Checker note (round 3, wording differs from both suggestions):** for line 1004, B proposed "The remaining items are computational observations; …". "Items" would still cover the Duality remark (A's finding), so the adopted text says "observations". Both of B's wordings refer to "the first and third claims of Observation~\ref{obs:inversion}". The adopted text names the claims instead, because after entry 29 the sentence of Obs. 10.5 has three clauses and the ordinal depends on how it is split. A suggested "The remaining observations are computational, except …" with a list of exceptions. The adopted text keeps A's "observations" but uses a rule with examples instead of a list, so it stays true for every item after the two laws.

### 29. Observation 10.5(b) — "by $`d=3`$ this inverts for small $`n`$" (lines 1022–1023)

- **(a) Severity:** IMPRECISE (overstatement).
- **(b) Current:** see entry 28 (lines 1020–1023).
- **(c) Proposed:** replace "by $`d=3`$ this inverts for small $`n`$ (Observation~\ref{obs:extrema})," with
```latex
by $d=3$ ($\sigma=2$) this inverts for the pair $(5,6)$
(Observation~\ref{obs:extrema}), but for no pair $(p,p\pm1)$ with
$7\le p\le23$,
```
- **(d) Lean:** `ShiftSym.P11.inversionD3_proved` and `ShiftSym.P11.inversionD3Scope_proved`.
- **(e) Justification:** Among the prime/composite-neighbour pairs with $`3\le p\le23`$ at $`d=3`$, only $`(3,4)`$, which was never non-inverted, and $`(5,6)`$ are inverted.
- **Revised after the second checker reports:**
  - "not yet" became "for no" (checker A, blocking; checker B). "Yet" presupposed that the pairs $`(p,p-1)`$ invert at a larger $`d`$. They never do (entry 13 (e); `inversionDeepensStatement` docstring), and checker A's exact check finds no inversion of the pairs $`(p,p-1)`$, $`p=5,7,11`$, at any $`d\le6`$.
  - "($`\sigma=2`$)" added after "by $`d=3`$" (checker B). Entry 28 opens the observation with "for every $`\sigma\ge2`$", but `inversionD3Statement` and `inversionD3ScopeStatement` are certified only at $`\sigma=2`$.

### 30. Remark (Duality) — "rank-$`r`$ and rank-$`(d-r)`$ symmetry types are equinumerous" (lines 1029–1030)

- **(a) Severity:** IMPRECISE. "Symmetry type" is undefined, and the range of $`r`$ is unstated.
- **(b) Current:**
```latex
1028: \begin{remark}[Duality]
1029: $\gaussbinom dr_p=\gaussbinom d{d-r}_p$, so rank-$r$ and rank-$(d{-}r)$
1030: symmetry types are equinumerous. We state this purely as the standard
1031: symmetry of Gaussian binomials; we do not attach further structural
1032: claims to it.
```
- **(c) Proposed** (replace lines 1029–1030 up to "We state this"):
```latex
$\gaussbinom dr_p=\gaussbinom d{d-r}_p$ for $0\le r\le d$, so $\FF_p^d$
has equally many subspaces of dimensions $r$ and $d-r$ (equivalently, for
a prime $p\mid n$, $\A[p]$ has equally many subgroups of orders $p^r$ and
$p^{d-r}$). We state this purely as the standard
```
- **(d) Lean:** `ShiftSym.P03.dualityGauss_proved`, `ShiftSym.P03.dualitySubspace_proved`, `ShiftSym.P03.dualityLattice_proved`.
- **(e) Justification:** This states the evident meaning, in terms the paper defines (§3, Lemma 3.3).
- **Revised after the checker reports:** the hypothesis $`p\mid n`$ was added. `dualityLatticeStatement` requires it, $`\mathcal{A}[p]`$ is defined in Lemma 3.3 only for primes $`p\mid n`$, and the remark itself speaks of an arbitrary prime $`p`$.

### 31. Table 2 — "polylog only for smooth/typical $`n`$" (lines 1130–1131)

- **(a) Severity:** FALSE ("typical"; consequential to entry 19; outside the formalized ranges).
- **(b) Current:**
```latex
1130: Detection, average case & $O(n^2)$; polylog for random $n$ &
1131: $O(\sum_{p\mid n}p^d)$; polylog only for smooth/typical $n$ \\
```
- **(c) Proposed:**
```latex
Detection, average case & $O(n^2)$; polylog claimed for random $n$ &
$O(\sum_{p\mid n}p^d)$; polylog only on a set of $n$ of density $0$
(e.g.\ polylog-smooth $n$) \\
```
- **(d) Lean:**
  - "polylog only on a set of $`n`$ of density $`0`$": `ShiftSym.P08.remPolylogRandomN_proved`. For every $`C`$ and exponent $`k`$, the $`n`$ with $`\sum_{p\mid n}p^d\le C\log^k N`$ have natural density zero, so every set of $`n`$ on which the bound is polylogarithmic has density zero.
  - "e.g. polylog-smooth $`n`$": `ShiftSym.P08.remPolylogSmooth_proved`. For every exponent $`c`$, the bound is polylogarithmic on the $`n`$ whose prime factors are all at most $`\log^c n`$. This is the sufficiency direction only; the cell makes no necessity claim.
- **(e) Justification:** The $`n`$ for which the bound is polylogarithmic form a set of natural density zero, so they are not "typical". The 2D column restates the 2019 claim, which is false as a claim (entry 19).
- **Revised after the third checker reports:** both checkers (A blocking) objected to "polylog only for polylog-smooth $`n`$". It asserts that polylog-smoothness is necessary and identifies the exceptional set with the polylog-smooth $`n`$. The claim is elementarily true (each $`p^d`$ is at most the sum), but no frozen statement certifies it, and the Revision 3 Checker note under entry 19 rejected exactly this content for contribution (iv). The new cell states the density-zero fact of `remPolylogRandomN_proved`, as contribution (iv) does, and gives the polylog-smooth $`n`$ as an example, which is the certified sufficiency direction (B's suggestion). A's alternative, "polylog for polylog-smooth $`n`$, a set of density $`0`$", is also true. But certifying "a set of density $`0`$" for the polylog-smooth $`n`$ needs a composition of the two theorems (fix the exponent $`c`$, take $`C,k`$ from `remPolylogSmooth_proved`, then apply `remPolylogRandomN_proved`), so the adopted wording avoids it.

### 32. Appendix A, proof of Theorem 6.1 — the imported 2D base step (lines 1325–1327)

- **(a) Severity:** CITATION. The imported inequality is true; the source's case split is incomplete.
- **(b) Current:**
```latex
1324: $d=2$: $F_2(n,\sigma)=(n{+}1)\sigma^n-n\sigma$ and the claim is
1325: \cite[Lemma~E.21]{banda2019}; we import its base step
1326: ($q^1>(n{+}1)\sigma^n-n\sigma$ at composite $n$, final display of the
1327: source proof), while the chain step is re-proved uniformly by
```
- **(c) Proposed** (replace lines 1326–1327 up to "while"):
```latex
($q^1>(n{+}1)\sigma^n-n\sigma$ at composite $n$, final display of the
source proof; the inequality holds at every composite $n$, including the
prime powers $p^\alpha$, $\alpha\ge2$, which the source's case split
(``If $k=1$, i.e., $n$ is a prime'') does not treat, and it is
machine-checked, Section~\ref{sec:formal}), while the chain step is re-proved uniformly by
```
- **(d) Lean:** `ShiftSym.P10.baseD2_proved` (for every composite $`n`$, $`\sigma\ge2`$). Theorem 6.1 itself does not depend on the import: `ShiftSym.lowerBound_proved`. The source quotation was checked against arXiv:1703.09030v2 (proof of Lemma E.21: "If $`k = 1`$, i.e., $`n`$ is a prime, the equality holds as shown in Corollary E.20. If $`k > 1`$ …").
- **(e) Justification:** $`k=\omega(n)=1`$ also covers prime powers, which the source's branch misreads as primality. The imported display holds for all composites, so the $`d=2`$ argument is valid. The slip could be added to the companion erratum.

---

## Further reviewer observations: not proposed, need a certificate or are optional

- **Lines 661–662, "for $`n\in\lbrace3,4\rbrace`$ the two are comparable":** this is vague. If "the two" means the union prefactor $`\mathrm{sopf}_d(n)`$ and $`N-1`$, it is misleading: at $`n=4`$, $`\mathrm{sopf}_d(4)=2^d-1\ll4^d-1`$. It is true for $`2\log_2(n)n^{d-1}`$ vs $`N-1`$. S06 recorded it as non-mathematical, and no comparison theorem is frozen, so no wording is proposed. Adding a one-line Lean lemma would allow e.g. "(for $`n\in\lbrace3,4\rbrace`$, $`2\log_2(n)\thinspace n^{d-1} > N-1`$)".
- **Line 765, "image translation":** literal translation by a vector $`\mathbf w`$ is itself an equivariant CA. A kernel-checked `example` in `S07_Dynamics.lean` gives `caMap (fun _ => w) (fun x => x 0) = shift w` by `rfl`. So the paper means the image-processing task of [banda2019]. An optional clarification is "image translation (the image-processing task of \cite{banda2019})".
  *Update 2026-10-19 (v5):* following finding 2 of the independent review, the sentence became "every pattern-recognition or image-processing task whose required output breaks a symmetry of some admissible input". *Update 2026-10-27 (v7):* that clause had no frozen statement and is strictly more than `insolvGeneralStatement` (on $`\mathbb{Z}_4`$, $`0000	o0101`$ breaks a symmetry of the input although the output is shift-symmetric). It is now frozen and proved, `ShiftSym.P07.insolvSymBreak_proved` and `ShiftSym.P07.insolvFull_proved` (supplement `S07_Dynamics_SymmetryBreaking.lean`, Run 027). Its "This covers" was imprecise (IMPRECISE: the corollary's stated argument "no trajectory leaves $`S_{n^d}`$" does not exclude such tasks; the stabilizer form of Theorem 8.1 does), so v7 rewords it: "More generally, since $`\operatorname{Stab}`$ can only grow along a trajectory (Theorem~\ref{thm:irrev}), every pattern-recognition or image-processing task whose required output breaks a symmetry of some admissible input is unsolvable, as in the two-dimensional discussion of \cite{banda2019}."

---

## Formal-verification section and Open Problem 3

### Facts the new text relies on, checked today

| Item | Value | Source |
|---|---|---|
| Lean / library | Lean 4 v4.33.0-rc1 + mathlib (rev `e76b9967…`) | `lean-toolchain`, `lake-manifest.json` |
| Core layer | 3165 lines: `Definitions` 87, `Statement` 113, 15 lemma modules 2795, `Audit` 150, `Experiments` 20. The theorems are `ShiftSym.enumeration_proved` and `ShiftSym.lowerBound_proved` | `wc -l` |
| Paper-wide layer | 48 modules, 23 290 lines: `Paper/Common.lean` 27, 11 statement modules 9270, 35 proof modules 13 884, `AuditPaper.lean` 109 | `wc -l` |
| Reused E1 modules | `Shiftsym/Lemmas/Relative.lean` 391 lines + `Shiftsym/StatementE1.lean` 122 lines ($`\approx 510`$; Relative imports StatementE1, which imports only the core `Lemmas/Evaluate`). `relativeEnumeration_proved` is applied in `P05_KActive_Rank` (Theorem 5.1, `kActive_proved`), `relative_regroup` in `P10_AppendixLemmas_Core` (union interpretation of the truncations $`q^m`$, Appendix A), and `P10_AppendixLemmas_Basic` imports the module. No other E1/E2 module (`Linear`, `StatementE2`, `Mismatch`, `Ext/`) is imported by any paper-layer file | `grep '^import'` in `Paper/` |
| Frozen statements per group | S01 §2 Model + the §3-preamble Gaussian-binomial sentence (lines 261–264) **31**; S02 §3 **20**; S03 Lemma 4.1/Def. 4.2/Table 1/Duality **22**; S04 §4 rest **48**; S05 §5 + Cor. 7.2 **31**; S06 §6 + Cor. 7.1 **41**; S07 §8 + Fig. 1 caption (`fig:pattern-flip`, a §7 figure) **31**; S08 §9 **25**; S09 Props 10.1–10.2 + Fig. 2 caption (`fig:rate-classes`) **21**; S10 Appendix A **33**; S11 Obs. 7.3, Rem. 10.3 + Fig. 3 caption (`fig:inversion`), Obs. 10.4–10.5 **34**; total **337** | `grep -c '^def .*Statement'`; gate reports |
| Proofs | 337/337 `X_proved`, each of type literally `X`, or `∀ params, X params` for a parameterized `X` (gate step 4; `AuditPaper` checks this shape with `forallTelescope`); about 1060 named theorems in the proof modules | gate reports, `AuditPaper.lean` |
| Refutations of literal readings | Not counted exactly in the new text ("several"). Frozen counter-statements and evidence for corrections include `locFromFourRefuted`, `conventionScopeLiteral`, `banda2019Eq29Standard`, `banda2019Eq32/33PrintedFalse`, `levelSetInvariantFalse`, `dcOffsetLimit`, `measuredGapCause`, `dstarLiteralDegenerate`, `dstarUnclampedByTheta`, `compositeNearestPrimeFail`, `inversionD3Scope` (12; the total depends on whether one also counts e.g. `naiveCounterexample` and `extremaBoundary`) | S01, S05, S06, S07, S11 |
| Strengthenings | Several, all disclosed in docstrings: e.g. `compositeAdvantageD2` ("Strengthening (documented)": an infinite theorem for every $`\sigma\ge2`$), `dstarAllPrimes` (EXTENSION, all primes), `locNotEquivariantFromTwo` ("sharper truth"), and minor ones in S04 and S07 | S01, S04, S07, S11 |
| Docstrings | All 337 statements have one. 137 contain an explicit "verbatim" paper quotation, and about 128 more quote the paper in quotation marks. The rest cite line numbers only (e.g. `refValue32Statement`, whole-statement conjunctions), or are bridges/evidence marked "not a paper claim" (16) | script count over `S*.lean` |
| Axioms | only `propext`, `Classical.choice`, `Quot.sound` (some theorems use fewer) | gate reports |
| Forbidden constructs | no `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, `implemented_by`, `extern`, kernel-bypass options. Numerical certificates use `decide +kernel` (kernel evaluation) | `gate.py`, P11 header |
| Kernel replay | 73 modules: exactly the modules reachable from `import Shiftsym` (root `Shiftsym.lean` in the working copy, which imports core, E1, E2 and the paper layer). The root imports 72 modules; the 73 include the root itself. 2783 theorems and 717 definitions re-sent to the kernel, 0 errors. Six compiler-generated non-safe auxiliaries (`ShiftSym.gaussBinom._unsafe_rec`, `ShiftSym.cseq._unsafe_rec` and four in `ShiftSym.P08`) were skipped. The kernel does not check unsafe declarations, and safe declarations cannot refer to them. The replay ran 20 s before the last edit of `Shiftsym.lean`, but it also imported `AuditPaper`, so it covered the same 73 modules (checker B). The `lean_lib` globs `["Shiftsym", "Shiftsym.+"]` build 80 modules. The 7 not replayed are `Shiftsym/Basic.lean` (placeholder `def hello`) and the 6 `Shiftsym/Ext/` statement files (frozen E1/E2 extension Props, no proofs, not used by the paper) | `reports/kernel_replay.txt` (05:15, after the last proof edit at 04:16); `Shiftsym.lean`; `find Shiftsym -name '*.lean'` (79 files + root) |
| Reviews | per group: referee PASS; fidelity reviews PASS under the paper-to-Lean, exploit and numeric lenses | `prove_result.json`, `freeze_result.json` |
| Coverage | §§2–10 (lines 196–1050) and Appendix A (lines 1166–1342). Not formalized: abstract, introduction, §11, Table 2/conclusion. Proof-internal steps of the prose proofs are frozen only selectively (some in S03, S05, S09 and S10; S06, for instance, freezes no proof step of Theorem 6.3(ii)). The formal proofs take their own routes | S-file headers, fidelity "uncovered" lists |

**Preconditions before the paper can say this:**
1. `Shiftsym/Paper/` and `Shiftsym/AuditPaper.lean` are **untracked in git** and must be committed. So must the **modified** root `Shiftsym.lean` (git status `M`), which adds the 48 imports of `Paper/` and `AuditPaper`. Without it, `import Shiftsym` would not reach the paper layer, and the 73-module kernel replay would not be reproducible from the repository. `Shiftsym/Ext/` is also untracked; it holds frozen E1/E2 extension statements without proofs, is not part of the paper, and is not counted below. It must stay out of the committed library until its statements are proved (checker B). The six files match the `Shiftsym.+` glob, so once committed they would be built by default, and the §11 sentence "Every frozen statement … of the core and paper-wide layers has a theorem `X_proved`" depends on that restriction. Possible ways: keep `Ext/` uncommitted, move it outside the glob (e.g. into a separate `lean_lib`), or commit it only together with proofs. It is still being edited (the latest file, `SX2c_AutocorrUpper.lean`, changed at 06:38 today) and has no build products. `research/formal/check_placeholders.py` (untracked) should be committed or removed.
2. `research/formal/STATEMENT_PRESERVATION.md` and `FORMALIZATION_PLAN.md` do not yet mention Phase H. The new text refers to per-statement docstrings and should also point to an updated preservation table.
3. A clean `lake build` should be run (the default `globs` builds every `Shiftsym.*` module, so `AuditPaper` runs), with the log recorded, together with the `Audit.lean`/`AuditPaper.lean` axiom printout and the `sorry` grep (CLAUDE.md gates). In a working copy that still contains `Shiftsym/Ext/`, the glob compiles those files too. So the build should be run on a checkout of the commit itself (precondition 1), or after `Ext/` has been moved outside the glob.
4. The paper text below assumes entries 1–32 are adopted. "Every numbered statement is certified" means: in the corrected form.

### Proposed new §11 (replaces lines 1055–1105)

```latex
The mathematical content of every numbered statement of
Sections~\ref{sec:model}--\ref{sec:empirical} and
Appendix~\ref{app:lower} has been formally verified in the Lean~4 proof
assistant (v4.33.0-rc1) on top of the \textsf{mathlib} library: that of
all definitions, lemmas, theorems, propositions, corollaries, remarks,
and computational observations there, of Table~1, of the table of
Remark~\ref{rem:dc-measured}, and of the captions of
Figures~\ref{fig:pattern-flip}--\ref{fig:inversion}, together with every
mathematical claim in the surrounding (non-proof) prose that is precise
enough to be stated formally. Statistical summaries (such as the fitted
constant $C$ of Observation~\ref{obs:dstar}), vague, bibliographic, and
record-keeping sentences, and the summary table of the concluding section
are not formalized. Where the verification found
a mathematical claim of an earlier version ambiguous or false, the text
above states the corrected claim, and that is the claim certified.

The development has two layers. The core layer ($\approx$3200 lines: 15
lemma modules plus definition, statement, experiment, and audit files)
defines the model from first principles --- lattice, configurations,
shifts, stabilizers, fixed sets, equivariant maps --- and proves the two
main theorems:
\begin{itemize}
    \item \texttt{enumeration\_proved}: Theorem~\ref{thm:main-enum} for
    all $n\ge2$, $d\ge1$, $\sigma\ge1$, exactly as stated ($\sigma\ge1$
    being weaker than the standing alphabet assumption $\sigma\ge2$ of
    Section~\ref{sec:model});
    \item \texttt{lowerBound\_proved}: Theorem~\ref{thm:lower-bound}
    verbatim ($n\ge2$, $d\ge1$, $\sigma\ge2$), including both directions
    of the equality-iff-prime characterization.
\end{itemize}
The paper-wide layer ($\approx$23\,300 lines in 48 modules) states and
proves everything else: 337 \texttt{Prop}-valued statements (including
selected proof-internal claims, representation bridges, a
few disclosed strengthenings, and machine-checked evidence for the
corrections), organized by part of the paper ---
Section~\ref{sec:model} with the convention sentence opening
Section~\ref{sec:prelim} (31), the rest of
Section~\ref{sec:prelim} (20), Lemma~\ref{lem:mobius},
Definition~4.2, Table~1 and the Duality remark (22), the rest of
Section~\ref{sec:enumeration} (48), Section~\ref{sec:kactive} with
Corollary~\ref{cor:dens} (31), Section~\ref{sec:bounds} with
Corollary~\ref{cor:prob} (41), Section~\ref{sec:dynamics} with the
caption of Figure~\ref{fig:pattern-flip} (31),
Section~\ref{sec:detection} (25),
Propositions~\ref{prop:rate}--\ref{prop:inversion} with the caption of
Figure~\ref{fig:rate-classes} (21),
Appendix~\ref{app:lower} (33), and
Observation~\ref{obs:extrema}, Remark~\ref{rem:dc-measured} with the
caption of Figure~\ref{fig:inversion}, and
Observations~\ref{obs:dstar}--\ref{obs:inversion} (34). Some of its proofs
also use certified results of a companion development (two further
modules, $\approx$510 lines): the proof of Theorem~\ref{thm:kactive}
uses the relative enumeration theorem, which extends the
inclusion--exclusion behind Theorem~\ref{thm:main-enum} from the set of
all configurations to an arbitrary set of configurations, and proofs in
Appendix~\ref{app:lower} use its weight-generic regrouping lemma.
Multi-part results
are stated part by part and as a whole; asymptotic claims carry explicit
quantifiers; a rounded decimal is stated as the interval its rounding
asserts; the detection algorithm of Section~\ref{sec:detection} is a Lean
function with explicit read counting, and its statements are quantified
over every enumeration of the subgroups, every traversal order, and both
variants of a failing orbit walk (except the exact factor of
Remark~\ref{rem:polylog}, which is stated for completed walks only); the
density-uniform distribution of
Corollary~\ref{cor:dens} is a probability mass function in
\textsf{mathlib}. Numerical claims are proved with exact integer
certificates checked by the Lean kernel, combined, for large lattices
(up to $14^9$ cells in Remark~\ref{rem:dc-measured}), with proved
analytic bounds such as the one-fixed-set and union bounds; no compiled
code or floating-point arithmetic is trusted.
Several of the 337 statements record, as machine-checked facts, why an
earlier wording or a cited formula fails in its literal reading.

All formal statements were frozen as \texttt{Prop}-valued definitions
\emph{before} their proofs were written, each with a documentation string
that locates the passage it formalizes, in most cases quoting it
verbatim, and records its representation choices
(e.g.\ the alphabet is realized as $\{0,\dots,\sigma-1\}$, harmless since
only $|\Sigma|$ enters; rank vectors are reindexed by divisors of
$(p_1\cdots p_k)^d$; quotients are exact), and each group of statements
passed independent reviews of its fidelity to the paper. Every frozen
statement \texttt{XStatement} of the core and paper-wide layers has a
theorem \texttt{X\_proved} whose type is literally \texttt{XStatement}
or, for a statement with parameters,
$\forall$\,\texttt{params, XStatement params}. A few details of the
corrected text, such as the constant $20$ in
Proposition~\ref{prop:inversion}, are certified by auxiliary theorems of
the formal proofs, which are kernel-checked but were not frozen in
advance. Two audit modules are part of the default build: one prints the
axiom set of every declaration it lists from the core layer and from
companion developments, and one discovers all frozen statements of the
paper-wide layer from the environment and fails the build unless each
has such a theorem depending only on the three standard axioms of the Lean/mathlib
foundation (propositional extensionality, choice, quotient soundness). The
development contains no unproved placeholder and no further axiom, and
every theorem and every safe definition in the 73 modules reachable from
the library's root module, the root included (2783 theorems and 717
definitions, including those of companion extension modules not
discussed here), was additionally re-checked by the Lean kernel.

Three features of the formalization deserve mention. First, it is
self-contained precisely where the prose leans on the literature: the
signed spanning-set count (Lemma~\ref{lem:mobius}), the Grassmannian
subspace count, and the $p$-group M\"obius evaluation (in its
subspace-lattice instance) are proved from first principles; so are the
ingredients of the second derivation of Section~\ref{sec:second-derivation}
--- Lemma~7(i) of \cite{cg2017} for every finite group, the product rule
for the M\"obius function of the subgroup lattice, and Hall's evaluation
on the primary components of $\A$ --- as well as the bounds of
\cite{gjs2016} and \cite{cg2017} specialized to $\ZZ_n^d$ and
\cite[Lemmas~E.21, E.22]{banda2019}. No verified step rests on the cited
results of Stanley, Hall, or Hawkes--Isaacs--\"Ozaydin. Second, the certified proof
of Theorem~\ref{thm:lower-bound} takes a shorter route than
Appendix~\ref{app:lower}: with the enumeration theorem available as a
verified identity, the prime case reduces to a reindexing of divisors of
$p^d$, and the composite case follows from the single fixed-set bound
$|S_{n^d}|\ge\sigma^{n^d/p_1}$ ($p_1$ the least prime factor) together with
elementary coefficient estimates (chiefly $\gaussbinom dr_q\le 2^d
q^{r(d-r)}$). In particular the certified chain nowhere invokes
\cite[Lemma~E.21]{banda2019} or its erratum, so the verified results are
independent of the published 2D bounds and their repairs. Third, and more
generally, the prose proofs are not replayed line by line: the formal
proofs follow their own routes, and proof-internal claims of the prose
proofs are formalized only selectively.

The Lean sources reside in \texttt{research/formal/shiftsym/} in the
project repository (the paper-wide layer in
\texttt{Shiftsym/Paper/} and \texttt{Shiftsym/AuditPaper.lean}), together
with the formalization plan and the
statement-preservation table.
```

Notes on the replacement:
- "Definition~4.2" is cited by number because Definition 4.2 has no `\label`. Table 1 and the Duality remark are likewise unlabelled; adding `\label{tab:coef}`/`\label{rem:duality}` would allow `\ref`s.
- The core-layer theorem descriptions are kept verbatim from the current text; they remain accurate.
- "Lemmas E.21, E.22 … specialized": E.21 is `ShiftSym.P06.e21_proved`, derived from `lowerBound_proved` at $`d=2`$, and the base step is `ShiftSym.P10.baseD2_proved`. E.22 is `ShiftSym.P06.e22Bound_proved`. GJS and CG Thm 5(ii) specialized are `ShiftSym.P06.gjsBound_proved` and `ShiftSym.P06.cgBound_proved`. The second derivation is `ShiftSym.P04.secondDerivation_proved`, with `cgLemma7i_proved`, `mobiusMultiplicative_proved` and `hallMobius_proved`.
- "Two audit modules … default build": `Audit.lean` is imported by `Shiftsym.lean`. So is `AuditPaper.lean`, in the working copy (precondition 1). It is also built by the default target through `globs = ["Shiftsym", "Shiftsym.+"]` in `lakefile.toml`. It throws an error, failing the build, on any missing or ill-typed `_proved` or disallowed axiom.
- "every declaration it lists from the core layer and from companion developments" / "all frozen statements of the paper-wide layer": `Audit.lean` runs `#check` and `#print axioms` on a hand-written list of core, E1 and E2 declarations (lines 29–150) and cannot fail the build. `AuditPaper.lean` scans the constants `ShiftSym.Pxx.<X>Statement` declared in modules `Shiftsym.Paper.Sxx_*` ($`xx=01,\dots,11`$) and throws an error on any violation (checker B).
- "`XStatement` … `X_proved`": the naming convention of all layers (`enumerationStatement`/`enumeration_proved`, `locIffStatement`/`locIff_proved`). The sentence is restricted to the core and paper-wide layers because `Shiftsym/Ext/` holds frozen extension statements without proofs (precondition 1).
- "A few details … auxiliary theorems": the three helper-certified details listed under the conservativeness rule (`const_of_stab_prime`, `p10_lt_p9_d3`, `window_i`/`window_ii`).
- "exact integer certificates … combined … with proved analytic bounds": the header of `Paper/Proofs/P11_Numerics_Meas.lean` says "one fixed set / the union bound / the first two terms of Corollary 4.4 (large lattices) and exact values (`p = 5`); all numerical certificates are integer inequalities checked by `decide +kernel`". The kernel never evaluates $`\sigma^{14^9}`$, which has about $`2\cdot10^{10}`$ bits (checker A).
- "the summary table of the concluding section": Table 2 (§12), which was not formalized (facts table, Coverage).
- "relative enumeration theorem … weight-generic regrouping lemma … two further modules, $`\approx 510`$ lines": `ShiftSym.relativeEnumeration_proved` and the weight-generic `relative_regroup` in `Shiftsym/Lemmas/Relative.lean` (391 lines), with its frozen statement file `Shiftsym/StatementE1.lean` (122 lines). These lie outside both counted layers, which is why the sentence is needed (see the facts table). The paper does not mention the E1 extension, hence "a companion development". The weighted identity can be named explicitly if the authors prefer: $`\lvert X\cap S_{n^d}\rvert=\sum_H c(H)\thinspace \lvert X\cap\mathrm{Fix}(H)\rvert`$ for any $`X`$.
- "73 modules reachable from the library's root module, the root included": the root `Shiftsym.lean` imports 72 modules, and the replay count of 73 includes the root. The globs build 80 modules. The 7 others are a placeholder and the 6 unproved `Ext/` statement files (facts table).
- "every safe definition": the replay skipped the six compiler-generated `*._unsafe_rec` auxiliaries listed in `kernel_replay.txt`. They are irrelevant to soundness. In print, "safe" is Lean's own term for declarations that the kernel checks.
- "literally X or, for a statement with parameters, $`\forall`$ params, X params": this is the shape that `AuditPaper.lean` checks (`forallTelescope pci.type`, error message "type is not $`\forall`$ params, X params"). Most frozen statements are closed `Prop`s, so their `_proved` theorems have type literally `X`.
- Group labels: S01 also covers the §3-preamble sentence (lines 261–264), S07 the caption of Fig. 1 (`fig:pattern-flip`), S09 the caption of Fig. 2 (`fig:rate-classes`), and S11 the caption of Fig. 3 (`fig:inversion`). All three figure labels exist (lines 735, 931, 1001).
- "Some of its proofs also use certified results of a companion development": `P05_KActive_Rank` applies `ShiftSym.relativeEnumeration_proved`, and `P10_AppendixLemmas_Core` uses `ShiftSym.relative_regroup` (checker B).
- "except the exact factor of Remark~\ref{rem:polylog}": `remPolylogFactorConservativeStatement` is stated for `detect false` (completed walks) only (entry 16).
- "in most cases quoting it verbatim": about 265 of the 337 docstrings quote the paper; the others cite line numbers or are marked "not a paper claim" (facts table).

**Revised after the checker reports (§11):**
- *E1 dependency* (checker A): the two counted layers omitted `Lemmas/Relative.lean` and `StatementE1.lean`. `P05_KActive_Rank` (Theorem 5.1) applies `relativeEnumeration_proved`, and the Appendix A proofs use `relative_regroup`. A sentence now says so, and the facts table counts the files ($`\approx 510`$ lines).
- *Module count* (checker A): "the 73 modules of the library" became "the 73 modules imported by the library's root module". The globs build 80 modules, and the replay covered the 73 reachable from `import Shiftsym`.
- *Walk variants* (checker B): the exception `remPolylogFactorConservativeStatement` (completed walks only) is now stated, consistently with entry 16.
- *Strengthenings* (checker B): "one strengthening" became "a few disclosed strengthenings". `compositeAdvantageD2`, `dstarAllPrimes`, `locNotEquivariantFromTwo` and minor ones in S04/S07 are all documented as such.
- *Docstrings* (checker B): "quotes the paper verbatim and lists every representation choice" became "locates the passage it formalizes, in most cases quoting it verbatim, and records its representation choices". Evidence Props such as `dcOffsetLimit`, `measuredGapCause` and `inversionD3Scope` are "not a paper claim", and short docstrings such as `refValue32Statement` cite only a line number.
- *"Eleven"* (checker B): the count left out `banda2019Eq29Standard`, which plays the same role, and any exact count depends on what is counted. The text now says "Several".
- *First sentence* (checker B, consequential to the title/introduction finding): it now speaks of the mathematical content of the numbered statements, and it says explicitly that statistical summaries (Obs. 10.4's $`C`$) are not formalized.
- *Precondition* (checker A): the modified `Shiftsym.lean` is listed among the files to commit.

**Revised after the second checker reports (§11):**
- *Module count* (checker A): "73 modules imported by the library's root module" became "73 modules reachable from the library's root module, the root included". The root imports 72 modules.
- *Unsafe auxiliaries* (checker A): "every theorem and definition" became "every theorem and every safe definition". The six skipped declarations are listed in the facts table.
- *Parameterized statements* (checker A): "whose type is literally X" now adds "or, for a statement with parameters, $`\forall`$ params, X params", which is what `AuditPaper` checks. The status paragraph and the facts table say the same.
- *Group labels* (checkers A and B): the captions of Figs. 1–3 and the §3-preamble sentence are now named in the group list and in the facts table. The totals were already right (B re-verified 31/20/22/48/31/41/31/25/21/33/34 = 337).
- *Proof-internal claims* (checker B): the earlier "proof-internal claims are formalized only where the text asserts them as facts" overstated the coverage, since every proof step is asserted as fact and many are not frozen. The text now says "(non-proof) prose", "selected proof-internal claims" and "formalized only selectively".
- *Companion development* (checker B): Theorem 5.1 uses the relative enumeration theorem, and Appendix A uses the weight-generic regrouping lemma. The text now names both.
- *"the text above states the corrected claim"* (checker B): restricted to "a mathematical claim". The two unadopted optional items (lines 661–662 and 765, "Further reviewer observations") are classified non-mathematical in S06/S07, so the restricted sentence is accurate without them.

**Revised after the third checker reports (§11):**
- *Scope of the first sentence* (checker B): "every numbered statement of this paper" also covered the summary Table 2 of §12, which is not formalized. The sentence now speaks of Sections 2–10 and Appendix A, and the summary table is listed among the unformalized items.
- *Numerical claims* (checker A): the old wording suggested that the kernel evaluated the probabilities on lattices with up to $`14^9`$ cells exactly, which is impossible. The new wording names the integer certificates and the proved bounds, as the `P11_Numerics_Meas` header does.
- *Audit modules* (checker B): `AuditPaper.lean` scans only the paper-wide layer, and `Audit.lean` prints the axioms of a listed set of core and companion declarations without being able to fail the build. The sentence now says so.
- *Frozen statements* (checker B): the sentence is restricted to the core and paper-wide layers (see the `Ext/` precondition), and the naming is now exact.
- *Helper-certified details* (checker B): one sentence discloses that a few details rest on auxiliary theorems that were not frozen in advance.
- *Location of the sources* (checker B): `Shiftsym/AuditPaper.lean`, one of the 48 counted modules, lies outside `Shiftsym/Paper/`. The last paragraph now names it.

### Open Problem (3) (lines 1161–1165)

- **Current:**
```latex
1156: \paragraph{Open problems.}
1157: (1) A theorem (not only computation) delimiting for which $(n,d)$ the
1158: prime-dip/even-peak pattern of $P^{\mathrm{unif}}$ holds. (2) Extension to
1159: rectangular tori $\ZZ_{n_1}\times\dots\times\ZZ_{n_d}$ (the preliminary
1160: lemmas hold; the subspace-lattice step requires per-prime ranks over
1161: possibly unequal torsion ranks). (3) Extending the formalization of
1162: Section~\ref{sec:formal} beyond the two main theorems, to
1163: Theorem~\ref{thm:kactive} and to the upper bounds of
1164: Theorem~\ref{thm:upper-bound} (the latter needs real-exponent
1165: machinery).
```
- **Proposed:** delete item (3), which is now resolved. Replace lines 1161–1165 with:
```latex
possibly unequal torsion ranks).
```
  This leaves "Open problems." with items (1)–(2). If the authors want the resolution recorded, append one sentence to the first paragraph of §11: "In particular, Theorem~\ref{thm:kactive} and the upper bounds of Theorem~\ref{thm:upper-bound} are certified (\texttt{kActive\_proved}, \texttt{upperBounds\_proved}); the latter use real powers and base-2 logarithms from \textsf{mathlib}."
- **Lean:** `ShiftSym.P05.kActive_proved` (Theorem 5.1, for all $`n\ge2`$, $`d\ge1`$, $`\sigma\ge1`$, $`0\le k\le N`$), `ShiftSym.P06.upperBounds_proved` (Theorem 6.3 (i) and (ii)), `ShiftSym.P06.upperUnion_proved` and `ShiftSym.P06.upperClosed_proved`.

### Open Problem (1) (lines 1157–1158) — consequential, optional

Found while applying the checker reports to entries 13 and 28. Open Problem (1) asks for "a theorem (not only computation) delimiting for which $`(n,d)`$ the prime-dip/even-peak pattern of $`P^{\mathrm{unif}}`$ holds". Two parts of that are now certified:
- the prime-dip half at $`d=2`$, for every prime $`p\ge5`$ and every $`\sigma\ge2`$ (`ShiftSym.P11.compositeAdvantageD2_proved`);
- the failure of the pattern at every $`d\ge3`$ for $`\sigma=2`$ (`ShiftSym.P11.extremaBreaks_proved`, via $`P(6^d) < P(5^d)`$).

The even-peak half at $`d=2`$ and the per-$`n`$ delimitation for $`d\ge3`$ remain open. A possible narrowed wording: "(1) A theorem (not only computation) for the even-peak half of the $`d=2`$ pattern of $`P^{\mathrm{unif}}`$, and a delimitation of its local extrema for $`d\ge3`$ (the prime-dip half at $`d=2`$ holds for every prime $`p\ge5`$ and every $`\sigma\ge2`$, Observation~\ref{obs:inversion}, and the pattern fails at every $`d\ge3`$ for $`\sigma=2`$, Observation~\ref{obs:extrema})." Whether to keep the open problem as stated is the authors' call. No wording is proposed as mandatory.

### Title-page tag (line 47)

- **Current:**
```latex
47: \date{October 2026 --- revised draft (v3.1, post-audit, formally verified)}
```
- **Proposed** (the version number is the authors' call):
```latex
\date{October 2026 --- revised draft (v3.2, post-audit, formally verified in Lean~4)}
```
- **Revised after the third checker reports:** the Revision 3 tag ("mathematical content of all numbered statements formally verified in Lean~4") lacked the qualifier "statistical summaries aside" that §11, the introduction and the abstract carry (checker A). In addition, "all numbered statements" also covers the summary Table 2, which is not formalized (checker B). The tag now uses the fallback both checkers offered, and §11 states the scope. The Revision 3 decision to keep the longer tag is withdrawn.

### Consequential sentences elsewhere (optional, same backing as §11)

- **Introduction, lines 147–151.** Current:
```latex
147: bounds of \cite{banda2019} is also included there.} Beyond testing and
148: review, both main theorems are \emph{machine-checked}:
149: Theorems~\ref{thm:main-enum} and~\ref{thm:lower-bound} have been formally
150: verified in the Lean~4 proof assistant, in the generality stated here
151: (Section~\ref{sec:formal}).
```
  Replace lines 148–151 (line 147, ending "Beyond testing and", is kept) with:
```latex
review, the numbered results are \emph{machine-checked}:
Theorems~\ref{thm:main-enum} and~\ref{thm:lower-bound}, in the generality
stated here, and the mathematical content of the other numbered
statements of Sections~\ref{sec:model}--\ref{sec:empirical} and
Appendix~\ref{app:lower} (statistical summaries aside) have been formally
verified in the Lean~4 proof assistant (Section~\ref{sec:formal}).
```
- **Abstract, lines 84–87.** After "…subgroup-level evaluators throughout.", optionally add: "The mathematical content of every numbered definition, result, remark, and observation (statistical summaries aside) is, moreover, formally verified in Lean~4." All numbered definitions, results, remarks and observations lie in Sections 2–10 and Appendix A, so this wording excludes the summary table without a section reference.
- **Conclusion, lines 1153–1154.** "each verified computationally at the definition level" could become "each verified computationally at the definition level and formally in Lean~4".
- `CLAUDE.md` and `README.md` repository-map lines about the Lean development ("Both main theorems are kernel-verified, ~3100 lines") should be updated with the Phase H layer after the commit.
- **Revised after the checker reports (title, introduction, abstract):** checker A objected that "the paper is machine-checked" overclaims, since the abstract, introduction, Table 2 and the conclusion are not formalized. Checker B objected that "every numbered statement" overclaims as well, since numbered statements contain parts that were deliberately not frozen, such as the statistical fit $`C\approx2.2`$–$`2.65`$ of Obs. 10.4 (NON-MATHEMATICAL in `obsDstarStatement`) and record-keeping sentences. All three texts, and the first sentence of the new §11, now say "the mathematical content of / every mathematical claim of" the numbered statements.
- **Revised after the second checker reports (introduction, abstract):** checker A noted that "every mathematical claim of the other numbered statements" in the introduction claims more than §11, which explicitly leaves statistical summaries unformalized. One example is the fitted $`C`$ of Obs. 10.4, which becomes a fairly precise numerical claim once entry 27 defines the fractional $`d^{\ast}`$. The introduction now reads "the mathematical content of the other numbered statements (statistical summaries aside)", and the optional abstract sentence carries the same qualifier. The title tag is kept (see "Not adopted as suggested" under Revision 3).
- **Revised after the third checker reports (introduction, abstract):** aligned with the restricted first sentence of §11 (checker B's point about Table 2). The introduction now names Sections 2–10 and Appendix A. The optional abstract sentence speaks of numbered definitions, results, remarks and observations, which leaves out the summary table without a section reference. The title tag now uses the fallback (above).
