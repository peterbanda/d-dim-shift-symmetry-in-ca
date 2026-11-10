# Fidelity review: the window constant 20 of Proposition 10.2 (2026-10-22)

Subject: `research/formal/shiftsym/Shiftsym/Paper/S09_CrossoverLaws_Window20.lean`, the
group-09 supplement with the frozen statements `inversionExplicitWindow20Statement` (criteria
form), `inversionWindow20Statement` (probability form) and `inversionLaw20Statement`
(Proposition 10.2 as stated in paper v5). The paper sentence is `shift_symmetry_d_dimensions.tex`
lines 997–1000: "(i) applies to every integer $d\ge1$ with $d\le d_c(p)-20$, and (ii) to every
integer $d\ge d_c(p)+20$." Logged as Run 025 in `../README.md`.

## Procedure

As in Phase H (`research/formal/STATEMENT_PRESERVATION.md`, "Procedure"): three fresh-context
reviewers with different angles, each working from the paper and the draft file, none seeing the
others' reports. The `_proved` theorems were written only after all three passed. Two mechanical
checks came first: each window body is, token for token, the reviewed group-09 `∃ C` body with
`C := 20`, and `fun h => ⟨20, h⟩` type-checks from each new window statement to its `∃ C` original.

The statements were frozen after the helper theorems `window_i` / `window_ii` (which supplied the
paper's 20) existed, so the Phase H guarantee "frozen before any proof" does not apply to them;
fidelity rests on these reviews.

| Reviewer | Angle | Verdict | Artifacts |
| --- | --- | --- | --- |
| A | literal comparison, symbol by symbol, against the elaborated terms | PASS | `A_literal/Check.lean`, `A_literal/Check2.lean` |
| B | exploit hunting: vacuity, junk values, coercions, truncating subtraction | PASS | `B_exploits/Check.lean` (output `check_output.txt`), `B_exploits/num.py` |
| C | numerical reconstruction from the paper alone, against a literal transcription of the Lean | PASS | `C_numerics/` (scripts, outputs, `SHA256SUMS`) |

## Findings and what was done

- A1 (minor): the file header cited Run 025 and the proofs file before they existed. Both now exist.
- A2, B2 (cosmetic): the probability-form docstring said "the sign change … lies in
  (d_c − 20, d_c + 20)", which assumes a single sign change (at p = 3, P₃ = P₄ at d = 1). Replaced
  by the equivalent reading of the two implications.
- A3 (cosmetic): "a dimension that grows linearly in the prime" and "the two-dimensional" were not
  accounted for in the Delta. Pointers added (`dcAsymptoticStatement`; a name for the phenomenon).
- A4 (cosmetic): a header sentence read as if all three Props were `∃ C` bodies. Reworded.
- B1 (minor; a property of the paper's constant, faithfully copied): the lower branch is empty for
  every prime p ≤ 31 and first reached at p = 37, for exactly d ∈ {1, …, 4}. Stated in the docstring
  and kernel-checked in the proofs file (`inversionWindow20_nonvacuous`,
  `inversionWindow20_lower_empty`).
- B3 (process): `check_frozen.py` is red because `Shiftsym/Definitions.lean` differs from its
  recorded hash (commit c909527: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` in the proof fields of
  `stab`; the meaning of every definition is unchanged). Pre-existing; not addressed here.
- B4 (process): the module was not imported yet. Now imported in `Shiftsym.lean` and
  `Shiftsym/AuditPaper.lean`; AuditPaper reports 345/345.
- C: no finding on meaning. Remark: at p = 3, d = 21 the window condition holds with equality
  (d_c(3) = 1 exactly), so numerical checks must resolve that point exactly, not in floating point.

The docstring corrections were made before the file was fingerprinted; the Props did not change
(re-checked mechanically).

## Numbers (reviewer C)

- Grid: 302 primes 3–1999 × σ ∈ {2, 3, 5, 10, 100, 10⁶} × every d from 1 to ⌈d_c(p)⌉ + 60:
  1,260,654 points, 0 disagreements between the paper and Lean readings on the window conditions
  and on the hypotheses of (i) and (ii). Branch (i) exercised at 1,114,494 points (292 primes, from
  p = 37), branch (ii) at 74,298 points, 0 violations. Smallest constants that work on the grid:
  (i) C > 3.036 (p = 7), (ii) C > 1 (p = 3).
- Probability form, composite branch, exact integer comparison: 35 of 35 cases true
  (p ∈ {37, 41, 43, 47}, d ≤ 4, σ ∈ {2, 3}, plus σ = 2 at d = 5 for p ∈ {41, 43, 47}).
- Probability form, prime branch: a rigorous log-space dominance bound from Theorem 4.3 (self-test
  185/185 on small tori) proves the prime advantage at all 74,298 grid points.

## Reproduce

- C (Python 3.14.8, mpmath 1.3.0, sympy; about 10 CPU minutes): in `C_numerics`, run
  `python3 X.py > X_output.txt` for X = sanity_S, check_enum, grid, exact_c, logspace_d (the recorded outputs carry the
  timing lines of the original run, so compare everything else; `sha256sum -c SHA256SUMS` checks the recorded files).
- B (from `research/formal/shiftsym`): `lake env lean ../../experiments/window20_fidelity/B_exploits/Check.lean`.
- A (from `research/formal/shiftsym`): `lake env lean ../../experiments/window20_fidelity/A_literal/Check.lean`
  (it re-declares the draft Props on top of `S09_CrossoverLaws` only, to diff the elaborated terms).
