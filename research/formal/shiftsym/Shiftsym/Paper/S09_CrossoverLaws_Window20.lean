/-
Phase H, group 09 (CrossoverLaws), SUPPLEMENT of 2026-10-22 — the explicit
window constant 20 of Proposition 10.2. FROZEN STATEMENTS, no proofs of them
here (proofs: `Shiftsym/Paper/Proofs/P09_CrossoverLaws_Window20.lean`).

Paper: `shift_symmetry_d_dimensions.tex` (v5), Proposition 10.2
`prop:inversion`, lines 980–1001; the window sentence is lines 997–1000.

Why a supplement. Group 09 (`S09_CrossoverLaws.lean`, unchanged) was frozen
against the v3.1 text, which said only "an explicitly bounded window";
`inversionExplicitWindowStatement` and `inversionWindowStatement` render that
as `∃ C`. Paper v4 made the window explicit with the constant 20
(PAPER_CORRECTIONS_PROPOSAL.md, entry 22), and until this supplement the value
20 was certified only by the helper theorems `window_i` / `window_ii` of
`Proofs/P09_CrossoverLaws.lean` (disclosed in the paper's §11 and in the
proposal's conservativeness rule, which names a supplementary statement file
as the way to freeze it).

Provenance, stated plainly: unlike the Phase H files, these statements were
frozen AFTER a proof of their content existed (the constant 20 was taken from
the helpers, which predate this file). The first two new Props are the bodies
of the corresponding reviewed `∃ C` statements with `C := 20`; the third is
Proposition 10.2 as a whole (a conjunction). Their fidelity to the paper was
checked by three fresh-context reviewers (literal comparison; exploit hunting;
numerical reconstruction from the paper alone), all PASS, before the
`_proved` theorems were written; the docstrings then took the reviewers'
cosmetic corrections, the Props themselves did not change
(research/experiments/README.md, Run 025; artifacts in
research/experiments/window20_fidelity/).

Frozen Props:
* `inversionExplicitWindow20Statement` — criteria form: (i)'s hypothesis holds for
                                         `1 ≤ d ≤ d_c(p) − 20`, (ii)'s for `d ≥ d_c(p) + 20`
* `inversionWindow20Statement`         — probability form: composite advantage for
                                         `d ≤ d_c(p) − 20`, prime advantage for `d ≥ d_c(p) + 20`
* `inversionLaw20Statement`            — Proposition 10.2 as stated in v5:
                                         `inversionLawStatement` and the two Props above
-/
import Shiftsym.Paper.S09_CrossoverLaws

namespace ShiftSym.P09

/-- **Proposition 10.2, the window with the explicit constant 20, criteria
form** (`prop:inversion`, v5 lines 997–1000).

Paper (verbatim): "so the two-dimensional ``composite advantage'' inverts
within an explicitly bounded window around $d_c(p)$, a dimension that grows
\emph{linearly} in the prime: (i) applies to every integer $d\ge1$ with
$d\le d_c(p)-20$, and (ii) to every integer $d\ge d_c(p)+20$."
(with the standing "Let $p\ge3$ be prime, $\sigma\ge2$", line 981).

Formal: for every prime `p ≥ 3`, every `σ ≥ 2` and every `d ≥ 1`: if
`d ≤ d_c(p) − 20` then the hypothesis of (i) holds,
`log_σ(2 log₂(p) p^{d−1}) < φ(d)`; if `d ≥ d_c(p) + 20` then the hypothesis
of (ii) holds, `φ(d) < −log_σ(2 log₂(p+1) (p+1)^{d−1})`.

Delta: "(i) applies" = the hypothesis of (i) holds, as in
`inversionExplicitWindowStatement`, whose body this is with `C := 20`; `d_c(p)`
= `dc p`, `φ(d)` = `phi p (d : ℝ)`, and the two logarithmic thresholds are
literally those of `inversionCompositeStatement` / `inversionPrimeStatement`
(`p^{d−1}` with `ℕ`-subtraction, exact as `d ≥ 1`); `d` is a natural number,
cast to `ℝ` for the comparison with `d_c(p) ± 20`. The paper states `d ≥ 1`
for (i); for (ii) the shared antecedent `1 ≤ d` excludes nothing, since
`d ≥ d_c(p) + 20 > 20` (`d_c(p) > 0` for `p ≥ 3`). The rest of the quoted
sentence is frozen elsewhere: "a dimension that grows linearly in the prime"
(the location `d_c(p)`) is `dcAsymptoticStatement`, and "the two-dimensional"
names the phenomenon (Observation 10.5) without a claim at `d = 2`.

Non-vacuity (kernel-checked in `Proofs/P09_CrossoverLaws_Window20.lean`):
the upper branch is reached for every `p` (e.g. `p = 3`, every `d ≥ 21`, as
`d_c(3) = 1`). The lower branch is reached first at `p = 37`, where
`24 ≤ d_c(37) < 25` admits exactly `d ∈ {1, …, 4}`; for every prime
`p ≤ 31`, `d_c(p) < 21`, so there the sentence asserts only the upper branch.
PAPER ISSUE: none. -/
def inversionExplicitWindow20Statement : Prop :=
  ∀ p σ d : ℕ, p.Prime → 3 ≤ p → 2 ≤ σ → 1 ≤ d →
    ((d : ℝ) ≤ dc p - 20 →
        Real.logb (σ : ℝ) (2 * Real.logb 2 (p : ℝ) * (p : ℝ) ^ (d - 1)) < phi p (d : ℝ)) ∧
      (dc p + 20 ≤ (d : ℝ) →
        phi p (d : ℝ) <
          -Real.logb (σ : ℝ) (2 * Real.logb 2 ((p : ℝ) + 1) * ((p : ℝ) + 1) ^ (d - 1)))

/-- **Proposition 10.2, the inversion window with the explicit constant 20,
probability form** (`prop:inversion`, v5 lines 997–1000).

Paper (verbatim): as for `inversionExplicitWindow20Statement`; this is the
"inverts within an explicitly bounded window around $d_c(p)$" part, with the
bound the sentence makes explicit.

Formal: for every prime `p ≥ 3`, every `σ ≥ 2` and every `d ≥ 1`:
`d ≤ d_c(p) − 20` implies the composite advantage
`P^unif_{p^d} < P^unif_{(p+1)^d}`, and `d ≥ d_c(p) + 20` implies the prime
advantage `P^unif_{(p+1)^d} < P^unif_{p^d}`. Equivalently, every integer
`d ≥ 1` without composite advantage has `d > d_c(p) − 20`, and every one
without prime advantage has `d < d_c(p) + 20`.

Delta: the body of `inversionWindowStatement` with `C := 20` (composite
advantage below the window, prime advantage above it, as the names are
attached to (i) and (ii) on lines 985–989); `P^unif_{m^d}` = `probUnif m d σ`
(real). PAPER ISSUE: none. -/
def inversionWindow20Statement : Prop :=
  ∀ p σ d : ℕ, p.Prime → 3 ≤ p → 2 ≤ σ → 1 ≤ d →
    ((d : ℝ) ≤ dc p - 20 → probUnif p d σ < probUnif (p + 1) d σ) ∧
      (dc p + 20 ≤ (d : ℝ) → probUnif (p + 1) d σ < probUnif p d σ)

/-- **Proposition 10.2** (`prop:inversion`, v5 lines 980–1001), the whole
statement as stated in v5: the frozen group-09 whole statement
`inversionLawStatement` ((i), (ii), the sign pattern and unique zero of `φ`,
`d_c(p) = p ln 2 + O(1)`, and the window with `∃ C`) together with the window
with the explicit constant 20 in both forms. (The `∃ C` conjuncts are implied
by the explicit ones and are kept so that the reviewed statement is contained
unchanged.) -/
def inversionLaw20Statement : Prop :=
  inversionLawStatement ∧ inversionExplicitWindow20Statement ∧ inversionWindow20Statement

end ShiftSym.P09
