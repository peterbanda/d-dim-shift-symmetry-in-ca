/-
Phase H, group 09 (CrossoverLaws) — FROZEN STATEMENTS, no proofs of them here.

Paper: `shift_symmetry_d_dimensions.tex` (v3.1), §10 "Crossover laws and
empirical observations in higher dimensions", lines 879–967:
* section preamble (lines 884–886, non-mathematical);
* Proposition 10.1 `prop:rate` (decay-rate law), lines 888–907, its proof
  (lines 909–916), the pointer and Figure 2 caption `fig:rate-classes` (lines 918–932,
  restates Proposition 10.1);
* Proposition 10.2 `prop:inversion` (inversion law), lines 934–954, and its
  proof (lines 956–966).

Frozen Props (each closed over all its parameters; a proof is
`theorem <name>_proved : <name>Statement`):

Proposition 10.1 (decay-rate law)
* `rateLowerStatement`            — `σ^{N/p_1} ≤ |S_{n^d}|`
* `rateUpperStatement`            — `|S_{n^d}| ≤ 2 log_2(n) n^{d−1} σ^{N/p_1}`
* `rateBoundsStatement`           — the displayed two-sided bound (conjunction)
* `rateGapStatement`              — `0 ≤ (1 − 1/p_1) − c(n,d) ≤ log_σ(2 n^{d−1} log_2 n)/N`
* `rateGapBoundTendstoStatement`  — that upper bound `→ 0` as `d → ∞`
* `rateLimitStatement`            — `c(n,d) → 1 − 1/p_1(n)` as `d → ∞`
* `rateUniversalityStatement`     — the limit depends only on `p_1(n)`
* `rateEvenClassStatement`        — even `n`: `c(n,d) → 1/2`
* `ratePrimeClassStatement`       — prime `p`: `c(p,d) → 1 − 1/p`
* `rateExtremalClassStatement`    — `1/2` is the least class value, attained iff `n` even
* `rateFloorStatement`            — "the floor permitted by Theorem 6.3": `liminf_d c(n,d) ≥ 1/2`
* `rateLawStatement`              — Proposition 10.1 (conjunction of all of the above)
* `rateProofPrefactorStatement`   — AUXILIARY: proof-internal prefactor chain (lines 912–915);
                                    not part of `rateLawStatement`

Proposition 10.2 (inversion law)
* `inversionCompositeStatement`       — part (i)
* `inversionPrimeStatement`           — part (ii)
* `phiSignStatement`                  — `φ > 0` below, `< 0` above its unique zero `d_c(p)`
* `dcAsymptoticStatement`             — `d_c(p) = p ln 2 + O(1)` as `p → ∞`
* `inversionExplicitWindowStatement`  — the window left open by (i)/(ii) is a bounded
                                        window around `d_c(p)`
* `inversionWindowStatement`          — the composite advantage inverts within a bounded
                                        window around `d_c(p)`
* `inversionLawStatement`             — Proposition 10.2 (conjunction)
* `inversionProofLogRatioStatement`   — AUXILIARY: proof-internal log-ratio sandwich
                                        (lines 957–962); not part of `inversionLawStatement`

Global representation choices (repeated in each docstring where relevant):
* `|S_{n^d}|` is the shared `numSS n d σ` (alphabet `Fin σ`, `Nat.card` of the
  subtype of shift-symmetric configurations, paper Definition 2.2) and
  `P^unif_{n^d}` is the shared `probUnif n d σ = |S_{n^d}| / σ^{n^d}` in `ℝ`
  (paper Corollary 7.1), both from `Shiftsym.Paper.Common`;
* `p_1(n)` = `Nat.minFac n` (mathlib: the smallest prime factor of `n` for
  `n ≠ 1`; every statement carries `2 ≤ n`, so `minFac n` is prime);
* `N/p_1 = n^d / minFac n` is `ℕ`-division, exact because
  `minFac n ∣ n ∣ n^d` for `d ≥ 1` (lemma `p1_dvd_pow` below, proved);
* real quantities (`log_2`, `log_σ`, `ln`, `1/p`, `φ`, `d_c`) live in `ℝ`:
  `log_b x` = `Real.logb b x` (= `Real.log x / Real.log b`), `ln` = `Real.log`;
  every logarithm in a frozen statement is applied to a quantity that is
  strictly positive under the stated hypotheses and has base `σ ≥ 2` or `2`,
  so the mathlib conventions `log 0 = 0`, `log (−x) = log x`, `logb 1 = 0`
  never fire (argued per statement below);
* `n^{d−1}` with `d : ℕ`: `ℕ`-subtraction `d - 1` is exact because `1 ≤ d` is
  an explicit antecedent (in the limit statements only large `d` matter);
* limits "as `d → ∞`" are `Filter.Tendsto (fun d : ℕ => …) atTop (𝓝 L)` for
  fixed `n`, `σ` (the paper fixes `n`; `σ ≥ 2` is fixed throughout);
* the paper suppresses `σ` in `c(n,d)`; here `decayRate n d σ`.
-/
import Shiftsym.Paper.Common

namespace ShiftSym.P09

open ShiftSym Filter
open scoped Topology

/-! ## Definitions -/

/-- `p_1(n)`, "the smallest prime factor of `n`" (paper §3 preamble:
`n = ∏ p_i^{α_i}` with `p_1 < ⋯ < p_k`; restated in Proposition 10.1:
"Let `p_1 = p_1(n)` be the smallest prime factor of `n`").
Representation: mathlib's `Nat.minFac n`, which for `n ≥ 2` is the least
prime dividing `n` (`Nat.minFac_prime`, `Nat.minFac_le_of_dvd`). -/
abbrev p1 (n : ℕ) : ℕ := n.minFac

/-- Exactness of the `ℕ`-division `N / p_1 = n^d / minFac n` used in the
exponents below: `minFac n ∣ n^d` whenever `d ≥ 1`. (Representation check,
not a paper statement.) -/
theorem p1_dvd_pow (n d : ℕ) (hd : 1 ≤ d) : p1 n ∣ n ^ d :=
  (Nat.minFac_dvd n).trans (dvd_pow_self n (by omega))

/-- The decay rate `c(n,d) := −log_σ P^unif_{n^d} / N`, `N = n^d`
(paper Proposition 10.1, lines 896–897: "the decay rate
$c(n,d):=-\log_\sigma P^{\mathrm{unif}}_{n^d}/N$").

Delta: the paper suppresses the alphabet size; here it is the third
argument `σ`. Real arithmetic: `−(Real.logb σ P) / (n:ℝ)^d`. Conventions:
for `n ≥ 2`, `d ≥ 1`, `σ ≥ 2` we have `P^unif > 0` (constant configurations
are shift-symmetric, so `|S| ≥ σ ≥ 1`), hence the `Real.log 0 = 0`
convention never fires in the statements below, and `(n:ℝ)^d > 0`. -/
noncomputable def decayRate (n d σ : ℕ) : ℝ :=
  -Real.logb (σ : ℝ) (probUnif n d σ) / (n : ℝ) ^ d

/-- The function `φ(d) = (1 − 1/p) p^d − ½ (p+1)^d` of Proposition 10.2
(line 936: "set $\varphi(d)=(1-\tfrac1p)\,p^d-\tfrac12(p+1)^d$"), as a function
of a REAL variable `x` (real powers `Real.rpow` with the positive bases `p`,
`p + 1`, `p ≥ 3`). At integer dimensions it is the paper's expression with
natural powers (`phi_natCast`, proved below). The real extension is needed
because the paper speaks of the "unique zero" `d_c(p)` of `φ`, which is
in general not an integer (see `phiSignStatement`). -/
noncomputable def phi (p : ℕ) (x : ℝ) : ℝ :=
  (1 - 1 / (p : ℝ)) * (p : ℝ) ^ x - (1 / 2) * ((p : ℝ) + 1) ^ x

/-- At natural-number arguments `φ` is the paper's expression with ordinary
powers. (Representation check, not a paper statement.) -/
theorem phi_natCast (p d : ℕ) :
    phi p (d : ℝ) = (1 - 1 / (p : ℝ)) * (p : ℝ) ^ d - (1 / 2) * ((p : ℝ) + 1) ^ d := by
  simp [phi, Real.rpow_natCast]

/-- The inversion dimension `d_c(p) = ln(2 − 2/p) / ln(1 + 1/p)`
(Proposition 10.2, line 948). Real arithmetic, `ln` = `Real.log`.
Conventions: for `p ≥ 3`, `2 − 2/p ≥ 4/3 > 0` and `1 + 1/p > 1`, so both
logarithms are of positive arguments and the denominator is `> 0`
(no `x/0 = 0` or `log` of a nonpositive number). -/
noncomputable def dc (p : ℕ) : ℝ :=
  Real.log (2 - 2 / (p : ℝ)) / Real.log (1 + 1 / (p : ℝ))

/-! ## Proposition 10.1 (decay-rate law), lines 888–907 -/

/-- **Proposition 10.1, lower bound** (`prop:rate`, lines 890–895).

Paper (verbatim): "Let $p_1=p_1(n)$ be the smallest prime factor of $n$ and
$N=n^d$. For all $n\ge2$, $d\ge1$, $\sigma\ge2$:
\[ \sigma^{N/p_1}\;\le\;|S_{n^d}|\;\le\; 2\log_2(n)\,n^{d-1}\,\sigma^{N/p_1}. \]"
(this Prop: the left inequality).

Delta:
* `|S_{n^d}|` = `numSS n d σ` (alphabet `Fin σ`); `p_1` = `Nat.minFac n`;
* the inequality is stated in `ℕ` (both sides are natural numbers);
* exponent `N/p_1` = `n ^ d / n.minFac` (`ℕ`-division, exact by `p1_dvd_pow`).

PAPER ISSUE: none. -/
def rateLowerStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    σ ^ (n ^ d / p1 n) ≤ numSS n d σ

/-- **Proposition 10.1, upper bound** (`prop:rate`, lines 890–895).

Paper (verbatim): "For all $n\ge2$, $d\ge1$, $\sigma\ge2$:
\[ \sigma^{N/p_1}\;\le\;|S_{n^d}|\;\le\; 2\log_2(n)\,n^{d-1}\,\sigma^{N/p_1}. \]"
(this Prop: the right inequality).

Delta:
* stated in `ℝ` (the prefactor `2 log_2 n` is irrational in general);
  `log_2 n` = `Real.logb 2 n`, with `n ≥ 2` so its argument is positive;
* `n^{d−1}` = `(n:ℝ) ^ (d - 1)` with `ℕ`-subtraction, exact since `1 ≤ d`;
* exponent `N/p_1` = `n ^ d / n.minFac` (exact `ℕ`-division, `p1_dvd_pow`).

PAPER ISSUE: none (checked against the exact formula for all
`2 ≤ n ≤ 40`, `d ≤ 4`, `n^d ≤ 2·10^5`, `2 ≤ σ ≤ 5`: 548 triples, no violation;
largest ratio `|S| / (2 log_2(n) n^{d−1} σ^{N/p_1}) = 0.931` at `(2,4,5)`). -/
def rateUpperStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    (numSS n d σ : ℝ) ≤
      2 * Real.logb 2 (n : ℝ) * (n : ℝ) ^ (d - 1) * (σ : ℝ) ^ (n ^ d / p1 n)

/-- **Proposition 10.1, displayed two-sided bound** (lines 890–895):
conjunction of `rateLowerStatement` and `rateUpperStatement`. -/
def rateBoundsStatement : Prop :=
  rateLowerStatement ∧ rateUpperStatement

/-- **Proposition 10.1, decay-rate sandwich** (lines 896–902).

Paper (verbatim): "Consequently the decay rate
$c(n,d):=-\log_\sigma P^{\mathrm{unif}}_{n^d}/N$ satisfies
\[ 0\;\le\;\Bigl(1-\frac1{p_1}\Bigr)-c(n,d)\;\le\;
\frac{\log_\sigma\bigl(2\,n^{d-1}\log_2 n\bigr)}{N} \]"
(for all `n ≥ 2`, `d ≥ 1`, `σ ≥ 2`, the proposition's standing quantifiers).

Delta:
* `c(n,d)` = `decayRate n d σ` (real; `P^unif` = `probUnif n d σ > 0` here);
* `1/p_1` = `1 / (n.minFac : ℝ)` (real division, `minFac n ≥ 2`);
* `log_σ(2 n^{d−1} log_2 n)` = `Real.logb σ (2 * n^(d-1) * Real.logb 2 n)`; its
  argument is `≥ 2 > 0` since `log_2 n ≥ 1`; base `σ ≥ 2`;
* `N` = `(n:ℝ)^d > 0`.

PAPER ISSUE: none (both inequalities are equivalent to the two bounds of
`rateBoundsStatement`; checked numerically on the same 548 triples). -/
def rateGapStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    0 ≤ (1 - 1 / (p1 n : ℝ)) - decayRate n d σ ∧
      (1 - 1 / (p1 n : ℝ)) - decayRate n d σ ≤
        Real.logb (σ : ℝ) (2 * (n : ℝ) ^ (d - 1) * Real.logb 2 (n : ℝ)) / (n : ℝ) ^ d

/-- **Proposition 10.1, the gap bound tends to 0** (lines 899–901).

Paper (verbatim): "\[ \dots\;\le\;
\frac{\log_\sigma\bigl(2\,n^{d-1}\log_2 n\bigr)}{N}
\;\xrightarrow[d\to\infty]{}\;0 , \]"

Delta: for fixed `n ≥ 2` and `σ ≥ 2` (the proposition's standing
hypotheses; the paper's limit is in `d` only), `Filter.Tendsto` along
`d : ℕ → ∞`. The values at small `d` (including `d = 0`, where `d - 1`
truncates) are irrelevant to the limit.

PAPER ISSUE: none. -/
def rateGapBoundTendstoStatement : Prop :=
  ∀ n σ : ℕ, 2 ≤ n → 2 ≤ σ →
    Tendsto
      (fun d : ℕ =>
        Real.logb (σ : ℝ) (2 * (n : ℝ) ^ (d - 1) * Real.logb 2 (n : ℝ)) / (n : ℝ) ^ d)
      atTop (𝓝 0)

/-- **Proposition 10.1, limit of the decay rate** (line 903).

Paper (verbatim): "so $c(n,d)\to1-1/p_1(n)$".

Delta: for fixed `n ≥ 2`, `σ ≥ 2`, as `d → ∞` (the preceding display is
"$\xrightarrow[d\to\infty]{}$"); `Filter.Tendsto` along `d : ℕ`.
`c(n,d)` = `decayRate n d σ`.

PAPER ISSUE: none (exact data, `σ = 2`: e.g. `n = 6`: `c = 0.4463, 0.4552,
0.4870, 0.4970, 0.4994, 0.4999` for `d = 1..6`). -/
def rateLimitStatement : Prop :=
  ∀ n σ : ℕ, 2 ≤ n → 2 ≤ σ →
    Tendsto (fun d : ℕ => decayRate n d σ) atTop (𝓝 (1 - 1 / (p1 n : ℝ)))

/-- **Proposition 10.1, universality classes** (lines 903–905).

Paper (verbatim): "asymptotically in $d$, lattice sides fall into
\emph{universality classes} determined solely by their smallest prime
factor".

Delta: "determined solely by their smallest prime factor" is formalized as:
two lattice sides `n, m ≥ 2` with the same smallest prime factor have the
same limiting decay rate (for every fixed `σ ≥ 2`), the limit existing.
Only this direction is asserted by "determined solely by"; that different
`p_1` give different classes follows from the explicit class values
(`rateLimitStatement`) and is not frozen separately.

PAPER ISSUE: none. -/
def rateUniversalityStatement : Prop :=
  ∀ n m σ : ℕ, 2 ≤ n → 2 ≤ m → 2 ≤ σ → p1 n = p1 m →
    ∃ L : ℝ, Tendsto (fun d : ℕ => decayRate n d σ) atTop (𝓝 L) ∧
      Tendsto (fun d : ℕ => decayRate m d σ) atTop (𝓝 L)

/-- **Proposition 10.1, even class** (lines 905–906).

Paper (verbatim): "with even $n$ on the extremal class $c=1/2$".

Delta: "on the class `c = 1/2`" = the decay rate converges to `1/2` as
`d → ∞` (fixed `σ ≥ 2`); "even" = `Even n`; `n ≥ 2`.

PAPER ISSUE: none. Note: the convergence is NOT monotone and `c(n,d) < 1/2`
at finite `d` is possible (exact: `c(2,2) = 1/4`, `c(2,3) ≈ 0.2288` at
`σ = 2`), so "on the class" can only mean the limit. -/
def rateEvenClassStatement : Prop :=
  ∀ n σ : ℕ, 2 ≤ n → Even n → 2 ≤ σ →
    Tendsto (fun d : ℕ => decayRate n d σ) atTop (𝓝 (1 / 2))

/-- **Proposition 10.1, prime classes** (line 906).

Paper (verbatim): "and primes $p$ on $c=1-1/p$".

Delta: for every prime `p` and fixed `σ ≥ 2`, `c(p,d) → 1 − 1/p` as
`d → ∞` (`p` prime gives `p ≥ 2`).

PAPER ISSUE: none. -/
def ratePrimeClassStatement : Prop :=
  ∀ p σ : ℕ, p.Prime → 2 ≤ σ →
    Tendsto (fun d : ℕ => decayRate p d σ) atTop (𝓝 (1 - 1 / (p : ℝ)))

/-- **Proposition 10.1, `1/2` is the extremal class** (lines 905–906).

Paper (verbatim): "with even $n$ on the extremal class $c=1/2$ (the floor
permitted by Theorem~\ref{thm:upper-bound})".

Delta: "extremal class" is formalized as: among all class values
`1 − 1/p_1(n)` (`n ≥ 2`), `1/2` is the least, and it is attained exactly for
even `n`. Pure real arithmetic in `minFac n`.

PAPER ISSUE: none. -/
def rateExtremalClassStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (1 / 2 : ℝ) ≤ 1 - 1 / (p1 n : ℝ) ∧ (1 - 1 / (p1 n : ℝ) = 1 / 2 ↔ Even n)

/-- **Proposition 10.1, "the floor permitted by Theorem 6.3"** (lines 905–906;
also the Figure 2 caption, lines 928–930: "the floor permitted by
Theorem~\ref{thm:upper-bound} (shaded region excluded asymptotically)").

Paper (verbatim): "(the floor permitted by Theorem~\ref{thm:upper-bound})".

Delta: the claim that no lattice side has asymptotic decay rate below
`1/2` (Theorem 6.3(ii) gives `c(n,d) ≥ 1/2 − log_σ(2^d − 1 + 2 log_2 n)/N`),
formalized as `liminf_{d→∞} c(n,d) ≥ 1/2` in ε-form: for fixed `n ≥ 2`,
`σ ≥ 2` and every `ε > 0`, eventually `c(n,d) ≥ 1/2 − ε`. Asymptotic only:
`c(2,2) = 1/4 < 1/2` at `σ = 2`, so a finite-`d` floor would be false.

PAPER ISSUE: none. -/
def rateFloorStatement : Prop :=
  ∀ n σ : ℕ, 2 ≤ n → 2 ≤ σ →
    ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, ∀ d : ℕ, D ≤ d → 1 / 2 - ε ≤ decayRate n d σ

/-- **Proposition 10.1 (`prop:rate`), whole statement** (lines 888–907):
the two-sided bound, the decay-rate sandwich, the vanishing of the gap
bound, the limit `c(n,d) → 1 − 1/p_1(n)`, and the universality-class
restatements (classes determined by `p_1`; even `n` on `c = 1/2`; primes on
`1 − 1/p`; `1/2` extremal; `1/2` the asymptotic floor). -/
def rateLawStatement : Prop :=
  rateBoundsStatement ∧ rateGapStatement ∧ rateGapBoundTendstoStatement ∧
    rateLimitStatement ∧ rateUniversalityStatement ∧ rateEvenClassStatement ∧
    ratePrimeClassStatement ∧ rateExtremalClassStatement ∧ rateFloorStatement

/-- **AUXILIARY — proof of Proposition 10.1, prefactor chain** (lines 912–915;
proof-internal claims, frozen for the proof phase; NOT part of
`rateLawStatement`).

Paper (verbatim): "Upper bound: in Theorem~\ref{thm:upper-bound}(i), every
exponent satisfies $N/p\le N/p_1$, and
$\sum_{p\mid n}\gaussbinom d1_p\le\sum_{p\mid n}2p^{d-1}
\le2\,\omega(n)\,n^{d-1}\le2\log_2(n)\,n^{d-1}$."

Delta:
* `Σ_{p∣n} [d 1]_p` = the shared `sopfD n d` (sum over `n.primeFactors` of the
  project's `gaussBinom p d 1`), cast to `ℝ`;
* `ω(n)` = `n.primeFactors.card` (number of distinct prime factors);
* `N/p ≤ N/p_1` for every prime `p ∣ n`: `n^d / p ≤ n^d / minFac n` in `ℕ`
  (both divisions exact for `d ≥ 1`);
* real arithmetic for the chain; `n^{d−1}`, `p^{d−1}` with `1 ≤ d`.

PAPER ISSUE: none (checked for all `2 ≤ n ≤ 2000`, `1 ≤ d ≤ 8`). -/
def rateProofPrefactorStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d →
    (∀ p ∈ n.primeFactors, n ^ d / p ≤ n ^ d / p1 n) ∧
      (sopfD n d : ℝ) ≤ ∑ p ∈ n.primeFactors, 2 * (p : ℝ) ^ (d - 1) ∧
      ∑ p ∈ n.primeFactors, 2 * (p : ℝ) ^ (d - 1) ≤
        2 * (n.primeFactors.card : ℝ) * (n : ℝ) ^ (d - 1) ∧
      2 * (n.primeFactors.card : ℝ) * (n : ℝ) ^ (d - 1) ≤
        2 * Real.logb 2 (n : ℝ) * (n : ℝ) ^ (d - 1)

/-! ## Proposition 10.2 (inversion law), lines 934–954 -/

/-- **Proposition 10.2 (i), composite advantage** (`prop:inversion`,
lines 935–940).

Paper (verbatim): "Let $p\ge3$ be prime, $\sigma\ge2$, and set
$\varphi(d)=(1-\tfrac1p)\,p^d-\tfrac12(p+1)^d$. Then:
(i) if $\varphi(d)>\log_\sigma\bigl(2\log_2(p)\,p^{d-1}\bigr)$, then
$P^{\mathrm{unif}}_{(p+1)^d}>P^{\mathrm{unif}}_{p^d}$ (composite
advantage);"

Delta:
* `d` ranges over dimensions `d ≥ 1` (paper Definition 2.1 standing
  hypothesis "Fix integers $n\ge2$, $d\ge1$"; `P^unif` is only defined on
  lattices). The antecedent `1 ≤ d` is NECESSARY: at `d = 0` both lattices
  are a single point with no nonzero translation, so `numSS = 0` and both
  probabilities are `0`, while the hypothesis of (i) holds (e.g. `p = 3`,
  `σ = 2`: `φ(0) = 1/6 > log_2(2 log_2(3)/3) ≈ 0.079`);
* `φ(d)` = `phi p (d : ℝ)` (real powers at an integer point, equal to the
  natural powers by `phi_natCast`);
* `log_σ(2 log_2(p) p^{d−1})` = `Real.logb σ (2 * Real.logb 2 p * p^(d-1))`;
  argument `≥ 2 log_2 3 > 0`, base `σ ≥ 2`; `p^{d−1}` exact since `d ≥ 1`;
* `P^unif_{m^d}` = `probUnif m d σ` (real), with `m = p` and `m = p + 1`.

PAPER ISSUE: none (exact data `p ∈ {3,5,7,11,13,17,19,23}`, `2 ≤ σ ≤ 5`,
`(p+1)^d ≤ 4·10^5`: hypothesis hit 100 times, conclusion always true;
non-vacuous, e.g. `p = 7`, `d = 2`, `σ = 2`, see `inversionComposite_nonvacuous`). -/
def inversionCompositeStatement : Prop :=
  ∀ p σ d : ℕ, p.Prime → 3 ≤ p → 2 ≤ σ → 1 ≤ d →
    Real.logb (σ : ℝ) (2 * Real.logb 2 (p : ℝ) * (p : ℝ) ^ (d - 1)) < phi p (d : ℝ) →
      probUnif p d σ < probUnif (p + 1) d σ

/-- **Proposition 10.2 (ii), prime advantage** (`prop:inversion`,
lines 941–943).

Paper (verbatim): "(ii) if
$\varphi(d)<-\log_\sigma\bigl(2\log_2(p{+}1)\,(p{+}1)^{d-1}\bigr)$, then
$P^{\mathrm{unif}}_{(p+1)^d}<P^{\mathrm{unif}}_{p^d}$ (prime advantage)."
(with the standing "Let $p\ge3$ be prime, $\sigma\ge2$").

Delta: as for part (i): `d ≥ 1` (Definition 2.1); `φ(d)` = `phi p d`;
`log_σ(2 log_2(p+1) (p+1)^{d−1})` =
`Real.logb σ (2 * Real.logb 2 (p + 1) * (p + 1)^(d-1))` (argument `≥ 4 > 0`,
base `σ ≥ 2`); probabilities `probUnif`.

PAPER ISSUE: none (same exact data: hypothesis hit 49 times, conclusion
always true; non-vacuous, e.g. `p = 3`, `d = 3`, `σ = 2`, see
`inversionPrime_nonvacuous`). -/
def inversionPrimeStatement : Prop :=
  ∀ p σ d : ℕ, p.Prime → 3 ≤ p → 2 ≤ σ → 1 ≤ d →
    phi p (d : ℝ) <
        -Real.logb (σ : ℝ) (2 * Real.logb 2 ((p : ℝ) + 1) * ((p : ℝ) + 1) ^ (d - 1)) →
      probUnif (p + 1) d σ < probUnif p d σ

/-- **Proposition 10.2, sign pattern of `φ`** (lines 945–950).

Paper (verbatim): "The function $\varphi$ is positive below and negative
above its unique zero
\[ d_c(p)\;=\;\frac{\ln\bigl(2-\tfrac2p\bigr)}{\ln\bigl(1+\tfrac1p\bigr)} \]"
(standing hypothesis: `p ≥ 3` prime).

Delta:
* `φ` as a function of a REAL variable `x` (`phi p x`, real powers), and the
  claims for all `x ∈ ℝ`: `φ(x) = 0 ↔ x = d_c(p)` (unique zero, and it is
  `d_c(p)`), `φ(x) > 0` for `x < d_c(p)`, `φ(x) < 0` for `x > d_c(p)`;
* `d_c(p)` = `dc p` (`Real.log`, positive arguments since `p ≥ 3`);
* the hypothesis `σ ≥ 2` of the proposition is dropped here because `φ`
  and `d_c` do not involve `σ` (this does not weaken the claim).

PAPER ISSUE (ambiguity): the paper defines `φ(d)` with `d` the dimension
(an integer), but at integer arguments `φ` has in general no zero
(`d_c(5) ≈ 2.578`); "unique zero" only makes sense for `φ` regarded as a
function of a real variable `d` (which the proof's monotonicity argument
`d ↦ φ(d)/p^d = (1−1/p) − ½(1+1/p)^d` implicitly does). The paper should say
"regarded as a function of real $d$". Formalized on all of `ℝ` (the formula
defines `φ` on `ℝ`; the statement holds there since `φ(x)/p^x` is strictly
decreasing on `ℝ`). -/
def phiSignStatement : Prop :=
  ∀ p : ℕ, p.Prime → 3 ≤ p →
    (∀ x : ℝ, phi p x = 0 ↔ x = dc p) ∧
      (∀ x : ℝ, x < dc p → 0 < phi p x) ∧
      (∀ x : ℝ, dc p < x → phi p x < 0)

/-- **Proposition 10.2, asymptotics of `d_c`** (lines 948–950).

Paper (verbatim): "\[ d_c(p)\;=\;\frac{\ln\bigl(2-\tfrac2p\bigr)}{\ln\bigl(1+\tfrac1p\bigr)}
\;=\;p\ln2+O(1)\qquad(p\to\infty), \]"

Delta: `O(1)` as `p → ∞` through the primes (the proposition's `p` is a
prime) in explicit form: `∃ C, ∃ P₀, ∀ p prime, p ≥ P₀ → |d_c(p) − p ln 2| ≤ C`.
`ln 2` = `Real.log 2`.

PAPER ISSUE: none (numerically `|d_c(p) − p ln 2| ≤ 1.0795` for all primes
`3 ≤ p ≤ 10^6`, maximum at `p = 3`; the difference tends to
`(ln 2)/2 − 1 ≈ −0.6534`). -/
def dcAsymptoticStatement : Prop :=
  ∃ C : ℝ, ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p → |dc p - p * Real.log 2| ≤ C

/-- **Proposition 10.2, the window left by (i)/(ii) is bounded**
(lines 951–953).

Paper (verbatim): "so the two-dimensional ``composite advantage'' inverts
within an explicitly bounded window around $d_c(p)$, which grows
\emph{linearly} in the prime."

Delta: the "explicitly bounded window" is read as the set of dimensions
left undecided by the explicit criteria (i) and (ii); the claim that it is
a bounded window around `d_c(p)` is formalized as: there is a constant `C`,
uniform in the prime `p ≥ 3` and the alphabet size `σ ≥ 2`, such that every
dimension `d ≥ 1` with `d ≤ d_c(p) − C` satisfies the hypothesis of (i) and
every dimension `d ≥ 1` with `d ≥ d_c(p) + C` satisfies the hypothesis of
(ii). "Explicitly" is rendered as existence (`∃ C`); any proof exhibits a
value. "which grows linearly in the prime" (the window's location `d_c(p)`)
is `dcAsymptoticStatement`.

PAPER ISSUE (vague): the paper never states the window. Numerically
(`σ = 2` is the worst case, as both log terms decrease in `σ`; primes
`3 ≤ p < 3000`): the hypothesis of (i) fails at `(p,d) = (5,1),(5,2),(7,1)`
(so `C > d_c(7) − 1 ≈ 3.037` is needed), that of (ii) fails at `(3,2)`
(`C > 1`), and for `11 ≤ p < 3000` (i)/(ii) decide every integer `d ≠ d_c(p)`;
any `C ≥ 3.04` works there. Truth for ALL primes with `C = 4` (sketch, using
`φ(d) = p^d (1−1/p)(1 − (1+1/p)^{d−d_c})` and `log_σ x ≤ log_2 x` for `x ≥ 1`):
for `p ∈ {3,5,7}` no `d ≥ 1` lies below `d_c(p) − 4`; for `p ≥ 11`, `d = 1`:
`φ(1) = (p−3)/2 > 1 + log_2 log_2 p`; `2 ≤ d ≤ d_c − 4`:
`φ(d) ≥ 3p^{d−1}(p−1)/(p+1) ≥ 2.5 p^{d−1} > 1 + log_2 log_2 p + (d−1) log_2 p`;
`d ≥ d_c + 4 (≥ 5)`: `−φ(d) ≥ 4(1−1/p) p^{d−1} > 1 + log_2 log_2(p+1) + (d−1) log_2(p+1)`.
The paper should state an explicit window, e.g. "for every integer
$d\ge1$ with $|d-d_c(p)|\ge 4$, (i) or (ii) applies". -/
def inversionExplicitWindowStatement : Prop :=
  ∃ C : ℝ, ∀ p σ d : ℕ, p.Prime → 3 ≤ p → 2 ≤ σ → 1 ≤ d →
    ((d : ℝ) ≤ dc p - C →
        Real.logb (σ : ℝ) (2 * Real.logb 2 (p : ℝ) * (p : ℝ) ^ (d - 1)) < phi p (d : ℝ)) ∧
      (dc p + C ≤ (d : ℝ) →
        phi p (d : ℝ) <
          -Real.logb (σ : ℝ) (2 * Real.logb 2 ((p : ℝ) + 1) * ((p : ℝ) + 1) ^ (d - 1)))

/-- **Proposition 10.2, the composite advantage inverts within a bounded
window around `d_c(p)`** (lines 951–953).

Paper (verbatim): "so the two-dimensional ``composite advantage'' inverts
within an explicitly bounded window around $d_c(p)$, which grows
\emph{linearly} in the prime."

Delta: formalized as: there is a constant `C`, uniform in the prime `p ≥ 3`
and the alphabet size `σ ≥ 2`, such that for every dimension `d ≥ 1`:
`d ≤ d_c(p) − C` implies the composite advantage
`P^unif_{p^d} < P^unif_{(p+1)^d}`, and `d ≥ d_c(p) + C` implies the prime
advantage `P^unif_{(p+1)^d} < P^unif_{p^d}`. ("Inverts": composite
advantage below the window, prime advantage above it.) "Explicitly" is
rendered as existence (`∃ C`). "The two-dimensional" names the phenomenon
(Observation 10.5 / the 2019 paper); no claim about `d = 2` is frozen here
(for `p = 3`, `d_c(3) = 1 < 2` and there is no 2D composite advantage:
`P(3²) > P(4²)`, consistent with this statement). "which grows linearly in
the prime" is `dcAsymptoticStatement`.

PAPER ISSUE (vague): window not specified, see
`inversionExplicitWindowStatement`. Exact data (`p ≤ 13`, `2 ≤ σ ≤ 6`)
plus (i)/(ii) for `11 ≤ p < 3000`: the sign of
`log(P_{(p+1)^d}/P_{p^d})` equals the sign of `d_c(p) − d` at every integer
`d ≥ 1` with `d ≠ d_c(p)` (equality at `p = 3`, `d = 1 = d_c(3)`:
`P_3 = P_4 = σ^{-2}`), so `C = 1` works for this (true-probability) form. -/
def inversionWindowStatement : Prop :=
  ∃ C : ℝ, ∀ p σ d : ℕ, p.Prime → 3 ≤ p → 2 ≤ σ → 1 ≤ d →
    ((d : ℝ) ≤ dc p - C → probUnif p d σ < probUnif (p + 1) d σ) ∧
      (dc p + C ≤ (d : ℝ) → probUnif (p + 1) d σ < probUnif p d σ)

/-- **Proposition 10.2 (`prop:inversion`), whole statement**
(lines 934–954): parts (i), (ii), the sign pattern of `φ` around its
unique zero `d_c(p)`, `d_c(p) = p ln 2 + O(1)`, and the bounded-window
inversion (both the explicit-criteria form and the probability form). -/
def inversionLawStatement : Prop :=
  inversionCompositeStatement ∧ inversionPrimeStatement ∧ phiSignStatement ∧
    dcAsymptoticStatement ∧ inversionExplicitWindowStatement ∧ inversionWindowStatement

/-- **AUXILIARY — proof of Proposition 10.2, log-ratio sandwich**
(lines 957–962; proof-internal claim, frozen for the proof phase; NOT part
of `inversionLawStatement`).

Paper (verbatim): "(i) By Proposition~\ref{prop:rate} applied to $n=p+1$
(whose smallest prime factor is $2$) and to $n=p$:
$P_{(p+1)^d}\ge\sigma^{-(p+1)^d/2}$ and
$P_{p^d}\le2\log_2(p)\,p^{d-1}\sigma^{-p^d(1-1/p)}$, so
$\log_\sigma\bigl(P_{(p+1)^d}/P_{p^d}\bigr)\ge
\varphi(d)-\log_\sigma(2\log_2(p)p^{d-1})>0$. (ii) is symmetric."

Delta:
* the first conjunct is the displayed lower bound on the log-ratio, which the
  proof derives for every `d ≥ 1` BEFORE invoking the hypothesis of (i) (the
  final `> 0` is that hypothesis and is not part of this Prop);
* the second conjunct is the "symmetric" upper bound behind (ii):
  `log_σ(P_{(p+1)^d}/P_{p^d}) ≤ φ(d) + log_σ(2 log_2(p+1) (p+1)^{d−1})`
  (from `P_{(p+1)^d} ≤ 2 log_2(p+1)(p+1)^{d−1} σ^{−(p+1)^d/2}` and
  `P_{p^d} ≥ σ^{−p^d(1−1/p)}`); the paper only says "(ii) is symmetric";
* `P_{m^d}` = `probUnif m d σ`, positive for `m ≥ 2`, `d ≥ 1`, `σ ≥ 2`, so the
  ratio and its `Real.logb` (base `σ ≥ 2`) are genuine; `d ≥ 1`, `p ≥ 3`
  prime as in the proposition.

PAPER ISSUE: none (exact data `p ∈ {3,5,7,11,13}`, `2 ≤ σ ≤ 5`: 120 cases,
both inequalities hold). -/
def inversionProofLogRatioStatement : Prop :=
  ∀ p σ d : ℕ, p.Prime → 3 ≤ p → 2 ≤ σ → 1 ≤ d →
    phi p (d : ℝ) - Real.logb (σ : ℝ) (2 * Real.logb 2 (p : ℝ) * (p : ℝ) ^ (d - 1)) ≤
        Real.logb (σ : ℝ) (probUnif (p + 1) d σ / probUnif p d σ) ∧
      Real.logb (σ : ℝ) (probUnif (p + 1) d σ / probUnif p d σ) ≤
        phi p (d : ℝ) +
          Real.logb (σ : ℝ) (2 * Real.logb 2 ((p : ℝ) + 1) * ((p : ℝ) + 1) ^ (d - 1))

/-! ## Sanity checks (no paper statement is proved here) -/

/-- `d_c(3) = 1` (the boundary case of Remark 10.3: `ln(4/3)/ln(4/3)`). -/
example : dc 3 = 1 := by
  have h : (2 : ℝ) - 2 / 3 = 1 + 1 / 3 := by norm_num
  have hpos : 0 < Real.log (1 + 1 / 3 : ℝ) := Real.log_pos (by norm_num)
  simp only [dc]
  push_cast
  rw [h, div_self hpos.ne']

/-- `φ(7)` at `d = 2`: `(6/7)·49 − 32 = 10`. -/
example : phi 7 (2 : ℕ) = 10 := by
  rw [phi_natCast]; norm_num

/-- Non-vacuity of part (i): at `p = 7`, `d = 2`, `σ = 2` the hypothesis
`φ(2) = 10 > log_2(2 log_2(7)·7)` holds (`log_2 7 < 3`, so the right side is
`< log_2 42 < 10`). -/
theorem inversionComposite_nonvacuous :
    Real.logb ((2 : ℕ) : ℝ) (2 * Real.logb 2 ((7 : ℕ) : ℝ) * ((7 : ℕ) : ℝ) ^ (2 - 1)) <
      phi 7 ((2 : ℕ) : ℝ) := by
  rw [phi_natCast]
  have h7 : Real.logb 2 (7 : ℝ) < 3 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
    norm_num
  have h7p : 0 < Real.logb 2 (7 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  have harg : 0 < 2 * Real.logb 2 (7 : ℝ) * (7 : ℝ) ^ (2 - 1) := by positivity
  push_cast
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)]
  norm_num
  nlinarith

/-- Non-vacuity of part (ii): at `p = 3`, `d = 3`, `σ = 2` the hypothesis
`φ(3) = 18 − 32 = −14 < −log_2(2 log_2(4)·16)` holds (`log_2 4 < 3`, so the
log term is `< log_2 96 < 14`). -/
theorem inversionPrime_nonvacuous :
    phi 3 ((3 : ℕ) : ℝ) <
      -Real.logb ((2 : ℕ) : ℝ)
        (2 * Real.logb 2 (((3 : ℕ) : ℝ) + 1) * (((3 : ℕ) : ℝ) + 1) ^ (3 - 1)) := by
  rw [phi_natCast]
  have h4 : Real.logb 2 (4 : ℝ) < 3 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
    norm_num
  have h4p : 0 < Real.logb 2 (4 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  push_cast
  have hlt : Real.logb 2 (2 * Real.logb 2 (3 + 1 : ℝ) * (3 + 1 : ℝ) ^ (3 - 1)) < 14 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num; positivity)]
    norm_num
    nlinarith
  norm_num at hlt ⊢
  linarith

/-- The hypotheses of Proposition 10.1 are satisfiable, and `minFac` is the
smallest prime factor on small instances. -/
example : ∃ n d σ : ℕ, 2 ≤ n ∧ 1 ≤ d ∧ 2 ≤ σ := ⟨2, 1, 2, by norm_num⟩
example : p1 6 = 2 ∧ p1 15 = 3 ∧ p1 35 = 5 ∧ p1 13 = 13 := by norm_num [p1]

/- Numeric sanity (`#eval` prints only; exact integers / Float). Exact
counts via the certified `enumerationRHS` (= `|S|` by `enumeration_proved`):
`|S_{6^2}| = 801064` at `σ = 2`, lower bound `2^{36/2} = 262144`, upper bound
`2·log_2(6)·6·2^18 ≈ 8.13·10^6`. -/
#eval (enumerationRHS 6 2 2, 2 ^ (6 ^ 2 / Nat.minFac 6))   -- (801064, 262144)
#eval 2 * Float.log2 6 * 6 * 2 ^ 18                        -- ≈ 8.13e6
-- d_c(p) for p = 3, 5, 7, 11, 13 (paper table: 1.00, 2.58, 4.04, 6.87, 8.27)
#eval [3, 5, 7, 11, 13].map fun p : Float => Float.log (2 - 2 / p) / Float.log (1 + 1 / p)

end ShiftSym.P09
