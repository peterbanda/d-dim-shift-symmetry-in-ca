/-
Phase H, group 06 (BoundsProbability): frozen statements for paper
`shift_symmetry_d_dimensions.tex` (v3.1), §6 "Bounds" and the first
corollary of §7 "Probability of shift-symmetry", paper lines 566–691:

* §6.1 preamble (lines 567–569): Gaussian binomials at integer `q` are
  polynomials in `q` with nonnegative integer coefficients;
* prose after Theorem 6.1 (lines 581–608): `d = 2` is Lemma E.21 of the 2019
  paper; primes meet the envelope, composites exceed it strictly;
* Remark 6.2 (`rem:oldbound-false`, lines 596–604);
* the definition of `sopf_d` (lines 612–616);
* Theorem 6.3 (`thm:upper-bound`, lines 618–628), parts (i), (ii);
* the comparison paragraph after its proof (lines 653–667);
* Corollary 7.1 (`cor:prob`, lines 673–691).

Theorem 6.1 itself is `ShiftSym.lowerBoundStatement` (frozen earlier,
`Shiftsym/Statement.lean`) and is NOT restated here; Theorem 5.1 and
Corollary 7.2 belong to other groups.

Statements only: every `…Statement` below is a `Prop`-valued definition,
not an axiom and not a theorem. Conventions used throughout (each
docstring repeats the ones that matter for it):

* `|S_{n^d}|` is `numSS n d σ` (`Shiftsym/Paper/Common.lean`): the
  alphabet `Σ` is `Fin σ`, the count is `Nat.card` of the subtype of
  shift-symmetric configurations on `Lat n d = Fin d → ZMod n`.
* `N = n^d`; `p_1` (smallest prime factor of `n`) is `Nat.minFac n`, which
  for `n ≥ 2` is the least prime dividing `n`.
* "`p ∣ n`" in a sum ranges over the PRIME divisors: `n.primeFactors`.
* `log_2` is `Real.logb 2` applied to the real cast of `n` (`n ≥ 2`, so the
  argument is positive); `log_σ` is `Real.logb σ` (`σ ≥ 2`).
* Non-integer exponents (`σ^{n^d/2}`, `σ^{-n^d/2}`, `σ^{N/p_1 - N}`) are
  real powers `Real.rpow` of the positive real `σ`; `σ^{-n^d}` likewise.
* The paper's standing hypotheses `n ≥ 2`, `d ≥ 1`, `σ ≥ 2` (Definition 2.1)
  appear as explicit antecedents wherever the paper relies on them.
-/
import Shiftsym.Paper.Common

namespace ShiftSym.P06

open ShiftSym

/-! ## §6.1 preamble: Gaussian binomials at an integer argument -/

/-- The paper's Gaussian binomial (§3, line 262), literally as the product
of fractions `[d r]_q = ∏_{i=0}^{r-1} (q^{d-i} - 1)/(q^{i+1} - 1)`, evaluated
in `ℚ` at a natural number `q`.

Delta: the exponent `d - i` is `ℕ`-subtraction. This changes nothing: for
`i ≤ d - 1` it is exact, and if `r > d` the factor `i = d` is
`(q^0 - 1)/(q^{d+1} - 1) = 0` in both readings, so the product is `0` either
way (the correct value of `[d r]` for `r > d`). For `q ≥ 2` all denominators
`q^{i+1} - 1` are nonzero. -/
def gaussProd (q d r : ℕ) : ℚ :=
  ∏ i ∈ Finset.range r, (((q : ℚ) ^ (d - i) - 1) / ((q : ℚ) ^ (i + 1) - 1))

/-- **§6.1 preamble, lines 567–569 (polynomiality).**

Paper: "For the statement we evaluate Gaussian binomials at the (possibly
composite) integer argument $q=n$; since $\gaussbinom dr_q$ is a polynomial
in $q$ with nonnegative integer coefficients, all quantities are integers."

Formal: for all `d r` there is one polynomial `P ∈ ℕ[X]` (nonnegative
integer coefficients) whose value at every integer `q ≥ 2` is the paper's
product `[d r]_q`.

Delta: Gaussian binomial = the paper's product formula `gaussProd` (§3);
"integer argument" = natural `q ≥ 2` (the product is undefined at `q = 1`
because of the `0/0` factors, and at `q = n ≥ 2` it is what Theorem 6.1
uses); "nonnegative integer coefficients" = coefficients in `ℕ`. -/
def gaussPolynomialStatement : Prop :=
  ∀ d r : ℕ, ∃ P : Polynomial ℕ, ∀ q : ℕ, 2 ≤ q →
    ((P.eval q : ℕ) : ℚ) = gaussProd q d r

/-- **Representation bridge for §6 (fidelity obligation, not a paper
sentence).** The Lean development uses the `q`-Pascal recursion
`ShiftSym.gaussBinom` everywhere (`rdCoeff`, `lowerEnvelope`, `sopfD`). The
paper defines `[d r]_q` by the product formula. This Prop says the two agree
at every natural `q ≥ 2`, so `lowerEnvelope n d σ` IS the paper's
`F_d(n, σ)` and `sopfD n d` IS the paper's `sopf_d(n)` (including at
composite `q = n`). The value being a natural number is the "all quantities
are integers" clause of lines 567–569.

Delta: none beyond the definition of `gaussProd` (see there). -/
def gaussProdEqStatement : Prop :=
  ∀ q d r : ℕ, 2 ≤ q → gaussProd q d r = (gaussBinom q d r : ℚ)

/-- The paper's envelope `F_d(n,σ) = Σ_{r=1}^{d} (-1)^{r+1} n^{C(r,2)} [d r]_n
σ^{n^{d-r}}` (Theorem 6.1, lines 574–576), written with the paper's product
formula for the Gaussian binomial, in `ℚ`. (Compare
`ShiftSym.lowerEnvelope`, which uses `gaussBinom`.)

Delta: `d - r` is `ℕ`-subtraction, exact on the range `1 ≤ r ≤ d`. -/
def paperEnvelope (n d σ : ℕ) : ℚ :=
  ∑ r ∈ Finset.Icc 1 d,
    (-1 : ℚ) ^ (r + 1) * (n : ℚ) ^ (r.choose 2) * gaussProd n d r *
      (σ : ℚ) ^ (n ^ (d - r))

/-- **§6.1 preamble, lines 567–569 ("all quantities are integers"), for
`F_d`.** The paper's `F_d(n,σ)` (product-formula binomials) is the integer
`lowerEnvelope n d σ` used by the frozen `ShiftSym.lowerBoundStatement`.

Paper: "… all quantities are integers."

Delta: `n ≥ 2` (standing hypothesis; needed for the product formula to be
defined); `σ` arbitrary natural (the identity is polynomial in `σ`). -/
def envelopeIntegralStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → paperEnvelope n d σ = (lowerEnvelope n d σ : ℚ)

/-- Conjunction of the three §6.1-preamble Props. -/
def preambleStatement : Prop :=
  gaussPolynomialStatement ∧ gaussProdEqStatement ∧ envelopeIntegralStatement

/-! ## Prose after Theorem 6.1 -/

/-- Lemma E.21 of Banda–Caughman–Cenek–Teuscher (2019), as cited at paper
line 588: `|Σ|^n (n+1) - |Σ| n ≤ |S_{n×n}|`, with equality iff `n` is prime.

Delta: `|Σ| = σ`, alphabet `Fin σ`, `|S_{n×n}| = numSS n 2 σ`; integer
arithmetic in `ℤ` (no truncation); the hypotheses `2 ≤ n`, `1 ≤ 2`, `2 ≤ σ`
are those of the paper's Theorem 6.1, so that the comparison below is
between statements with identical hypotheses. (The 2019 paper states the
bound "for any `n ∈ ℕ`" without restating the alphabet range; read
literally it fails at `n = 1` (`σ ≤ 0`) and its equality clause fails at
`σ = 1` for composite `n` (both sides are `1`), so `n ≥ 2`, `σ ≥ 2` is the
only sensible reading. This concerns the 2019 paper, not the present one.) -/
def e21Statement (n σ : ℕ) : Prop :=
  2 ≤ n → 1 ≤ 2 → 2 ≤ σ →
    ((n : ℤ) + 1) * (σ : ℤ) ^ n - (n : ℤ) * σ ≤ (numSS n 2 σ : ℤ)
      ∧ (((n : ℤ) + 1) * (σ : ℤ) ^ n - (n : ℤ) * σ = (numSS n 2 σ : ℤ)
          ↔ n.Prime)

/-- **Prose after Theorem 6.1, line 588 (envelope at `d = 2`).**

Paper: "For $d=2$ the statement is exactly \cite[Lemma~E.21]{banda2019}, …"

Formal, part 1: the envelope at `d = 2` is the two-term 2019 bound,
`F_2(n,σ) = (n+1)σ^n - nσ`.

Delta: identity in `ℤ` for all naturals `n, σ` (it is a polynomial
identity; no hypothesis is needed). -/
def envelopeTwoStatement : Prop :=
  ∀ n σ : ℕ, lowerEnvelope n 2 σ = ((n : ℤ) + 1) * (σ : ℤ) ^ n - (n : ℤ) * σ

/-- **Prose after Theorem 6.1, line 588 ("the statement is exactly
Lemma E.21").** Formal, part 2: for every `n, σ`, Theorem 6.1 at `d = 2`
(the frozen `lowerBoundStatement n 2 σ`) is equivalent to Lemma E.21
(`e21Statement n σ`).

Delta: "exactly" is read as logical equivalence of the two statements for
each `(n, σ)`, with identical hypotheses. -/
def d2IsE21Statement : Prop :=
  ∀ n σ : ℕ, lowerBoundStatement n 2 σ ↔ e21Statement n σ

/-- **Prose after Remark 6.2, lines 605–608 (primes minimize).**

Paper: "Theorem~\ref{thm:lower-bound} makes precise, and proves, the sense
in which \emph{primes minimize shift-symmetry in every dimension}: the count
$|S_{n^d}|$ meets the universal lower envelope $F_d(n,\sigma)$ exactly at
the primes and exceeds it strictly at every composite $n$."

Formal: for `n ≥ 2, d ≥ 1, σ ≥ 2`: prime `n` ⇒ `|S| = F_d`; non-prime
(= composite, as `n ≥ 2`) `n` ⇒ `F_d < |S|`.

Delta: `F_d = lowerEnvelope` (bridged by `envelopeIntegralStatement`);
comparison in `ℤ`; "composite" = `¬ n.Prime` under `2 ≤ n`. The slogan
"primes minimize shift-symmetry" is interpretive and is captured only
through this precise sentence. This is a restatement of Theorem 6.1. -/
def primesMeetEnvelopeStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    (n.Prime → (numSS n d σ : ℤ) = lowerEnvelope n d σ)
      ∧ (¬ n.Prime → lowerEnvelope n d σ < (numSS n d σ : ℤ))

/-! ## Remark 6.2 (`rem:oldbound-false`, lines 596–604) -/

/-- The naive two-term expression of Remark 6.2,
`σ^{n^{d-1}} (n^d - 1)/(n - 1) - σ((n^d - 1)/(n - 1) - 1)`, in `ℚ`.

Delta: the fraction `(n^d-1)/(n-1)` is kept as a rational division (exact,
no `ℕ`-truncation; the denominator is nonzero for `n ≥ 2`, the only case in
which it is used); `n^{d-1}` uses `ℕ`-subtraction, exact for `d ≥ 1`. -/
def naiveBound (n d σ : ℕ) : ℚ :=
  (σ : ℚ) ^ (n ^ (d - 1)) * (((n : ℚ) ^ d - 1) / ((n : ℚ) - 1))
    - (σ : ℚ) * (((n : ℚ) ^ d - 1) / ((n : ℚ) - 1) - 1)

/-- The (false for `d ≥ 3`) naive claim of Remark 6.2 in dimension `d`:
"`|S_{n^d}| ≥ naiveBound n d σ` with equality iff `n` prime", for all
`n ≥ 2` and `σ ≥ 2` (the quantifier range of Theorem 6.1, which it was
meant to generalize). This is a definition of the claim, not an assertion. -/
def naiveClaim (d : ℕ) : Prop :=
  ∀ n σ : ℕ, 2 ≤ n → 2 ≤ σ →
    naiveBound n d σ ≤ (numSS n d σ : ℚ)
      ∧ (naiveBound n d σ = (numSS n d σ : ℚ) ↔ n.Prime)

/-- **Remark 6.2, presupposition ("direct generalization of the two-term 2D
bound").** At `d = 2` the naive expression is the two-term bound of
Lemma E.21, `(n+1)σ^n - nσ`.

Paper: "The direct generalization of the two-term 2D bound,
$|S_{n^d}|\ge\sigma^{n^{d-1}}\tfrac{n^d-1}{n-1}
-\sigma\bigl(\tfrac{n^d-1}{n-1}-1\bigr)$ with equality iff $n$ prime, …"

Delta: identity in `ℚ`, for `n ≥ 2` (so that `n - 1 ≠ 0`) and every `σ`. -/
def naiveAtTwoStatement : Prop :=
  ∀ n σ : ℕ, 2 ≤ n →
    naiveBound n 2 σ = ((n : ℚ) + 1) * (σ : ℚ) ^ n - (n : ℚ) * σ

/-- **Remark 6.2, main claim.**

Paper: "The direct generalization of the two-term 2D bound,
$|S_{n^d}|\ge\sigma^{n^{d-1}}\tfrac{n^d-1}{n-1}
-\sigma\bigl(\tfrac{n^d-1}{n-1}-1\bigr)$ with equality iff $n$ prime, is
\emph{false} for every $d\ge3$: …"

Formal: for every `d ≥ 3`, `naiveClaim d` fails.

Delta: the naive claim is quantified over `n ≥ 2, σ ≥ 2` (see `naiveClaim`);
"false" = its negation, i.e. some `(n, σ)` in that range violates the
inequality or the equality-iff-prime clause. -/
def naiveFalseStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ¬ naiveClaim d

/-- **Remark 6.2, the counterexample.**

Paper: "… at $(n,d,\sigma)=(2,3,2)$ it claims $|S_{2^3}|\ge100$, while
$|S_{2^3}|=72$."

Formal: the naive expression at `(2,3,2)` equals `100`, and
`|S_{2^3}| = 72` over a binary alphabet.

Delta: alphabet `Fin 2`; `100` is an exact rational value. -/
def naiveCounterexampleStatement : Prop :=
  naiveBound 2 3 2 = 100 ∧ numSS 2 3 2 = 72

/-- **Remark 6.2, "for prime `n` the true count is the full alternating sum
of Corollary 4.4".**

Paper: "For prime $n$ the true count is the full alternating sum of
Corollary~\ref{cor:prime}, …"

Formal: for prime `p`, `d ≥ 1`, `σ ≥ 1`:
`|S_{p^d}| = Σ_{r=1}^{d} (-1)^{r+1} p^{C(r,2)} [d r]_p σ^{p^{d-r}}`, the sum
being `lowerEnvelope p d σ` (the same expression as `F_d` at `n = p`).

Delta: `σ ≥ 1` as for every counting statement of the paper
(Definition 2.1: "for counting statements σ = 1 is also allowed"; this is
also the range of Corollary 4.4); identity in `ℤ`. This repeats
Corollary 4.4 (`cor:prime`), which another group freezes too. -/
def primeCountFullSumStatement : Prop :=
  ∀ p d σ : ℕ, p.Prime → 1 ≤ d → 1 ≤ σ →
    (numSS p d σ : ℤ) = lowerEnvelope p d σ

/-- **Remark 6.2, "only for `d ≤ 2` do the two coincide" — reading (a):
true count vs. the naive two-term expression.**

Paper: "For prime $n$ the true count is the full alternating sum of
Corollary~\ref{cor:prime}, not its first two terms; only for $d\le2$ do the
two coincide."

Formal: for prime `p`, `d ≥ 1`, `σ ≥ 2`: `|S_{p^d}| = naiveBound p d σ`
iff `d ≤ 2`.

Delta: comparison in `ℚ`. `σ ≥ 2` is necessary and is the remark's range
(Theorem 6.1): at `σ = 1` both sides equal `1` for every `d`.

PAPER ISSUE (wording): "not its first two terms" suggests that the naive
expression is the truncation of the alternating sum to `r ∈ {1, 2}`. It is
not: its second term is `-σ([d 1]_p - 1)`, whereas the `r = 2` term of the
sum is `-p [d 2]_p σ^{p^{d-2}}`; they agree only for `d ≤ 2`. Both readings
of "the two coincide only for `d ≤ 2`" are true and both are frozen
(reading (b) is `truncationCoincideStatement`). Suggested wording: "For
prime `n` the true count is the full `d`-term alternating sum of
Corollary 4.4, which agrees with the naive two-term expression only for
`d ≤ 2`." -/
def naiveCoincideStatement : Prop :=
  ∀ p d σ : ℕ, p.Prime → 1 ≤ d → 2 ≤ σ →
    ((numSS p d σ : ℚ) = naiveBound p d σ ↔ d ≤ 2)

/-- **Remark 6.2, "only for `d ≤ 2` do the two coincide" — reading (b):
the full alternating sum vs. its first two terms.**

Formal: for prime `p`, `d ≥ 1`, `σ ≥ 2`, the alternating sum
`Σ_{r=1}^{d}` equals its truncation `Σ_{r=1}^{min(d,2)}` iff `d ≤ 2`.

Delta: as in reading (a); the truncation keeps the terms `r = 1` and (if
`d ≥ 2`) `r = 2`; identity in `ℤ`. See the PAPER ISSUE recorded at
`naiveCoincideStatement`. -/
def truncationCoincideStatement : Prop :=
  ∀ p d σ : ℕ, p.Prime → 1 ≤ d → 2 ≤ σ →
    (lowerEnvelope p d σ
        = ∑ r ∈ Finset.Icc 1 (min d 2),
            (-1 : ℤ) ^ (r + 1) * (rdCoeff p r d : ℤ) * (σ : ℤ) ^ (p ^ (d - r))
      ↔ d ≤ 2)

/-- **Remark 6.2 (`rem:oldbound-false`), whole statement.** -/
def remarkNaiveStatement : Prop :=
  naiveAtTwoStatement ∧ naiveFalseStatement ∧ naiveCounterexampleStatement
    ∧ primeCountFullSumStatement ∧ naiveCoincideStatement
    ∧ truncationCoincideStatement

/-! ## The function `sopf_d` (lines 612–616) -/

/-- **Definition of `sopf_d`, lines 612–616 (closed form).**

Paper: "Let $\mathrm{sopf}_d(n)=\sum_{p\mid n}\gaussbinom d1_p
=\sum_{p\mid n}\frac{p^d-1}{p-1}$ denote the total number of order-$p$
cyclic subgroups over all primes $p\mid n$ (the $d$-dimensional analogue of
the integer logarithm)."

Formal (first equality is the definition `ShiftSym.sopfD`): the second
equality, `sopf_d(n) = Σ_{p ∣ n} (p^d - 1)/(p - 1)`, in `ℚ`.

Delta: `p ∣ n` ranges over `n.primeFactors`; division in `ℚ` (exact,
`p - 1 ≥ 1`); standing hypotheses `n ≥ 2`, `d ≥ 1`. "(the d-dimensional
analogue of the integer logarithm)" is an analogy: NON-MATHEMATICAL. -/
def sopfFormulaStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d →
    (sopfD n d : ℚ) = ∑ p ∈ n.primeFactors, (((p : ℚ) ^ d - 1) / ((p : ℚ) - 1))

/-- **Definition of `sopf_d`, lines 612–616 (counting meaning).**
`sopf_d(n)` is "the total number of order-`p` cyclic subgroups over all
primes `p ∣ n`" of `(ℤ/nℤ)^d`.

Formal: the number of additive subgroups `C` of `Lat n d` that are cyclic
and have order a prime `p` dividing `n` equals `sopfD n d`.

Delta: subgroups are `AddSubgroup (Lat n d)`; "cyclic" = `IsAddCyclic C`
(redundant for prime order, kept to be literal); order = `Nat.card C`;
standing hypotheses `n ≥ 2`, `d ≥ 1`. -/
def sopfCountStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d →
    Nat.card {C : AddSubgroup (Lat n d) //
        IsAddCyclic C ∧ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ Nat.card C = p}
      = sopfD n d

/-! ## Theorem 6.3 (`thm:upper-bound`, lines 618–628) -/

/-- Right-hand side of Theorem 6.3(i): `Σ_{p ∣ n} [d 1]_p σ^{n^d/p}`.

Delta: `p` ranges over `n.primeFactors`; `[d 1]_p = gaussBinom p d 1`
(bridged to the paper's product formula by `gaussProdEqStatement`); the
exponent `n^d / p` is `ℕ`-division, exact because `p ∣ n ∣ n^d` for
`d ≥ 1`. -/
def unionRHS (n d σ : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, gaussBinom p d 1 * σ ^ (n ^ d / p)

/-- The prefactor `2^d - 1 + 2 log_2 n` of Theorem 6.3(ii) (real number).

Delta: `log_2 n = Real.logb 2 n`; `2^d - 1` is real (no truncation). -/
noncomputable def closedPrefactor (n d : ℕ) : ℝ :=
  (2 : ℝ) ^ d - 1 + 2 * Real.logb 2 n

/-- **Theorem 6.3(i) (union form).**

Paper: "For all $n\ge2$, $d\ge1$, $\sigma\ge2$: … (union form)\quad
$\displaystyle |S_{n^d}| \;\le\; \sum_{p\mid n}\gaussbinom d1_p\,
\sigma^{\,n^d/p}$;"

Delta: alphabet `Fin σ`; `p ∣ n` over prime divisors; exact `ℕ`-division
in the exponent (see `unionRHS`); inequality in `ℕ`. -/
def upperUnionStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → numSS n d σ ≤ unionRHS n d σ

/-- **Theorem 6.3(ii) (closed form).**

Paper: "For all $n\ge2$, $d\ge1$, $\sigma\ge2$: … (closed form)\quad
$\displaystyle |S_{n^d}| \;\le\; \bigl(2^d-1+2\log_2 n\bigr)\,
\sigma^{\,n^d/2}$."

Delta: inequality in `ℝ`; `log_2` = `Real.logb 2`; `σ^{n^d/2}` is the real
power `(σ : ℝ) ^ ((n^d : ℝ) / 2)`. For odd `n^d` the exponent is not an
integer: `ℕ`-division would truncate it to `⌊n^d/2⌋ = (n^d - 1)/2`, shrinking
the right-hand side by the factor `σ^{1/2}` and so asserting a STRONGER
inequality than the paper's; that is why the real power is used. (Review fix,
round 1: the first draft said "`ℕ`-division would weaken the bound", which
was backwards.) -/
def upperClosedStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    (numSS n d σ : ℝ) ≤ closedPrefactor n d * (σ : ℝ) ^ (((n ^ d : ℕ) : ℝ) / 2)

/-- **Theorem 6.3 (`thm:upper-bound`), whole statement: (i) ∧ (ii).** -/
def upperBoundsStatement : Prop :=
  upperUnionStatement ∧ upperClosedStatement

/-! ## The comparison paragraph after Theorem 6.3 (lines 653–667) -/

/-- The bound `2 log_2(n) n^{d-1} σ^{N/p_1}` of line 658 (= the upper bound
of Proposition 10.1, `prop:rate`).

Delta: real arithmetic; `n^{d-1}` with `ℕ`-subtraction (exact for `d ≥ 1`);
`p_1 = Nat.minFac n`; the exponent `N/p_1` is the real quotient (an integer
since `p_1 ∣ n`), used as a real power. -/
noncomputable def rateRHS (n d σ : ℕ) : ℝ :=
  2 * Real.logb 2 n * (n : ℝ) ^ (d - 1)
    * (σ : ℝ) ^ (((n ^ d : ℕ) : ℝ) / (n.minFac : ℝ))

/-- **Lines 657–659, "Bound (i) implies …" (the implication).**

Paper: "Bound (i) implies $|S|\le2\log_2(n)\,n^{d-1}\,\sigma^{N/p_1}$
(Proposition~\ref{prop:rate}), …"

Formal: the right-hand side of (i) is at most `2 log_2(n) n^{d-1}
σ^{N/p_1}` — the inequality that makes "(i) implies" valid.

Delta: comparison in `ℝ`; standing hypotheses `n ≥ 2, d ≥ 1, σ ≥ 2`. -/
def unionImpliesRateStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → (unionRHS n d σ : ℝ) ≤ rateRHS n d σ

/-- **Lines 657–659, the implied bound.** `|S| ≤ 2 log_2(n) n^{d-1}
σ^{N/p_1}`.

Delta: as for `rateRHS`. This is the upper half of Proposition 10.1
(`prop:rate`), which another group freezes too. -/
def rateBoundStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → (numSS n d σ : ℝ) ≤ rateRHS n d σ

/-- **Line 655, the cited bound of Gao–Jackson–Seward, specialized.**

Paper: "For comparison, on $G=\ZZ_n^d$ the general-group bounds give
$|S|\le\sigma^{N-1}$ \cite[Cor.~1.7.2]{gjs2016} and …"

Formal: `|S_{n^d}| ≤ σ^{n^d - 1}`.

Delta: `ℕ` arithmetic; `n^d - 1` is exact since `n^d ≥ 1`; GJS state "at
least `(k-1)k^{|G|-1}` aperiodic points" for `k > 1`, i.e. this bound by
complementation; hypotheses `n ≥ 2, d ≥ 1, σ ≥ 2`. -/
def gjsBoundStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → numSS n d σ ≤ σ ^ (n ^ d - 1)

/-- **Lines 656–657, the cited bound of Castillo-Ramirez–Gadouleau,
specialized.**

Paper: "… and $|S|\le(N-1)\sigma^{N/p_1}$ \cite[Thm.~5(ii)]{cg2017}, $p_1$
the smallest prime factor."

Formal: `|S_{n^d}| ≤ (n^d - 1) σ^{n^d / p_1}`.

Delta: `ℕ` arithmetic; `n^d - 1` exact (`n^d ≥ 1`); `n^d / p_1` exact
(`p_1 = Nat.minFac n ∣ n ∣ n^d`); CG state `q^n - (n-1)q^{n/p} ≤ ac(G;A)`
for `|G| = n ≥ 2`, `q ≥ 2`, i.e. this bound by complementation. -/
def cgBoundStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    numSS n d σ ≤ (n ^ d - 1) * σ ^ (n ^ d / n.minFac)

/-- **Lines 659–661, sharpening the prefactor of [cg2017].**

Paper: "… sharpening the prefactor $N-1=n^d-1$ of \cite{cg2017} at the same
exponent for every $n\ge7$ (and for $n\ge5$ when $d\ge2$; …"

Formal: if `n ≥ 7, d ≥ 1`, or `n ≥ 5, d ≥ 2`, then
`2 log_2(n) n^{d-1} < n^d - 1` (strict: "sharpening").

Delta: real arithmetic; "at the same exponent" holds by construction (both
bounds carry `σ^{N/p_1}`), so only the prefactors are compared.

Remark (not part of the frozen claim; it only shows that the paper's
thresholds cannot be lowered): the inequality FAILS for every `d ≥ 1` at
`n = 2` and `n = 4` (the left side is `2^d`, resp. `4^d`, against `2^d - 1`,
resp. `4^d - 1`) and at `n = 3` (`2 log_2 3 > 3` because `3^2 > 2^3`, so the
left side exceeds `3^d`), and at `d = 1` for `n = 5` (`2 log_2 5 > 4` because
`5^2 > 2^4`) and `n = 6` (`2 log_2 6 > 5` because `6^2 > 2^5`); each step is
an exact integer comparison. The frozen inequality itself was confirmed in
exact big-integer arithmetic through the equivalent form
`n^{2 n^{d-1}} < 2^{n^d - 1}` on 970 instances (`n ≤ 300, d ≤ 3`;
`n ≤ 64, d = 4`; `n ≤ 16, d ∈ {5, 6}`), with no violation, while all 20
excluded instances of that range fail (script `s06/cg_sharpen_exact.py`,
see the S06 report). (Review fix, round 1: the first draft said "checked
exactly" for a check that was done in floating-point log space.) -/
def cgSharpenStatement : Prop :=
  ∀ n d : ℕ, ((7 ≤ n ∧ 1 ≤ d) ∨ (5 ≤ n ∧ 2 ≤ d)) →
    2 * Real.logb 2 n * (n : ℝ) ^ (d - 1) < (n : ℝ) ^ d - 1

/-- **Lines 661–662, the tie at `n = 2`.**

Paper: "… at $n=2$ the union prefactor $\mathrm{sopf}_d(2)=2^d-1$ exactly
ties $N-1$, …"

Formal: for `d ≥ 1`, `sopf_d(2) = 2^d - 1` (which is `N - 1` for `n = 2`),
and the union bound (i) at `n = 2` coincides with the [cg2017] bound
`(N - 1) σ^{N/p_1}` for every `σ`.

Delta: `ℕ` arithmetic, `2^d - 1` exact; `p_1 = Nat.minFac 2`. The phrase
"for `n ∈ {3,4}` the two are comparable" that follows is vague:
NON-MATHEMATICAL (precisely: for `n ∈ {3,4}`, `2 log_2(n) n^{d-1} > N - 1`,
i.e. no sharpening; recorded in the report, not frozen). -/
def tieAtTwoStatement : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    sopfD 2 d = 2 ^ d - 1
      ∧ ∀ σ : ℕ, unionRHS 2 d σ = (2 ^ d - 1) * σ ^ (2 ^ d / Nat.minFac 2)

/-- **Lines 663–664, even `n`: the closed form improves the prefactor
further.**

Paper: "… for even $n\ge4$ and $d\ge2$, the closed form (ii) improves the
prefactor further to $2^d-1+2\log_2 n$."

Formal: for even `n ≥ 4`, `d ≥ 2`: `p_1 = 2` (so (ii) has the same
exponent `N/2 = N/p_1`), and `2^d - 1 + 2 log_2 n` is strictly smaller than
both previous prefactors, `2 log_2(n) n^{d-1}` and `N - 1 = n^d - 1`.

Delta: real arithmetic; "further" read as: strictly below the prefactor of
the preceding sentence (`2 log_2(n) n^{d-1}`) and below `N - 1`.

PAPER ISSUE (ambiguity): "the prefactor" must refer to `2 log_2(n) n^{d-1}`
(and `N - 1`). It does NOT hold for the union prefactor `sopf_d(n)` that the
same paragraph mentions at `n = 2`: e.g. `n = 4`: `sopf_d(4) = 2^d - 1 <
2^d + 3 = 2^d - 1 + 2 log_2 4`; `n = 6, d = 2`: `sopf_2(6) = 7 < 3 + 2 log_2 6
≈ 8.17`. Suggested wording: "improves the prefactor
`2 log_2(n) n^{d-1}` further to `2^d - 1 + 2 log_2 n`". -/
def evenImproveStatement : Prop :=
  ∀ n d : ℕ, Even n → 4 ≤ n → 2 ≤ d →
    n.minFac = 2
      ∧ closedPrefactor n d < 2 * Real.logb 2 n * (n : ℝ) ^ (d - 1)
      ∧ closedPrefactor n d < (n : ℝ) ^ d - 1

/-- **Lines 664–665, odd `n`: the exponent of (i).**

Paper: "(For odd $n$ the exponent $N/p_1\le N/3$ of (i) is stronger than the
$N/2$ of (ii); the two forms serve different purposes.)"

Formal: for odd `n ≥ 2` (so `n ≥ 3`) and `d ≥ 1`: every exponent `N/p` of
(i) is at most `N/p_1`, `N/p_1 ≤ N/3`, and `N/3 < N/2` ("stronger" =
strictly smaller exponent).

Delta: exponents compared as real numbers (they are integers since
`p ∣ n`); "the two forms serve different purposes" is NON-MATHEMATICAL. -/
def oddExponentStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d → Odd n →
    (∀ p ∈ n.primeFactors,
        ((n ^ d : ℕ) : ℝ) / (p : ℝ) ≤ ((n ^ d : ℕ) : ℝ) / (n.minFac : ℝ))
      ∧ ((n ^ d : ℕ) : ℝ) / (n.minFac : ℝ) ≤ ((n ^ d : ℕ) : ℝ) / 3
      ∧ ((n ^ d : ℕ) : ℝ) / 3 < ((n ^ d : ℕ) : ℝ) / 2

/-- **Line 667, the cited bound of Lemma E.22 of the 2019 paper.**

The comparison sentence presupposes the 2019 bound
`|S_{n×n}| ≤ 6 log_2(n) |Σ|^{n^2/2}` (banda2019, Lemma E.22).

Delta: `|Σ| = σ`, alphabet `Fin σ`; real arithmetic; `σ^{n^2/2}` is the real
power; hypotheses `n ≥ 2`, `σ ≥ 2` (the 2019 lemma states it for every `n`;
`n ≥ 2` is the range of this paper). -/
def e22BoundStatement : Prop :=
  ∀ n σ : ℕ, 2 ≤ n → 2 ≤ σ →
    (numSS n 2 σ : ℝ) ≤ 6 * Real.logb 2 n * (σ : ℝ) ^ (((n ^ 2 : ℕ) : ℝ) / 2)

/-- **Lines 666–667, `d = 2`: (ii) sharpens Lemma E.22.**

Paper: "For $d=2$ and $n\ge4$, (ii) also slightly sharpens the
$6\log_2(n)\sigma^{n^2/2}$ of \cite[Lemma~E.22]{banda2019}."

Formal: for `n ≥ 4`, `σ ≥ 2`:
`(2^2 - 1 + 2 log_2 n) σ^{n^2/2} < 6 log_2(n) σ^{n^2/2}`.

Delta: real arithmetic; "sharpens" = strictly smaller bound; "slightly" is
NON-MATHEMATICAL.

PAPER ISSUE (minor, misleading but not false): the restriction `n ≥ 4` is
unnecessary — `3 + 2 log_2 n < 6 log_2 n` iff `n > 2^{3/4}`, so (ii) also
sharpens E.22 at `n = 2` (5 vs 6) and `n = 3` (≈ 6.17 vs ≈ 9.51). The
statement is frozen as written (`n ≥ 4`). -/
def e22SharpenStatement : Prop :=
  ∀ n σ : ℕ, 4 ≤ n → 2 ≤ σ →
    closedPrefactor n 2 * (σ : ℝ) ^ (((n ^ 2 : ℕ) : ℝ) / 2)
      < 6 * Real.logb 2 n * (σ : ℝ) ^ (((n ^ 2 : ℕ) : ℝ) / 2)

/-- **The comparison paragraph (lines 653–667), whole.** -/
def comparisonStatement : Prop :=
  unionImpliesRateStatement ∧ rateBoundStatement ∧ gjsBoundStatement
    ∧ cgBoundStatement ∧ cgSharpenStatement ∧ tieAtTwoStatement
    ∧ evenImproveStatement ∧ oddExponentStatement ∧ e22BoundStatement
    ∧ e22SharpenStatement

/-! ## Corollary 7.1 (`cor:prob`, lines 673–691) -/

/-- The decay rate of Corollary 7.1,
`c = log_σ(1/P^unif_{n^d}) / N`, `N = n^d`.

Delta: `log_σ = Real.logb σ`; `P^unif = probUnif n d σ` (Common.lean,
`|S| / σ^{n^d}` in `ℝ`). For `n ≥ 2`, `d ≥ 1`, `σ ≥ 2` one has
`0 < P^unif ≤ 1` (the constant configurations are shift-symmetric), so
neither `1/0 = 0` nor `Real.log` of a nonpositive number is ever hit; this
positivity is part of what the proofs must establish, not an assumption. -/
noncomputable def decayRate (n d σ : ℕ) : ℝ :=
  Real.logb σ (1 / probUnif n d σ) / ((n ^ d : ℕ) : ℝ)

/-- **Corollary 7.1, "decays as `σ^{-cN}`" (consistency of the definition of
`c`).**

Paper: "… so $P^{\mathrm{unif}}_{n^d}$ decays as $\sigma^{-cN}$ with
$N=n^d$ and decay rate $c=\log_\sigma(1/P^{\mathrm{unif}}_{n^d})/N$ …"

Formal: `P^unif = σ^{-c N}` exactly, with `c = decayRate n d σ`.

Delta: real power of `σ > 0`. The identity needs `P^unif > 0`, which holds
for `n ≥ 2, d ≥ 1, σ ≥ 2` and is part of what must be proved. -/
def decayIdentityStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    probUnif n d σ = (σ : ℝ) ^ (-(decayRate n d σ * ((n ^ d : ℕ) : ℝ)))

/-- **Corollary 7.1, the sandwich.**

Paper: "For a configuration drawn uniformly from $\Sigma^{n^d}$,
$P^{\mathrm{unif}}_{n^d}=|S_{n^d}|/\sigma^{n^d}$ satisfies
\[ F_d(n,\sigma)\,\sigma^{-n^d} \;\le\; P^{\mathrm{unif}}_{n^d} \;\le\;
\bigl(2^d-1+2\log_2 n\bigr)\,\sigma^{-n^d/2}, \]"

Delta: real arithmetic; `F_d = lowerEnvelope` (bridged by
`envelopeIntegralStatement`); `σ^{-n^d}` and `σ^{-n^d/2}` are real powers
of `σ > 0`; `P^unif = probUnif` (the paper's definition
`|S_{n^d}|/σ^{n^d}`); hypotheses: the standing `n ≥ 2, d ≥ 1, σ ≥ 2`
(both ends rest on Theorems 6.1 and 6.3, which assume them). -/
def probSandwichStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    (lowerEnvelope n d σ : ℝ) * (σ : ℝ) ^ (-((n ^ d : ℕ) : ℝ)) ≤ probUnif n d σ
      ∧ probUnif n d σ
          ≤ closedPrefactor n d * (σ : ℝ) ^ (-(((n ^ d : ℕ) : ℝ) / 2))

/-- **Corollary 7.1, the single-subgroup inclusion.**

Paper: "… the upper end is the single-subgroup inclusion
$\Fix(C)\subseteq S_{n^d}$ for one order-$p_1$ cyclic subgroup $C$, …"

Formal: there is a cyclic subgroup `C ≤ (ℤ/nℤ)^d` of order `p_1` with
`Fix(C) ⊆ S_{n^d}`; and `|Fix(C)| = σ^{N/p_1}` (the count that turns the
inclusion into the probability bound; Lemma 3.2(i)).

Delta: `Fix(C) = ShiftSym.fixedBy (Fin σ) C`; `S_{n^d}` = the set of
`IsShiftSymmetric` configurations; "cyclic" = `IsAddCyclic C`; order =
`Nat.card C`; `N/p_1` is exact `ℕ`-division (`p_1 ∣ n ∣ n^d`). -/
def singleSubgroupStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∃ C : AddSubgroup (Lat n d),
      IsAddCyclic C ∧ Nat.card C = n.minFac
        ∧ fixedBy (Fin σ) C ⊆ {s | IsShiftSymmetric s}
        ∧ Nat.card (fixedBy (Fin σ) C) = σ ^ (n ^ d / n.minFac)

/-- **Corollary 7.1, `P^unif ≥ σ^{N/p_1 - N}`.**

Paper: "… which gives $P^{\mathrm{unif}}_{n^d}\ge\sigma^{N/p_1-N}$ (this is
also the lower bound of Proposition~\ref{prop:rate})."

Delta: real arithmetic; `σ^{N/p_1 - N}` is the real power with exponent
`N/p_1 - N` computed in `ℝ`; `p_1 = Nat.minFac n`. The parenthetical
identification with Proposition 10.1 is frozen separately as
`probSingleLowerIsRateLowerStatement`. -/
def probSingleLowerStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    (σ : ℝ) ^ (((n ^ d : ℕ) : ℝ) / (n.minFac : ℝ) - ((n ^ d : ℕ) : ℝ))
      ≤ probUnif n d σ

/-- **Corollary 7.1, "(this is also the lower bound of Proposition 10.1)".**

Paper: "… which gives $P^{\mathrm{unif}}_{n^d}\ge\sigma^{N/p_1-N}$ (this is
also the lower bound of Proposition~\ref{prop:rate})."

Proposition 10.1 (`prop:rate`, lines 888–895): "For all $n\ge2$, $d\ge1$,
$\sigma\ge2$: $\sigma^{N/p_1}\le|S_{n^d}|\le\dots$" — its lower bound is
`σ^{N/p_1} ≤ |S_{n^d}|`.

Formal: for every `n ≥ 2, d ≥ 1, σ ≥ 2`, the inequality
`σ^{N/p_1 - N} ≤ P^unif` (the instance of `probSingleLowerStatement`) holds
if and only if the inequality `σ^{N/p_1} ≤ |S_{n^d}|` (the instance of
Proposition 10.1's lower bound) holds.

Delta: "is also" is read as logical equivalence of the two inequalities
for each `(n, d, σ)`, with identical hypotheses — the same reading that
`d2IsE21Statement` gives to "exactly" (per-instance equivalence implies
equivalence of the two universally quantified statements). The left side
is verbatim the body of `probSingleLowerStatement` (real power, exponent
`N/p_1 - N` computed in `ℝ`, `P^unif = probUnif n d σ`). The right side is
verbatim the body of `ShiftSym.P09.rateLowerStatement` (`ℕ` arithmetic;
`N/p_1 = n^d / Nat.minFac n` is exact `ℕ`-division because
`p_1 ∣ n ∣ n^d` for `d ≥ 1`; S09 writes `p1 n`, an `abbrev` for
`n.minFac`). S09 belongs to another group and is not imported, so the body
is restated here; a scratch probe importing S09 checks by `Iff.rfl` that
the universally closed right side IS `ShiftSym.P09.rateLowerStatement` (see
the S06 report). The other possible reading of the parenthetical — "the
same single-subgroup argument also proves the lower bound of
Proposition 10.1" — is a claim about proofs: NON-MATHEMATICAL; its
mathematical content is this equivalence together with
`singleSubgroupStatement`. -/
def probSingleLowerIsRateLowerStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ((σ : ℝ) ^ (((n ^ d : ℕ) : ℝ) / (n.minFac : ℝ) - ((n ^ d : ℕ) : ℝ))
        ≤ probUnif n d σ
      ↔ σ ^ (n ^ d / n.minFac) ≤ numSS n d σ)

/-- **Corollary 7.1, upper end of the decay rate.**

Paper: "… so $P^{\mathrm{unif}}_{n^d}$ decays as $\sigma^{-cN}$ with $N=n^d$
and decay rate $c=\log_\sigma(1/P^{\mathrm{unif}}_{n^d})/N\in
[\tfrac12-o(1),\,1-\tfrac1{p_1}]$, where $p_1$ is the smallest prime factor
of $n$ …"

Formal (upper end, exact, no error term): `c ≤ 1 - 1/p_1`.

Delta: `c = decayRate n d σ`; `p_1 = Nat.minFac n`; real arithmetic. -/
def decayUpperStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    decayRate n d σ ≤ 1 - 1 / (n.minFac : ℝ)

/-- **Corollary 7.1, lower end of the decay rate, explicit form.**

Paper: "… the lower end is Theorem~\ref{thm:upper-bound}(ii), …"

Formal: what Theorem 6.3(ii) gives after taking `log_σ`:
`c ≥ 1/2 - log_σ(2^d - 1 + 2 log_2 n)/N`; the subtracted term is the
paper's `o(1)` (see `decayLowerUniformStatement`).

Delta: real arithmetic; `c = decayRate n d σ`. -/
def decayLowerExplicitStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    1 / 2 - Real.logb σ (closedPrefactor n d) / ((n ^ d : ℕ) : ℝ) ≤ decayRate n d σ

/-- **Corollary 7.1, lower end of the decay rate, `1/2 - o(1)`.**

Paper: "… decay rate … $\in [\tfrac12-o(1),\,1-\tfrac1{p_1}]$ … Here
$o(1)$ refers to any regime with $N=n^d\to\infty$."

Formal (explicit uniform ε–M form): for every `ε > 0` there is `M` such
that `c ≥ 1/2 - ε` for ALL `n ≥ 2, d ≥ 1, σ ≥ 2` with `n^d ≥ M`.

Delta: "any regime with `N → ∞`" is formalized as uniformity in `(n, d, σ)`
jointly, conditioned only on `N = n^d ≥ M`; this implies the limit
statement along every sequence of parameters with `N → ∞` (any mix of
`n → ∞` and `d → ∞`, with `σ` arbitrary, even varying). -/
def decayLowerUniformStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → M ≤ n ^ d →
    1 / 2 - ε ≤ decayRate n d σ

/-- **Corollary 7.1, `c ∈ [1/2 - o(1), 1 - 1/p_1]`.** -/
def decayIntervalStatement : Prop :=
  decayLowerUniformStatement ∧ decayUpperStatement

/-- **Corollary 7.1 (`cor:prob`), whole statement.** -/
def probUnifCorollaryStatement : Prop :=
  probSandwichStatement ∧ decayIdentityStatement ∧ decayIntervalStatement
    ∧ decayLowerExplicitStatement ∧ singleSubgroupStatement
    ∧ probSingleLowerStatement ∧ probSingleLowerIsRateLowerStatement

/-! ## Sanity checks (no proofs of the frozen Props)

Computable sides evaluated with `#eval` (compiler, no kernel trust needed,
no axioms added) and kernel `decide`/`rfl` where cheap. -/

-- Remark 6.2: the naive expression at (2,3,2) is 100 (expected: 100).
#eval naiveBound 2 3 2
-- At d = 2 it is the 2019 two-term bound: (n+1)σ^n - nσ at (3,2): 4*8-6 = 26.
#eval naiveBound 3 2 2
-- F_3(2,2) = 7*16 - 2*7*4 + 8*2 = 72 = |S_{2^3}| (prime n: equality).
example : lowerEnvelope 2 3 2 = 72 := by decide
-- The certified enumeration RHS at (2,3,2) is 72 (|S_{2^3}| = 72; expected: 72).
#eval enumerationRHS 2 3 2
-- The two-term truncation at (2,3,2): 7*16 - 2*7*4 = 56 ≠ 72.
example : (∑ r ∈ Finset.Icc 1 (min 3 2),
    (-1 : ℤ) ^ (r + 1) * (rdCoeff 2 r 3 : ℤ) * (2 : ℤ) ^ (2 ^ (3 - r))) = 56 := by
  decide
-- Remark 6.2 at the primes 3 and 2, d = 3, 4: naive expression vs certified count
-- (expected: (6632, 6398) and (3812, 3072); naive > |S|, so equality-at-primes fails).
#eval (naiveBound 3 3 2, enumerationRHS 3 3 2)
#eval (naiveBound 2 4 2, enumerationRHS 2 4 2)
-- Theorem 6.3(i) RHS at (2,3,2): [3 1]_2 * 2^4 = 112 ≥ 72.
#eval unionRHS 2 3 2
-- sopf_2(6) = [2 1]_2 + [2 1]_3 = 3 + 4 = 7; sopf_3(2) = 7 = 2^3 - 1.
#eval sopfD 6 2
#eval sopfD 2 3
-- Product formula agrees with q-Pascal on small cases (#eval, ℚ).
#eval (gaussProd 2 4 2, gaussBinom 2 4 2, gaussProd 3 3 1, gaussBinom 3 3 1,
  gaussProd 6 3 2, gaussBinom 6 3 2, gaussProd 2 2 3)
-- Paper's F_d with product-formula binomials vs lowerEnvelope (composite n = 6).
#eval (paperEnvelope 6 2 2, lowerEnvelope 6 2 2, paperEnvelope 4 3 3, lowerEnvelope 4 3 3)

/-! Non-vacuity of hypotheses (each antecedent block is satisfiable). -/
example : 2 ≤ 2 ∧ 1 ≤ 3 ∧ 2 ≤ 2 := by decide
example : (7 ≤ 7 ∧ 1 ≤ 1) ∨ (5 ≤ 7 ∧ 2 ≤ 1) := by decide
example : (7 ≤ 5 ∧ 1 ≤ 2) ∨ (5 ≤ 5 ∧ 2 ≤ 2) := by decide
example : Even 4 ∧ 4 ≤ 4 ∧ 2 ≤ 2 := by decide
example : 2 ≤ 3 ∧ 1 ≤ 1 ∧ Odd 3 := by decide
example : Nat.Prime 2 ∧ 1 ≤ 3 ∧ 2 ≤ 2 := by decide
-- For every M the guard `M ≤ n^d` of the uniform o(1) form is satisfiable.
example (M : ℕ) : ∃ n d : ℕ, 2 ≤ n ∧ 1 ≤ d ∧ M ≤ n ^ d :=
  ⟨M + 2, 1, by omega, le_refl 1, by simp⟩
-- `Nat.minFac` is the smallest prime factor on small cases.
example : Nat.minFac 2 = 2 ∧ Nat.minFac 9 = 3 ∧ Nat.minFac 15 = 3 ∧ Nat.minFac 12 = 2 := by
  norm_num

end ShiftSym.P06
