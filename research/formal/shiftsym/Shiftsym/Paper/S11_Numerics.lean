/-
Group 11 (Numerics) of the paper-wide formalization (Phase H, 2026-10-15):
frozen statements (NO proofs) for the exact-computation claims of
`shift_symmetry_d_dimensions.tex` (v3.1):

* Observation 7.3 `obs:extrema`            (paper lines 704–724);
* Remark 10.3     `rem:dc-measured`        (paper lines 968–988), with the
  caption of Figure 3 `fig:inversion`      (paper lines 990–1002) that it cites;
* Observation 10.4 `obs:dstar`             (paper lines 1006–1018);
* Observation 10.5 `obs:inversion`         (paper lines 1020–1026).

Conventions used throughout (all recorded again under "Delta" per Prop):
* `|S_{n^d}|` is `numSS n d σ` (alphabet `Fin σ`) and
  `P^unif_{n^d}` (written `P(n)` in the paper when `d, σ` are fixed) is
  `probUnif n d σ = numSS n d σ / σ^(n^d)` in `ℝ` (both from
  `Shiftsym/Paper/Common.lean`). Every frozen `Prop` speaks about these
  real objects, never about an evaluator.
* `log₁₀` is `Real.logb 10`. All arguments of `Real.logb` below are
  positive (each `probUnif` with `n ≥ 2, σ ≥ 1` is positive: constant
  configurations are shift-symmetric), so the `Real.log` junk values at
  `x ≤ 0` never enter.
* A decimal printed with `k` digits after the point stands for the closed
  rounding interval of half-width `5·10^{-(k+1)}` around it
  (e.g. `−28.61` ↦ `|x − (−28.61)| ≤ 0.005`).
* "Local minimum/maximum at `n`" of a sequence `f : ℕ → ℝ` is a
  comparison with both neighbours `f (n−1)` and `f (n+1)`; it is only ever
  applied at `n ≥ 3`, so `n − 1` is the true predecessor. The paper does not
  say strict or non-strict, so every claim is frozen reading-independently:
  POSITIVE claims ("has local minima at …") use the strict predicates
  `IsLocalMinAt`/`IsLocalMaxAt` (the definition of the paper's audit,
  research/experiments/verify_bruteforce.py §[6]), which imply the
  non-strict ones; NEGATIVE claims ("is not a local minimum", "the pattern
  breaks") are stated under BOTH readings, `¬ strict ∧ ¬ non-strict` (the
  non-strict negation is the stronger one; repair round 2).

Pre-verification (exact arithmetic, definition-level brute force on small
cases + the certified divisor form of Theorem 4.3 + a 60-digit log-space
evaluator cross-checked against exact integers):
scratchpad/research/formal_ext/s11/check_s11.py (output alongside); the
claims added in repair round 1 (after the fidelity review) are checked by
scratchpad/research/formal_ext/s11/check_s11_r1.py (80 digits, output
alongside), those of repair round 2 by s11/check_s11_r2.py (80/200 digits,
output alongside), those of repair round 3 by s11/check_s11_r3.py (90 digits,
a fresh implementation sharing no code with the earlier scripts; output
alongside).

Besides the paper's claims, the file freezes a few EVIDENCE Props
(`dcOffsetLimitStatement`, `measuredGapCauseStatement`,
`dstarLiteralDegenerateStatement`, `dstarUnclampedByThetaStatement`,
`compositeNearestPrimeFailStatement`, `inversionD3ScopeStatement`) that make
the recorded PAPER ISSUEs machine-checkable, and one EXTENSION (`dstarAllPrimesStatement`). None of
them is part of `group11Statement`.

Figure numbers are those of the compiled paper (`fig:pattern-flip` =
Figure 1, image chart14_pattern_flip.png; `fig:inversion` = Figure 3, image
chart15_inversion_dimension.png — the name `fig15SignFlipStatement` refers
to that image file, not to a paper figure number).
-/
import Shiftsym.Paper.Common

namespace ShiftSym.P11

/-! ## Shared vocabulary of this group -/

/-- `n` is a (strict) local minimum of `f`: `f n < f (n-1)` and
`f n < f (n+1)`. Only used with `n ≥ 3`. -/
def IsLocalMinAt (f : ℕ → ℝ) (n : ℕ) : Prop :=
  f n < f (n - 1) ∧ f n < f (n + 1)

/-- `n` is a (strict) local maximum of `f`: `f (n-1) < f n` and
`f (n+1) < f n`. Only used with `n ≥ 3`. -/
def IsLocalMaxAt (f : ℕ → ℝ) (n : ℕ) : Prop :=
  f (n - 1) < f n ∧ f (n + 1) < f n

/-- `n` is a non-strict local minimum of `f`: `f n ≤ f (n-1)` and
`f n ≤ f (n+1)` (the other reading of "local minimum"). Only used with
`n ≥ 3`. -/
def IsLocalMinAtWeak (f : ℕ → ℝ) (n : ℕ) : Prop :=
  f n ≤ f (n - 1) ∧ f n ≤ f (n + 1)

/-- `n` is a non-strict local maximum of `f`: `f (n-1) ≤ f n` and
`f (n+1) ≤ f n`. Only used with `n ≥ 3`. -/
def IsLocalMaxAtWeak (f : ℕ → ℝ) (n : ℕ) : Prop :=
  f (n - 1) ≤ f n ∧ f (n + 1) ≤ f n

/-- The extremal pattern of Observation 7.3 for fixed `d, σ`, over the
range the paper computed: `n ↦ P^unif_{n^d}` has a local minimum at every
prime `5 ≤ n ≤ 40` and a local maximum at every even `4 < n ≤ 40` (this
uses the values `P(n)` for `4 ≤ n ≤ 41`, i.e. "exact computation for
`n ≤ 41`"). -/
def ExtremalPattern (d σ : ℕ) : Prop :=
  (∀ n : ℕ, n.Prime → 5 ≤ n → n ≤ 40 →
      IsLocalMinAt (fun m => probUnif m d σ) n) ∧
    (∀ n : ℕ, Even n → 4 < n → n ≤ 40 →
      IsLocalMaxAt (fun m => probUnif m d σ) n)

/-- `ExtremalPattern` under the non-strict reading of "local
minimum/maximum" (same range). It is implied by `ExtremalPattern`, so its
negation is the stronger form of "the pattern breaks". -/
def ExtremalPatternWeak (d σ : ℕ) : Prop :=
  (∀ n : ℕ, n.Prime → 5 ≤ n → n ≤ 40 →
      IsLocalMinAtWeak (fun m => probUnif m d σ) n) ∧
    (∀ n : ℕ, Even n → 4 < n → n ≤ 40 →
      IsLocalMaxAtWeak (fun m => probUnif m d σ) n)

/-! ## Observation 7.3 (`obs:extrema`, paper lines 704–724) -/

/-- **Obs. 7.3, part (a): the `d = 2` pattern** (paper lines 706–708).

Paper (verbatim): "For $d=2$, $\sigma=2$, exact computation for $n\le41$
confirms the pattern of \cite[Figs.~6,~8]{banda2019}: $P^{\mathrm{unif}}$
has local minima at every prime $5\le n\le40$ and local maxima at every
even $4<n\le40$".

Delta: alphabet `Fin 2`; `P(n) = probUnif n 2 2`; "local minimum /
maximum" = STRICT comparison with both neighbours (`IsLocalMinAt`,
`IsLocalMaxAt`) — the paper does not say strict/non-strict; strict is the
audit's definition and implies the non-strict one (`ExtremalPattern 2 2 →
ExtremalPatternWeak 2 2`), so the frozen claim holds under either reading
(there are no ties among `P(2), …, P(41)`, checked exactly, s11/check_s11_r2.py). The range is exactly the paper's
(primes `5 ≤ n ≤ 40`, even `4 < n ≤ 40`; neighbours reach `n = 41`). The
attribution to [banda2019, Figs. 6, 8] is bibliographic, not formalized.
Odd composites (9, 15, …) are not claimed and not included (they happen to
be local minima too). -/
def extremaD2Statement : Prop :=
  ExtremalPattern 2 2

/-- **Obs. 7.3, part (b): the boundary exception `n = 3`** (lines 708–711).

Paper (verbatim): "(the boundary is a genuine exception:
$P(3)=26/2^9>736/2^{16}=P(4)$, so $3$ is not a local minimum)".

Delta: `d = 2`, `σ = 2` (context of the sentence); the equalities
`P(3) = 26/2^9`, `P(4) = 736/2^16` are stated in `ℝ` together with the
underlying counts `|S_{3^2}| = 26`, `|S_{4^2}| = 736` that they encode
(`2^9 = σ^{3^2}`, `2^16 = σ^{4^2}`); "not a local minimum" is stated under
both readings, `¬ IsLocalMinAt _ 3 ∧ ¬ IsLocalMinAtWeak _ 3` (both follow
from `P(4) < P(3)`; repair round 2 added the non-strict conjunct). -/
def extremaBoundaryStatement : Prop :=
  numSS 3 2 2 = 26 ∧ numSS 4 2 2 = 736 ∧
    probUnif 3 2 2 = (26 : ℝ) / 2 ^ 9 ∧
    probUnif 4 2 2 = (736 : ℝ) / 2 ^ 16 ∧
    (736 : ℝ) / 2 ^ 16 < (26 : ℝ) / 2 ^ 9 ∧
    ¬ IsLocalMinAt (fun m => probUnif m 2 2) 3 ∧
    ¬ IsLocalMinAtWeak (fun m => probUnif m 2 2) 3

/-- **Obs. 7.3, part (c): the `d = 3` values** (lines 711–715).

Paper (verbatim): "For $d\ge3$ the pattern \emph{breaks}: at $d=3$,
$\sigma=2$, \[ \log_{10}P(5)=-28.61 \;>\; \log_{10}P(6)=-31.67, \]".

Delta: `log₁₀ = Real.logb 10`; the two rounded decimals are the closed
intervals `|x − (−28.61)| ≤ 0.005`, `|y − (−31.67)| ≤ 0.005`; the strict
inequality `>` is stated for the exact values (it is also implied by the two
intervals, which are disjoint). Exact values (60 digits, two
independent evaluators): `log₁₀ P(5³) = −28.611639839…`,
`log₁₀ P(6³) = −31.666141491…`. -/
def extremaD3ValuesStatement : Prop :=
  |Real.logb 10 (probUnif 5 3 2) - (-28.61)| ≤ 0.005 ∧
    |Real.logb 10 (probUnif 6 3 2) - (-31.67)| ≤ 0.005 ∧
    Real.logb 10 (probUnif 6 3 2) < Real.logb 10 (probUnif 5 3 2)

/-- **Obs. 7.3, part (d): consequences at `n = 5, 6`, `d = 3`**
(lines 716–717).

Paper (verbatim): "so the prime $5$ is not a local minimum and the
composite $6$ is not a local maximum;".

Delta: `d = 3`, `σ = 2`; each negative claim under BOTH readings of
"local minimum/maximum" (`¬ strict ∧ ¬ non-strict`; the non-strict
negation implies the strict one, the strict conjuncts are kept for
literalness). The "so" refers to the strict inequality `P(5³) > P(6³)` of
part (c), which implies all four conjuncts.
Repair round 2: the non-strict conjuncts were added.
Review note (literal reviewer, non-blocking recommendation to add witness
inequalities): implemented as the both-readings negation instead. That is
exactly "not a local minimum/maximum" under either reading; a witness such
as `P(10³) < P(9³)` would additionally name WHICH neighbour is larger, which
the paper does not say for `n = 10` or at `d = 4` (here at `d = 3` the
witness `P(6³) < P(5³)` is the paper's own and is frozen in part (c)). -/
def extremaD3FailStatement : Prop :=
  (¬ IsLocalMinAt (fun m => probUnif m 3 2) 5 ∧
      ¬ IsLocalMinAtWeak (fun m => probUnif m 3 2) 5) ∧
    (¬ IsLocalMaxAt (fun m => probUnif m 3 2) 6 ∧
      ¬ IsLocalMaxAtWeak (fun m => probUnif m 3 2) 6)

/-- **Obs. 7.3, part (e): the failure at `n = 10`, `d = 3`** (line 717).

Paper (verbatim): "the same failure occurs at $n=10$".

Delta: `d = 3`, `σ = 2`. Precise reading: the even `n = 10` is not a
local maximum, under both readings (`¬ strict ∧ ¬ non-strict`, as in part
(d); repair round 2 added the non-strict conjunct).
PAPER ISSUE (ambiguity, minor): "the same failure" cannot mean a prime
failing to be a local minimum — the neighbours of 10 are 9 (composite) and
11, and 11 IS a local minimum at `d = 3`. The failure at 10 is only the
"even `n` is not a local maximum" half, caused by `P(9³) > P(10³)`
(`log₁₀ P(9³) − log₁₀ P(10³) = 4.483…`; `P(11³) < P(10³)`). The paper
should say: "likewise the even $n=10$ is not a local maximum
($P(9^3)>P(10^3)$)". The frozen Prop is the claim "the even `n = 10` is not
a local maximum" (the parenthetical witness is the reason, not frozen; see
the review note at part (d)). The full audit (`n ≤ 24` at `d = 3`) finds
exactly the failures 5, 6, 10. Witness for the prover: `log₁₀ P(9³) =
−145.1866… > log₁₀ P(10³) = −149.6699…` (s11/check_s11_r2.py). -/
def extremaN10Statement : Prop :=
  ¬ IsLocalMaxAt (fun m => probUnif m 3 2) 10 ∧
    ¬ IsLocalMaxAtWeak (fun m => probUnif m 3 2) 10

/-- **Obs. 7.3, part (f): persistence at `d = 4`** (lines 717–718).

Paper (verbatim): "and persists at $d=4$."

Delta: `σ = 2`. Precise reading: all three failures recorded at `d = 3`
(prime 5 not a local minimum, 6 not a local maximum, 10 not a local
maximum) also hold at `d = 4`, each under both readings (`¬ strict ∧
¬ non-strict`, as in part (d); repair round 2 added the non-strict
conjuncts). (The audit `n ≤ 12` at `d = 4` finds exactly these three.)
Witnesses for the prover (not frozen, see the review note at part (d)):
`log₁₀ P(6⁴) = −193.891… < log₁₀ P(5⁴) = −148.322…` and
`log₁₀ P(10⁴) = −1503.974… < log₁₀ P(9⁴) = −1315.103…`
(s11/check_s11_r2.py). -/
def extremaD4Statement : Prop :=
  (¬ IsLocalMinAt (fun m => probUnif m 4 2) 5 ∧
      ¬ IsLocalMinAtWeak (fun m => probUnif m 4 2) 5) ∧
    (¬ IsLocalMaxAt (fun m => probUnif m 4 2) 6 ∧
      ¬ IsLocalMaxAtWeak (fun m => probUnif m 4 2) 6) ∧
    (¬ IsLocalMaxAt (fun m => probUnif m 4 2) 10 ∧
      ¬ IsLocalMaxAtWeak (fun m => probUnif m 4 2) 10)

/-- **Obs. 7.3, part (g): the pattern breaks for every `d ≥ 3`**
(title, lines 704–705, and lines 711–712).

Paper (verbatim): title "Extremal pattern in $n$: true for $d=2$, false
for $d\ge3$"; text "For $d\ge3$ the pattern \emph{breaks}".

Delta: `σ = 2` (the setting of the observation); "the pattern" is the one
of part (a) over the same range (`ExtremalPattern d 2`, and
`ExtremalPatternWeak d 2` for the non-strict reading); "breaks" = its
negation under BOTH readings (repair round 2 added the non-strict one,
which implies the strict one), for EVERY `d ≥ 3` (the title quantifies
over all `d ≥ 3`; the paper exhibits `d = 3, 4`). Negating the range-bounded pattern is the
stronger of the two readings (it implies the failure of the unbounded
"every prime ≥ 5 / every even > 4" pattern); it is true because
`P(5^d) > P(6^d)` for all `d ≥ 3` (the pair `(5,6)` lies past its
inversion point `d_c(5) ≈ 2.58`, Prop. 10.2(ii); checked exactly for
`3 ≤ d ≤ 12`, at 80 digits for `3 ≤ d ≤ 60`), which contradicts
"5 is a (non-strict) local minimum". -/
def extremaBreaksStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d → ¬ ExtremalPattern d 2 ∧ ¬ ExtremalPatternWeak d 2

/-- **Observation 7.3 (`obs:extrema`), all mathematical content.**

NON-MATHEMATICAL parts (not formalized): "confirms the pattern of
[banda2019, Figs. 6, 8]" (attribution); "See
Figure~\ref{fig:pattern-flip}" (pointer; compiled Figure 1 — its caption,
paper lines 726–736, lies outside this group's range and is formalized in
group 7, S07_Dynamics.lean; it restates parts (a), (b), (c), (d));
"These are exact computations, not asymptotic claims; we know of no proof
of either pattern as a theorem for general $n$." (epistemic remark).

PAPER ISSUE (misleading explanation, minor; repair round 3; paper lines
719–721): "The reason is the state-space effect: relative to lattices
with the same cell count, the composite's extra symmetric configurations
are exponentially outweighed once $d\ge3$." This heuristic names no precise comparison (the lattices
compared, `p^d` and `(p±1)^d`, do NOT have the same cell count, and
"exponentially outweighed" fixes no quantity), so it is not frozen as a
Prop of its own. Read as a statement about the composites of the pattern,
its threshold "once $d\ge3$" is false: at `d = 3`, `σ = 2`, every prime
`7 ≤ p ≤ 23` still has strictly smaller `P^unif` than both composite
neighbours `p ± 1` (`log₁₀` ratios from `10.53` for `(7, 8)` to `1898.8`
for `(23, 22)`), so those composites' extra symmetric configurations are
NOT outweighed at `d = 3` (machine-checkable: `inversionD3ScopeStatement`,
where only `(3, 4)` and `(5, 6)` are inverted). By Prop. 10.2 the pair
`(p, p+1)` inverts only near `d_c(p) = p ln 2 + O(1)`, a dimension growing
linearly in `p`; in exact data (`σ = 2`) the composite advantage of
`(7, 8)`, `(11, 12)`, `(13, 14)` lasts up to `d = 4, 6, 8 = ⌊d_c(p)⌋`
(`measuredRowStatement` with the bracket `⌊x⌋ = ⌊d_c(p)⌋` of
`measuredGapCauseStatement`). The pattern breaks at `d = 3` through the
smallest prime–even pair `(5, 6)` (`d_c(5) ≈ 2.58 < 3`; this pair alone
breaks it at every `d ≥ 3`, `extremaBreaksStatement`) and the composite
pair `(9, 10)` (part (e)), not through a general loss of the composite
advantage. The paper should say: "The reason is the state-space effect of
Proposition~\ref{prop:inversion}: for each prime--even pair $(p,p+1)$ the
composite's extra symmetric configurations are outweighed by its larger
cell count once $d$ exceeds $d_c(p)\approx p\ln2$; at $d=3$ this has
already happened for the smallest pair $(5,6)$ ($d_c(5)\approx2.58$),
which suffices to break the pattern, while the pairs with $p\ge7$ still
show the composite advantage." Numbers: s11/check_s11_r3.py, part (B).
(Raised as optional by the round-3 exploit reviewer.) -/
def obsExtremaStatement : Prop :=
  extremaD2Statement ∧ extremaBoundaryStatement ∧ extremaD3ValuesStatement ∧
    extremaD3FailStatement ∧ extremaN10Statement ∧ extremaD4Statement ∧
    extremaBreaksStatement

/-! ## Remark 10.3 (`rem:dc-measured`, paper lines 968–988) -/

/-- The predicted inversion dimension of Prop. 10.2,
`d_c(p) = ln(2 − 2/p) / ln(1 + 1/p)` (paper line 948), literally, in `ℝ`.
(Evaluated at `p ∈ {3, 5, 7, 11, 13}` and, in the asymptotic Props, at all
large primes; for every `p ≥ 3` both logarithms are of numbers `> 1`. The
value at `p = 2` (`ln 1 / ln(3/2) = 0`) only enters statements with an
existential threshold `P₀` or a limit, where it is irrelevant.) -/
noncomputable def dc (p : ℕ) : ℝ :=
  Real.log (2 - 2 / (p : ℝ)) / Real.log (1 + 1 / (p : ℝ))

/-- `log₁₀ [P^unif_{(p+1)^d} / P^unif_{p^d}]` at alphabet size `σ`, the
quantity whose sign change Remark 10.3 measures. -/
noncomputable def inversionLogRatio (σ p d : ℕ) : ℝ :=
  Real.logb 10 (probUnif (p + 1) d σ / probUnif p d σ)

/-- "`x` is the interpolated sign change of `f` (on `d ≥ 1`)": with `d₀`
the last dimension before the FIRST negative value (`f ≥ 0` on
`1 ≤ d ≤ d₀`, `f (d₀+1) < 0`), `x` is the zero of the straight line
through `(d₀, f d₀)` and `(d₀+1, f (d₀+1))`:
`x = d₀ + f d₀ / (f d₀ − f (d₀+1))`. `d₀` (hence `x`) is unique when it
exists. An exact zero at `d₀` gives `x = d₀` (the `p = 3` case). This is
the procedure of compute_dimension_insights.py (`crossing`, chart 15). -/
def IsInterpolatedSignChange (f : ℕ → ℝ) (x : ℝ) : Prop :=
  ∃ d₀ : ℕ, 1 ≤ d₀ ∧ (∀ d : ℕ, 1 ≤ d → d ≤ d₀ → 0 ≤ f d) ∧
    f (d₀ + 1) < 0 ∧ x = (d₀ : ℝ) + f d₀ / (f d₀ - f (d₀ + 1))

/-- **Rem. 10.3, the `d_c(p)` row** (lines 974, 977).

Paper (verbatim): table row "$d_c(p)$ & $1.00$ & $2.58$ & $4.04$ &
$6.87$ & $8.27$" under "$p$ & 3 & 5 & 7 & 11 & 13".

Delta: two-decimal roundings ↦ closed intervals of half-width `0.005`;
`d_c` is the paper's closed form (`dc`). Exact values: `d_c(3) = 1`
(`ln(4/3)/ln(4/3)`), `2.577883`, `4.036478`, `6.870791`, `8.273124`. -/
def dcRowStatement : Prop :=
  |dc 3 - 1.00| ≤ 0.005 ∧ |dc 5 - 2.58| ≤ 0.005 ∧ |dc 7 - 4.04| ≤ 0.005 ∧
    |dc 11 - 6.87| ≤ 0.005 ∧ |dc 13 - 8.27| ≤ 0.005

/-- One entry of the "measured" row: at `σ = 2` the interpolated sign
change of `d ↦ log₁₀[P_{(p+1)^d}/P_{p^d}]` exists and rounds to `m`
(two decimals). -/
def MeasuredEntry (p : ℕ) (m : ℝ) : Prop :=
  ∃ x : ℝ, IsInterpolatedSignChange (inversionLogRatio 2 p) x ∧
    |x - m| ≤ 0.005

/-- **Rem. 10.3, the "measured" row** (lines 969–976).

Paper (verbatim): "Interpolated sign changes of
$\log_{10}[P_{(p+1)^d}/P_{p^d}]$ in exact data ($\sigma=2$) against
$d_c(p)$:" and the row "measured & $1.00$ & $2.10$ & $4.00$ & $6.37$ &
$8.03$" for $p$ = 3, 5, 7, 11, 13.

Delta: `σ = 2`; `P_{m^d} = probUnif m d 2`; "interpolated sign change" is
`IsInterpolatedSignChange` (linear interpolation between the consecutive
integer dimensions bracketing the first sign change, `d ≥ 1`); roundings ↦
half-width `0.005`. Exact values (60-digit evaluator):
`1` (exact zero `f(1) = 0`, `d₀ = 1`), `2.098107` (`d₀ = 2`),
`4.002645` (`d₀ = 4`), `6.369733` (`d₀ = 6`), `8.027095` (`d₀ = 8`); each
`f` has exactly one sign change on `1 ≤ d ≤ 13`.
PAPER ISSUE (minor, ambiguity): "interpolated" is not specified; the
paper should say "linearly interpolated zero of
$d\mapsto\log_{10}[P_{(p+1)^d}/P_{p^d}]$ between the consecutive integer
dimensions at its first sign change". We freeze that reading (it is the
one that reproduces all five entries).
Note: the entries for `p = 11, 13` involve lattices with up to `14⁹`
cells; they are finite statements but not kernel-computable by brute
evaluation — a proof needs two-sided bounds of `|S|`. -/
def measuredRowStatement : Prop :=
  MeasuredEntry 3 1.00 ∧ MeasuredEntry 5 2.10 ∧ MeasuredEntry 7 4.00 ∧
    MeasuredEntry 11 6.37 ∧ MeasuredEntry 13 8.03

/-- **Rem. 10.3, "at or below"** (lines 981–982).

Paper (verbatim): "Measured values sit at or slightly below $d_c$
because the coefficient corrections in Proposition~\ref{prop:rate} favor
the prime side."

Delta: the precise content of "sit at or below" is `measured(p) ≤ d_c(p)`
for the five tabulated primes, for the EXACT (unrounded) quantities;
equality occurs at `p = 3` (both are `1`). NON-MATHEMATICAL: "slightly"
(vague; the exact gaps are `0, 0.480, 0.034, 0.501, 0.246`, i.e. half a
dimension at `p = 5, 11`). The premise "the coefficient corrections …
favor the prime side" is frozen separately and is true
(`coefficientsFavorPrimeStatement`).
PAPER ISSUE (false causal attribution; repair round 3, exploit reviewer):
the gap `d_c(p) − measured(p)` is NOT (mainly) caused by the coefficient
corrections; it is an artefact of the linear interpolation itself. Write
`x(p)` for the measured value and `y(p)` for the interpolated sign change,
by the same procedure, of the bare exponent
`φ(d) = (1 − 1/p)p^d − (p+1)^d/2` of Prop. 10.2 (`phiInv`; no coefficients
at all — `d_c(p)` is the exact real zero of `φ`). Exactly,
`y(p) = 11/5, 3981/994, 1012195/158906, 1117456751/139210604`
`= 2.2, 4.005030, 6.369772, 8.0270951` for `p = 5, 7, 11, 13`, already
below `d_c(p) = 2.577883, 4.036478, 6.870791, 8.273124`: the chord through
`(⌊d_c⌋, φ(⌊d_c⌋))` and `(⌊d_c⌋+1, φ(⌊d_c⌋+1))` crosses zero before `φ`
does (`φ` bends downward across its zero: `φ'' < 0` on `[d_c, ∞)`; `φ` is
concave on the whole bracket except on `[6, 6.052]` at `p = 11`, and the
chord is negative at `d_c` for all four). The coefficient corrections
(everything in `log P` beyond the exponents) move `x` below `y` only by
`y − x = 0.1019, 0.0024, 3.9·10⁻⁵, 3.2·10⁻⁸`, i.e. `21%, 7%, 0.008%,
0.00001%` of the gap `d_c − x`; the interpolation accounts for the rest
(`79%, 93%, 99.99%, ≈100%`). They do not even move the bracketing integer
dimensions: `⌊x⌋ = ⌊y⌋ = ⌊d_c(p)⌋ = 2, 4, 6, 8`. And as `σ → ∞`, where the
coefficient corrections vanish in `log_σ` units, the measured value
increases to `y(p)` but stays below `d_c(p)` (e.g. `σ = 10^6`: `2.1939,
4.0049, 6.369770, 8.0270951`; `σ = 10^300`: `2.19988, 4.0050278, …`).
Machine-checkable evidence (at `σ = 2`): `measuredGapCauseStatement`.
Moreover, the direction "favor the prime side" does not follow from
Prop. 10.1 (`\ref{prop:rate}`), whose bounds
`σ^{N/p₁} ≤ |S| ≤ 2 log₂(n) n^{d−1} σ^{N/p₁}` are two-sided on BOTH sides of
the comparison; it comes from the exact leading coefficients of Theorem 4.3
(`[d 1]_p` order-`p` subgroups on the prime side against `2^d − 1` order-2
subgroups on the even side). The paper should say: "Measured values sit at
or below $d_c$: linear interpolation between the integer dimensions
$\lfloor d_c\rfloor$ and $\lfloor d_c\rfloor+1$ underestimates the zero
of $\varphi$ (by $0.38$, $0.03$, $0.50$, $0.25$ for $p=5,7,11,13$), and the
coefficient corrections of Theorem~\ref{thm:main-enum}, which favor the
prime side (leading coefficients $\gaussbinom d1_p$ against $2^d-1$), lower
it only slightly further." Numbers: s11/check_s11_r3.py, parts (A), (A*),
(A'), (A''). (The Prop below is unchanged; only its classification of the
causal clause changed, from NON-MATHEMATICAL to this PAPER ISSUE.) -/
def measuredAtOrBelowStatement : Prop :=
  ∀ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
    ∃ x : ℝ, IsInterpolatedSignChange (inversionLogRatio 2 p) x ∧ x ≤ dc p

/-- The exponent function `φ(d) = (1 − 1/p)·p^d − ½(p+1)^d` of Prop. 10.2
(`prop:inversion`, paper line 936), literally, in `ℝ`: the base-`σ`
log-ratio `log_σ[P_{(p+1)^d}/P_{p^d}]` with all coefficient corrections
dropped (exponent `−p^d(1 − 1/p)` on the prime side, `−(p+1)^d/2` on the
even side). Its real zero is `d_c(p)` (Prop. 10.2). -/
noncomputable def phiInv (p d : ℕ) : ℝ :=
  (1 - 1 / (p : ℝ)) * (p : ℝ) ^ d - ((p : ℝ) + 1) ^ d / 2

/-- **Rem. 10.3, the premise "the coefficient corrections … favor the prime
side"** (lines 981–982).

Paper (verbatim): "Measured values sit at or slightly below $d_c$
because the coefficient corrections in Proposition~\ref{prop:rate} favor
the prime side."

Delta: only the premise "the coefficient corrections … favor the prime
side" is frozen here ("at or below" is `measuredAtOrBelowStatement`; the
causal "because" is false — PAPER ISSUE there). Precise reading, in the
context of the table (`σ = 2`, the five tabulated primes): the "coefficient
corrections" are everything in `log P^unif` beyond the bare exponents
(`log_σ P_{n^d} = −N(1 − 1/p₁) + log_σ(|S_{n^d}|/σ^{N/p₁})`, the second
summand being what Prop. 10.1 bounds), and "favor the prime side" means
that including them moves the interpolated sign change of
`log[P_{(p+1)^d}/P_{p^d}]` toward the prime side, i.e. to a dimension no
larger than the one of the bare exponents: `x(p) ≤ y(p)`, where `x(p)` is
the measured value (data `inversionLogRatio 2 p`) and `y(p)` the
interpolated sign change of `φ` (`phiInv p`), both by the same procedure
`IsInterpolatedSignChange`. That procedure is invariant under positive
rescaling of the data, so comparing `log₁₀` data with the exponent `φ`
(in `log₂` units at `σ = 2`) is consistent. Strict for `p ≥ 5`
(`y − x = 0.1019, 0.0024, 3.9·10⁻⁵, 3.2·10⁻⁸`); at `p = 3` the measured
zero is exact and there is nothing to move: `x = y = 1` (at `d = 1`,
`|S_3| = σ` and `|S_4| = σ²` are pure powers). Checked also pointwise (not
frozen): the coefficient part of the base-2 log-ratio is negative at every
`2 ≤ d ≤ 14` for all five primes (so at both bracketing dimensions), and
`≥ 0` at `d = 1` (it vanishes for `p = 3, 7`, where `p + 1` is a power of
2) (s11/check_s11_r3.py, part (A*)).
PAPER ISSUE: see `measuredAtOrBelowStatement` (the premise is true but is
not the reason for the gap; and its direction comes from the exact leading
coefficients of Theorem 4.3, not from Prop. 10.1).
Repair round 3: added together with that PAPER ISSUE. -/
def coefficientsFavorPrimeStatement : Prop :=
  ∀ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), ∃ x y : ℝ,
    IsInterpolatedSignChange (inversionLogRatio 2 p) x ∧
      IsInterpolatedSignChange (phiInv p) y ∧ x ≤ y ∧ (5 ≤ p → x < y)

/-- **Rem. 10.3, the exact boundary case at `p = 3`** (lines 982–985).

Paper (verbatim): "At $p=3$ the boundary case is exact and
alphabet-independent: $P^{\mathrm{unif}}_{3}=P^{\mathrm{unif}}_{4}=
\sigma^{-2}$ at $d=1$, since $|S_3|=\sigma$ and $|S_4|=\sigma^2$."

Delta: `d = 1`; the counts are stated for every `σ ≥ 1` (paper convention:
counting statements allow `σ = 1`), the probabilities for every `σ ≥ 2`
(paper convention for probabilities; they also hold at `σ = 1`);
`σ^{-2}` is `((σ : ℝ)^2)⁻¹`.
"The boundary case is exact" is the equality case of the preceding sentence
("Measured values sit AT or slightly below $d_c$"): for `p = 3` the measured
inversion point EQUALS `d_c(3)`, both exactly `1`. Frozen as: `dc 3 = 1`
EXACTLY (`ln(2 − 2/3) = ln(1 + 1/3)`; `dcRowStatement` only has the rounded
table entry), `log₁₀[P_4/P_3] = 0` at `d = 1`, and the interpolated sign
change of the `p = 3` row is exactly `1`
(`IsInterpolatedSignChange (inversionLogRatio σ 3) 1`).
"Alphabet-independent" is frozen by quantifying the last two over EVERY
`σ ≥ 2` (the table itself is at `σ = 2` only). For the interpolated sign
change this needs, besides the paper's `d = 1` reason (`P_3 = P_4`), that
the ratio is negative at `d = 2` for every `σ`: `P(4²) < P(3²)` ⇔
`(3σ⁸ − 2σ⁴)/σ¹⁶ < (4σ³ − 3σ)/σ⁹` ⇔ `4σ¹⁰ − 6σ⁸ + 2σ⁴ > 0`, true for all
`σ ≥ 2` (checked exactly for `σ = 2..100`, s11/check_s11_r1.py).
Repair round 1: the exact `dc 3 = 1` and the all-`σ` sign change were
missing in the first freeze (exploit reviewer); added. -/
def boundaryCaseStatement : Prop :=
  (∀ σ : ℕ, 1 ≤ σ → numSS 3 1 σ = σ ∧ numSS 4 1 σ = σ ^ 2) ∧
    (∀ σ : ℕ, 2 ≤ σ →
      probUnif 3 1 σ = ((σ : ℝ) ^ 2)⁻¹ ∧ probUnif 4 1 σ = ((σ : ℝ) ^ 2)⁻¹ ∧
        inversionLogRatio σ 3 1 = 0) ∧
    dc 3 = 1 ∧
    (∀ σ : ℕ, 2 ≤ σ → IsInterpolatedSignChange (inversionLogRatio σ 3) 1)

/-- **Figure 3 caption (`fig:inversion`, cited by Rem. 10.3; image
chart15_inversion_dimension.png, whence the name): every tabulated pair
flips sign once** (paper lines 993–997).

Paper (verbatim): "The inversion law (Proposition~\ref{prop:inversion},
Remark~\ref{rem:dc-measured}; $\sigma=2$, exact arithmetic). Left: the
ratio $\log_{10}\bigl[P^{\mathrm{unif}}_{(p+1)^d}/P^{\mathrm{unif}}_{p^d}
\bigr]$ for the prime--even pairs $(p,p{+}1)$, $p\in\{3,5,7,11,13\}$,
flips sign at a pair-dependent inversion dimension".

Delta: `σ = 2` (caption); "flips sign at an inversion dimension" = there is
`d₀ ≥ 1` with the ratio `≥ 0` on `1 ≤ d ≤ d₀` and `< 0` for EVERY `d > d₀`
(one permanent `+ → −` change; in the checked range `d ≤ 30` the value
`0` occurs only at `(p, d) = (3, 1)`). The figure plots `d ≤ 12` (`p ≤ 7`) and `d ≤ 11`
(`p = 11, 13`); the flip is frozen for ALL `d ≥ 1`, the reading under which
"inversion dimension" is well defined (a curve that changed sign again
would have no single inversion dimension, and `IsInterpolatedSignChange`
looks only at the first change); the plotted-range statement is a
consequence. "Pair-dependent" adds nothing beyond the distinct entries of
`measuredRowStatement` (`d₀ = 1, 2, 4, 6, 8`). Checked exactly / at 80
digits for `d ≤ 30`; for all `d` it follows from
`inversionDeepensStatement` (Obs. 10.5) plus the first values.
Repair round 1: added (literal reviewer, optional item). -/
def fig15SignFlipStatement : Prop :=
  ∀ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ), ∃ d₀ : ℕ, 1 ≤ d₀ ∧
    (∀ d : ℕ, 1 ≤ d → d ≤ d₀ → 0 ≤ inversionLogRatio 2 p d) ∧
    (∀ d : ℕ, d₀ < d → inversionLogRatio 2 p d < 0)

/-- The line `p ↦ a·p + b` is a linear (oblique) asymptote of `f` as
`p → ∞` through the primes: `f p − (a·p + b) → 0`, in explicit quantifier
form. (The standard meaning of "linear asymptote".) -/
def IsLinearAsymptotePrimes (f : ℕ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p →
    |f p - (a * (p : ℝ) + b)| ≤ ε

/-- **Figure 3 caption (`fig:inversion`, cited by Rem. 10.3), right panel:
the line `p ln 2`** (paper lines 998–1000).

Paper (verbatim): "Right: the measured inversion dimensions against the
prediction $d_c(p)=\ln(2-2/p)/\ln(1+1/p)$ and its linear asymptote
$p\ln2$."

Delta: `d_c` is `dc` (the paper's closed form, in `ℝ`); `p → ∞` through
the primes (the domain of Prop. 10.2, "Let $p\ge3$ be prime"; the same
statements over all `p ∈ ℕ` are also true and imply these); the limit and
the `O(1)` in explicit quantifier form (`∀ ε > 0, ∃ P₀, …`;
`∃ C, ∃ P₀, …`); in `dc p / p` the prime `p ≥ 2` is nonzero, so no
`x / 0` junk.
PAPER ISSUE (false as written): in its standard meaning, "the linear
asymptote of `d_c` is the line `p ln 2`" says `d_c(p) − p ln 2 → 0`, i.e.
`IsLinearAsymptotePrimes dc (Real.log 2) 0`. That is false. Expanding both
logarithms in `x = 1/p`:
`d_c(p) = p ln 2 + (ln 2/2 − 1) − 1.05776…/p + O(p⁻²)` (Taylor
coefficients of `x·d_c(1/x)`: `ln 2`, `ln 2/2 − 1`, `−1.05776…`), so the
offset `d_c(p) − p ln 2` tends to `ln 2/2 − 1 = −0.6534264…`, not to `0`.
Over the primes `3 ≤ p < 20000` it increases strictly, from `−1.0794`
(`p = 3`) via `−0.7378` (`p = 13`) and `−0.66395` (`p = 101`), staying
below the limit, so `|d_c(p) − p ln 2| > 0.65` at every prime checked (all
primes `3 ≤ p < 20000`, and `p ≈ 10^6, 10^9, 10^15, 10^30`;
s11/check_s11_r2.py). The dotted line of the right panel
(compute_dimension_insights.py, `ps * math.log(2)` for `3 ≤ p ≤ 14`, legend
"asymptote d_c ≈ p ln 2") accordingly runs 0.73–1.08 above the `d_c`
curve over the plotted range. The line `p ln 2` is only the asymptotic SLOPE (`d_c(p) ∼ p ln 2`),
equivalently Prop. 10.2's `d_c(p) = p ln 2 + O(1)`; the true linear
asymptote is `p ln 2 + ln 2/2 − 1`. Machine-checkable evidence:
`dcOffsetLimitStatement`. The paper should say "… and the line $p\ln2$
($d_c(p)=p\ln2+O(1)$; the exact linear asymptote is
$p\ln2+\tfrac12\ln2-1$)" or "… and its asymptotic slope $\ln2$
($d_c(p)\sim p\ln2$)".
Frozen (intended reading): the two properties the plotted line `p ln 2`
does have — the slope, `d_c(p)/p → ln 2`, and the bounded offset,
`d_c(p) − p ln 2 = O(1)`. (The second implies the first; both are listed
because "asymptote" most directly names the slope, while the caption cites
Prop. 10.2, whose display is the `O(1)` form. The `O(1)` part is also
frozen in group 9 as `dcAsymptoticStatement`; it is restated here so that
this file does not depend on S09.)
Repair round 2: this clause was previously dismissed as a plot description
(both fidelity reviewers); now frozen, with the PAPER ISSUE and evidence. -/
def figInversionAsymptoteStatement : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p →
      |dc p / (p : ℝ) - Real.log 2| ≤ ε) ∧
    (∃ C : ℝ, ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p →
      |dc p - (p : ℝ) * Real.log 2| ≤ C)

/-- **Remark 10.3 (`rem:dc-measured`), all mathematical content.**

Includes the two mathematical claims of the Figure 3 caption
(`fig:inversion`, lines 990–1002) that the remark cites: the sign flips
(`fig15SignFlipStatement`) and the line `p ln 2` of the right panel
(`figInversionAsymptoteStatement`, intended reading; the literal "linear
asymptote $p\ln2$" is false — PAPER ISSUE there, evidence
`dcOffsetLimitStatement`).
The sentence "Measured values sit at or slightly below $d_c$ because the
coefficient corrections in Proposition~\ref{prop:rate} favor the prime
side" is split: "at or below" is `measuredAtOrBelowStatement`; the premise
is `coefficientsFavorPrimeStatement` (true); the causal "because" is a
false attribution — PAPER ISSUE at `measuredAtOrBelowStatement`, evidence
`measuredGapCauseStatement` (repair round 3; it was previously classed as
a non-mathematical explanation).
NON-MATHEMATICAL parts: "slightly" (vague); "Figure~\ref{fig:inversion} displays both the sign
flips and the measured-versus-predicted inversion dimensions" (pointer;
compiled Figure 3); in the caption, "(Proposition~\ref{prop:inversion},
Remark~\ref{rem:dc-measured}; $\sigma=2$, exact arithmetic)" (provenance;
`σ = 2` is used in the frozen Props), "symlog scale; dotted verticals mark
the interpolated zeros" (plot description; the zeros are those of
`measuredRowStatement`) and "the measured inversion dimensions against the
prediction $d_c(p)=…$" (plot description; the plotted values are those of
`measuredRowStatement` and `dcRowStatement`); "The remaining items are
empirical." (line 1004) is a classification, not a claim.
Repair round 2: `figInversionAsymptoteStatement` added (it was wrongly
dismissed as a plot description); figure numbers corrected (the caption is
the paper's Figure 3, not "Figure 15"). -/
def remDcMeasuredStatement : Prop :=
  dcRowStatement ∧ measuredRowStatement ∧ measuredAtOrBelowStatement ∧
    coefficientsFavorPrimeStatement ∧ boundaryCaseStatement ∧
    fig15SignFlipStatement ∧ figInversionAsymptoteStatement

/-- **PAPER ISSUE evidence for the Figure 3 caption (not a paper claim).**
The linear asymptote of `d_c` (as `p → ∞` through the primes) is the line
`p ln 2 + (ln 2/2 − 1)`, and the line `p ln 2` that the caption calls "its
linear asymptote" is NOT a linear asymptote of `d_c`. (The second conjunct
follows from the first by uniqueness of limits, because
`ln 2/2 − 1 ≠ 0`; it is stated so that the refutation of the literal
caption is explicit.) Numbers: s11/check_s11_r2.py. -/
def dcOffsetLimitStatement : Prop :=
  IsLinearAsymptotePrimes dc (Real.log 2) (Real.log 2 / 2 - 1) ∧
    ¬ IsLinearAsymptotePrimes dc (Real.log 2) 0

/-- **PAPER ISSUE evidence for Rem. 10.3 (not a paper claim).** At `σ = 2`,
for `p ∈ {5, 7, 11, 13}`, with `x` the measured value and `y` the
interpolated sign change of the bare exponent `φ` (`phiInv`, no
coefficients): `y` already lies strictly below `d_c(p)`; `x` and `y` have
the integer bracket of `d_c(p)` (`⌊x⌋ = ⌊y⌋ = ⌊d_c(p)⌋ = 2, 4, 6, 8`, so the
first negative dimension is `⌊d_c(p)⌋ + 1` in both); and the coefficient
corrections, `y − x`, account for at most a quarter of the gap
`d_c(p) − x` (at most a thousandth of it for `p = 11, 13`). Hence the gap
is mainly an interpolation artefact, contrary to the paper's "because the
coefficient corrections … favor the prime side". Exact `y`: `11/5`,
`3981/994`, `1012195/158906`, `1117456751/139210604`; shares of the gap
due to the coefficients `21.2%, 7.0%, 0.0078%, 0.000013%`
(s11/check_s11_r3.py). Repair round 3 (exploit reviewer). -/
def measuredGapCauseStatement : Prop :=
  ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ), ∃ x y : ℝ,
    IsInterpolatedSignChange (inversionLogRatio 2 p) x ∧
      IsInterpolatedSignChange (phiInv p) y ∧
      ⌊x⌋ = ⌊dc p⌋ ∧ ⌊y⌋ = ⌊dc p⌋ ∧ y < dc p ∧
      4 * (y - x) ≤ dc p - x ∧ (11 ≤ p → 1000 * (y - x) ≤ dc p - x)

/-! ## Observation 10.4 (`obs:dstar`, paper lines 1006–1018) -/

/-- The `r`-th summand `T_r` of Corollary 4.4 for prime `n = p`:
`T_r = (−1)^{r+1} p^{C(r,2)} [d r]_p σ^{p^{d−r}}`, literally, in `ℝ`.
(For `r > d` the Gaussian binomial vanishes, so `T_r = 0`; the truncated
`ℕ`-exponent `d − r` is then irrelevant.) -/
noncomputable def primeTerm (p d σ r : ℕ) : ℝ :=
  (-1 : ℝ) ^ (r + 1) * (p : ℝ) ^ (r.choose 2) * (gaussBinom p d r : ℝ) *
    (σ : ℝ) ^ (p ^ (d - r))

/-- `|T₂/T₁|`, the relative size of the second term of Corollary 4.4. -/
noncomputable def t2t1 (p d σ : ℕ) : ℝ :=
  |primeTerm p d σ 2 / primeTerm p d σ 1|

/-- The set whose least element is `d*(p; θ)` in the intended reading:
dimensions `d ≥ 2` with `|T₂/T₁| < θ`. -/
def dStarSet (p : ℕ) (θ : ℝ) (σ : ℕ) : Set ℕ :=
  {d | 2 ≤ d ∧ t2t1 p d σ < θ}

/-- **Obs. 10.4, the displayed closed form of `|T₂/T₁|`** (lines
1009–1011).

Paper (verbatim): "$|T_2/T_1| = p\gaussbinom d2_p\gaussbinom d1_p^{-1}
\sigma^{-p^{d-2}(p-1)}$".

Delta: stated for prime `p`, `σ ≥ 2` (paper convention), and `d ≥ 2`
only: at `d = 1` the exponent `p^{d−2}(p−1) = (p−1)/p` is not an integer
and there is no second term (see the PAPER ISSUE at `dstarClaimStatement`);
the negative power is the integer power `σ ^ (−k : ℤ)` with
`k = p^{d−2}(p−1) ∈ ℕ` (`d − 2`, `p − 1` are true differences here). -/
def t2t1FormulaStatement : Prop :=
  ∀ p d σ : ℕ, p.Prime → 2 ≤ d → 2 ≤ σ →
    t2t1 p d σ =
      (p : ℝ) * (gaussBinom p d 2 : ℝ) / (gaussBinom p d 1 : ℝ) *
        (σ : ℝ) ^ (-((p ^ (d - 2) * (p - 1) : ℕ) : ℤ))

/-- **Obs. 10.4, the computed claim** (lines 1006–1012).

Paper (verbatim): "For prime $n=p$, define $d^*(p;\theta)$ as the least
$d$ at which the second term of Corollary~\ref{cor:prime} falls below a
fraction $\theta$ of the first, i.e.\ $|T_2/T_1|<\theta$ […]. Computing
$d^*$ for all 95 primes up to 499 ($\sigma=2$): only $p\in\{2,3,5\}$ have
$d^*>2$ at $\theta=0.05$".

Delta: `σ = 2`, `θ = 0.05`; "the 95 primes up to 499" is recorded as the
count `#{p ≤ 499 prime} = 95` plus the claim for every prime `p ≤ 499`;
`d*(p; θ)` is the least element of `dStarSet p θ 2` (asserted to exist);
"only `p ∈ {2,3,5}` have `d* > 2`" is the biconditional
`2 < d* ↔ p ∈ {2,3,5}` (the computation also confirms that these three
DO have `d* > 2`: `d* = 5, 3, 3`).
PAPER ISSUE (ill-posed at `d = 1`): read literally ("the least `d`", with
`d ≥ 1` the paper's standing range), `d = 1` always qualifies — Corollary
4.4 has no second term at `d = 1` (`[1 2]_p = 0`, so `T₂ = 0` and
`|T₂/T₁| = 0 < θ`) — hence `d*(p; θ) = 1` for every prime and every
`θ > 0`, and the claim "only `p ∈ {2,3,5}` have `d* > 2`" would be false
for `p = 2, 3, 5` (no prime would have `d* > 2`). See
`dstarLiteralDegenerateStatement`, which records this as a Prop. The
displayed formula's exponent `p^{d−2}(p−1)` is also non-integral at
`d = 1`. Intended reading (and the one used by compute_C_exploration.py,
which starts at `d = 2` "since at d = 1 there is only T_1"): the least
`d ≥ 2`. The paper should say "the least $d\ge2$". Frozen: that reading.
-/
def dstarClaimStatement : Prop :=
  ((Finset.Iic 499).filter Nat.Prime).card = 95 ∧
    ∀ p : ℕ, p.Prime → p ≤ 499 →
      ∃ D : ℕ, IsLeast (dStarSet p 0.05 2) D ∧ (2 < D ↔ p = 2 ∨ p = 3 ∨ p = 5)

/-- The primes `p ≤ 499` that are "unclamped" at threshold `θ` (`σ = 2`):
`d*(p; θ)` — the least element of `dStarSet p θ 2`, i.e. the least `d ≥ 2`
with `|T₂/T₁| < θ` — exists and exceeds `2` (is not clamped at its floor
`d = 2`). The set is contained in `[0, 499]`, hence finite, so `Set.ncard`
is its true cardinality. -/
def unclampedPrimes (θ : ℝ) : Set ℕ :=
  {p | p.Prime ∧ p ≤ 499 ∧ ∃ D : ℕ, IsLeast (dStarSet p θ 2) D ∧ 2 < D}

/-- **Obs. 10.4, "only three unclamped data points"** (lines 1012–1016).

Paper (verbatim): "a fit $d^*\approx1+C/\ln p$ gives $C\approx2.2$--$2.65$
depending on $\theta$ (about $2.5\pm0.3$), but with only three unclamped
data points and systematic residuals this is an indicative,
threshold-dependent summary".

Delta: an "unclamped data point" is a prime `p ≤ 499` with `d*(p; θ) > 2`
(all other primes sit at the floor `d* = 2` and carry no information about
`C`), `d*` as in `dstarClaimStatement` (least `d ≥ 2`); `σ = 2`; threshold
`θ = 0.05`, the only threshold the paper names (and the one of the
preceding clause, whose three primes `{2, 3, 5}` these are). The count is
`Set.ncard` of `unclampedPrimes 0.05` (a finite set).
PAPER ISSUE (the count depends on `θ`; the fit is not reproducible from the
paper's definition): (i) with the paper's integer `d*` the unclamped primes
are `{2,3,5,7}`, `{2,3,5}`, `{2,3}` at `θ = 0.01, 0.05, 0.10` (counts
4 / 3 / 2; `dstarUnclampedByThetaStatement`), so "three" is right only at
`θ = 0.05`, although the sentence speaks of fits "depending on $\theta$".
(ii) The range "$C\approx2.2$--$2.65$" is not reproduced by the fit that
the model $d^*\approx1+C/\ln p$ prescribes for the integer `d*` the paper
defines: least squares through the origin of `d* − 1` against `1/ln p` on
the unclamped points gives `C = 3.431 / 2.680 / 2.609` at
`θ = 0.01 / 0.05 / 0.10`. Other estimators, which the paper does not name,
give `3.38–3.47` at `θ = 0.01`, `2.60–2.77` at `θ = 0.05` and `2.47–3.76`
at `θ = 0.10` (per-point mean, median and geometric mean of
`(d* − 1) ln p`, and the slope of a fit with free intercept;
s11/check_s11_r2.py): some single values fall inside `2.2–2.65`, but at
`θ = 0.01` every one exceeds `3.3`, and none reproduces the quoted
per-`θ` values. (Repair round 2: the earlier wording "cannot be obtained
from the integer `d*`" overclaimed — only the through-origin fit had been
checked.) The quoted values (`2.654 / 2.533 / 2.206`)
come from compute_C_exploration.py, which fits a log-linearly interpolated
FRACTIONAL `d*` (never defined in the paper) with the clamp mask
`d* > 2.01`, leaving 4 / 2 / 2 points (at `θ = 0.05` the fractional
`d*(5) = 2.0044` is clamped) — so no fit behind the quoted range has three
points. The paper should either define the fractional `d*` (log-linear
interpolation of `|T₂/T₁|` between consecutive integer `d`) and give the
per-`θ` point counts (4 / 2 / 2), or report the integer-`d*` fits
(`C ≈ 2.6–3.4`, counts 4 / 3 / 2). Numbers: s11/check_s11_r1.py.
Frozen: the `θ = 0.05` count under the paper's own definition (true).
Repair round 1: this clause was previously classed NON-MATHEMATICAL
(exploit reviewer); now frozen, with the PAPER ISSUE recorded. -/
def dstarUnclampedStatement : Prop :=
  (unclampedPrimes 0.05).ncard = 3

/-- **Observation 10.4 (`obs:dstar`), all mathematical content.**

NON-MATHEMATICAL parts: the fitted constant ("a fit $d^*\approx1+C/\ln p$
gives $C\approx2.2$--$2.65$ depending on $\theta$ (about $2.5\pm0.3$)
… systematic residuals … an indicative, threshold-dependent summary, not
an estimate of a universal constant") — a statistical summary whose
estimator and `θ` grid the paper does not specify (and which, see the
PAPER ISSUE at `dstarUnclampedStatement`, uses a fractional `d*` the paper
never defines); "The driver is the doubly-exponential suppression
$\sigma^{-p^{d-2}(p-1)}$." (explanation). The point count "only three
unclamped data points" IS frozen (`dstarUnclampedStatement`). -/
def obsDstarStatement : Prop :=
  t2t1FormulaStatement ∧ dstarClaimStatement ∧ dstarUnclampedStatement

/-- **PAPER ISSUE evidence for Obs. 10.4 (not a paper claim).** Under the
literal reading ("least `d ≥ 1` with `|T₂/T₁| < θ`") the crossover
dimension is `1` for every prime `p`, every `σ ≥ 2` and every `θ > 0`,
because `T₂ = 0` at `d = 1`. Recorded so that the ill-posedness is itself
machine-checkable. -/
def dstarLiteralDegenerateStatement : Prop :=
  ∀ p σ : ℕ, p.Prime → 2 ≤ σ → ∀ θ : ℝ, 0 < θ →
    IsLeast {d : ℕ | 1 ≤ d ∧ t2t1 p d σ < θ} 1

/-- **PAPER ISSUE evidence for Obs. 10.4 (not a paper claim).** The set of
unclamped primes depends on the threshold: `{2,3,5,7}` at `θ = 0.01`
(`d* = 6, 4, 3, 3`), `{2,3,5}` at `θ = 0.05` (`d* = 5, 3, 3`), `{2,3}` at
`θ = 0.10` (`d* = 5, 3`), all at `σ = 2` among the primes `≤ 499`, so the
paper's "only three unclamped data points" holds only at `θ = 0.05`. -/
def dstarUnclampedByThetaStatement : Prop :=
  unclampedPrimes 0.01 = {2, 3, 5, 7} ∧ unclampedPrimes 0.05 = {2, 3, 5} ∧
    unclampedPrimes 0.1 = {2, 3}

/-- **EXTENSION (not claimed by the paper; requested scope check).** The
`θ = 0.05`, `σ = 2` statement of Obs. 10.4 holds for ALL primes, not only
the 95 primes `≤ 499`: for `p ≥ 7`, `|T₂/T₁|` at `d = 2` equals
`p/(p+1) · 2^{−(p−1)} ≤ 7/512 < 0.05`, so `d* = 2`; `p = 2, 3, 5` have
`d* = 5, 3, 3`. Kept OUT of `obsDstarStatement`. -/
def dstarAllPrimesStatement : Prop :=
  ∀ p : ℕ, p.Prime →
    ∃ D : ℕ, IsLeast (dStarSet p 0.05 2) D ∧ (2 < D ↔ p = 2 ∨ p = 3 ∨ p = 5)

/-! ## Observation 10.5 (`obs:inversion`, paper lines 1020–1026) -/

/-- **Obs. 10.5, part (a): composite advantage at `d = 2`** (lines 1021–1022).

Paper (verbatim): "At $d=2$ composites have higher $P^{\mathrm{unif}}$
than neighboring primes;".

Delta: `d = 2`; "neighboring" = ADJACENT integers, i.e. pairs `(p, c)` with
`p` prime, `c ≥ 2` composite (not prime) and `c = p ± 1` (the `−` side
written `c + 1 = p` to avoid `ℕ`-subtraction). For `p ≥ 5` both neighbours
are composite (and even); `p = 2` has none; `p = 3` has only `c = 4`.
The sentence fixes no alphabet, so it is quantified over every `σ ≥ 2`
(paper convention for probabilities; the same choice as for Prop. 10.2).
Strengthening (documented): the paper's evidence is `σ = 2`, `n ≤ 41`
(Obs. 7.3); the frozen Prop is an infinite theorem the paper does not
prove. It is true: `P(c²) ≥ σ^{−c²/2}` (one order-2 subgroup) against
`P(p²) < (p+1)σ^{p−p²}` leaves only `(σ, p, c) = (2, 5, 6)` to exact
computation (`P(6²)/P(5²) = 10^{0.332…} > 1`); checked exactly for
`σ ∈ {2,3,4,5,10}`, `p < 120`.
PAPER ISSUE 1 (false as written at one pair): for `(p, c) = (3, 4)` the
claim fails for EVERY `σ ≥ 2`: `P(4²) = (3σ⁸ − 2σ⁴)/σ¹⁶ < 3σ⁻⁸ < σ⁻⁶ ≤
(4σ³ − 3σ)/σ⁹ = P(3²)` (at `σ = 2`: `736/2¹⁶ < 26/2⁹`, the exception the
paper itself records in Obs. 7.3, but omits here). Frozen: the claim with
the pair `(3,4)` excluded.
PAPER ISSUE 2 (ambiguity; the other reading is false): "neighboring primes"
can also be read as the NEAREST primes of a composite `c` (the largest prime
below `c` and the smallest prime above it) — the only reading that says
anything about odd composites, which have no prime at distance 1. Under that
reading the claim fails beyond `(4, 3)`: `(c, p) = (9, 7), (10, 7), (35, 31)`
have `P(c²) < P(p²)` (`log₁₀` ratios `−3.91, −2.83, −15.78` at `σ = 2`,
`−6.03, −4.24, −24.58` at `σ = 3`; the only failures for composites
`c ≤ 60`, s11/check_s11_r1.py; see `compositeNearestPrimeFailStatement`).
Odd composites `9, 15, 21, 25, …` are even local MINIMA of `P` at `d = 2`.
So "neighboring primes $p\ge5$" alone would not repair the sentence. The
paper should say: "At $d=2$ every prime $p\ge5$ has smaller
$P^{\mathrm{unif}}$ than both adjacent integers $p\pm1$". Frozen: exactly
that (the adjacency reading with `(3,4)` excluded).
Repair round 1: PAPER ISSUE 2 and the corrected wording added (exploit
reviewer). -/
def compositeAdvantageD2Statement : Prop :=
  ∀ σ : ℕ, 2 ≤ σ → ∀ p c : ℕ, p.Prime → 2 ≤ c → ¬ c.Prime →
    (c = p + 1 ∨ c + 1 = p) → ¬ (p = 3 ∧ c = 4) →
      probUnif p 2 σ < probUnif c 2 σ

/-- **PAPER ISSUE evidence for Obs. 10.5(a) (not a paper claim).** Under the
nearest-prime reading of "neighboring primes" the `d = 2` composite
advantage fails (`σ = 2`): `7` is the largest prime below `9` and below
`10`, and `31` the largest prime below `35`, yet `P(9²) < P(7²)`,
`P(10²) < P(7²)` and `P(35²) < P(31²)`. -/
def compositeNearestPrimeFailStatement : Prop :=
  probUnif 9 2 2 < probUnif 7 2 2 ∧ probUnif 10 2 2 < probUnif 7 2 2 ∧
    probUnif 35 2 2 < probUnif 31 2 2

/-- **Obs. 10.5, part (b): the inversion by `d = 3`** (lines 1022–1023).

Paper (verbatim): "by $d=3$ this inverts for small $n$
(Observation~\ref{obs:extrema}),".

Delta: `σ = 2` (the setting of the cited Obs. 7.3); "this inverts" = for a
prime/composite-neighbour pair the composite no longer has the higher
`P^unif`; frozen: the instance the sentence cites, `(p, c) = (5, 6)` at
`d = 3`: `P(6³) < P(5³)`.
PAPER ISSUE (overstatement): "for small $n$" (plural) suggests that the
`d = 2` composite advantage inverts for the small pairs in general. At
`d = 3`, `σ = 2`, among all prime/composite-neighbour pairs with
`3 ≤ p ≤ 23` the inverted ones are exactly `(3, 4)` — which was never
non-inverted (PAPER ISSUE 1 of part (a)) — and `(5, 6)`: e.g.
`P(4³) > P(5³)`, `P(6³) > P(7³)`, `P(8³) > P(7³)` (see
`inversionD3ScopeStatement`; the `n = 10` failure of Obs. 7.3 is the
composite pair `(9, 10)`, not a prime/composite pair). The paper should
say: "by $d=3$ this inverts for the pair $(5,6)$
(Observation~\ref{obs:extrema})". Frozen: that instance.
Repair round 1: the narrowing was previously recorded only as a Delta;
now a PAPER ISSUE with machine-checkable evidence (literal reviewer). -/
def inversionD3Statement : Prop :=
  probUnif 6 3 2 < probUnif 5 3 2

/-- **PAPER ISSUE evidence for Obs. 10.5(b) (not a paper claim).** At
`d = 3`, `σ = 2`, for every prime `3 ≤ p ≤ 23` and each composite
neighbour `c = p ± 1`, the composite has the smaller `P^unif` exactly for
`(p, c) ∈ {(3, 4), (5, 6)}`. -/
def inversionD3ScopeStatement : Prop :=
  ∀ p c : ℕ, p.Prime → 3 ≤ p → p ≤ 23 → 2 ≤ c → ¬ c.Prime →
    (c = p + 1 ∨ c + 1 = p) →
      (probUnif c 3 2 < probUnif p 3 2 ↔ (p = 3 ∧ c = 4) ∨ (p = 5 ∧ c = 6))

/-- **Obs. 10.5, part (c): the inversion deepens with `d`** (lines 1023–1025),
general form.

Paper (verbatim): "and the inversion deepens with $d$ (e.g., $P(6)/P(5)$
falls from ${\sim}10^{0.33}$ at $d=2$ to $10^{-419.2}$ at $d=5$,
$\sigma=2$)."

Delta: the "e.g." marks `(5, 6)` as ONE instance of a general claim, frozen
here; the instance is `inversionDeepens56Statement`.
* Pairs: `(p, p + 1)` with `p ≥ 3` prime (so `p + 1` is an even composite)
  — the prime–even pairs of Prop. 10.2, Rem. 10.3 and Fig. 3, the pairs
  that do invert. Pairs `(p, p − 1)` never invert (for `p ≥ 5`, `d ≥ 1`,
  `σ ≥ 2`: `P((p−1)^d) ≥ σ^{−(p−1)^d/2} > [d 1]_p σ^{p^{d−1} − p^d} ≥
  P(p^d)`; checked for `p < 62`, `d ≤ 22`), so they carry no inversion to
  deepen.
* "Deepens": once the pair is inverted at dimension `d` (log-ratio `< 0`),
  the log-ratio is strictly smaller at `d + 1`. By induction it then stays
  negative and keeps decreasing (a single, permanent sign change).
* Alphabet: every `σ ≥ 2` — the clause fixes no `σ` (the parenthetical
  `σ = 2` belongs to the example), consistent with part (a) and Prop. 10.2.
  The `σ = 2` reading is a special case.
Truth: for `p ≥ 5` and every `d ≥ 1`, `σ ≥ 2`, the union bound and one
fixed set give `Δ ≤ −(p−1)p^{d−1} + (p+1)log_σ[d 1]_p + (d+1)log_σ 2 < 0`
for the base-`σ` log-ratio increment `Δ`, whenever the ratio is negative at
`d`. The same holds for `p = 3` when `d ≥ 4` or `σ ≥ 4`. The cases
`p = 3`, `d ∈ {2, 3}`, `σ ∈ {2, 3}` are exact computations. Checked
numerically for `σ ∈ {2,3,4,5,10}`, primes `3 ≤ p < 62`, `d ≤ 22`
(s11/check_s11_r1.py).
Repair round 1: previously only the example pair `(5, 6)` was frozen
(literal reviewer); the general form is added. -/
def inversionDeepensStatement : Prop :=
  ∀ σ : ℕ, 2 ≤ σ → ∀ p : ℕ, p.Prime → 3 ≤ p → ∀ d : ℕ, 1 ≤ d →
    inversionLogRatio σ p d < 0 →
      inversionLogRatio σ p (d + 1) < inversionLogRatio σ p d

/-- **Obs. 10.5, part (c'): the example pair `(5, 6)`** (lines 1023–1025).

Paper (verbatim): "(e.g., $P(6)/P(5)$ falls from ${\sim}10^{0.33}$ at $d=2$
to $10^{-419.2}$ at $d=5$, $\sigma=2$)".

Delta: `σ = 2`; for the example pair "falls from … at $d=2$" means that
`d ↦ log₁₀[P(6^d)/P(5^d)]` is strictly decreasing from `d = 2` on. This
includes the inverting step `d = 2 → 3`, which the general form (only
from a negative value on) does not cover. The ratio is negative (inverted)
for every `d ≥ 3`. The quoted values are `inversionExampleStatement`.
Checked exactly for `1 ≤ d ≤ 30`. For large `d` it follows from Prop.
10.1's two-sided bounds: the gap `φ(d) − φ(d+1) = (5/2)6^d − (16/5)5^d`
dwarfs the logarithmic prefactors for `d ≥ 3`. -/
def inversionDeepens56Statement : Prop :=
  (∀ d : ℕ, 3 ≤ d → inversionLogRatio 2 5 d < 0) ∧
    (∀ d : ℕ, 2 ≤ d → inversionLogRatio 2 5 (d + 1) < inversionLogRatio 2 5 d)

/-- **Obs. 10.5, part (d): the two quoted values** (lines 1024–1025).

Paper (verbatim): "$P(6)/P(5)$ falls from ${\sim}10^{0.33}$ at $d=2$ to
$10^{-419.2}$ at $d=5$, $\sigma=2$".

Delta: `σ = 2`; `P(m) = probUnif m d 2`; "`∼10^{0.33}`" ↦
`|log₁₀(P(6²)/P(5²)) − 0.33| ≤ 0.005`; "`10^{−419.2}`" (a one-decimal
rounding) ↦ `|log₁₀(P(6⁵)/P(5⁵)) − (−419.2)| ≤ 0.05`. Exact values:
`0.332265874…` (`= log₁₀(801064/(182·2¹¹))`) and `−419.230923…`. -/
def inversionExampleStatement : Prop :=
  |inversionLogRatio 2 5 2 - 0.33| ≤ 0.005 ∧
    |inversionLogRatio 2 5 5 - (-419.2)| ≤ 0.05

/-- **Observation 10.5 (`obs:inversion`), all mathematical content.**
(No purely interpretive sentences; the vague scope "for small `n`" is a
PAPER ISSUE at part (b).) -/
def obsInversionStatement : Prop :=
  compositeAdvantageD2Statement ∧ inversionD3Statement ∧
    inversionDeepensStatement ∧ inversionDeepens56Statement ∧
    inversionExampleStatement

/-- **Whole group 11** (the four environments, with the Figure 3
(`fig:inversion`) caption inside Rem. 10.3). Deliberately NOT included: the
PAPER-ISSUE evidence Props `dcOffsetLimitStatement`,
`measuredGapCauseStatement`,
`dstarLiteralDegenerateStatement`, `dstarUnclampedByThetaStatement`,
`compositeNearestPrimeFailStatement`, `inversionD3ScopeStatement`, and the
EXTENSION `dstarAllPrimesStatement`. -/
def group11Statement : Prop :=
  obsExtremaStatement ∧ remDcMeasuredStatement ∧ obsDstarStatement ∧
    obsInversionStatement

/-! ## Sanity checks (non-vacuity; computable sides; no main Prop proved) -/

/- The interpolation predicate computes the zero of the chord: on the
line `f d = 5/2 − d` it returns the true zero `5/2` (`d₀ = 2`). -/
example : IsInterpolatedSignChange (fun d => (5 : ℝ) / 2 - d) (5 / 2) := by
  refine ⟨2, le_of_lt one_lt_two, ?_, ?_, ?_⟩
  · intro d h1 h2
    interval_cases d <;> norm_num
  · norm_num
  · norm_num

/- An exact zero at `d₀` yields `x = d₀` (the `p = 3` mechanism). -/
example : IsInterpolatedSignChange (fun d => (1 : ℝ) - d) 1 := by
  refine ⟨1, le_rfl, ?_, ?_, ?_⟩
  · intro d h1 h2
    interval_cases d
    norm_num
  · norm_num
  · norm_num

/- `phiInv` is Prop. 10.2's `φ`: at `p = 5`, `φ(1) = 1`, `φ(2) = 2`,
`φ(3) = −8`, and its interpolated sign change is the chord zero `11/5`
(the `y(5)` of `measuredGapCauseStatement`); at `p = 3`, `φ(1) = 0`
exactly (the boundary case), so `y(3) = 1`. -/
example : phiInv 5 1 = 1 ∧ phiInv 5 2 = 2 ∧ phiInv 5 3 = -8 ∧ phiInv 3 1 = 0 := by
  norm_num [phiInv]
example : IsInterpolatedSignChange (phiInv 5) (11 / 5) := by
  refine ⟨2, by norm_num, ?_, ?_, ?_⟩
  · intro d h1 h2
    interval_cases d <;> norm_num [phiInv]
  · norm_num [phiInv]
  · norm_num [phiInv]

/- The local-extremum predicates are not degenerate. -/
example : IsLocalMinAt (fun n => ((n : ℝ) - 5) ^ 2) 5 := by
  constructor <;> norm_num
example : ¬ IsLocalMaxAt (fun n => ((n : ℝ) - 5) ^ 2) 5 := by
  intro h; norm_num [IsLocalMaxAt] at h

/- Hypotheses of the quantified Props are satisfiable. -/
example : Nat.Prime 5 ∧ 2 ≤ 6 ∧ ¬ Nat.Prime 6 ∧ (6 = 5 + 1 ∨ 6 + 1 = 5) ∧
    ¬ (5 = 3 ∧ 6 = 4) := by
  refine ⟨by norm_num, by norm_num, by norm_num, Or.inl rfl, by omega⟩
example : Nat.Prime 2 ∧ 2 ≤ 2 ∧ 2 ≤ 2 := ⟨Nat.prime_two, le_rfl, le_rfl⟩

/- Gaussian binomials entering `|T₂/T₁|` at `d = 2` (`[2 2]_p = 1`,
`[2 1]_p = p + 1`). -/
example : gaussBinom 7 2 2 = 1 ∧ gaussBinom 7 2 1 = 8 ∧ gaussBinom 2 1 2 = 0 := by
  decide

/- The literal `|T₂/T₁|` reproduces the expected values: `7/512` at
`(p,d,σ) = (7,2,2)`; `1/2` at `(2,3,2)` (above its `d = 2` value `1/3`, so
`d ↦ |T₂/T₁|` is not monotone and "least `d`" ≠ "eventually below"); and
`0` at `d = 1` (the PAPER ISSUE of Obs. 10.4). Decimal literals denote the
intended rationals. -/
example : t2t1 7 2 2 = 14 / 1024 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
example : t2t1 2 3 2 = 1 / 2 := by norm_num [t2t1, primeTerm, gaussBinom, abs_div]
example : t2t1 2 1 2 = 0 := by simp [t2t1, primeTerm, gaussBinom]
example : (0.05 : ℝ) = 1 / 20 ∧ (-28.61 : ℝ) = -2861 / 100 := by norm_num

/- Computable sides (`#eval` only — prints, proves nothing). Counts via the
certified closed form (`enumeration_proved` links it to `numSS`):
expected 26, 736 (Obs. 7.3), 801064, 182 (Obs. 10.5), 2, 4, 3, 9
(Rem. 10.3 at d = 1, σ = 2, 3). -/
#eval enumerationRHS 3 2 2
#eval enumerationRHS 4 2 2
#eval enumerationRHS 6 2 2
#eval enumerationRHS 5 2 2
#eval (enumerationRHS 3 1 2, enumerationRHS 4 1 2, enumerationRHS 3 1 3,
  enumerationRHS 4 1 3)
/- `|T₂/T₁|` at `d = 2`, `σ = 2` as an exact rational, `p/(p+1)·2^{-(p-1)}`:
expected 1/3, 3/16, 5/96 (all ≥ 1/20) and 7/512 (< 1/20). -/
#eval [2, 3, 5, 7].map fun p : ℕ =>
  ((p : ℚ) * gaussBinom p 2 2 / gaussBinom p 2 1) / 2 ^ (p - 1)
/- Number of primes up to 499 (expected 95). -/
#eval ((Finset.Iic 499).filter Nat.Prime).card

/- Repair round 1: hypotheses of the new quantified Props are satisfiable
(`inversionD3ScopeStatement` at `(p, c) = (5, 6)`;
`inversionDeepensStatement` at `σ = 2`, `p = 3`, `d = 2`). -/
example : Nat.Prime 5 ∧ 3 ≤ 5 ∧ 5 ≤ 23 ∧ 2 ≤ 6 ∧ ¬ Nat.Prime 6 ∧
    (6 = 5 + 1 ∨ 6 + 1 = 5) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
example : 2 ≤ 2 ∧ Nat.Prime 3 ∧ 3 ≤ 3 ∧ 1 ≤ 2 :=
  ⟨le_rfl, Nat.prime_three, le_rfl, one_le_two⟩

/- `|T₂/T₁|` (exact rationals, `σ = 2`) behind `dstarUnclampedByThetaStatement`:
`(p, d) = (7, 2)`: 7/512 ≥ 1/100 but < 1/20 (so `7` is unclamped at
`θ = 0.01` only); `(5, 2)`: 5/96 ≥ 1/20 but < 1/10; `(3, 2)`: 3/16 ≥ 1/10,
`(3, 3)`: 3/64 < 1/10. Expected: [true, true, true, true, true, true]. -/
#eval
  let r : ℕ → ℕ → ℚ := fun p d =>
    ((p : ℚ) * gaussBinom p d 2 / gaussBinom p d 1) / 2 ^ (p ^ (d - 2) * (p - 1))
  [decide ((1 : ℚ) / 100 ≤ r 7 2), decide (r 7 2 < 1 / 20),
    decide ((1 : ℚ) / 20 ≤ r 5 2), decide (r 5 2 < 1 / 10),
    decide ((1 : ℚ) / 10 ≤ r 3 2), decide (r 3 3 < 1 / 10)]

/- Repair round 2: the non-strict predicates differ from the strict ones
exactly on ties (a constant sequence is a non-strict but not a strict local
minimum), and the strict pattern implies the non-strict one. -/
example : IsLocalMinAtWeak (fun _ => (0 : ℝ)) 5 ∧ ¬ IsLocalMinAt (fun _ => (0 : ℝ)) 5 := by
  refine ⟨⟨le_rfl, le_rfl⟩, fun h => lt_irrefl _ h.1⟩
example (d σ : ℕ) (h : ExtremalPattern d σ) : ExtremalPatternWeak d σ :=
  ⟨fun n hp h5 h40 => ⟨(h.1 n hp h5 h40).1.le, (h.1 n hp h5 h40).2.le⟩,
    fun n he h4 h40 => ⟨(h.2 n he h4 h40).1.le, (h.2 n he h4 h40).2.le⟩⟩

/- `IsLinearAsymptotePrimes` is neither vacuous nor trivial: `2p + 1` has the
asymptote `(a, b) = (2, 1)`, while `p` does not have the asymptote `0`
(this uses that there are infinitely many primes). The two candidate offsets
of `dcOffsetLimitStatement` differ (`ln 2/2 − 1 ≠ 0`). -/
example : IsLinearAsymptotePrimes (fun p => 2 * (p : ℝ) + 1) 2 1 := by
  intro ε hε
  exact ⟨0, fun p _ _ => by simp [hε.le]⟩
example : ¬ IsLinearAsymptotePrimes (fun p => (p : ℝ)) 0 0 := by
  intro h
  obtain ⟨P₀, hP⟩ := h 1 one_pos
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (max P₀ 2)
  have h1 := hP p hp2 (le_trans (le_max_left _ _) hp1)
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast le_trans (le_max_right _ _) hp1
  have h3 : |(p : ℝ) - (0 * (p : ℝ) + 0)| = p := by
    rw [zero_mul, zero_add, sub_zero, abs_of_nonneg (by linarith)]
  linarith
example : Real.log 2 / 2 - 1 ≠ 0 := by
  have := Real.log_two_lt_d9
  intro h
  linarith

end ShiftSym.P11
