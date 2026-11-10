/-
Phase H, group 10 — Appendix A ("Proof of Theorem 6.1"), paper
`shift_symmetry_d_dimensions.tex` lines 1166–1342.

FROZEN STATEMENTS ONLY (no proofs of the `…Statement` props here).

Contents
* §0  Notation of Appendix A: the increasing prime list `p_1 < … < p_k`
      (`primeAt`, 0-indexed), `k = ω(n)` (`kOf`), the truncations `q^m(c)`
      (`qTrunc`, literal real-exponent definition), `q^m = q^m(1)` (`qm`),
      `N_j = n^d/p^j` (`Nj`), `D = d(d-1)/2` (`DD`), the product-formula
      Gaussian binomial for real `q` (`gaussProd`, `rdReal`), the
      rectangular torus `T_j` (`RectTorus`), "composite" (`IsComposite`).
* §1  Claims of the preamble (lines 1172–1186).
* §2  Lemma A.1 (`lem:dtorus`) + its proof-internal claims (AUXILIARY).
* §3  Lemma A.2 (`lem:coef`) + the numerical product bound (AUXILIARY).
* §4  Lemma A.3 (`lem:chain`) + decomposition identity and conditions
      (I), (II) (AUXILIARY).
* §5  Lemma A.4 (`lem:base`) + its sufficient conditions (AUXILIARY).
* §6  "Proof of Theorem 6.1" paragraph: the d = 1 and d = 2 base claims.
* §7  Representation bridges (NOT paper claims; they back two Deltas).
* §8  Sanity checks (`#eval`s and non-vacuity `example`s).

"AUXILIARY" props are mathematical claims made inside the appendix's proofs
(the closing paragraph, lines 1337–1341, itself lists "decomposition
identity, torus sandwich, union bound, coefficient estimates, conditions
(I)/(II), the chain, and the base case"); they are frozen so that the proof
phase can follow the paper's route, and they are NOT part of the
conjunctions that represent the numbered lemmas.

Standing hypotheses of the appendix. The appendix is the proof of
Theorem 6.1, whose hypotheses are `n ≥ 2, d ≥ 1, σ ≥ 2`; paper Definition 2.1
fixes `σ ≥ 2` "(for counting statements σ = 1 is also allowed)". Where a
lemma does not restate them, they are made explicit as antecedents
(documented in each Delta). Composite means `n ≥ 2` and `n` not prime
(`IsComposite`).

Brute-force pre-verification of every prop (exact arithmetic, from the
paper's definitions, independent of this file):
scratchpad/research/formal_ext/s10/check_s10.py (0 failures).
-/
import Shiftsym.Paper.Common

namespace ShiftSym.P10

open Finset

/-! ## §0 Notation of Appendix A -/

/-- `p_{i+1}` — the `(i+1)`-st smallest prime factor of `n` (paper §3,
line 261: "`n = ∏_{i=1}^k p_i^{α_i}` with `p_1 < ⋯ < p_k` prime and
`k = ω(n)`"). **0-indexed**: `primeAt n 0 = p_1`, and the appendix's
`p := p_{m+1}` is `primeAt n m`. The default value `0` outside the range
`i < k` is never used under the hypotheses of the statements below (every
statement that mentions `primeAt n i` has `i ≤ m < k` or `i < kOf n`). -/
def primeAt (n i : ℕ) : ℕ := (n.primeFactors.sort (· ≤ ·)).getD i 0

/-- `k = ω(n)`, the number of distinct prime factors of `n` (paper line
262). -/
def kOf (n : ℕ) : ℕ := n.primeFactors.card

/-- "Composite": `n ≥ 2` and `n` not prime (so `n ≥ 4`; prime powers
`p^α`, `α ≥ 2`, are composite with `k = 1`). -/
def IsComposite (n : ℕ) : Prop := 2 ≤ n ∧ ¬ n.Prime

/-- The truncation `q^m(c)` (paper lines 1172–1178), literally:
`q^m(c) = Σ_{v ∈ {0,…,d}^m, v ≠ 0} (−1)^{1+|v|} ∏_{i=1}^m r_d(p_i, v_i)
σ^{c N ∏_i p_i^{−v_i}}` with `N = n^d` (paper line 203) and `|v| = Σ v_i`.

Delta: `v ∈ {0,…,d}^m` is `v : Fin m → Fin (d+1)` (component `i` is the
paper's `v_{i+1}`); `r_d(p, v) = p^{binom v 2} [d v]_p` is the existing
`rdCoeff p v d` (Gaussian binomial by the `q`-Pascal recurrence; it equals
the paper's product formula at every integer `q ≥ 2`, see
`gaussBinomEqProdStatement`, §7); `c` is a real number and the power of
`σ` is the real power `Real.rpow` with the real exponent
`c · n^d · ∏ p_i^{−v_i}` (no rounding; the paper only evaluates at `c = 1`
and `c = p^{−j}`, where the exponent is a nonnegative integer — paper's own
integrality claim, frozen as `exponentIntegralityStatement`); `p_i^{−v_i}`
is the integer power (`zpow`) in `ℝ`. -/
noncomputable def qTrunc (n d σ m : ℕ) (c : ℝ) : ℝ :=
  ∑ v ∈ (Finset.univ : Finset (Fin m → Fin (d + 1))).erase 0,
    (-1 : ℝ) ^ (1 + ∑ i : Fin m, ((v i : Fin (d + 1)) : ℕ)) *
      (∏ i : Fin m, (rdCoeff (primeAt n i) ((v i : Fin (d + 1)) : ℕ) d : ℝ)) *
      (σ : ℝ) ^ (c * (n : ℝ) ^ d *
        ∏ i : Fin m, (primeAt n i : ℝ) ^ (-(((v i : Fin (d + 1)) : ℕ) : ℤ)))

/-- `q^m := q^m(1)` (paper line 1177). -/
noncomputable def qm (n d σ m : ℕ) : ℝ := qTrunc n d σ m 1

/-- `N_j := n^d / p^j` (paper line 1180), as a real number (no truncation;
it is an integer whenever `p^j ∣ n^d`). -/
noncomputable def Nj (n d p j : ℕ) : ℝ := (n : ℝ) ^ d / (p : ℝ) ^ j

/-- `D := d(d−1)/2` (paper line 1180). `ℕ`-division is exact (`d(d−1)` is
even) and `d − 1` does not truncate for `d ≥ 1` (for `d = 0` both sides are
`0`). -/
def DD (d : ℕ) : ℕ := d * (d - 1) / 2

/-- Gaussian binomial by the product formula for a real argument `q`
(paper line 262: `[d r]_q = ∏_{i=0}^{r−1} (q^{d−i} − 1)/(q^{i+1} − 1)`;
Lemma A.2, line 1213: "defined by the product formula").
Delta: the exponent `d − i` is `ℕ`-subtraction; it never truncates for
`i < r ≤ d` (the only range used below). -/
noncomputable def gaussProd (q : ℝ) (d r : ℕ) : ℝ :=
  ∏ i ∈ Finset.range r, ((q ^ (d - i) - 1) / (q ^ (i + 1) - 1))

/-- `r_d(q, j) = q^{binom j 2} [d j]_q` with the product-formula Gaussian
binomial, for real `q` (paper Lemma A.2, line 1213). -/
noncomputable def rdReal (q : ℝ) (d j : ℕ) : ℝ := q ^ (j.choose 2) * gaussProd q d j

/-- The rectangular torus `T_j = (ℤ/nℤ)^{d−j} × (ℤ/(n/p)ℤ)^j` (paper line
1198). Delta: `n/p` is `ℕ`-division, exact because `p ∣ n` under every
hypothesis where `T_j` is used (`p = p_{m+1}`); `d − j` does not truncate
for `j ≤ d`. -/
abbrev RectTorus (n d p j : ℕ) : Type :=
  (Fin (d - j) → ZMod n) × (Fin j → ZMod (n / p))

/-- A configuration `s : T_j → Fin σ` is "fixed by some order-`p_i` cyclic
subgroup, `i ≤ m`" (paper lines 1204–1205), where `T_j` is built with
`p = p_{m+1}`. Fixed by `H` means `τ_h s = s` for all `h ∈ H`, with
`(τ_h s)(u) = s(u + h)` (paper Definitions 2.1/2.2). -/
def FixedByLowPrime (n d σ m j : ℕ) (s : RectTorus n d (primeAt n m) j → Fin σ) : Prop :=
  ∃ i < m, ∃ H : AddSubgroup (RectTorus n d (primeAt n m) j),
    IsAddCyclic H ∧ Nat.card H = primeAt n i ∧ ∀ h ∈ H, ∀ u, s (u + h) = s u

/-! ## §1 Claims of the preamble (lines 1172–1186) -/

/-- **Appendix A, line 1179** (claim inside the definition of `q^m(c)`):
"so $q^k=|S_{n^d}|$ by Theorem~\ref{thm:main-enum}."

Delta: `|S_{n^d}|` is `numSS n d σ` (alphabet `Fin σ`), cast to `ℝ`;
`k = kOf n`. Hypotheses are those of Theorem 4.3 (`n ≥ 2, d ≥ 1, σ ≥ 1`),
by which the claim is justified ("counting statement", σ = 1 allowed per
Definition 2.1); the appendix itself only needs `σ ≥ 2`.
PAPER ISSUE: none. -/
def qkEqCardStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 1 ≤ σ → qm n d σ (kOf n) = (numSS n d σ : ℝ)

/-- **Appendix A, lines 1182–1183** (and line 1331):
"If $n$ is prime, Theorem~\ref{thm:lower-bound} holds with equality by
Corollary~\ref{cor:prime}."

Delta: `F_d(n,σ)` is the existing `lowerEnvelope n d σ` (the frozen
envelope of `lowerBoundStatement`; Gaussian binomial at `q = n` by the
`q`-Pascal recurrence); hypotheses of Theorem 6.1 (`d ≥ 1, σ ≥ 2`).
PAPER ISSUE: none. -/
def primeEqualityStatement : Prop :=
  ∀ n d σ : ℕ, n.Prime → 1 ≤ d → 2 ≤ σ → lowerEnvelope n d σ = (numSS n d σ : ℤ)

/-- **Appendix A, lines 1183–1184**: "For composite $n$ we prove
$q^1\le q^2\le\dots\le q^k$ (Lemma~\ref{lem:chain})".

Delta: the chain is stated as monotonicity of `m ↦ q^m` on `[1, k]`
(`1 ≤ a ≤ b ≤ k ⇒ q^a ≤ q^b`), equivalent to the displayed chain; for
`k = 1` it is trivially true. Standing hypotheses `d ≥ 1, σ ≥ 2` made
explicit. PAPER ISSUE: none. -/
def chainOverviewStatement : Prop :=
  ∀ n d σ a b : ℕ, IsComposite n → 1 ≤ d → 2 ≤ σ → 1 ≤ a → a ≤ b → b ≤ kOf n →
    qm n d σ a ≤ qm n d σ b

/-- **Appendix A, line 1185**: "[For composite $n$ we prove] …
$q^1>F_d(n,\sigma)$ (Lemma~\ref{lem:base} for $d\ge3$; $d\le2$ below)".

Delta: all `d ≥ 1` (Lemma A.4 for `d ≥ 3`, §6 claims for `d ∈ {1,2}`);
`F_d` is `lowerEnvelope` cast to `ℝ`; standing `σ ≥ 2`.
PAPER ISSUE: none (for `d = 1` the text "below" argues directly with
`|S_n|`; since `q^1 = σ^{n/p_1}` for `d = 1` the claim holds as stated —
verified). -/
def baseAllDimsStatement : Prop :=
  ∀ n d σ : ℕ, IsComposite n → 1 ≤ d → 2 ≤ σ → (lowerEnvelope n d σ : ℝ) < qm n d σ 1

/-- **Appendix A, line 1186**: "… which give strict inequality at every
composite $n$." (The overall conclusion of the appendix, for composite
`n`; together with `primeEqualityStatement` it yields Theorem 6.1.)

Delta: `F_d < |S_{n^d}|` in `ℤ`; hypotheses of Theorem 6.1.
PAPER ISSUE: none. -/
def strictCompositeStatement : Prop :=
  ∀ n d σ : ℕ, IsComposite n → 1 ≤ d → 2 ≤ σ → lowerEnvelope n d σ < (numSS n d σ : ℤ)

/-- The preamble of Appendix A (lines 1172–1186) as a whole. -/
def appendixOverviewStatement : Prop :=
  qkEqCardStatement ∧ primeEqualityStatement ∧ chainOverviewStatement ∧
    baseAllDimsStatement ∧ strictCompositeStatement

/-! ## §2 Lemma A.1 (`lem:dtorus`, lines 1188–1209) -/

/-- **Lemma A.1 (Union interpretation on rectangular tori), first part**,
lines 1188–1191: "Let $1\le m<k$ and $1\le j\le d$. Then
$0\le q^m(p^{-j})\le\sigma^{N_j}$".

Delta: `p = p_{m+1} = primeAt n m`; `p^{−j}` is the real `zpow`;
`σ^{N_j}` is `Real.rpow` with the real `N_j = n^d/p^j`. The appendix's
standing hypotheses `n ≥ 2, d ≥ 1, σ ≥ 2` are made explicit (`n ≥ 2`,
`d ≥ 1` are anyway implied by `1 ≤ m < k`, `1 ≤ j ≤ d`; the inequalities
also hold for `σ = 1`, checked, but the lemma sits in the `σ ≥ 2` proof).
PAPER ISSUE: none. -/
def lemA1SandwichStatement : Prop :=
  ∀ n d σ m j : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 ≤ m → m < kOf n → 1 ≤ j → j ≤ d →
    0 ≤ qTrunc n d σ m ((primeAt n m : ℝ) ^ (-(j : ℤ))) ∧
      qTrunc n d σ m ((primeAt n m : ℝ) ^ (-(j : ℤ))) ≤ (σ : ℝ) ^ (Nj n d (primeAt n m) j)

/-- **Lemma A.1, second part**, lines 1192–1193: "and
$q^m(p^{-1})\le\sum_{i\le m}\gaussbinom d1_{p_i}\,\sigma^{N_1/p_i}$."

Delta: `Σ_{i ≤ m}` (1-indexed) is `Σ_{i ∈ range m}` (0-indexed,
`primeAt n i = p_{i+1}`); `[d 1]_{p_i}` is `gaussBinom (p_i) d 1`
(`q`-Pascal; equal to the product formula, §7); `σ^{N_1/p_i}` is
`Real.rpow` with real exponent `N_1 / p_i`; `p^{−1}` is `zpow (−1)`.
Standing hypotheses as in the first part.
PAPER ISSUE: none. -/
def lemA1UnionBoundStatement : Prop :=
  ∀ n d σ m : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 ≤ m → m < kOf n →
    qTrunc n d σ m ((primeAt n m : ℝ) ^ (-(1 : ℤ))) ≤
      ∑ i ∈ Finset.range m,
        (gaussBinom (primeAt n i) d 1 : ℝ) * (σ : ℝ) ^ (Nj n d (primeAt n m) 1 / (primeAt n i : ℝ))

/-- **Lemma A.1** (`lem:dtorus`), the whole statement. -/
def lemA1Statement : Prop := lemA1SandwichStatement ∧ lemA1UnionBoundStatement

/-- AUXILIARY (proof of Lemma A.1, lines 1198–1201): "Consider
$T_j=(\ZZ/n\ZZ)^{d-j}\times(\ZZ/\tfrac np\ZZ)^{j}$ with $N_j$ cells. For
$i\le m$, $p_i$ divides both $n$ and $n/p$ (as $p_i\neq p$), so the
$p_i$-torsion of $T_j$ is again $\cong\FF_{p_i}^d$".

Delta: "`N_j` cells" is `Nat.card T_j = N_j` (cast to `ℝ`); the
`p_i`-torsion is `AddSubgroup.torsionBy T_j p_i`, and "≅ F_{p_i}^d" is an
additive-group isomorphism with `Fin d → ZMod p_i`; `i ≤ m` (1-indexed) is
`i < m` (0-indexed). Hypotheses as in Lemma A.1 (σ plays no role).
PAPER ISSUE: none. -/
def rectTorusStatement : Prop :=
  ∀ n d m j : ℕ, 2 ≤ n → 1 ≤ d → 1 ≤ m → m < kOf n → 1 ≤ j → j ≤ d →
    (Nat.card (RectTorus n d (primeAt n m) j) : ℝ) = Nj n d (primeAt n m) j ∧
      ∀ i < m, primeAt n i ∣ n ∧ primeAt n i ∣ n / primeAt n m ∧
        Nonempty (↥(AddSubgroup.torsionBy (RectTorus n d (primeAt n m) j) (primeAt n i : ℤ))
          ≃+ (Fin d → ZMod (primeAt n i)))

/-- AUXILIARY (proof of Lemma A.1, lines 1202–1205) — the "union
interpretation" of the lemma's title: "By the computation in the proof of
Theorem~\ref{thm:main-enum}, restricted to $p_1,\dots,p_m$, $q^m(p^{-j})$
equals the number of configurations of $T_j$ fixed by some order-$p_i$
cyclic subgroup, $i\le m$ --- a union of fixed-point sets."

Delta: configurations of `T_j` over the alphabet `Fin σ`; "order-`p_i`
cyclic subgroup" is an `AddSubgroup H` with `IsAddCyclic H` and
`Nat.card H = p_i`; the count is `Nat.card` of the subtype, cast to `ℝ`.
Since this is a counting statement, `σ ≥ 1` (Definition 2.1).
PAPER ISSUE: none. -/
def unionInterpretationStatement : Prop :=
  ∀ n d σ m j : ℕ, 2 ≤ n → 1 ≤ d → 1 ≤ σ → 1 ≤ m → m < kOf n → 1 ≤ j → j ≤ d →
    (Nat.card {s : RectTorus n d (primeAt n m) j → Fin σ // FixedByLowPrime n d σ m j s} : ℝ)
      = qTrunc n d σ m ((primeAt n m : ℝ) ^ (-(j : ℤ)))

/-- AUXILIARY (proof of Lemma A.1, lines 1207–1208): "Exponent integrality:
$v_{p_i}(N_j)=d\,\alpha_{p_i}\ge d\ge v_i$."

Delta: three conjuncts — `p^j ∣ n^d` (so `N_j = n^d / p^j` is an exact
`ℕ`-quotient), the valuation identity `v_{p_i}(N_j) = d·α_{p_i}` for
`i ≤ m` (`α_{p_i} = v_{p_i}(n)`, via `Nat.factorization`), and the
consequence that makes every exponent of `q^m(p^{−j})` an integer:
`∏_i p_i^{v_i} ∣ N_j` for every `v ∈ {0,…,d}^m`.
PAPER ISSUE: none. -/
def exponentIntegralityStatement : Prop :=
  ∀ n d m j : ℕ, 2 ≤ n → 1 ≤ d → 1 ≤ m → m < kOf n → 1 ≤ j → j ≤ d →
    primeAt n m ^ j ∣ n ^ d ∧
      (∀ i < m, (n ^ d / primeAt n m ^ j).factorization (primeAt n i)
          = d * n.factorization (primeAt n i)) ∧
      ∀ v : Fin m → Fin (d + 1),
        (∏ i : Fin m, primeAt n i ^ ((v i : Fin (d + 1)) : ℕ)) ∣ n ^ d / primeAt n m ^ j

/-! ## §3 Lemma A.2 (`lem:coef`, lines 1211–1230) -/

/-- **Lemma A.2 (Coefficient estimates), first part**, lines 1212–1214:
"Let $q\ge2$ be real, with $\gaussbinom dj_q$ … defined by the product
formula. Then $\gaussbinom dj_q\le 4q^{\,j(d-j)}$".

Delta: `[d j]_q` is `gaussProd q d j`; the (unstated) ranges are the
paper's standing `d ≥ 1` and `0 ≤ j ≤ d` (so `j(d−j)` is a nonnegative
integer, `ℕ`-subtraction exact). PAPER ISSUE: none. -/
def lemA2Part1Statement : Prop :=
  ∀ (q : ℝ) (d j : ℕ), 2 ≤ q → 1 ≤ d → j ≤ d → gaussProd q d j ≤ 4 * q ^ (j * (d - j))

/-- **Lemma A.2, second part**, line 1215: "$\gaussbinom d1_q\le
2q^{\,d-1}$".

Delta: real `q ≥ 2`, `d ≥ 1` (so `d − 1` is exact). PAPER ISSUE: none. -/
def lemA2Part2Statement : Prop :=
  ∀ (q : ℝ) (d : ℕ), 2 ≤ q → 1 ≤ d → gaussProd q d 1 ≤ 2 * q ^ (d - 1)

/-- **Lemma A.2, third part**, lines 1213 and 1216: "$r_d(q,j)=
q^{\binom j2}\gaussbinom dj_q$ defined by the product formula … and
$\sum_{j=2}^{d}r_d(q,j)\le 4(d-1)\,q^{D}$."

Delta: `Σ_{j=2}^d` is `Σ_{j ∈ Icc 2 d}` (empty for `d = 1`, where the claim
reads `0 ≤ 0`); `4(d−1)` uses real subtraction; `D = DD d`.
PAPER ISSUE: none. -/
def lemA2Part3Statement : Prop :=
  ∀ (q : ℝ) (d : ℕ), 2 ≤ q → 1 ≤ d →
    ∑ j ∈ Finset.Icc 2 d, rdReal q d j ≤ 4 * ((d : ℝ) - 1) * q ^ DD d

/-- **Lemma A.2** (`lem:coef`), the whole statement. -/
def lemA2Statement : Prop := lemA2Part1Statement ∧ lemA2Part2Statement ∧ lemA2Part3Statement

/-- AUXILIARY (proof of Lemma A.2, lines 1223–1224):
"$\prod_{i\ge1}(1-2^{-i})\ge\frac12\cdot\frac34\cdot\frac78
\bigl(1-\sum_{i\ge4}2^{-i}\bigr)=\frac{147}{512}>\frac14$".

Delta: the infinite product is represented by all its partial products
(they decrease to it, so "infinite product ≥ 147/512" ⇔ "every partial
product ≥ 147/512"); the middle equality uses `tsum` for `Σ_{i≥4} 2^{−i}`
(reindexed `i = i' + 4`); `2^{−i}` is the real `zpow`.
PAPER ISSUE: none. -/
def lemA2ProductBoundStatement : Prop :=
  (∀ M : ℕ, (147 / 512 : ℝ) ≤ ∏ i ∈ Finset.Icc 1 M, (1 - (2 : ℝ) ^ (-(i : ℤ)))) ∧
    (1 / 2 : ℝ) * (3 / 4) * (7 / 8) * (1 - ∑' i : ℕ, (2 : ℝ) ^ (-((i + 4 : ℕ) : ℤ))) = 147 / 512 ∧
    (1 / 4 : ℝ) < 147 / 512

/-! ## §4 Lemma A.3 (`lem:chain`, lines 1232–1282) -/

/-- **Lemma A.3 (Monotone chain)**, lines 1232–1234: "For composite $n$
with $k\ge2$, $d\ge1$, $\sigma\ge2$, and $1\le m<k$: $q^m\le q^{m+1}$."

Delta: `q^m = qm n d σ m` (real); "composite with `k ≥ 2`" kept literally
(`IsComposite n ∧ 2 ≤ kOf n`; the first is implied by the second).
PAPER ISSUE: none. -/
def lemA3ChainStatement : Prop :=
  ∀ n d σ m : ℕ, IsComposite n → 2 ≤ kOf n → 1 ≤ d → 2 ≤ σ → 1 ≤ m → m < kOf n →
    qm n d σ m ≤ qm n d σ (m + 1)

/-- AUXILIARY (proof of Lemma A.3, eq. (decomp), lines 1238–1243):
"Splitting $q^{m+1}$ by the value $j$ of $v_{m+1}$ … :
$q^{m+1}-q^m=\sum_{j=1}^{d}(-1)^{j+1}r_d(p,j)\,B_j$,
$B_j:=\sigma^{N_j}-q^m(p^{-j})$".
(The bracket `B_j ∈ [0, σ^{N_j}]` is `lemA1SandwichStatement`.)

Delta: `p = primeAt n m`; `r_d(p,j) = rdCoeff p j d`; `σ^{N_j}` is
`Real.rpow`; hypotheses of Lemma A.3 (the identity is algebraic).
PAPER ISSUE: none. -/
def decompositionStatement : Prop :=
  ∀ n d σ m : ℕ, IsComposite n → 2 ≤ kOf n → 1 ≤ d → 2 ≤ σ → 1 ≤ m → m < kOf n →
    qm n d σ (m + 1) - qm n d σ m =
      ∑ j ∈ Finset.Icc 1 d, (-1 : ℝ) ^ (j + 1) * (rdCoeff (primeAt n m) j d : ℝ) *
        ((σ : ℝ) ^ (Nj n d (primeAt n m) j) - qTrunc n d σ m ((primeAt n m : ℝ) ^ (-(j : ℤ))))

/-- AUXILIARY (proof of Lemma A.3, condition (I), lines 1248 and 1265):
"(I) $\sigma^{N_1/2}\ge 4\,t^{\,d-1}$" — "It remains to prove (I), (II)
for composite $n\ge6$, $d\ge2$."

Delta: `p = p_{m+1}` with `1 ≤ m < k` (context of the proof), `t = n/p`
(real division; an integer), `σ ≥ 2` (Lemma A.3); `σ^{N_1/2}` is
`Real.rpow` (`N_1/2` need not be an integer, e.g. `n = 15, p = 5, d = 2`).
PAPER ISSUE: none. -/
def condIStatement : Prop :=
  ∀ n d σ m : ℕ, IsComposite n → 6 ≤ n → 2 ≤ d → 2 ≤ σ → 1 ≤ m → m < kOf n →
    4 * ((n : ℝ) / (primeAt n m : ℝ)) ^ (d - 1) ≤ (σ : ℝ) ^ (Nj n d (primeAt n m) 1 / 2)

/-- AUXILIARY (proof of Lemma A.3, condition (II), lines 1249 and 1265):
"(II) $\sigma^{N_1-N_2}\ge 8(d-1)\,p^{D}$" — for composite `n ≥ 6`,
`d ≥ 2`.

Delta: as for (I); `N_1 − N_2` is real subtraction, `σ^{N_1−N_2}` is
`Real.rpow`, `8(d−1)` uses real subtraction, `D = DD d`.
PAPER ISSUE: none. -/
def condIIStatement : Prop :=
  ∀ n d σ m : ℕ, IsComposite n → 6 ≤ n → 2 ≤ d → 2 ≤ σ → 1 ≤ m → m < kOf n →
    8 * ((d : ℝ) - 1) * (primeAt n m : ℝ) ^ DD d ≤
      (σ : ℝ) ^ (Nj n d (primeAt n m) 1 - Nj n d (primeAt n m) 2)

/-! ## §5 Lemma A.4 (`lem:base`, lines 1284–1319) -/

/-- **Lemma A.4 (Base case, d ≥ 3)**, lines 1284–1285: "For composite $n$,
$\sigma\ge2$, $d\ge3$: $q^1>F_d(n,\sigma)$."

Delta: `q^1 = qm n d σ 1` (real); `F_d = lowerEnvelope n d σ` cast to `ℝ`.
PAPER ISSUE: none. -/
def lemA4BaseStatement : Prop :=
  ∀ n d σ : ℕ, IsComposite n → 2 ≤ σ → 3 ≤ d → (lowerEnvelope n d σ : ℝ) < qm n d σ 1

/-- AUXILIARY (proof of Lemma A.4, line 1312): the proviso
"provided $2^{n^{d-1}}\ge12d\,n^{D}$", which the proof establishes for
the lemma's range (composite `n`, `d ≥ 3`).

Delta: exact `ℕ` inequality; `D = DD d`. PAPER ISSUE: none. -/
def lemA4ProvisoStatement : Prop :=
  ∀ n d : ℕ, IsComposite n → 3 ≤ d → 12 * d * n ^ DD d ≤ 2 ^ (n ^ (d - 1))

/-- AUXILIARY (proof of Lemma A.4, lines 1313–1315): "Taking logarithms it
suffices that $n^{d-1}\ge4+d+\tfrac{d(d-1)}2\log_2n$ for $n\ge4$, $d\ge3$".

Delta: `n` ranges over naturals `≥ 4` (as written, not only composites);
`log₂` is `Real.logb 2`. PAPER ISSUE: none. -/
def lemA4LogConditionStatement : Prop :=
  ∀ n d : ℕ, 4 ≤ n → 3 ≤ d →
    4 + (d : ℝ) + (d : ℝ) * ((d : ℝ) - 1) / 2 * Real.logb 2 n ≤ (n : ℝ) ^ (d - 1)

/-! ## §6 "Proof of Theorem 6.1" (lines 1321–1335): the d ≤ 2 claims -/

/-- **Proof of Theorem 6.1, `d = 1`**, line 1322: "$d=1$: $F_1=\sigma$".

Delta: in `ℤ`, for all `n ≥ 2`, `σ ≥ 2` (Theorem 6.1's range).
PAPER ISSUE: none. -/
def envelopeD1Statement : Prop :=
  ∀ n σ : ℕ, 2 ≤ n → 2 ≤ σ → lowerEnvelope n 1 σ = (σ : ℤ)

/-- **Proof of Theorem 6.1, `d = 1`**, line 1322: "primes give
$|S_n|=\sigma$".

Delta: `|S_n| = numSS p 1 σ`; `σ ≥ 2`. PAPER ISSUE: none. -/
def primeD1Statement : Prop :=
  ∀ p σ : ℕ, p.Prime → 2 ≤ σ → numSS p 1 σ = σ

/-- **Proof of Theorem 6.1, `d = 1`**, lines 1322–1323: "composites
$|S_n|\ge\sigma^{n/p_1}\ge\sigma^2>\sigma$."

Delta: `p_1 = primeAt n 0` (smallest prime factor); `n/p_1` is
`ℕ`-division, exact since `p_1 ∣ n`; all in `ℕ`; `σ ≥ 2`.
PAPER ISSUE: none. -/
def compositeD1Statement : Prop :=
  ∀ n σ : ℕ, IsComposite n → 2 ≤ σ →
    σ ^ (n / primeAt n 0) ≤ numSS n 1 σ ∧ σ ^ 2 ≤ σ ^ (n / primeAt n 0) ∧ σ < σ ^ 2

/-- **Proof of Theorem 6.1, `d = 2`**, line 1324:
"$d=2$: $F_2(n,\sigma)=(n{+}1)\sigma^n-n\sigma$".

Delta: in `ℤ`, `n ≥ 2`, `σ ≥ 2`. PAPER ISSUE: none. -/
def envelopeD2Statement : Prop :=
  ∀ n σ : ℕ, 2 ≤ n → 2 ≤ σ →
    lowerEnvelope n 2 σ = ((n : ℤ) + 1) * (σ : ℤ) ^ n - (n : ℤ) * σ

/-- **Proof of Theorem 6.1, `d = 2`**, lines 1325–1327: "we import its
base step ($q^1>(n{+}1)\sigma^n-n\sigma$ at composite $n$, final display
of the source proof)".

Delta: `q^1 = qm n 2 σ 1` (real); `σ ≥ 2`.
PAPER ISSUE (minor, attribution precision; the claim itself is TRUE): in
the source (arXiv:1703.09030v2, proof of Lemma E.21) the final display
sits in the branch "If k > 1", and the branch "If k = 1, i.e., n is a
prime" misreads `k = ω(n) = 1` as primality, so the source's case split
never treats prime powers `n = p^α`, `α ≥ 2` (for which the k = 1 branch's
"equality holds" is false). The displayed inequality nevertheless holds
verbatim at every composite `n` (its derivation only uses `p_1 < n`,
`p_1 ≤ n/2`), and it is that inequality — not the source's case split —
that the paper imports, so the d = 2 argument is valid. Suggested wording:
"…final display of the source proof, whose derivation uses only
`p_1 ≤ n/2` and therefore also covers prime powers"; the slip in the
source could be added to the companion erratum. Verified for all
composite `n ≤ 60`, `σ ∈ {2,3,4}` (incl. `n = 4, 8, 9, 16, 25, 27, 32, 49`). -/
def baseD2Statement : Prop :=
  ∀ n σ : ℕ, IsComposite n → 2 ≤ σ →
    ((n : ℝ) + 1) * (σ : ℝ) ^ n - (n : ℝ) * σ < qm n 2 σ 1

/-- The `d ≤ 2` claims of the "Proof of Theorem 6.1" paragraph
(lines 1322–1330) as a whole. The `d ≥ 3` sentence (lines 1331–1334) is
the combination `primeEqualityStatement`, `qkEqCardStatement` (its `k = 1`
instance `|S| = q^1`), `lemA3ChainStatement` and `lemA4BaseStatement`;
the attribution "the claim is [Lemma E.21]" and the remark on the
published chain (Lemma A.21 of the 2019 paper) are recorded as
non-mathematical in the group report. -/
def proofLowDimStatement : Prop :=
  envelopeD1Statement ∧ primeD1Statement ∧ compositeD1Statement ∧
    envelopeD2Statement ∧ baseD2Statement

/-- The "Proof of Theorem 6.1" paragraph (lines 1321–1335) as a whole:
the `d ≤ 2` claims plus the ingredients of the `d ≥ 3` sentence and its
conclusion (equality at primes, strict inequality at composites). -/
def proofOfThm61Statement : Prop :=
  proofLowDimStatement ∧ primeEqualityStatement ∧ qkEqCardStatement ∧
    lemA3ChainStatement ∧ lemA4BaseStatement ∧ strictCompositeStatement

/-! ## §7 Representation bridges (NOT paper claims) -/

/-- BRIDGE (backs the Delta "`q`-Pascal `gaussBinom` = paper's product
formula"): for every integer `q ≥ 2` and all `d, r`, the recurrence-defined
`gaussBinom q d r` equals the product formula
`∏_{i<r} (q^{d−i} − 1)/(q^{i+1} − 1)` (including `0` for `r > d`). This is
what lets Lemma A.2 (stated for the product formula) be applied to the
coefficients `r_d(p_i, ·)` of `q^m` and to `F_d` at `q = n` (Lemma A.4's
proof, line 1292–1293: "using Lemma A.2 at $q=p_1$ and at the composite
argument $q=n$"). Implicit in the paper's §6 sentence "since
$\gaussbinom dr_q$ is a polynomial in $q$ with nonnegative integer
coefficients". -/
def gaussBinomEqProdStatement : Prop :=
  ∀ q d r : ℕ, 2 ≤ q → (gaussBinom q d r : ℝ) = gaussProd (q : ℝ) d r

/-- Computable integer shadow of `q^m(1/e)` (`e ≥ 1`), with `ℕ`-division
in the exponent; used ONLY for the `#eval` sanity checks of §8. -/
def qTruncZ (n d σ m e : ℕ) : ℤ :=
  ∑ v ∈ (Finset.univ : Finset (Fin m → Fin (d + 1))).erase 0,
    (-1 : ℤ) ^ (1 + ∑ i : Fin m, ((v i : Fin (d + 1)) : ℕ)) *
      (∏ i : Fin m, (rdCoeff (primeAt n i) ((v i : Fin (d + 1)) : ℕ) d : ℤ)) *
      (σ : ℤ) ^ (n ^ d / (e * ∏ i : Fin m, primeAt n i ^ ((v i : Fin (d + 1)) : ℕ)))

/-- BRIDGE (links the `#eval` shadow to the frozen definition): whenever
every exponent is integral (`e · ∏ p_i^{v_i} ∣ n^d` for all `v`), the
literal real `q^m(1/e)` equals the integer shadow. -/
def qTruncZBridgeStatement : Prop :=
  ∀ n d σ m e : ℕ, 2 ≤ n → m ≤ kOf n → 1 ≤ e →
    (∀ v : Fin m → Fin (d + 1),
      e * ∏ i : Fin m, primeAt n i ^ ((v i : Fin (d + 1)) : ℕ) ∣ n ^ d) →
    qTrunc n d σ m ((e : ℝ)⁻¹) = (qTruncZ n d σ m e : ℝ)

/-! ## §8 Sanity checks -/

-- The increasing prime list and `k`:
#eval (List.range 3).map (primeAt 30)   -- [2, 3, 5]
#eval kOf 30                             -- 3
#eval (List.range 2).map (primeAt 12)   -- [2, 3]
#eval primeAt 9 0                        -- 3

-- `q^k = |S|` reference values (CLAUDE.md table), via the integer shadow
-- (e = 1): 8, 26, 182, 72, 6398, 801064.
#eval [qTruncZ 2 2 2 (kOf 2) 1, qTruncZ 3 2 2 (kOf 3) 1, qTruncZ 5 2 2 (kOf 5) 1,
       qTruncZ 2 3 2 (kOf 2) 1, qTruncZ 3 3 2 (kOf 3) 1, qTruncZ 6 2 2 (kOf 6) 1]

-- Lemma A.1 at (n,d,σ,m,j) = (6,2,2,1,1) and (6,2,2,1,2): 0 ≤ q^1(3^{-j}) ≤ 2^{36/3^j},
-- union bound q^1(3^{-1}) ≤ [2 1]_2 · 2^{12/2} = 192.
#eval (qTruncZ 6 2 2 1 3, (2 : ℤ) ^ 12, qTruncZ 6 2 2 1 9, (2 : ℤ) ^ 4,
       (gaussBinom 2 2 1 : ℤ) * 2 ^ 6)

-- Decomposition identity (eq:decomp) at (n,d,σ,m) = (6,2,2,1), p = 3: `true`.
#eval decide (qTruncZ 6 2 2 2 1 - qTruncZ 6 2 2 1 1 =
  ∑ j ∈ Finset.Icc 1 2, (-1 : ℤ) ^ (j + 1) * (rdCoeff 3 j 2 : ℤ) *
    ((2 : ℤ) ^ (36 / 3 ^ j) - qTruncZ 6 2 2 1 (3 ^ j)))

-- Lemma A.3 at (30,1,2,m) and (12,2,2,1); Lemma A.4 at (4,3,2), (6,3,2); base d=2 at n=4,6: all `true`.
#eval (decide (qTruncZ 30 1 2 1 1 ≤ qTruncZ 30 1 2 2 1), decide (qTruncZ 30 1 2 2 1 ≤ qTruncZ 30 1 2 3 1),
       decide (qTruncZ 12 2 2 1 1 ≤ qTruncZ 12 2 2 2 1))
#eval (decide (lowerEnvelope 4 3 2 < qTruncZ 4 3 2 1 1), decide (lowerEnvelope 6 3 2 < qTruncZ 6 3 2 1 1),
       decide ((4 + 1) * 2 ^ 4 - 4 * 2 < qTruncZ 4 2 2 1 1), decide ((6 + 1) * 2 ^ 6 - 6 * 2 < qTruncZ 6 2 2 1 1))

-- F_1 = σ and F_2 = (n+1)σ^n − nσ on small instances: `true`.
#eval (decide (lowerEnvelope 6 1 3 = 3), decide (lowerEnvelope 6 2 3 = 7 * 3 ^ 6 - 6 * 3))

-- Lemma A.4 proviso at (4,3) and log-condition anchor "(4,3): 16 ≥ 13".
#eval (decide (12 * 3 * 4 ^ DD 3 ≤ 2 ^ (4 ^ 2)), 4 + 3 + DD 3 * 2, 4 ^ 2)

/-- Non-vacuity: `6` is composite with two prime factors `2 < 3`, so the
hypotheses `1 ≤ m < k` of Lemmas A.1/A.3 are satisfiable (m = 1), and
`p_{m+1} = primeAt 6 1 = 3`. -/
theorem primeFactors_six : Nat.primeFactors 6 = {2, 3} := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  rfl

example : IsComposite 6 ∧ kOf 6 = 2 ∧ primeAt 6 0 = 2 ∧ primeAt 6 1 = 3 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_⟩
  · rw [kOf, primeFactors_six]; rfl
  · rw [primeAt, primeFactors_six,
      Finset.sort_insert (r := (· ≤ ·)) (s := {3}) (a := 2) (by simp) (by simp),
      Finset.sort_singleton]
    rfl
  · rw [primeAt, primeFactors_six,
      Finset.sort_insert (r := (· ≤ ·)) (s := {3}) (a := 2) (by simp) (by simp),
      Finset.sort_singleton]
    rfl

/-- Non-vacuity of Lemma A.4 / the d = 1, 2 base claims: `4` is composite
(a prime power, `k = 1`). -/
example : IsComposite 4 := ⟨by norm_num, by norm_num⟩

end ShiftSym.P10
