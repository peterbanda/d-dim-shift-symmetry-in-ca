/-
Phase H, group 04 — **Enumeration corollaries** (paper
`shift_symmetry_d_dimensions.tex`, lines 397–500: Theorem 4.3's integrality
sentence, Corollary 4.4, Remark 4.5, the prose claims of §4.3 "Alternative
derivation via the subgroup lattice" and the reference values of §4.4).
Table 1 (paper lines 502–517) is NOT frozen here: it belongs to group 03
(declared range 351–396, 502–517) and is frozen there as
`ShiftSym.P03.table1Statement` (repairer round 1: the duplicate copy that
this file used to carry was removed).

FROZEN STATEMENTS ONLY: every paper claim is a `def …Statement : Prop`; no
`theorem` in this file proves any of them. Proofs belong in
`Shiftsym/Paper/Proofs/P04_EnumerationCorollaries.lean`.

Theorem 4.3 itself is NOT restated: it is the already frozen (and proved)
`ShiftSym.enumerationStatement` (divisor-reindexed). This file adds the
paper's own rank-vector form of the right-hand side, `mainFormulaRHS`, and
the encoding bridge `rankVectorReindexStatement` (rank-vector sum =
`enumerationRHS`), so that every rank-vector statement below is in the
paper's form and can still be connected to the certified theorem.

Conventions used throughout (each repeated under "Delta:" where it matters):
* `n = ∏ pᵢ^{αᵢ}`, `p₁ < ⋯ < p_k`, `k = ω(n)` (paper §3): `k` is
  `n.primeFactors.card` and `pᵢ` is `primeSeq n i`, the `i`-th smallest prime
  factor (`Finset.orderEmbOfFin`, 0-based `i : Fin k`).
* rank vectors `v ∈ {0,…,d}^k` are functions `Fin k → ℕ` in
  `Fintype.piFinset (fun _ => Finset.range (d+1))`; `v ≠ 0` is `v ≠ 0` as a
  function; `|v| = ∑ i, v i`.
* exponents `n^d ∏ pᵢ^{-vᵢ}` are the `ℕ`-quotients `n ^ d / ∏ pᵢ ^ vᵢ`; that
  this quotient is exact (and equals the rational number the paper writes) is
  itself frozen (`exponentEncodingStatement`).
* `|S_{n^d}|` is `ShiftSym.numSS n d σ` (alphabet `Fin σ`, from `Common.lean`).
* `r_d(p,v) = p^{C(v,2)} [d v]_p` is the project's `rdCoeff p v d`, with the
  Gaussian binomial `gaussBinom` defined by the q-Pascal recurrence (the
  paper's product definition of §3 is equivalent; that equivalence is a
  group-03 statement and is spot-checked here by `#eval`).
-/
import Shiftsym.Paper.Common

namespace ShiftSym.P04

open ShiftSym Finset

/-! ## Paper notation (rank vectors) -/

/-- `p₁ < p₂ < ⋯ < p_k`: the prime factors of `n` in increasing order
(paper §3: "Throughout, `n = ∏_{i=1}^k pᵢ^{αᵢ}` with `p₁ < ⋯ < p_k` prime and
`k = ω(n)`"). Index `i : Fin k` is 0-based (`primeSeq n 0 = p₁`). -/
def primeSeq (n : ℕ) : Fin n.primeFactors.card → ℕ :=
  fun i => n.primeFactors.orderEmbOfFin rfl i

/-- The index set `{0,…,d}^k` of eq. (2), as functions `Fin k → ℕ`. -/
def allRankVectors (n d : ℕ) : Finset (Fin n.primeFactors.card → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (d + 1)

/-- The summation range of eq. (2): `v ∈ {0,…,d}^k`, `v ≠ 0`. -/
def rankVectors (n d : ℕ) : Finset (Fin n.primeFactors.card → ℕ) :=
  (allRankVectors n d).filter fun v => v ≠ 0

/-- Right-hand side of eq. (2) of Theorem 4.3 in the paper's OWN indexing:
`∑_{v ∈ {0..d}^k, v ≠ 0} (-1)^{1+|v|} ∏ᵢ r_d(pᵢ,vᵢ) σ^{n^d ∏ᵢ pᵢ^{-vᵢ}}`.
The exponent is the `ℕ`-quotient `n ^ d / ∏ pᵢ ^ vᵢ` (exact by
`exponentEncodingStatement`). -/
def mainFormulaRHS (n d σ : ℕ) : ℤ :=
  ∑ v ∈ rankVectors n d,
    (-1 : ℤ) ^ (1 + ∑ i, v i) * (∏ i, (rdCoeff (primeSeq n i) (v i) d : ℤ)) *
      (σ : ℤ) ^ (n ^ d / ∏ i, primeSeq n i ^ v i)

/-! ## Theorem 4.3 (`thm:main-enum`, lines 397–406): the integrality sentence -/

/-- **Theorem 4.3, last sentence** (`thm:main-enum`, paper line 405).

Paper (lines 397–406, verbatim): "For all $n\ge2$, $d\ge1$, and
$\sigma\ge1$: [eq. (2)] $|S_{n^d}| = \sum_{\vv=(v_1,\dots,v_k)\in
\{0,\dots,d\}^k, \vv\neq\mathbf 0} (-1)^{1+|\vv|}\,\prod_{i=1}^{k} r_d(p_i,
v_i)\; \sigma^{\,n^d\prod_i p_i^{-v_i}}$ where $|\vv|=\sum_i v_i$. All
exponents are integers."

Formalized: for every rank vector `v ∈ {0,…,d}^k` the rational number
`n^d ∏ᵢ pᵢ^{-vᵢ}` is a natural number.

Delta:
* the exponent is computed in `ℚ` with integer powers `zpow` (literal
  reading of `p_i^{-v_i}`); "is an integer" is `∃ m : ℕ, … = m` (it is
  positive, so ℕ rather than ℤ loses nothing);
* hypotheses `2 ≤ n`, `1 ≤ d` are the theorem's; `σ` does not occur in the
  exponents and is therefore not quantified;
* `v` ranges over ALL of `{0,…,d}^k`, i.e. also `v = 0` (exponent `n^d`),
  whereas the sentence refers to the exponents of eq. (2) (`v ≠ 0`); this is
  a deliberate, harmless strengthening by one trivially integral case, as in
  the paper's own proof ("Integrality: $v_i\le d$ and $p_i\mid n$ imply
  $\prod_i p_i^{v_i}\mid n^d$").

PAPER ISSUE: none. -/
def exponentsIntegerStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d → ∀ v ∈ allRankVectors n d,
    ∃ m : ℕ, (n : ℚ) ^ d * ∏ i, ((primeSeq n i : ℚ) ^ (-(v i : ℤ))) = (m : ℚ)

/-- **Encoding lemma for the exponents** (not a paper sentence; justifies the
`ℕ`-division used in `mainFormulaRHS`, `e19RHS`): for every
`v ∈ {0,…,d}^k` the `ℕ`-quotient `n ^ d / ∏ pᵢ ^ vᵢ` equals the rational
number `n^d ∏ pᵢ^{-vᵢ}` written in the paper, i.e. no truncation occurs.

Delta: stated for all `n`, `d` (the degenerate `n ∈ {0,1}` have `k = 0`, the
empty product, and the identity `n^d / 1 = n^d`); no hypothesis is needed.
PAPER ISSUE: none. -/
def exponentEncodingStatement : Prop :=
  ∀ n d : ℕ, ∀ v ∈ allRankVectors n d,
    (((n ^ d / ∏ i, primeSeq n i ^ v i : ℕ)) : ℚ)
      = (n : ℚ) ^ d * ∏ i, ((primeSeq n i : ℚ) ^ (-(v i : ℤ)))

/-- **Encoding bridge rank vectors ↔ divisors** (not a paper sentence): the
paper's rank-vector right-hand side of eq. (2) equals the divisor-reindexed
`ShiftSym.enumerationRHS` used by the frozen `enumerationStatement`
(`h = ∏ pᵢ^{vᵢ}`). Together with `enumeration_proved` this says that the
certified theorem is literally eq. (2).

Delta: stated for all `n d σ` (both sides vanish for `n ∈ {0,1}` or `d = 0`;
checked numerically for `1 ≤ n ≤ 60`, `d ≤ 4`, `σ ≤ 4`).
PAPER ISSUE: none. -/
def rankVectorReindexStatement : Prop :=
  ∀ n d σ : ℕ, mainFormulaRHS n d σ = enumerationRHS n d σ

/-! ## Corollary 4.4 (`cor:prime`, lines 440–447) -/

/-- The right-hand side of Corollary 4.4:
`∑_{r=1}^{d} (-1)^{r+1} p^{C(r,2)} [d r]_p σ^{p^{d-r}}`
(`ℕ`-subtraction `d - r` is exact on `1 ≤ r ≤ d`). -/
def cor44RHS (p d σ : ℕ) : ℤ :=
  ∑ r ∈ Icc 1 d,
    (-1 : ℤ) ^ (r + 1) * (p : ℤ) ^ (r.choose 2) * (gaussBinom p d r : ℤ) *
      (σ : ℤ) ^ (p ^ (d - r))

/-- **Corollary 4.4, main formula** (`cor:prime`, lines 440–443).

Paper (verbatim): "For prime $n=p$: $|S_{p^d}| = \sum_{r=1}^{d}(-1)^{r+1}\,
p^{\binom r2}\gaussbinom dr_p\,\sigma^{\,p^{d-r}}$."

Delta: the hypotheses `1 ≤ d`, `1 ≤ σ` are inherited from Theorem 4.3 (the
corollary does not restate them); alphabet `Fin σ`; `[d r]_p` = `gaussBinom`;
equation in `ℤ`. PAPER ISSUE: none. -/
def cor44GeneralStatement : Prop :=
  ∀ p d σ : ℕ, p.Prime → 1 ≤ d → 1 ≤ σ → (numSS p d σ : ℤ) = cor44RHS p d σ

/-- **Corollary 4.4, `d = 1`** (line 443): "In particular $|S_p|=\sigma$
($d=1$)".

Delta: `1 ≤ σ` inherited from Theorem 4.3; equation in `ℕ`.
PAPER ISSUE: none. -/
def cor44d1Statement : Prop :=
  ∀ p σ : ℕ, p.Prime → 1 ≤ σ → numSS p 1 σ = σ

/-- **Corollary 4.4, `d = 2`** (line 444): "$|S_{p^2}|=(p{+}1)\sigma^p-p
\sigma$ ($d=2$, \cite[Cor.~E.20]{banda2019})".

Delta: `1 ≤ σ` inherited; equation in `ℤ` (the right side is a difference).
PAPER ISSUE: none. -/
def cor44d2Statement : Prop :=
  ∀ p σ : ℕ, p.Prime → 1 ≤ σ →
    (numSS p 2 σ : ℤ) = ((p : ℤ) + 1) * (σ : ℤ) ^ p - (p : ℤ) * σ

/-- **Corollary 4.4, `d = 3`** (lines 445–446): "and $|S_{p^3}|=(p^2{+}p{+}1)
\sigma^{p^2}-p(p^2{+}p{+}1)\sigma^{p} +p^3\sigma$."

Delta: `1 ≤ σ` inherited; equation in `ℤ`. PAPER ISSUE: none. -/
def cor44d3Statement : Prop :=
  ∀ p σ : ℕ, p.Prime → 1 ≤ σ →
    (numSS p 3 σ : ℤ)
      = ((p : ℤ) ^ 2 + p + 1) * (σ : ℤ) ^ (p ^ 2)
        - (p : ℤ) * ((p : ℤ) ^ 2 + p + 1) * (σ : ℤ) ^ p + (p : ℤ) ^ 3 * σ

/-- **Corollary 4.4** (`cor:prime`), the whole statement: conjunction of the
general formula and the three displayed special cases. -/
def cor44Statement : Prop :=
  cor44GeneralStatement ∧ cor44d1Statement ∧ cor44d2Statement ∧ cor44d3Statement

/-- **[banda2019, Corollary E.20] as stated there** (cited by Corollary 4.4
for `d = 2`). 2019 paper (verbatim, Appendix E): "Corollary E.20 Let n = p, where
p is a prime. Then |S_{n×n}| = |Σ|^n (n + 1) − |Σ|n."

Delta: `|Σ| = σ`, alphabet `Fin σ`, `σ ≥ 1` (the 2019 paper puts no
hypothesis on `Σ`; a state set is nonempty); `S_{n×n}` = `numSS n 2 σ`.
The citation claim of Corollary 4.4 is that this is the `d = 2` case, which
it is verbatim up to commutativity. PAPER ISSUE: none. -/
def banda2019CorE20Statement : Prop :=
  ∀ n σ : ℕ, n.Prime → 1 ≤ σ →
    (numSS n 2 σ : ℤ) = (σ : ℤ) ^ n * ((n : ℤ) + 1) - (σ : ℤ) * n

/-! ## Remark 4.5 (`rem:boundary`, lines 449–463) -/

/-- Number of **aperiodic** configurations, `ac(A;Σ) = |{s : Stab(s) = {0}}|`
(Castillo-Ramirez–Gadouleau's definition, used by Remark 4.5(i) and §4.3:
"ac(G;A) := |{x ∈ A^G : G_x = {e}}|"). Alphabet `Fin σ`. -/
noncomputable def acount (n d σ : ℕ) : ℕ :=
  Nat.card {s : Config n d (Fin σ) // stab s = ⊥}

/-- **Remark 4.5(i), complement form** (line 450): "In complement form
($\mathrm{ac}=\sigma^N-|S|$)".

The paper uses the equation `ac = σ^N − |S|` as the definition of the
complement form; since `acount` is defined literally (trivial stabilizer),
the equation is a claim. Delta: `N = n^d`; hypotheses are those of the
paper's model (`n ≥ 2`, `d ≥ 1`, `σ ≥ 1` for counting); equation in `ℤ`.
PAPER ISSUE: none. -/
def acComplementStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 1 ≤ σ →
    (acount n d σ : ℤ) = (σ : ℤ) ^ (n ^ d) - numSS n d σ

/-- The right-hand side of [cg2017, Lemma 7(iv)]:
`q^{p^m} + ∑_{r=1}^{m} (-1)^r q^{p^{m-r}} p^{r(r-1)/2} [m r]_p`
(`r(r-1)/2` as the `ℕ`-quotient `r * (r - 1) / 2`, exact since `r(r-1)` is
even; it equals `C(r,2)`). -/
def cgLemma7ivRHS (p m q : ℕ) : ℤ :=
  (q : ℤ) ^ (p ^ m) +
    ∑ r ∈ Icc 1 m,
      (-1 : ℤ) ^ r * (q : ℤ) ^ (p ^ (m - r)) * (p : ℤ) ^ (r * (r - 1) / 2) *
        (gaussBinom p m r : ℤ)

/-- **[cg2017, Lemma 7(iv)] as stated there** (cited by Remark 4.5(i)).
CG (verbatim, arXiv:1610.00532 §4 "Aperiodic Configurations"): "Lemma 7. Let G be a finite group of order n ≥ 2 and A a finite
set of size q ≥ 2. … (iv) If G ≅ Z_p^m is an elementary abelian group, then
ac(Z_p^m; A) = q^{p^m} + Σ_{r=1}^m (−1)^r q^{p^{m−r}} p^{r(r−1)/2} [m r]_p,
where [m r]_p is the Gaussian binomial coefficient: [m r]_p :=
(1 − p^m)(1 − p^{m−1})…(1 − p^{m−r+1}) / ((1 − p^r)(1 − p^{r−1})…(1 − p))."

Delta: `G = Z_p^m` is the lattice `Lat p m = (ZMod p)^m` itself (no abstract
isomorphism); `A = Fin q`; `ac` = `acount` (trivial stabilizer for the
translation action `τ_v s(u) = s(u+v)`; CG's right action has the same
stabilizers); "order ≥ 2" is `1 ≤ m`; the Gaussian binomial is the q-Pascal
`gaussBinom` (equal to CG's product). PAPER ISSUE: none. -/
def cgLemma7ivStatement : Prop :=
  ∀ p m q : ℕ, p.Prime → 1 ≤ m → 2 ≤ q → (acount p m q : ℤ) = cgLemma7ivRHS p m q

/-- **Remark 4.5(i), the attribution identity** (lines 450–452): "In
complement form ($\mathrm{ac}=\sigma^N-|S|$), Corollary~\ref{cor:prime} is
Lemma~7(iv) of Castillo-Ramirez and Gadouleau \cite{cg2017}".

Formalized (checkable content): `σ^{p^d}` minus the right side of
Corollary 4.4 is the right side of CG Lemma 7(iv) with `m = d`, `q = σ`.
Delta: restricted to the common scope of both results (`d ≥ 1`; CG's
`q ≥ 2`); the identity is between closed forms (the counting content is in
`cor44GeneralStatement`, `cgLemma7ivStatement`, `acComplementStatement`).
PAPER ISSUE: none. -/
def remark45iIdentityStatement : Prop :=
  ∀ p d σ : ℕ, p.Prime → 1 ≤ d → 2 ≤ σ →
    (σ : ℤ) ^ (p ^ d) - cor44RHS p d σ = cgLemma7ivRHS p d σ

/-- **Remark 4.5(i)**, mathematical content as a conjunction (the remaining
sentences of (i) are bibliographic, see the group report). -/
def remark45iStatement : Prop :=
  acComplementStatement ∧ cgLemma7ivStatement ∧ remark45iIdentityStatement

/-- **Remark 4.5(ii), `n = 1`** (line 455): "$n=1$: both sides vanish."

Formalized: `|S_{1^d}| = 0` and the right side of eq. (2) at `n = 1` (an
empty sum: `k = ω(1) = 0`, so `{0,…,d}^0 ∖ {0} = ∅`) is `0`.
Delta: `d ≥ 1`, `σ ≥ 1` as in Theorem 4.3 (only `n ≥ 2` is relaxed); the
paper's model fixes `n ≥ 2`, the remark extends both sides to `n = 1`, where
`Lat 1 d` has the single element `0`. PAPER ISSUE: none. -/
def remark45n1Statement : Prop :=
  ∀ d σ : ℕ, 1 ≤ d → 1 ≤ σ → numSS 1 d σ = 0 ∧ mainFormulaRHS 1 d σ = 0

/-- `lines(F_p^d)`: the 1-dimensional subspaces of `F_p^d = (ZMod p)^d`
(paper Lemma 4.1). -/
noncomputable def linesFp (p d : ℕ) [NeZero p] : Finset (Submodule (ZMod p) (Fin d → ZMod p)) :=
  @Finset.filter _ (fun L : Submodule (ZMod p) (Fin d → ZMod p) => Module.finrank (ZMod p) L = 1)
    (Classical.decPred _) (@Finset.univ _ (Fintype.ofFinite _))

/-- `c_r(p) := ∑_{J ⊆ lines(F_p^d), rk J = r} (-1)^{|J|}` (paper eq. (1),
the DEFINITION, not the closed form), where `rk J` is the dimension of the
span of the lines in `J` (`J.sup id`). -/
noncomputable def crSigned (p d r : ℕ) [NeZero p] : ℤ :=
  ∑ J ∈ @Finset.filter _
      (fun J : Finset (Submodule (ZMod p) (Fin d → ZMod p)) =>
        Module.finrank (ZMod p) ↥(J.sup id) = r)
      (Classical.decPred _) (linesFp p d).powerset,
    (-1 : ℤ) ^ J.card

/-- **Remark 4.5(ii), the per-prime identity** (lines 455–456): "the per-prime
identity $\sum_{r=0}^d c_r(p)=0$".

Delta: `c_r(p)` is the signed spanning-set count of eq. (1) as DEFINED
(`crSigned`); `d ≥ 1` (for `d = 0` the sum is `1`, and the remark is made
inside Theorem 4.3's scope `d ≥ 1`). PAPER ISSUE: none. -/
def perPrimeIdentityStatement : Prop :=
  ∀ (p d : ℕ) [NeZero p], p.Prime → 1 ≤ d → ∑ r ∈ range (d + 1), crSigned p d r = 0

/-- **Remark 4.5(ii), per-prime identity in closed form** (lines 455–456 combined
with the evaluation of eq. (1), `c_r(p) = (-1)^r p^{C(r,2)} [d r]_p`): the
form in which the identity is actually used for the right side of eq. (2).

Delta: as for `perPrimeIdentityStatement`. PAPER ISSUE: none. -/
def perPrimeIdentityClosedStatement : Prop :=
  ∀ p d : ℕ, p.Prime → 1 ≤ d →
    ∑ r ∈ range (d + 1), (-1 : ℤ) ^ r * (p : ℤ) ^ (r.choose 2) * (gaussBinom p d r : ℤ) = 0

/-- **Remark 4.5(ii), `σ = 1`, right side** (lines 455–456): "$\sigma=1$: the
per-prime identity $\sum_{r=0}^d c_r(p)=0$ makes the right side $1$,
correctly."

Formalized: the right side of eq. (2) at `σ = 1` equals `1`.
Delta: `n ≥ 2`, `d ≥ 1` (Theorem 4.3's scope). PAPER ISSUE: none. -/
def remark45sigma1RHSStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d → mainFormulaRHS n d 1 = 1

/-- **Remark 4.5(ii), `σ = 1`, "correctly"**: the left side is also `1` (the
unique configuration over a one-letter alphabet is constant, hence fixed by
every translation, and `n ≥ 2` provides a nonzero one).

Delta: `n ≥ 2`, `d ≥ 1`. PAPER ISSUE: none. -/
def remark45sigma1LHSStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d → numSS n d 1 = 1

/-- The coefficient `r(i)` of [banda2019, Thm E.19], as a function of
`pᵢ` and `vᵢ ∈ {0,1,2}`: `1` if `vᵢ = 0`, `pᵢ + 1` if `vᵢ = 1`, `pᵢ` if
`vᵢ = 2`. (E.19 only defines `r(i)` for `vᵢ ≤ 2`; the value `0` for `vᵢ > 2`
is never used.) -/
def e19r (p v : ℕ) : ℕ :=
  if v = 0 then 1 else if v = 1 then p + 1 else if v = 2 then p else 0

/-- The right-hand side of [banda2019, Thm E.19]:
`∑_{0 ◁ v ⊴ 2} (-1)^{1+|v|} |Σ|^{g(v)} ∏_{i=1}^k r(i)`, `g(v) = n² ∏ pᵢ^{-vᵢ}`,
where `v ⊴ w` is coordinatewise `≤` and `v ◁ w` means `v ⊴ w ∧ v ≠ w`; so
`0 ◁ v ⊴ 2` is `v ∈ {0,1,2}^k`, `v ≠ 0`. `g(v)` is the `ℕ`-quotient
`n ^ 2 / ∏ pᵢ ^ vᵢ` (exact). -/
def e19RHS (n σ : ℕ) : ℤ :=
  ∑ v ∈ (Fintype.piFinset fun _ : Fin n.primeFactors.card => Finset.range 3).filter
      (fun v => v ≠ 0),
    (-1 : ℤ) ^ (1 + ∑ i, v i) * (σ : ℤ) ^ (n ^ 2 / ∏ i, primeSeq n i ^ v i) *
      ∏ i, (e19r (primeSeq n i) (v i) : ℤ)

/-- **[banda2019, Theorem E.19] as stated there** (cited by Remark 4.5(ii)).
2019 paper (verbatim, Appendix E): "Theorem E.19 Let n = ∏_{i=1}^k p_i^{α_i} be the
prime factorization of n, where k = ω(n), the number of distinct prime
factors of n. Then |S_{n×n}| = Σ_{0◁v⊴2} (−1)^{1+|v|} |Σ|^{g(v)} ∏_{i=1}^k r(i)
where g(v) = n² ∏_{i=1}^k p_i^{−v_i} and r(i) = 1 if v_i = 0, p_i + 1 if
v_i = 1, p_i if v_i = 2." Notation (2019, paragraph preceding Eq. (17), verbatim): "given any v, w ∈
Z^k, we write v ⊴ w whenever the coordinates satisfy v_i ≤ w_i for every i
(1 ≤ i ≤ k). We write v ◁ w if v ⊴ w and v ≠ w. We denote the sum of the
coordinates by |v| = Σ_{i=1}^k v_i, and for any m ∈ Z, we write m for the
k-tuple whose coordinates all equal m."

Delta: `n ≥ 1` (the 2019 paper takes any natural `n` and remarks that the
1×1 lattice has no symmetry — both sides are then `0`); `|Σ| = σ ≥ 1`,
alphabet `Fin σ`; primes indexed increasingly (the sum is order-independent);
`g(v)` as exact `ℕ`-quotient. PAPER ISSUE: none. -/
def banda2019ThmE19Statement : Prop :=
  ∀ n σ : ℕ, 1 ≤ n → 1 ≤ σ → (numSS n 2 σ : ℤ) = e19RHS n σ

/-- **Remark 4.5(ii), `d = 2`, coefficient level**: for `v ∈ {0,1,2}`,
`r_2(p,v)` is E.19's `r(i)`, i.e. `1, p+1, p` (also asserted in Definition 4.2,
group 03). Delta: `p` prime (where `r_d(p,v)` is defined).
PAPER ISSUE: none. -/
def remark45d2CoeffStatement : Prop :=
  ∀ p v : ℕ, p.Prime → v ≤ 2 → rdCoeff p v 2 = e19r p v

/-- **Remark 4.5(ii), `d = 2`** (lines 456–457): "$d=2$ recovers
\cite[Thm.~E.19]{banda2019} exactly."

Formalized: at `d = 2` the right side of eq. (2) (paper's rank-vector form)
equals the right side of E.19, for every `n`, `σ` in Theorem 4.3's scope; so
Theorem 4.3 at `d = 2` is E.19 on that scope (same index set
`{0,1,2}^k ∖ {0}`, same signs, same exponents `g(v)`, same coefficients by
`remark45d2CoeffStatement`). Delta: `n ≥ 2`, `σ ≥ 1` (Theorem 4.3's scope;
for `n = 1` both sums are empty). PAPER ISSUE: none. -/
def remark45d2FormulaStatement : Prop :=
  ∀ n σ : ℕ, 2 ≤ n → 1 ≤ σ → mainFormulaRHS n 2 σ = e19RHS n σ

/-- The Moreau–Witt complement `σ^n − ∑_{m ∣ n} μ(m) σ^{n/m}` (`μ` the
arithmetic Möbius function `ArithmeticFunction.moebius`; `n/m` exact for
`m ∣ n`). `∑_{m∣n} μ(m) σ^{n/m}` is the classical number of primitive
(aperiodic) words of length `n`. -/
def moreauWittComplement (n σ : ℕ) : ℤ :=
  (σ : ℤ) ^ n - ∑ m ∈ n.divisors, ArithmeticFunction.moebius m * (σ : ℤ) ^ (n / m)

/-- **Remark 4.5(ii), `d = 1`, formula level** (lines 457–459): "$d=1$
recovers the classical count of words with nontrivial period
(Moreau--Witt complement \cite{moreau1872,witt1937})."

Formalized: the right side of eq. (2) at `d = 1` equals
`σ^n − ∑_{m∣n} μ(m) σ^{n/m}`. Delta: `n ≥ 2`, `σ ≥ 1` (Theorem 4.3's scope).
PAPER ISSUE: the wording "words with nontrivial period" is ambiguous; see
`classicalNonprimitiveCountStatement` (the formula-level identity frozen here
is unaffected). -/
def remark45d1FormulaStatement : Prop :=
  ∀ n σ : ℕ, 2 ≤ n → 1 ≤ σ → mainFormulaRHS n 1 σ = moreauWittComplement n σ

/-- **Remark 4.5(ii), `d = 1`, count level**: `|S_n| = σ^n − ∑_{m∣n} μ(m)
σ^{n/m}` (as requested in the group brief).

Delta: `n ≥ 1` (at `n = 1` both sides are `0`), `σ ≥ 1`; `|S_n|` =
`numSS n 1 σ`, configurations on `Z_n = (ZMod n)^1` (cyclic words).
PAPER ISSUE: none for this identity (it is the intended reading of the
paper's sentence; for the ambiguity of "words with nontrivial period" see
`classicalNonprimitiveCountStatement`). -/
def remark45d1CountStatement : Prop :=
  ∀ n σ : ℕ, 1 ≤ n → 1 ≤ σ → (numSS n 1 σ : ℤ) = moreauWittComplement n σ

/-- A word `w` of length `n` is **non-primitive** (a proper power) if it is
constant on the residue classes mod some proper divisor `t` of `n`, i.e.
`w = u^{n/t}` with `|u| = t` and `n/t ≥ 2`; equivalently, the cyclic word `w`
is fixed by a nonzero rotation. These are the words counted by the
complement of the Moreau–Witt primitive-word count. (Renamed from
`HasNontrivialPeriod` in repairer round 1, so that the Lean name does not
repeat the paper's ambiguous term; the body is unchanged. For `n ≥ 1`, the
divisibility `t ∣ n` forces `t ≥ 1`, so `% t` never meets `t = 0`.) -/
def IsNonPrimitive {n σ : ℕ} (w : Fin n → Fin σ) : Prop :=
  ∃ t : ℕ, t ∣ n ∧ t < n ∧ ∀ i j : Fin n, (i : ℕ) % t = (j : ℕ) % t → w i = w j

/-- **The classical count invoked by Remark 4.5(ii), `d = 1`** (lines
457–459): "$d=1$ recovers the classical count of words with nontrivial
period (Moreau--Witt complement \cite{moreau1872,witt1937})."

Formalized (intended reading): the number of NON-PRIMITIVE words of length
`n` over `σ` letters (proper powers `u^m`, `m ≥ 2`; `IsNonPrimitive`) is
`σ^n − ∑_{m∣n} μ(m) σ^{n/m}` (Moreau 1872 / Witt 1937, complement form).

Delta: words are `Fin n → Fin σ`; `n ≥ 1`, `σ ≥ 1`; `μ` =
`ArithmeticFunction.moebius`; equation in `ℤ`.

PAPER ISSUE: "words with nontrivial period" is ambiguous. Under the usual
combinatorics-on-words notion (Lothaire; Fine–Wilf), `t` with `1 ≤ t < n` is
a period of `w` if `w_i = w_{i+t}` for all valid `i`, `t` NOT required to
divide `n`; the number of such words differs from the Moreau–Witt complement
for every `n ≥ 3` (σ = 2: 4 vs 2 at `n = 3` — `aaa, bbb, aba, bab` vs
`aaa, bbb`; 10 vs 4 at `n = 4`; 20 vs 2 at `n = 5`; 44 vs 10 at `n = 6`),
so read that way the paper's sentence is false; only the parenthetical
"(Moreau–Witt complement)" fixes the intended meaning. The intended reading
— non-primitive words, equivalently cyclic words fixed by a nonzero rotation
— is the one formalized here (and `remark45d1CountStatement` is the cyclic
form). The paper should say: "$d=1$ recovers the classical count of
non-primitive words (proper powers $u^m$, $m\ge2$; equivalently cyclic words
fixed by a nontrivial rotation), the complement of the Moreau--Witt count of
primitive words". -/
def classicalNonprimitiveCountStatement : Prop :=
  ∀ n σ : ℕ, 1 ≤ n → 1 ≤ σ →
    (Nat.card {w : Fin n → Fin σ // IsNonPrimitive w} : ℤ) = moreauWittComplement n σ

/-- **Remark 4.5(ii)**, the whole mathematical content as a conjunction. -/
def remark45iiStatement : Prop :=
  remark45n1Statement ∧ perPrimeIdentityStatement ∧ perPrimeIdentityClosedStatement ∧
    remark45sigma1RHSStatement ∧ remark45sigma1LHSStatement ∧
    banda2019ThmE19Statement ∧ remark45d2CoeffStatement ∧ remark45d2FormulaStatement ∧
    remark45d1FormulaStatement ∧ remark45d1CountStatement ∧
    classicalNonprimitiveCountStatement

/-- OEIS A323863, "Number of n X n aperiodic binary arrays", with the entry's
comment (verbatim, fetched 2026-10-15): "An n X k matrix is aperiodic if all
n * k rotations of its sequence of rows and its sequence of columns are
distinct." An `n × n` binary array is a configuration
`Config n 2 (Fin 2)`; the `n²` combined row/column rotations are the
translations `τ_v`, `v ∈ (ZMod n)²`; "all distinct" is injectivity of
`v ↦ τ_v s`. -/
noncomputable def a323863 (n : ℕ) : ℕ :=
  Nat.card {s : Config n 2 (Fin 2) // Function.Injective fun v : Lat n 2 => shift v s}

/-- **A323863 is the complement of `|S_{n^2}|` at `σ = 2`** (implicit in
Remark 4.5(iii): "the complement of Corollary 4.4 appears … in OEIS A323863").

Delta: `n ≥ 1` (OEIS offset is 0; `n = 0` is outside the torus model).
PAPER ISSUE: none. -/
def a323863ComplementStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a323863 n : ℤ) = 2 ^ (n ^ 2) - numSS n 2 2

/-- **The OEIS A323863 formula line** cited by Remark 4.5(iii) (verbatim,
R. Israel, Feb 04 2019): "a(n) = 2^(n^2) - (n+1)*2^n + 2*n if n is prime".
Delta: `a(n)` = `a323863 n` (definition above). PAPER ISSUE: none. -/
def oeisIsraelFormulaStatement : Prop :=
  ∀ p : ℕ, p.Prime → (a323863 p : ℤ) = 2 ^ (p ^ 2) - ((p : ℤ) + 1) * 2 ^ p + 2 * p

/-- **Remark 4.5(iii)** (lines 460–462), checkable content: "For $d=2$,
$\sigma=2$, prime $n$, the complement of Corollary~\ref{cor:prime} appears as
an unproved formula line in OEIS A323863 \cite{oeisA323863}."

Formalized: `2^{p²}` minus Corollary 4.4's right side at `d = 2`, `σ = 2` is
exactly Israel's expression `2^{p²} − (p+1)2^p + 2p`. ("unproved" and the
location in OEIS are bibliographic.) PAPER ISSUE: none. -/
def remark45iiiIdentityStatement : Prop :=
  ∀ p : ℕ, p.Prime → (2 : ℤ) ^ (p ^ 2) - cor44RHS p 2 2 = 2 ^ (p ^ 2) - ((p : ℤ) + 1) * 2 ^ p + 2 * p

/-- **Remark 4.5(iii)**, mathematical content as a conjunction. -/
def remark45iiiStatement : Prop :=
  a323863ComplementStatement ∧ oeisIsraelFormulaStatement ∧ remark45iiiIdentityStatement

/-- **Remark 4.5** (`rem:boundary`), all mathematical content. -/
def remark45Statement : Prop :=
  remark45iStatement ∧ remark45iiStatement ∧ remark45iiiStatement

/-! ## §4.3 "Alternative derivation via the subgroup lattice" (lines 465–486)

Prose, but every factual claim in it is frozen here (the derivation's
conclusion is eq. (2) itself). -/

/-- All subgroups of a finite group, as a `Finset` (the summation range
"`K ≤ G`"). -/
noncomputable def allSubgroupsG (G : Type*) [Group G] [Finite G] : Finset (Subgroup G) :=
  @Finset.univ _ (Fintype.ofFinite _)

/-- The Möbius function `μ(H,K)` of the subgroup lattice `L(G)` of a finite
group (mathlib's `IncidenceAlgebra.mu`: `μ(a,a) = 1`,
`μ(a,b) = −∑_{a ≤ x < b} μ(a,x)` for `a < b`, `0` otherwise — the
definition quoted by CG2017 §4). -/
noncomputable def subgroupMuG (G : Type*) [Group G] [Finite G] (H K : Subgroup G) : ℤ :=
  letI : Fintype (Subgroup G) := Fintype.ofFinite _
  letI : DecidableLE (Subgroup G) := Classical.decRel _
  letI : DecidableLT (Subgroup G) := Classical.decRel _
  letI : DecidableEq (Subgroup G) := Classical.decEq _
  letI : LocallyFiniteOrder (Subgroup G) := Fintype.toLocallyFiniteOrder
  IncidenceAlgebra.mu ℤ H K

/-- `ac(G;A)` for a finite group `G` acting on `A^G` by translation
`(x·g)(h) = x(hg)` (the paper's `τ_v s(u) = s(u+v)` written
multiplicatively): the configurations whose stabilizer is `{e}`. -/
noncomputable def acG (G : Type*) [Group G] (q : ℕ) : ℕ :=
  Nat.card {x : G → Fin q // ∀ g : G, (∀ h : G, x (h * g) = x h) → g = 1}

/-- **§4.3, cited [cg2017, Lemma 7(i)]** (lines 468–472): "Castillo-Ramirez
and Gadouleau \cite[Lemma~7(i)]{cg2017} show that for any finite group $G$ of
order $N$ and $|A|=q\ge2$, the number of aperiodic configurations is
$\mathrm{ac}(G;A)=\sum_{K\le G}\mu(\{e\},K)\,q^{N/|K|}$, with $\mu$ the
M\"obius function of the subgroup lattice."

Delta: `G : Type` (universe 0 — every finite group is isomorphic to one
there); `A = Fin q`; right translation action (stabilizer counts do not depend
on the left/right convention); `N/|K|` as exact `ℕ`-quotient (Lagrange).

PAPER ISSUE (minor, citation scope; the claim itself is true): CG state
Lemma 7 for a finite group "of order n ≥ 2"; the paper attributes it to them
"for any finite group $G$ of order $N$", i.e. it drops `|G| ≥ 2`. The
extension is harmless and true — for the trivial group every configuration
is aperiodic and both sides equal `q` (`μ({e},{e}) q^{1/1} = q`) — but it is
not what CG prove. The paper should write "of order $N\ge2$" (or note that
the case $N=1$ is trivial). The Prop follows the paper, i.e. it is stated
without `|G| ≥ 2` (this is not a weakening: it is the paper's own, slightly
stronger, scope). -/
def cgLemma7iStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (q : ℕ), 2 ≤ q →
    (acG G q : ℤ) = ∑ K ∈ allSubgroupsG G,
      subgroupMuG G ⊥ K * (q : ℤ) ^ (Nat.card G / Nat.card K)

/-- All subgroups `K ≤ A` of the lattice `A = (ZMod n)^d`. -/
noncomputable def allSubgroups (n d : ℕ) [NeZero n] : Finset (AddSubgroup (Lat n d)) :=
  @Finset.univ _ (Fintype.ofFinite _)

/-- The Möbius function `μ(H,K)` of the subgroup lattice of `A = (ZMod n)^d`
(mathlib's `IncidenceAlgebra.mu` on `AddSubgroup (Lat n d)`). -/
noncomputable def subgroupMu (n d : ℕ) [NeZero n] (H K : AddSubgroup (Lat n d)) : ℤ :=
  letI : Fintype (AddSubgroup (Lat n d)) := Fintype.ofFinite _
  letI : DecidableLE (AddSubgroup (Lat n d)) := Classical.decRel _
  letI : DecidableLT (AddSubgroup (Lat n d)) := Classical.decRel _
  letI : DecidableEq (AddSubgroup (Lat n d)) := Classical.decEq _
  letI : LocallyFiniteOrder (AddSubgroup (Lat n d)) := Fintype.toLocallyFiniteOrder
  IncidenceAlgebra.mu ℤ H K

/-- **§4.3, CG Lemma 7(i) for `G = A`** (the instance the paper uses, in the
lattice's additive notation): `ac(A;Σ) = ∑_{K ≤ A} μ({0},K) σ^{N/|K|}`.

Delta: as for `cgLemma7iStatement`; `n ≥ 2`, `d ≥ 1` (paper model);
`σ ≥ 2` (CG's `q ≥ 2`); `[NeZero n]` is implied by `2 ≤ n` and only makes the
subgroup lattice a `Fintype`. PAPER ISSUE: none. -/
def acLatMobiusStatement : Prop :=
  ∀ (n d σ : ℕ) [NeZero n], 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    (acount n d σ : ℤ) = ∑ K ∈ allSubgroups n d,
      subgroupMu n d ⊥ K * (σ : ℤ) ^ (n ^ d / Nat.card K)

/-- The `p`-primary component `A_p` of `A = (ZMod n)^d`: elements `x` with
`p^k • x = 0` for some `k` (mathlib's `AddCommGroup.primaryComponent`). -/
def primComp (n d p : ℕ) : AddSubgroup (Lat n d) :=
  AddCommGroup.primaryComponent (Lat n d) p

/-- **§4.3, `A_p ≅ (Z/p^α Z)^d`** (lines 477–478): "On each $p$-group factor
$\A_p\cong(\ZZ/p^{\alpha}\ZZ)^d$".

Delta: `α = v_p(n)` (`n.factorization p`); isomorphism of additive groups.
PAPER ISSUE: none. -/
def primaryIsoStatement : Prop :=
  ∀ n d p : ℕ, 2 ≤ n → 1 ≤ d → p.Prime → p ∣ n →
    Nonempty (primComp n d p ≃+ (Fin d → ZMod (p ^ n.factorization p)))

/-- **§4.3, primary splitting of subgroups** (lines 472–473): "every
subgroup splits along the primary decomposition
($K=\bigoplus_p(K\cap\A_p)$: …)".

Formalized: `K = ⨆_{p ∣ n} (K ⊓ A_p)` and the family `(K ⊓ A_p)_{p ∣ n}` is
independent (the sum is direct). Delta: `p` ranges over `n.primeFactors`;
directness as mathlib's `iSupIndep`. PAPER ISSUE: none. -/
def subgroupSplitStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d → ∀ K : AddSubgroup (Lat n d),
    K = (⨆ p ∈ n.primeFactors, K ⊓ primComp n d p) ∧
      iSupIndep fun p : n.primeFactors => K ⊓ primComp n d (p : ℕ)

/-- **§4.3, primary components are multiples** (lines 473–475): "the primary
components of any $\mathbf x\in K$ are integer multiples of $\mathbf x$ by
CRT, hence lie in $K$".

Formalized: every `x ∈ A` is `∑_{p∣n} c_p • x` with integers `c_p` such that
`c_p • x ∈ A_p` (so these summands are the primary components of `x`, which
are unique by directness). Delta: stated for all `x ∈ A` (membership in `K`
then follows by closure; that inference is the paper's "hence lie in K").
PAPER ISSUE: none. -/
def primaryComponentsMultiplesStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d → ∀ x : Lat n d, ∃ c : ℕ → ℤ,
    (∀ p ∈ n.primeFactors, c p • x ∈ primComp n d p) ∧
      x = ∑ p ∈ n.primeFactors, c p • x

/-- **§4.3, the subgroup lattice is a direct product** (lines 475–476): "the
subgroup lattice is the direct product of the primary lattices".

Formalized: `K ↦ (K ⊓ A_p)_{p∣n}` is an order isomorphism from `L(A)` onto
`∏_{p∣n} L(A_p)`: it reflects and preserves `≤`, and every family
`(L_p ≤ A_p)_p` is attained. Delta: `L(A_p)` is represented by the subgroups
of `A` below `A_p`. PAPER ISSUE: none. -/
def subgroupLatticeProductStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d →
    (∀ K K' : AddSubgroup (Lat n d),
        K ≤ K' ↔ ∀ p ∈ n.primeFactors, K ⊓ primComp n d p ≤ K' ⊓ primComp n d p) ∧
      (∀ L : ℕ → AddSubgroup (Lat n d), (∀ p ∈ n.primeFactors, L p ≤ primComp n d p) →
        ∃ K : AddSubgroup (Lat n d), ∀ p ∈ n.primeFactors, K ⊓ primComp n d p = L p)

/-- The Möbius function `μ(H,K)` of the subgroup lattice `L(B)` of an
arbitrary finite additive group `B` (mathlib's `IncidenceAlgebra.mu`, built
exactly as `subgroupMu`, which is the case `B = Lat n d`; see the `rfl`
sanity check at the end of the file). Used for the primary lattices
`L(A_p)`, `B = ↥A_p` (the subgroup lattice of the group `A_p` itself). -/
noncomputable def addSubgroupMu (B : Type*) [AddGroup B] [Finite B] (H K : AddSubgroup B) : ℤ :=
  letI : Fintype (AddSubgroup B) := Fintype.ofFinite _
  letI : DecidableLE (AddSubgroup B) := Classical.decRel _
  letI : DecidableLT (AddSubgroup B) := Classical.decRel _
  letI : DecidableEq (AddSubgroup B) := Classical.decEq _
  letI : LocallyFiniteOrder (AddSubgroup B) := Fintype.toLocallyFiniteOrder
  IncidenceAlgebra.mu ℤ H K

/-- **§4.3, multiplicativity of `μ`** (lines 475–477): "the subgroup lattice
is the direct product of the primary lattices, and $\mu$ is multiplicative
across it \cite[Prop.~3.8.2]{stanley2012}".

Stanley, EC1 Prop. 3.8.2 (product theorem): for finite posets `P`, `Q`,
`μ_{P×Q}((s,t),(s',t')) = μ_P(s,s') μ_Q(t,t')`. Transported along the
lattice isomorphism `L(A) ≅ ∏_{p∣n} L(A_p)`, `K ↦ (K ∩ A_p)_p` (frozen as
`subgroupLatticeProductStatement`), "μ is multiplicative across it" says:
for ALL pairs of subgroups `H, K ≤ A`,
`μ_{L(A)}(H,K) = ∏_{p∣n} μ_{L(A_p)}(H ∩ A_p, K ∩ A_p)`.

Delta:
* the full two-variable form is frozen (repairer round 1; the first draft
  only froze the bottom row `H = ⊥`, which is the special case the
  derivation uses, and was rejected as a weakening);
* the left factor is the Möbius function of `L(A)` (`subgroupMu`); each
  right factor is the Möbius function of the primary lattice `L(A_p)`, i.e.
  of the subgroup lattice of the group `A_p = primComp n d p` itself
  (`addSubgroupMu ↥A_p`), evaluated at `H ∩ A_p` and `K ∩ A_p` viewed as
  subgroups of `A_p` (mathlib's `AddSubgroup.addSubgroupOf`: "view `H ⊓ K`
  as a subgroup of `K`");
* `p` ranges over `n.primeFactors`; for `H ≰ K` both sides are `0` (the
  left by definition of `μ`, the right because some factor has
  `H ∩ A_p ≰ K ∩ A_p`) — this case is included, not excluded;
* `[NeZero n]` is implied by `2 ≤ n` and only makes the lattices finite.
(Equivalent form, not separately frozen: each factor may be computed in
`L(A)` at `(H ⊓ A_p, K ⊓ A_p)`, because the interval `[H ∩ A_p, K ∩ A_p]` is
the same in `L(A_p)` and `L(A)`; the bottom row `H = ⊥` is the special case
used by the derivation.)

PAPER ISSUE: none. -/
def mobiusMultiplicativeStatement : Prop :=
  ∀ (n d : ℕ) [NeZero n], 2 ≤ n → 1 ≤ d → ∀ H K : AddSubgroup (Lat n d),
    subgroupMu n d H K = ∏ p ∈ n.primeFactors,
      addSubgroupMu ↥(primComp n d p)
        ((H ⊓ primComp n d p).addSubgroupOf (primComp n d p))
        ((K ⊓ primComp n d p).addSubgroupOf (primComp n d p))

/-- A subgroup `K` is **elementary abelian** (for the prime `p`) if `p • x = 0`
for all `x ∈ K`; for `K ≤ A_p` this is the usual notion, and it says exactly
that `K` lies in the `p`-torsion `A[p]`. -/
def IsElemAbelian {n d : ℕ} (p : ℕ) (K : AddSubgroup (Lat n d)) : Prop :=
  ∀ x ∈ K, p • x = 0

/-- **§4.3, Hall's evaluation on `A_p`** (lines 477–482): "by the theorem of
Hall \cite{hall1933} (see \cite[Cor.~3.5]{hio1989}), $\mu(\{e\},K_p)$
vanishes unless $K_p$ is elementary abelian --- hence contained in the
$p$-torsion $\cong\FF_p^d$ --- in which case
$\mu(\{e\},K_p)=(-1)^{r}p^{\binom r2}$ for rank $r$".

Delta: `K_p` ranges over subgroups of `A` contained in `A_p`, `μ` computed in
`L(A)` (same intervals); "rank `r`" is `|K_p| = p^r`; "contained in the
`p`-torsion" is definitional for `IsElemAbelian` and `A[p] ≅ F_p^d` is
Lemma 3.3 (group 02, `ShiftSym.P02.torsionIsoStatement`), so neither is
restated. PAPER ISSUE: none. -/
def hallMobiusStatement : Prop :=
  ∀ (n d p : ℕ) [NeZero n], 2 ≤ n → 1 ≤ d → p.Prime → p ∣ n →
    ∀ K : AddSubgroup (Lat n d), K ≤ primComp n d p →
      (¬ IsElemAbelian p K → subgroupMu n d ⊥ K = 0) ∧
      (IsElemAbelian p K → ∀ r : ℕ, Nat.card K = p ^ r →
        subgroupMu n d ⊥ K = (-1 : ℤ) ^ r * (p : ℤ) ^ (r.choose 2))

/-- **§4.3, number of elementary abelian subgroups** (lines 482–483): "and
there are $\gaussbinom dr_p$ such subgroups".

Formalized: for `0 ≤ r ≤ d`, exactly `[d r]_p` subgroups `K ≤ A_p` are
elementary abelian of order `p^r`. Delta: `r ≤ d` (the ranks that occur);
classical decidability for the filter. PAPER ISSUE: none. -/
def elemAbelianCountStatement : Prop :=
  ∀ (n d p : ℕ) [NeZero n], 2 ≤ n → 1 ≤ d → p.Prime → p ∣ n → ∀ r : ℕ, r ≤ d →
    (@Finset.filter _ (fun K => K ≤ primComp n d p ∧ IsElemAbelian p K ∧ Nat.card K = p ^ r)
        (Classical.decPred _) (allSubgroups n d)).card = gaussBinom p d r

/-- **§4.3, conclusion** (lines 483–485): "Summing
$|S_{n^d}|=\sigma^N-\mathrm{ac}(\A;\Sigma)$ by rank vectors reproduces
\eqref{eq:main-formula}."

Formalized (the formula-level content): `σ^N − ∑_{K≤A} μ(0,K) σ^{N/|K|}` is
the right side of eq. (2) in the paper's rank-vector form. With
`acLatMobiusStatement` and `acComplementStatement` this yields Theorem 4.3
for `σ ≥ 2`. Delta: `N = n^d`; `n ≥ 2`, `d ≥ 1`, `σ ≥ 1` (Theorem 4.3's
scope; the identity does not need CG's `σ ≥ 2`). PAPER ISSUE: none. -/
def secondDerivationSumStatement : Prop :=
  ∀ (n d σ : ℕ) [NeZero n], 2 ≤ n → 1 ≤ d → 1 ≤ σ →
    (σ : ℤ) ^ (n ^ d) - ∑ K ∈ allSubgroups n d,
        subgroupMu n d ⊥ K * (σ : ℤ) ^ (n ^ d / Nat.card K)
      = mainFormulaRHS n d σ

/-- **§4.3**, all its mathematical claims as a conjunction. -/
def secondDerivationStatement : Prop :=
  cgLemma7iStatement ∧ acLatMobiusStatement ∧ primaryIsoStatement ∧
    subgroupSplitStatement ∧ primaryComponentsMultiplesStatement ∧
    subgroupLatticeProductStatement ∧ mobiusMultiplicativeStatement ∧
    hallMobiusStatement ∧ elemAbelianCountStatement ∧ secondDerivationSumStatement

/-! ## §4.4 reference values (lines 488–500)

The verification-log sentence of §4.4 (lines 490–496: "(L1) definition-level
brute force over all $\sigma^{n^d}$ configurations … and (L2) an independent
inclusion--exclusion … on 41 parameter triples covering $d\le4$, $n\le60$
… and $\sigma\le4$") is experimental provenance, NOT frozen
(NON-MATHEMATICAL). PAPER ISSUE (non-mathematical, recorded in the group
report): the logged run (research/experiments/verify_output.txt, Run 001)
does not support it as written — L1 ran on 29 triples only (all with
`n^d ≤ 16`), a further 15 distinct triples (up to `n = 60`) were L2-vs-formula
only, 44 distinct triples in all, not 41. The paper should say e.g. "(L1) on
the 29 triples with $n^d\le16$ and (L2) on all 44 triples …". -/

/-- **§4.4 reference value** `|S_{2^2}| = 8` (line 498).
Delta: `σ = 2` (see PAPER ISSUE). PAPER ISSUE: §4.4 does not state the
alphabet size for its reference values; they hold for `σ = 2` only (e.g.
`|S_{2^2}| = 21` for `σ = 3`). The paper should write "reference values
($\sigma=2$) include …". -/
def refValue22Statement : Prop := numSS 2 2 2 = 8

/-- **§4.4 reference value** `|S_{3^2}| = 26` (line 498), `σ = 2` (see
`refValue22Statement` for the PAPER ISSUE on the missing `σ = 2`). -/
def refValue32Statement : Prop := numSS 3 2 2 = 26

/-- **§4.4 reference value** `|S_{5^2}| = 182` (line 498), `σ = 2`. -/
def refValue52Statement : Prop := numSS 5 2 2 = 182

/-- **§4.4 reference value** `|S_{2^3}| = 72` (line 499), `σ = 2`. -/
def refValue23Statement : Prop := numSS 2 3 2 = 72

/-- **§4.4 reference value** `|S_{3^3}| = 6398` (line 499), `σ = 2`. -/
def refValue33Statement : Prop := numSS 3 3 2 = 6398

/-- **§4.4 reference value** `|S_{6^2}| = 801064` (line 499), `σ = 2`. -/
def refValue62Statement : Prop := numSS 6 2 2 = 801064

/-- **§4.4** (lines 496–499): "reference values include
$|S_{2^2}|=8,\quad |S_{3^2}|=26,\quad |S_{5^2}|=182,\quad |S_{2^3}|=72,\quad
|S_{3^3}|=6398,\quad |S_{6^2}|=801064$." All six, at `σ = 2`.
PAPER ISSUE: missing "σ = 2" (see `refValue22Statement`). -/
def referenceValuesStatement : Prop :=
  refValue22Statement ∧ refValue32Statement ∧ refValue52Statement ∧
    refValue23Statement ∧ refValue33Statement ∧ refValue62Statement

/-! ## Table 1 (paper lines 502–517)

Not frozen here: Table 1 is in group 03's range and is frozen there as
`ShiftSym.P03.table1Statement` (rows `ShiftSym.P03.table1Row{1,2,3,4}Statement`,
all 14 entries). The duplicate copy formerly in this file was removed in
repairer round 1 (reviewer cleanup: "Table 1 is duplicated with S03"). The
`#eval` below still cross-checks the table entries numerically. -/

/-! ## Sanity checks (display-only `#eval`s and kernel-checked instances;
none of them proves a frozen `Prop`) -/

-- primes of 60 in increasing order: [2, 3, 5]
#eval List.ofFn (primeSeq 60)
-- reference values through the rank-vector RHS: 8, 26, 182, 72, 6398, 801064
#eval [mainFormulaRHS 2 2 2, mainFormulaRHS 3 2 2, mainFormulaRHS 5 2 2,
       mainFormulaRHS 2 3 2, mainFormulaRHS 3 3 2, mainFormulaRHS 6 2 2]
-- rank-vector form = divisor form (Lean `enumerationRHS`), n ≤ 30, d ≤ 3, σ ≤ 3: true
#eval (List.range 31).all fun n => (List.range 4).all fun d => (List.range 4).all fun s =>
  mainFormulaRHS n d s == enumerationRHS n d s
-- n = 1: right side vanishes (d ≤ 4, σ ≤ 4): true
#eval (List.range 5).all fun d => (List.range 5).all fun s => mainFormulaRHS 1 d s == 0
-- σ = 1: right side is 1 (2 ≤ n ≤ 40, 1 ≤ d ≤ 3): true
#eval (List.range 39).all fun m => (List.range 3).all fun e => mainFormulaRHS (m + 2) (e + 1) 1 == 1
-- d = 2: rank-vector RHS = E.19 RHS (2 ≤ n ≤ 40, σ ≤ 3): true
#eval (List.range 39).all fun m => (List.range 4).all fun s => mainFormulaRHS (m + 2) 2 s == e19RHS (m + 2) s
-- d = 1: rank-vector RHS = Moreau–Witt complement (2 ≤ n ≤ 60, σ ≤ 4): true
#eval (List.range 59).all fun m => (List.range 5).all fun s =>
  mainFormulaRHS (m + 2) 1 s == moreauWittComplement (m + 2) s
-- Corollary 4.4 vs rank-vector RHS and closed forms, p ∈ {2,3,5,7}: true
#eval [2, 3, 5, 7].all fun p : ℕ => (List.range 4).all fun s : ℕ =>
  (List.range 4).all (fun e => cor44RHS p (e + 1) s == mainFormulaRHS p (e + 1) s) &&
  cor44RHS p 1 s == s &&
  cor44RHS p 2 s == ((p : ℤ) + 1) * (s : ℤ) ^ p - (p : ℤ) * s &&
  cor44RHS p 3 s == ((p : ℤ) ^ 2 + p + 1) * (s : ℤ) ^ (p ^ 2)
      - (p : ℤ) * ((p : ℤ) ^ 2 + p + 1) * (s : ℤ) ^ p + (p : ℤ) ^ 3 * s
-- Remark 4.5(i): complement of Cor 4.4 = CG Lemma 7(iv), p ∈ {2,3,5}, d ≤ 4, σ ∈ {2,3}: true
#eval [2, 3, 5].all fun p : ℕ => (List.range 4).all fun e => [2, 3].all fun s : ℕ =>
  (s : ℤ) ^ (p ^ (e + 1)) - cor44RHS p (e + 1) s == cgLemma7ivRHS p (e + 1) s
-- closed-form per-prime identity, p ∈ {2,3,5,7}, 1 ≤ d ≤ 6: true
#eval [2, 3, 5, 7].all fun p : ℕ => (List.range 6).all fun e =>
  (∑ r ∈ range (e + 2), (-1 : ℤ) ^ r * (p : ℤ) ^ (r.choose 2) * (gaussBinom p (e + 1) r : ℤ)) == 0

-- integrality (paper's rational form) and exactness of the ℕ-quotient, 2 ≤ n ≤ 40, 1 ≤ d ≤ 3: true
/-- Sanity helper (display only, not a statement): decides, for one `(n,d)`,
the integrality of every exponent (rational form) and the exactness of the
`ℕ`-quotient encoding. -/
private def sanityIntegralityCheck (n d : ℕ) : Bool :=
  decide (∀ v ∈ allRankVectors n d,
    ((n : ℚ) ^ d * ∏ i, ((primeSeq n i : ℚ) ^ (-(v i : ℤ)))).den = 1) &&
  decide (∀ v ∈ allRankVectors n d,
    (((n ^ d / ∏ i, primeSeq n i ^ v i : ℕ)) : ℚ)
      = (n : ℚ) ^ d * ∏ i, ((primeSeq n i : ℚ) ^ (-(v i : ℤ))))
#eval (List.range 39).all fun m => (List.range 3).all fun e => sanityIntegralityCheck (m + 2) (e + 1)
-- E.19 coefficients and (cross-check only; frozen in group 03) Table 1, primes below 30: true
#eval [2, 3, 5, 7, 11, 13, 17, 19, 23, 29].all fun p : ℕ =>
  ((List.range 3).all fun v => rdCoeff p v 2 == e19r p v) &&
  rdCoeff p 0 1 == 1 && rdCoeff p 1 1 == 1 &&
  rdCoeff p 0 3 == 1 && rdCoeff p 1 3 == p ^ 2 + p + 1 &&
  rdCoeff p 2 3 == p * (p ^ 2 + p + 1) && rdCoeff p 3 3 == p ^ 3 &&
  rdCoeff p 0 4 == 1 && rdCoeff p 1 4 == p ^ 3 + p ^ 2 + p + 1 &&
  rdCoeff p 2 4 == p * (p ^ 2 + 1) * (p ^ 2 + p + 1) &&
  rdCoeff p 3 4 == p ^ 3 * (p ^ 3 + p ^ 2 + p + 1) && rdCoeff p 4 4 == p ^ 6
-- Israel's OEIS expression = complement of Cor 4.4 (d = 2, σ = 2), primes below 30: true
#eval [2, 3, 5, 7, 11, 13, 17, 19, 23, 29].all fun p : ℕ =>
  (2 : ℤ) ^ (p ^ 2) - cor44RHS p 2 2 == 2 ^ (p ^ 2) - ((p : ℤ) + 1) * 2 ^ p + 2 * p

/- Kernel-checked instances (sanity only). -/
example : cor44RHS 2 2 2 = 8 := by decide
example : cor44RHS 3 3 2 = 6398 := by decide
example : cgLemma7ivRHS 2 2 2 = 8 := by decide
example : rdCoeff 2 2 4 = 2 * (2 ^ 2 + 1) * (2 ^ 2 + 2 + 1) := by decide
example : rdCoeff 3 3 4 = 3 ^ 3 * (3 ^ 3 + 3 ^ 2 + 3 + 1) := by decide
example : rdCoeff 5 2 3 = 5 * (5 ^ 2 + 5 + 1) := by decide
example : e19r 7 0 = 1 ∧ e19r 7 1 = 8 ∧ e19r 7 2 = 7 := by decide
example : (2 : ℤ) ^ (3 ^ 2) - cor44RHS 3 2 2 = 486 := by decide

/- Non-vacuity: the hypotheses of the frozen Props are satisfiable. -/
example : Nat.Prime 2 ∧ 2 ∣ 6 ∧ (2 : ℕ) ≤ 6 ∧ 1 ≤ 2 := by decide
example : (2 : ℕ) ≤ 2 ∧ 1 ≤ 1 ∧ 2 ≤ 2 := by decide
-- the Möbius function of the subgroup lattice is the genuine one: μ(K,K) = 1
example : subgroupMu 6 2 ⊥ ⊥ = 1 := by
  classical
  let _ : Fintype (AddSubgroup (Lat 6 2)) := Fintype.ofFinite _
  let _ : LocallyFiniteOrder (AddSubgroup (Lat 6 2)) := Fintype.toLocallyFiniteOrder
  unfold subgroupMu
  convert IncidenceAlgebra.mu_self (𝕜 := ℤ) (⊥ : AddSubgroup (Lat 6 2))
-- `subgroupMu` is literally `addSubgroupMu` at `B = Lat n d` (same construction)
example (n d : ℕ) [NeZero n] (H K : AddSubgroup (Lat n d)) :
    subgroupMu n d H K = addSubgroupMu (Lat n d) H K := rfl
-- the primary-lattice Möbius function is the genuine one on `L(A_p)`: μ(K,K) = 1
example : addSubgroupMu ↥(primComp 6 2 2) ⊥ ⊥ = 1 := by
  classical
  let _ : Fintype (AddSubgroup ↥(primComp 6 2 2)) := Fintype.ofFinite _
  let _ : LocallyFiniteOrder (AddSubgroup ↥(primComp 6 2 2)) := Fintype.toLocallyFiniteOrder
  unfold addSubgroupMu
  convert IncidenceAlgebra.mu_self (𝕜 := ℤ) (⊥ : AddSubgroup ↥(primComp 6 2 2))
-- `(H ⊓ A_p).addSubgroupOf A_p` is `H ∩ A_p` viewed inside `A_p`
example (n d p : ℕ) (H : AddSubgroup (Lat n d)) (x : primComp n d p) :
    x ∈ (H ⊓ primComp n d p).addSubgroupOf (primComp n d p) ↔ (x : Lat n d) ∈ H := by
  simp [AddSubgroup.mem_addSubgroupOf]
example : subgroupMuG (Equiv.Perm (Fin 3)) ⊥ ⊥ = 1 := by
  classical
  let _ : Fintype (Subgroup (Equiv.Perm (Fin 3))) := Fintype.ofFinite _
  let _ : LocallyFiniteOrder (Subgroup (Equiv.Perm (Fin 3))) := Fintype.toLocallyFiniteOrder
  unfold subgroupMuG
  convert IncidenceAlgebra.mu_self (𝕜 := ℤ) (⊥ : Subgroup (Equiv.Perm (Fin 3)))

end ShiftSym.P04
