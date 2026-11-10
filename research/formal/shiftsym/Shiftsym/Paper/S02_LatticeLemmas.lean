/-
Phase H, group 02 — paper Section 3 "Preliminaries"
(`shift_symmetry_d_dimensions.tex`, lines 257–350): the Gaussian-binomial
sentence of the section preamble and Lemmas 3.1–3.5.

FROZEN STATEMENTS ONLY. Every paper claim is a `def …Statement : Prop`; no
proofs of these Props live here (proofs go to `Paper/Proofs/P02_*.lean`).
The only definitions introduced are the paper's own objects:
* `gaussProd`      — the Gaussian binomial as the paper defines it (product
                     formula of the §3 preamble);
* `gcdAll`         — `gcd(l_1,…,l_d,n)` of Lemma 3.1;
* `orderPCyc`      — `𝓛_p`, the cyclic subgroups of order `p` (Lemma 3.4);
* `torsionCoord`   — the map `x = (n/p)·y ↦ y mod p` of Lemma 3.3, realised
                     with the canonical representative `y_i = val(x_i)/(n/p)`
                     (its agreement with EVERY representation `x = (n/p)·y`
                     is itself part of the frozen Lemma 3.3(b));
* `lineOf`, `rk`   — the line corresponding to `C ∈ 𝓛_p` and `rk J`.
The `p`-torsion `𝒜[p]` is the project's `latTorsion n d p` (Lemmas/Torsion.lean),
whose carrier is literally `{v | p • v = 0}`; `Fix(H)` is `fixedBy (Fin σ) H`
(Definitions.lean), `S_{n^d}` is `{s | IsShiftSymmetric s}`.

Standing hypotheses (paper Definition 2.1, line 201): "Fix integers n≥2, d≥1
and a finite alphabet Σ with σ=|Σ|≥2 (for counting statements σ=1 is also
allowed)". Hence counting statements carry `1 ≤ σ`, set identities `2 ≤ σ`.
The alphabet is `Fin σ` throughout (only `|Σ|` enters the paper).
-/
import Shiftsym.Paper.Common
import Shiftsym.Lemmas.Torsion

namespace ShiftSym.P02

open ShiftSym

/-! ## The Gaussian binomial of the §3 preamble -/

/-- The Gaussian binomial **as the paper defines it** (line 262–263):
`[d r]_q = ∏_{i=0}^{r-1} (q^{d-i} - 1)/(q^{i+1} - 1)`, evaluated in `ℚ` with
the integer exponent `d - i ∈ ℤ` (`zpow`), so no natural-number truncation
occurs. Well defined for every integer `q ≥ 2` (all denominators are
`q^{i+1} - 1 ≥ 1`). For `r > d` the factor `i = d` is `q^0 - 1 = 0`. -/
def gaussProd (q d r : ℕ) : ℚ :=
  ∏ i ∈ Finset.range r,
    (((q : ℚ) ^ ((d : ℤ) - (i : ℤ)) - 1) / ((q : ℚ) ^ (i + 1) - 1))

/-- **§3 preamble, Gaussian-binomial sentence** (paper lines 261–264).

Paper (verbatim): "Throughout, $n=\prod_{i=1}^{k}p_i^{\alpha_i}$ with
$p_1<\dots<p_k$ prime and $k=\omega(n)$, and $\gaussbinom dr_p=\prod_{i=0}^{r-1}
\frac{p^{d-i}-1}{p^{i+1}-1}$ is the Gaussian binomial, the number of
$r$-dimensional subspaces of $\FF_p^d$."

Formal: for prime `p` and `d ≥ 1`, the number of `r`-dimensional
`ZMod p`-subspaces of `Fin d → ZMod p` equals `gaussProd p d r`.

Delta:
* `𝔽_p^d` = `Fin d → ZMod p`; "r-dimensional" = `Module.finrank (ZMod p) W = r`;
  the count is `Nat.card` of the subtype of submodules (a finite type).
* The equality is stated in `ℚ` (the product formula is a priori a rational).
* `d ≥ 1` is the paper's standing hypothesis; `r` is NOT restricted (the paper
  leaves its range implicit): for `r > d` both sides are `0`, so allowing all
  `r` is an explicit, true extension, not a silent one.
* The first half of the sentence ("n = ∏ p_i^{α_i}, p_1<…<p_k, k = ω(n)") is
  notation, not a claim (see the report: NON-MATHEMATICAL).

PAPER ISSUE: none. -/
def gaussianCountStatement : Prop :=
  ∀ p d r : ℕ, p.Prime → 1 ≤ d →
    (Nat.card {W : Submodule (ZMod p) (Fin d → ZMod p) //
        Module.finrank (ZMod p) W = r} : ℚ) = gaussProd p d r

/-- **Definition-fidelity bridge (not a paper claim).** The project's
`gaussBinom` (q-Pascal recursion, `Statement.lean`, used in `Common.sopfD`,
`rdCoeff`, `enumerationRHS`, `lowerEnvelope`) agrees with the paper's
definition `gaussProd` for every integer `q ≥ 2` (the paper also evaluates
`[d r]_q` at composite `q = n` in `F_d(n,σ)`, §6), and all `d, r`.

Delta: stated in `ℚ`; `q ≥ 2` is exactly the range where the paper's product
has nonzero denominators. -/
def gaussBinomDefStatement : Prop :=
  ∀ q d r : ℕ, 2 ≤ q → (gaussBinom q d r : ℚ) = gaussProd q d r

/-! ## Lemma 3.1 (order of a translation) -/

/-- `gcd(l_1,…,l_d,n)` for integer coordinates `l_i` (paper Lemma 3.1):
the `gcd` of the absolute values `|l_i|` and `n`. -/
def gcdAll {d : ℕ} (l : Fin d → ℤ) (n : ℕ) : ℕ :=
  Nat.gcd (Finset.univ.gcd fun i => (l i).natAbs) n

/-- **Lemma 3.1, first equality** (`lem:order`, paper lines 266–272).

Paper (verbatim): "For $\mathbf 0\neq\vv=(l_1,\dots,l_d)\in\A$:
$|\langle\vv\rangle| = \lcm_i\bigl(n/\gcd(l_i,n)\bigr) =
n/\gcd(l_1,\dots,l_d,n)$, and
$|S_{n^d}(\vv)|=\sigma^{\,n^d/|\langle\vv\rangle|}
=\sigma^{\,n^{d-1}\gcd(l_1,\dots,l_d,n)}$."

Formal (this part): `|⟨v⟩| = lcm_i (n / gcd(l_i, n))`.

Delta:
* `⟨v⟩` = `AddSubgroup.zmultiples v`, `|·|` = `Nat.card`.
* The coordinates `l_i ∈ ℤ/nℤ` are read as integers: the statement is
  quantified over EVERY integer lift `l` of `v` (`(l i : ZMod n) = v i`), which
  is how `gcd(l_i, n)` is meaningful (it depends only on `l_i mod n`); the
  canonical lift `l_i = (v i).val` is one instance.
* `gcd(l_i, n)` = `Int.gcd (l i) n`; `n / gcd(l_i,n)` is `ℕ`-division, exact
  since `Int.gcd (l i) n ∣ n`; `lcm_i` = `Finset.univ.lcm` over `Fin d`
  (nonempty because `d ≥ 1`).
* Standing hypotheses `n ≥ 2`, `d ≥ 1`; `v ≠ 0` as in the paper.

PAPER ISSUE: none (only the notational looseness of applying `gcd` to residues,
resolved by the lift quantifier above). -/
def orderLcmStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d → ∀ v : Lat n d, v ≠ 0 →
    ∀ l : Fin d → ℤ, (∀ i, ((l i : ℤ) : ZMod n) = v i) →
      Nat.card (AddSubgroup.zmultiples v)
        = Finset.univ.lcm (fun i => n / Int.gcd (l i) (n : ℤ))

/-- **Lemma 3.1, second equality** (`lem:order`, paper lines 266–272; verbatim
quote in `orderLcmStatement`).

Formal (this part): `|⟨v⟩| = n / gcd(l_1,…,l_d,n)`.

Delta: as in `orderLcmStatement`; `gcd(l_1,…,l_d,n)` = `gcdAll l n`; the
`ℕ`-division is exact because `gcdAll l n ∣ n` (it is a `Nat.gcd _ n`).

PAPER ISSUE: none. -/
def orderGcdStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d → ∀ v : Lat n d, v ≠ 0 →
    ∀ l : Fin d → ℤ, (∀ i, ((l i : ℤ) : ZMod n) = v i) →
      Nat.card (AddSubgroup.zmultiples v) = n / gcdAll l n

/-- **Lemma 3.1, the count** (`lem:order`, paper lines 266–272; verbatim quote
in `orderLcmStatement`).

Formal (this part): `|⟨v⟩|` divides `n^d`, and
`|S_{n^d}(v)| = σ^{n^d/|⟨v⟩|}` and `|S_{n^d}(v)| = σ^{n^{d-1}·gcd(l_1,…,l_d,n)}`.

Delta:
* `S_{n^d}(v) = {s : τ_v s = s}` (paper Definition 2.2) is the set
  `{s : Config n d (Fin σ) | shift v s = s}`; `|·|` = `Nat.card`.
* `n^d/|⟨v⟩|` is `ℕ`-division; its exactness (`|⟨v⟩| ∣ n^d`, implicit in the
  paper since the exponent must be an integer) is made an explicit conjunct, so
  no truncation can hide. `n^{d-1}`: `d - 1` is truncated subtraction, exact
  because `d ≥ 1`.
* The paper's chain `a = b = c` is rendered as `a = b ∧ a = c` (values, not
  exponents: for `σ = 1` the exponents are not determined by the values).
* Counting statement: `σ ≥ 1` (paper Definition 2.1 allows `σ = 1` for
  counting statements); lifts `l` quantified as in `orderLcmStatement`.

PAPER ISSUE: none. -/
def orderCountStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 1 ≤ σ → ∀ v : Lat n d, v ≠ 0 →
    ∀ l : Fin d → ℤ, (∀ i, ((l i : ℤ) : ZMod n) = v i) →
      Nat.card (AddSubgroup.zmultiples v) ∣ n ^ d ∧
      Nat.card {s : Config n d (Fin σ) | shift v s = s}
          = σ ^ (n ^ d / Nat.card (AddSubgroup.zmultiples v)) ∧
      Nat.card {s : Config n d (Fin σ) | shift v s = s}
          = σ ^ (n ^ (d - 1) * gcdAll l n)

/-- **Lemma 3.1, whole statement** (`lem:order`): conjunction of its parts. -/
def orderLemmaStatement : Prop :=
  orderLcmStatement ∧ orderGcdStatement ∧ orderCountStatement

/-! ## Lemma 3.2 (fixed counts and joins) -/

/-- **Lemma 3.2(i)** (`lem:fix`, paper lines 282–289).

Paper (verbatim): "For a subgroup $H\le\A$ and any finite family
$H_1,\dots,H_\ell\le\A$: (i) $|\Fix(H)|=\sigma^{N/|H|}$; (ii)
$\bigcap_{a=1}^{\ell}\Fix(H_a)
=\Fix\bigl(\langle H_1\cup\dots\cup H_\ell\rangle\bigr)$."
(The paper's `enumerate` markup is rendered as "(i)", "(ii)".)

Formal (part (i)): `|H| ∣ n^d` and `|Fix(H)| = σ^{n^d / |H|}`.

Delta:
* `Fix(H)` = `fixedBy (Fin σ) H` (literally `{s | ∀ h ∈ H, shift h s = s}`),
  `N = n^d`, `|·|` = `Nat.card`.
* `N/|H|` is `ℕ`-division; its exactness (Lagrange, implicit in the paper) is an
  explicit conjunct.
* Counting statement: `σ ≥ 1` allowed (Definition 2.1).
* Overlap: `card_fixedBy_div` (Lemmas/FixedCount.lean) is the certified
  second conjunct for any finite alphabet; this Prop is the paper's own form.

PAPER ISSUE: none. -/
def fixCountStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 1 ≤ σ → ∀ H : AddSubgroup (Lat n d),
    Nat.card H ∣ n ^ d ∧ Nat.card (fixedBy (Fin σ) H) = σ ^ (n ^ d / Nat.card H)

/-- **Lemma 3.2(ii)** (`lem:fix`, paper lines 282–289; verbatim quote in
`fixCountStatement`).

Formal (part (ii)): for every finite family `H : Fin ℓ → AddSubgroup (Lat n d)`,
`⋂_a Fix(H_a) = Fix(⟨H_1 ∪ ⋯ ∪ H_ℓ⟩)` as sets of configurations.

Delta:
* The family `H_1,…,H_ℓ` is indexed by `Fin ℓ`; `ℓ = 0` is included (both
  sides are then all configurations, since `⟨∅⟩ = {0}`) — an explicit, true
  extension of "any finite family".
* `⟨H_1 ∪ ⋯ ∪ H_ℓ⟩` = `AddSubgroup.closure (⋃ a, (H a : Set _))` (the generated
  subgroup, literally).
* Not a counting statement: standing hypothesis `σ ≥ 2` kept (the identity holds
  for every alphabet; the hypothesis is kept only for fidelity).

PAPER ISSUE: none. -/
def fixJoinStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∀ (ℓ : ℕ) (H : Fin ℓ → AddSubgroup (Lat n d)),
      (⋂ a, fixedBy (Fin σ) (H a))
        = fixedBy (Fin σ) (AddSubgroup.closure (⋃ a, (H a : Set (Lat n d))))

/-- **Lemma 3.2, whole statement** (`lem:fix`): (i) ∧ (ii). -/
def fixLemmaStatement : Prop :=
  fixCountStatement ∧ fixJoinStatement

/-! ## Lemma 3.3 (torsion and lines) -/

/-- `𝓛_p`: the cyclic subgroups of order `p` of `𝒜 = (ℤ/nℤ)^d` (paper Lemma
3.3 "cyclic subgroups of order $p$", named $\mathcal L_p$ in Lemma 3.4).
"Cyclic" is rendered literally as `C = ⟨g⟩` for some `g`, "order `p`" as
`Nat.card C = p`. -/
def orderPCyc (n d p : ℕ) : Set (AddSubgroup (Lat n d)) :=
  {C | (∃ g : Lat n d, C = AddSubgroup.zmultiples g) ∧ Nat.card C = p}

/-- The map `x = (n/p)·y ↦ y mod p` of Lemma 3.3, realised with the canonical
representative: coordinate `i` is `val(x_i) / (n/p)` (natural division) reduced
mod `p`. For `x ∈ 𝒜[p]`, `val(x_i)` is a multiple of `n/p`, so this is `y_i`
for the representation `x_i = (n/p)·y_i`, `0 ≤ y_i < p`. That it agrees with
`y mod p` for EVERY integer representation `x = (n/p)·y` is part of the frozen
Lemma 3.3(b) (`torsionIsoStatement`), not an assumption. Off `𝒜[p]` the values
are irrelevant (every statement below only evaluates it on `𝒜[p]`). -/
def torsionCoord (n p d : ℕ) (x : Lat n d) : Fin d → ZMod p :=
  fun i => (((x i).val / (n / p) : ℕ) : ZMod p)

/-- The line of `𝔽_p^d` corresponding to a subgroup `C` (Lemma 3.3: "cyclic
subgroups of order $p$ correspond to lines"): the `𝔽_p`-span of the image of
`C ∩ 𝒜[p]` under the map of Lemma 3.3. (For `C ∈ 𝓛_p` the image is already a
line — that exactness is a conjunct of `torsionLinesStatement`.) -/
noncomputable def lineOf (n d p : ℕ) (C : AddSubgroup (Lat n d)) :
    Submodule (ZMod p) (Fin d → ZMod p) :=
  Submodule.span (ZMod p) (torsionCoord n p d '' {x : Lat n d | p • x = 0 ∧ x ∈ C})

/-- `rk J` (Lemma 3.3): "the dimension of the span of the corresponding
lines", i.e. `finrank` of `⨆_{C ∈ J} lineOf C`. -/
noncomputable def rk (n d p : ℕ) (J : Set (AddSubgroup (Lat n d))) : ℕ :=
  Module.finrank (ZMod p) ↥(⨆ C ∈ J, lineOf n d p C)

/-- **Lemma 3.3, torsion equality** (`lem:torsion`, paper lines 300–310).

Paper (verbatim): "Let $p\mid n$ be prime. The $p$-torsion
$\A[p]=\{\mathbf x:p\mathbf x=\mathbf 0\}$ equals
$\bigl(\tfrac np\ZZ/n\ZZ\bigr)^d$, and $\mathbf x=\tfrac np\,\mathbf
y\mapsto\mathbf y\bmod p$ is an isomorphism $\A[p]\cong\FF_p^d$ of
$\FF_p$-vector spaces. Under it, elements of order $p$ correspond to
nonzero vectors; cyclic subgroups of order $p$ correspond to lines, and
their number is $\gaussbinom d1_p=(p^d-1)/(p-1)$; and for a set $J$ of
order-$p$ cyclic subgroups, $|\langle\bigcup J\rangle|=p^{\rk J}$, where
$\rk J$ is the dimension of the span of the corresponding lines."

Formal (this part): `{x | p • x = 0} = {x | ∀ i, ∃ y : ℤ, x i = ((n/p)·y : ZMod n)}`.

Delta:
* `(n/p)ℤ/nℤ ≤ ℤ/nℤ` is the image of `(n/p)ℤ`, i.e. the residues of the integers
  `(n/p)·y`; `n/p` is `ℕ`-division, exact since `p ∣ n` is a hypothesis.
* `p𝐱` = `p • x` (`ℕ`-scalar multiplication on `Fin d → ZMod n`).
* Standing hypotheses `n ≥ 2`, `d ≥ 1`.

PAPER ISSUE: none. -/
def torsionEqStatement : Prop :=
  ∀ n d p : ℕ, 2 ≤ n → 1 ≤ d → p.Prime → p ∣ n →
    {x : Lat n d | p • x = 0}
      = {x : Lat n d | ∀ i, ∃ y : ℤ, x i = ((((n / p : ℕ) : ℤ) * y : ℤ) : ZMod n)}

/-- **Lemma 3.3, the isomorphism** (`lem:torsion`, paper lines 300–310;
verbatim quote in `torsionEqStatement`).

Formal (this part): (1) well-definedness and identification of the map: for
every `x` and every integer vector `y` with `x = (n/p)·y` (coordinatewise in
`ℤ/nℤ`), `torsionCoord x = y mod p`; (2) restricted to `𝒜[p]` (`latTorsion n d p`,
carrier `{x | p • x = 0}`) it is an additive bijection onto `𝔽_p^d`: there is an
`AddEquiv e : 𝒜[p] ≃+ (Fin d → ZMod p)` with `e x = torsionCoord x`.

Delta:
* `y` ranges over `ℤ^d` (the paper leaves its domain implicit; every
  `y ∈ (ℤ/nℤ)^d` lifts to `ℤ^d`).
* "isomorphism of `𝔽_p`-vector spaces" is rendered as an additive isomorphism:
  `𝒜[p]` carries no `ZMod p`-module instance in mathlib, its `𝔽_p`-structure is
  the unique one (`k • x = k.val • x`), and every additive map between
  `𝔽_p`-vector spaces is `𝔽_p`-linear (`AddMonoidHom.toZModLinearMap`); so `≃+`
  loses nothing.
* `torsionCoord` is the canonical-representative realisation of the paper's map;
  conjunct (1) is exactly the statement that the paper's formula determines it.

PAPER ISSUE: none. -/
def torsionIsoStatement : Prop :=
  ∀ n d p : ℕ, 2 ≤ n → 1 ≤ d → p.Prime → p ∣ n →
    (∀ (x : Lat n d) (y : Fin d → ℤ),
        (∀ i, x i = ((((n / p : ℕ) : ℤ) * y i : ℤ) : ZMod n)) →
          torsionCoord n p d x = fun i => ((y i : ℤ) : ZMod p)) ∧
    ∃ e : latTorsion n d p ≃+ (Fin d → ZMod p),
      ∀ x : latTorsion n d p, e x = torsionCoord n p d (x : Lat n d)

/-- **Lemma 3.3, elements of order `p`** (`lem:torsion`, paper lines 300–310;
verbatim quote in `torsionEqStatement`).

Formal (this part): every element of `𝒜` of order `p` lies in `𝒜[p]`, and for
`x ∈ 𝒜[p]`: `addOrderOf x = p ↔ torsionCoord x ≠ 0`. Together with the bijection
of `torsionIsoStatement` this is "elements of order $p$ correspond to nonzero
vectors".

Delta: order = `addOrderOf` in `𝒜` (equal to the order in the subgroup `𝒜[p]`).

PAPER ISSUE: none. -/
def torsionOrderStatement : Prop :=
  ∀ n d p : ℕ, 2 ≤ n → 1 ≤ d → p.Prime → p ∣ n →
    (∀ x : Lat n d, addOrderOf x = p → p • x = 0) ∧
    (∀ x : Lat n d, p • x = 0 → (addOrderOf x = p ↔ torsionCoord n p d x ≠ 0))

/-- **Lemma 3.3, cyclic subgroups of order `p` ↔ lines** (`lem:torsion`, paper
lines 300–310; verbatim quote in `torsionEqStatement`).

Formal (this part): `C ↦ lineOf C` is a bijection from `𝓛_p` onto the set of
1-dimensional subspaces of `𝔽_p^d`; moreover every `C ∈ 𝓛_p` lies in `𝒜[p]` and
`lineOf C` is exactly the image of `C` (for `x ∈ 𝒜[p]`:
`x ∈ C ↔ torsionCoord x ∈ lineOf C`), so the correspondence is "under" the
isomorphism of Lemma 3.3 and not an abstract equinumerosity.

Delta: "lines" = submodules of `Fin d → ZMod p` of `finrank` 1; bijection =
`Set.BijOn` (maps-to, injective on, surjective onto).

PAPER ISSUE: none. -/
def torsionLinesStatement : Prop :=
  ∀ n d p : ℕ, 2 ≤ n → 1 ≤ d → p.Prime → p ∣ n →
    Set.BijOn (lineOf n d p) (orderPCyc n d p)
        {W : Submodule (ZMod p) (Fin d → ZMod p) | Module.finrank (ZMod p) W = 1} ∧
    ∀ C ∈ orderPCyc n d p,
      (∀ x ∈ C, p • x = 0) ∧
      ∀ x : Lat n d, p • x = 0 → (x ∈ C ↔ torsionCoord n p d x ∈ lineOf n d p C)

/-- **Lemma 3.3, the line count** (`lem:torsion`, paper lines 300–310; verbatim
quote in `torsionEqStatement`).

Formal (this part): `|𝓛_p| = [d 1]_p` (paper's product definition `gaussProd`)
and `|𝓛_p| = (p^d − 1)/(p − 1)`, both in `ℚ`.

Delta: `|𝓛_p|` = `Nat.card` of the (finite) set `orderPCyc n d p`; the quotient
`(p^d−1)/(p−1)` is a rational division (no `ℕ` truncation possible).
Overlap: the certified `card_orderP_subgroups` (Lemmas/Lines.lean) counts the
order-`p` subgroups with the recursive `gaussBinom`; this Prop is the paper's
own form (cyclicity explicit, product formula).

PAPER ISSUE: none. -/
def torsionCountStatement : Prop :=
  ∀ n d p : ℕ, 2 ≤ n → 1 ≤ d → p.Prime → p ∣ n →
    (Nat.card (orderPCyc n d p) : ℚ) = gaussProd p d 1 ∧
    (Nat.card (orderPCyc n d p) : ℚ) = ((p : ℚ) ^ d - 1) / ((p : ℚ) - 1)

/-- **Lemma 3.3, joins of order-`p` subgroups** (`lem:torsion`, paper lines
300–310; verbatim quote in `torsionEqStatement`).

Formal (this part): for every set `J ⊆ 𝓛_p`,
`|⟨⋃ J⟩| = p ^ rk J` with `rk J = dim ⨆_{C ∈ J} lineOf C`.

Delta: `⟨⋃ J⟩` = `AddSubgroup.closure (⋃ C ∈ J, (C : Set _))`; `J` an arbitrary
`Set` (automatically finite); `J = ∅` included (`1 = p^0`), as in the paper's
"for a set $J$".

PAPER ISSUE: none. -/
def torsionJoinStatement : Prop :=
  ∀ n d p : ℕ, 2 ≤ n → 1 ≤ d → p.Prime → p ∣ n →
    ∀ J : Set (AddSubgroup (Lat n d)), J ⊆ orderPCyc n d p →
      Nat.card (AddSubgroup.closure (⋃ C ∈ J, (C : Set (Lat n d)))) = p ^ rk n d p J

/-- **Lemma 3.3, whole statement** (`lem:torsion`): conjunction of its six
parts (torsion equality, isomorphism, order-`p` elements, lines, line count,
joins). -/
def torsionLemmaStatement : Prop :=
  torsionEqStatement ∧ torsionIsoStatement ∧ torsionOrderStatement ∧
    torsionLinesStatement ∧ torsionCountStatement ∧ torsionJoinStatement

/-! ## Lemma 3.4 (completeness) -/

/-- **Lemma 3.4** (`lem:completeness`, paper lines 319–323).

Paper (verbatim): "Let $\mathcal L_p$ be the set of cyclic subgroups of order
$p$ of $\A$ and $\mathcal L=\bigcup_{p\mid n}\mathcal L_p$. Then
$S_{n^d}=\bigcup_{C\in\mathcal L}\Fix(C)$."

Formal: `{s | IsShiftSymmetric s} = ⋃_{p ∈ primeFactors n} ⋃_{C ∈ 𝓛_p} Fix(C)`.

Delta:
* `S_{n^d}` (Definition 2.2, `⋃_{v≠0} S_{n^d}(v)`) = `{s | IsShiftSymmetric s}`
  (`IsShiftSymmetric s := ∃ v ≠ 0, shift v s = s`, literally the union).
* "$p\mid n$" ranges over primes (the §3 convention "Let $p\mid n$ be prime");
  `n.primeFactors` = `{p | p.Prime ∧ p ∣ n}` for `n ≠ 0` (`Nat.mem_primeFactors`).
* `𝓛_p` = `orderPCyc n d p`; `Fix(C)` = `fixedBy (Fin σ) C`.
* Set identity, not a counting statement: standing hypothesis `σ ≥ 2` kept (the
  identity holds for every alphabet).
* Overlap: `isShiftSymmetric_iff_prime_order` (Lemmas/Completeness.lean) is the
  certified element form; this Prop is the paper's set form.

PAPER ISSUE: none. -/
def completenessStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    {s : Config n d (Fin σ) | IsShiftSymmetric s}
      = ⋃ p ∈ n.primeFactors, ⋃ C ∈ orderPCyc n d p, fixedBy (Fin σ) C

/-! ## Lemma 3.5 (multi-prime joins) -/

/-- **Delta justification for Lemma 3.5 (not a separate paper claim).** The
paper writes `J = \bigsqcup_{p ∣ n} J_p` (disjoint union). The sets `𝓛_p` for distinct
`p` are disjoint (a subgroup has one order), so the family form used in
`multiPrimeJoinStatement` loses nothing; this Prop records that fact. -/
def orderPCycDisjointStatement : Prop :=
  ∀ n d p q : ℕ, p ≠ q → Disjoint (orderPCyc n d p) (orderPCyc n d q)

/-- **Lemma 3.5** (`lem:joins`, paper lines 334–337).

Paper (verbatim): "Let $J=\bigsqcup_{p\mid n}J_p$ with
$J_p\subseteq\mathcal L_p$. Then
$\bigl|\langle\bigcup J\rangle\bigr|=\prod_{p\mid n}p^{\,\rk J_p}$."

Formal: for every family `Jf : ℕ → Set (AddSubgroup (Lat n d))` with
`Jf p ⊆ 𝓛_p` for every prime `p ∣ n`, and `J = ⋃_{p ∣ n} Jf p`:
`|⟨⋃ J⟩| = ∏_{p ∣ n} p ^ rk_p (Jf p)`.

Delta:
* The disjoint union `\bigsqcup` is rendered as the plain union of the family:
  the `𝓛_p` for distinct primes are disjoint (their members have different
  orders; frozen as `orderPCycDisjointStatement`), so the union is automatically
  disjoint and every `J ⊆ 𝓛` arises with `J_p = J ∩ 𝓛_p`; the values of `Jf` at
  non-prime-divisors are ignored.
* `p ∣ n` ranges over `n.primeFactors`; `rk J_p` = `rk n d p (Jf p)` (Lemma 3.3,
  computed in `𝔽_p^d`); empty `J_p` included (factor `p^0 = 1`).
* `⟨⋃ J⟩` = `AddSubgroup.closure` of the union of the carriers.
* Overlap: `card_univ_sup_of_torsion` (Lemmas/Primary.lean) is the certified
  coprime-torsion product rule used for this; this Prop is the paper's form.

PAPER ISSUE: none. -/
def multiPrimeJoinStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d →
    ∀ Jf : ℕ → Set (AddSubgroup (Lat n d)),
      (∀ p ∈ n.primeFactors, Jf p ⊆ orderPCyc n d p) →
        Nat.card (AddSubgroup.closure
            (⋃ p ∈ n.primeFactors, ⋃ C ∈ Jf p, (C : Set (Lat n d))))
          = ∏ p ∈ n.primeFactors, p ^ rk n d p (Jf p)

/-- **All of Section 3** (group 02): every frozen paper statement of the group
(the definition-fidelity bridge `gaussBinomDefStatement` is listed separately,
as it is not a paper claim). -/
def section3Statement : Prop :=
  gaussianCountStatement ∧ orderLemmaStatement ∧ fixLemmaStatement ∧
    torsionLemmaStatement ∧ completenessStatement ∧ multiPrimeJoinStatement

/-! ## Sanity checks (kernel-reducible, no proofs of the frozen Props)

The hypotheses are satisfiable (non-vacuity), and the computable sides evaluate
to the expected values on small instances. Exhaustive definition-level checks
of every Prop: `scratchpad/research/formal_ext/s02/bruteforce_s02.py`. -/

-- non-vacuity of the hypotheses
example : 2 ≤ 6 ∧ 1 ≤ 2 ∧ Nat.Prime 3 ∧ 3 ∣ 6 := by norm_num
example : (![2, 3] : Lat 6 2) ≠ 0 := by decide
example : ((((4 : ℤ) : ZMod 12)) = (4 : ZMod 12)) ∧ (((-3 : ℤ) : ZMod 12) = (9 : ZMod 12)) := by
  decide

-- `gaussProd` (paper definition) vs the project's `gaussBinom`
example : gaussProd 2 3 1 = 7 := by norm_num [gaussProd]
example : gaussProd 2 4 2 = 35 := by norm_num [gaussProd, Finset.prod_range_succ]
example : gaussProd 3 3 1 = 13 := by norm_num [gaussProd]
example : gaussProd 3 2 3 = 0 := by norm_num [gaussProd, Finset.prod_range_succ]
example : gaussProd 5 2 0 = 1 := by decide
example : (gaussBinom 2 4 2 : ℚ) = gaussProd 2 4 2 := by
  rw [show gaussBinom 2 4 2 = 35 by decide]; norm_num [gaussProd, Finset.prod_range_succ]
example : (gaussBinom 6 3 2 : ℚ) = gaussProd 6 3 2 := by
  rw [show gaussBinom 6 3 2 = 43 by decide]; norm_num [gaussProd, Finset.prod_range_succ]

-- Lemma 3.1, computable sides: v = (4, 9) ∈ (ℤ/12)², lift l = (4, -3):
-- lcm(12/4, 12/3) = 12 = 12/gcd(4,3,12); and v = (6, 3) ∈ (ℤ/12)²: lcm(2,4) = 4 = 12/3.
example : Finset.univ.lcm (fun i : Fin 2 => 12 / Int.gcd (![4, -3] i) (12 : ℤ)) = 12 := by
  decide
example : 12 / gcdAll ![4, -3] 12 = 12 := by decide
example : Finset.univ.lcm (fun i : Fin 2 => 12 / Int.gcd (![6, 3] i) (12 : ℤ)) = 4 := by
  decide
example : 12 / gcdAll ![6, 3] 12 = 4 := by decide
example : 12 / gcdAll ![18, -9] 12 = 4 := by decide

-- Lemma 3.3, the map `torsionCoord` on 𝒜 = (ℤ/6)², p = 3 (n/p = 2):
-- x = 2·(1, 2) = (2, 4) ↦ (1, 2); x = 2·(-1, 5) = (4, 4) ↦ (-1, 5) mod 3 = (2, 2).
example : torsionCoord 6 3 2 ![2, 4] = ![1, 2] := by decide
example : torsionCoord 6 3 2 ![4, 4] = ![2, 2] := by decide
-- |𝒜[3]| = 9 in (ℤ/6)² and |𝒜[2]| = 4 in (ℤ/4)²
example : (Finset.univ.filter fun x : Lat 6 2 => 3 • x = 0).card = 9 := by decide
example : (Finset.univ.filter fun x : Lat 4 2 => 2 • x = 0).card = 4 := by decide
-- `torsionCoord` is additive and injective on 𝒜[p] (computable core of 3.3(b)):
-- (ℤ/6)¹ with p = 3, and (ℤ/4)² with p = 2.
example : ∀ x y : Lat 6 1, 3 • x = 0 → 3 • y = 0 →
    torsionCoord 6 3 1 (x + y) = torsionCoord 6 3 1 x + torsionCoord 6 3 1 y := by decide
example : ∀ x y : Lat 4 2, 2 • x = 0 → 2 • y = 0 →
    torsionCoord 4 2 2 (x + y) = torsionCoord 4 2 2 x + torsionCoord 4 2 2 y := by decide
example : ∀ x y : Lat 4 2, 2 • x = 0 → 2 • y = 0 →
    torsionCoord 4 2 2 x = torsionCoord 4 2 2 y → x = y := by decide

end ShiftSym.P02
