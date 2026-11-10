/-
Phase H, group 03 — "MobiusCoefficients": paper §4.1 "The signed
spanning-set count" (Lemma 4.1 = `lem:mobius`, eq. `(cr)`), Definition 4.2
"Coefficient function", Table 1 (coefficients `r_d(p,v)` for `d ≤ 4`), and
Remark "Duality" of `shift_symmetry_d_dimensions.tex` (v3.1):
lines 351–396, 502–517, 1028–1033.

FROZEN STATEMENTS ONLY. Every paper claim is a `def …Statement : Prop`; no
proofs of these Props live here (proofs go to `Paper/Proofs/P03_*.lean`).

Objects introduced (each the paper's own definition, stated literally):
* `lines V`            — `lines(V)`: the 1-dimensional subspaces contained in `V`;
* `spanJ J`            — `span J`: the span of the union of the lines in `J`;
* `rkJ J`              — `rk J`: the dimension of `span J`;
* `signedSpanCount V`  — `f(V) = Σ_{J ⊆ lines(V), span J = V} (-1)^{|J|}`;
* `cr p d r`           — `c_r(p) = Σ_{J ⊆ lines(𝔽_p^d), rk J = r} (-1)^{|J|}`;
* `banda2019E19Coeff`  — the coefficient `r(i)` of Thm E.19 of the 2019 paper.
`μ` is mathlib's incidence-algebra Möbius function
`IncidenceAlgebra.mu ℤ` (Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean)
on the lattice `Submodule (ZMod p) (Fin d → ZMod p)` of subspaces of `𝔽_p^d`,
used directly (no stand-in); the only extra data are the finiteness instances
below (`LocallyFiniteOrder` is a `Subsingleton`, so the value of `μ` does not
depend on which instance is chosen).

The Gaussian binomial `[d r]_p` is the project's `gaussBinom p d r`
(`Statement.lean`, `q`-Pascal recurrence) and `r_d(p,v)` is the project's
`rdCoeff p v d = p^(v choose 2) * gaussBinom p d v` (`Statement.lean`) — the
very objects inside the certified `enumerationStatement`. Their agreement with
the paper's product formula / subspace count (§3 preamble, line 262) is frozen
by groups 01/02 (`gaussBinomProductFidelityStatement`, `gaussProd`); here it is
additionally `#eval`-checked on small values at the end of the file.

Standing hypotheses (paper Definition 2.1, line 201): `n ≥ 2`, `d ≥ 1`.
-/
import Shiftsym.Paper.Common

open scoped Classical

namespace ShiftSym.P03

open ShiftSym Module

/-! ## Finiteness instances for the subspace lattice of `𝔽_p^d`

All three are `scoped` (active only inside `ShiftSym.P03`). The `Fintype`
instance is literally `Fintype.ofFinite _`, i.e. definitionally the same as
the (global) instance of `Lemmas/Bridge.lean` up to proof irrelevance of the
`Finite` argument. -/

/-- The subspace lattice of `𝔽_p^d` is finite (`p ≠ 0`). -/
scoped instance instFiniteSubspace {p d : ℕ} [NeZero p] :
    Finite (Submodule (ZMod p) (Fin d → ZMod p)) :=
  Finite.of_injective (fun U => (U : Set (Fin d → ZMod p))) SetLike.coe_injective

noncomputable scoped instance instFintypeSubspace {p d : ℕ} [NeZero p] :
    Fintype (Submodule (ZMod p) (Fin d → ZMod p)) :=
  Fintype.ofFinite _

/-- Locally finite order structure on the (finite) subspace lattice, needed by
`IncidenceAlgebra.mu`. (`LocallyFiniteOrder` is a `Subsingleton`, so this
choice is immaterial.) -/
noncomputable scoped instance instLocallyFiniteOrderSubspace {p d : ℕ} [NeZero p] :
    LocallyFiniteOrder (Submodule (ZMod p) (Fin d → ZMod p)) :=
  LocallyFiniteOrder.ofFiniteIcc fun _ _ => Set.toFinite _

/-! ## The paper's objects -/

/-- `lines(V)` (paper line 354): "its set of `1`-dimensional subspaces" — the
subspaces `L` of `𝔽_p^d` with `dim L = 1` and `L ≤ V`. -/
noncomputable def lines {p d : ℕ} [NeZero p] (V : Submodule (ZMod p) (Fin d → ZMod p)) :
    Finset (Submodule (ZMod p) (Fin d → ZMod p)) :=
  Finset.univ.filter fun L => finrank (ZMod p) L = 1 ∧ L ≤ V

/-- `span J` (paper line 357): the subspace spanned by (the union of) the lines
in `J`, taken literally as `Submodule.span` of the union of their carriers. -/
noncomputable def spanJ {p d : ℕ} (J : Finset (Submodule (ZMod p) (Fin d → ZMod p))) :
    Submodule (ZMod p) (Fin d → ZMod p) :=
  Submodule.span (ZMod p) (⋃ L ∈ J, (L : Set (Fin d → ZMod p)))

/-- `rk J` (paper line 364, with the meaning fixed in Lemma 3.3, line 309:
"`rk J` is the dimension of the span of the corresponding lines"). -/
noncomputable def rkJ {p d : ℕ} (J : Finset (Submodule (ZMod p) (Fin d → ZMod p))) : ℕ :=
  finrank (ZMod p) (spanJ J)

/-- `f(V) := Σ_{J ⊆ lines(V), span J = V} (-1)^{|J|}` (paper lines 356–358),
the signed spanning-set count, in `ℤ`. -/
noncomputable def signedSpanCount {p d : ℕ} [NeZero p]
    (V : Submodule (ZMod p) (Fin d → ZMod p)) : ℤ :=
  ∑ J ∈ (lines V).powerset.filter (fun J => spanJ J = V), (-1 : ℤ) ^ J.card

/-- `c_r(p) := Σ_{J ⊆ lines(𝔽_p^d), rk J = r} (-1)^{|J|}` (paper eq. `(cr)`,
lines 363–366); `lines(𝔽_p^d) = lines ⊤`. (The paper's notation suppresses
the dependence on `d`.) -/
noncomputable def cr (p d : ℕ) [NeZero p] (r : ℕ) : ℤ :=
  ∑ J ∈ (lines (⊤ : Submodule (ZMod p) (Fin d → ZMod p))).powerset.filter
      (fun J => rkJ J = r), (-1 : ℤ) ^ J.card

/-! ## Lemma 4.1 (`lem:mobius`, paper lines 352–367) -/

/-- **Lemma 4.1, first equality** (paper lines 352–361).

Paper (verbatim): "Let $p$ be prime, $d\ge1$, and $V\le\FF_p^d$ a subspace of
dimension $r$, with $\mathrm{lines}(V)$ its set of $1$-dimensional subspaces.
Then
\[ f(V)\;:=\!\!\sum_{\substack{J\subseteq\mathrm{lines}(V)\\
\operatorname{span}J=V}}\!\!(-1)^{|J|} \;=\;\mu(0,V)\;=\;(-1)^r p^{\binom r2}, \]
where $\mu$ is the M\"obius function of the subspace lattice
\cite[Ex.~3.10.2]{stanley2012}."

Formal: `f(V) = μ(0,V)` with `μ = IncidenceAlgebra.mu ℤ` on the lattice of
subspaces of `𝔽_p^d` and `0 = ⊥`.

Delta:
* `𝔽_p^d` = `Fin d → ZMod p` (`ZMod p` is the field `𝔽_p` for prime `p`; the
  `Field` instance is not needed to STATE the claim — `Submodule` and
  `Module.finrank` only use the ring structure); "subspace" = `Submodule`;
  "dimension" = `Module.finrank (ZMod p)`; `0` (the zero subspace) = `⊥`.
  (Instance search equips `↥V` with mathlib's `AddSubgroupClass.instZModModule`,
  whose scalar action is the ambient one, and `Module (ZMod n) M` is a
  `Subsingleton`; so this `finrank` is the dimension of `V`. A scratch check
  confirmed it unifies with the `finrank` of the certified `spanSum_eq_mobius`.)
* `μ` = mathlib's `IncidenceAlgebra.mu ℤ`, i.e. `μ(a,a) = 1`,
  `μ(a,b) = -Σ_{a ≤ x < b} μ(a,x)` (`IncidenceAlgebra.mu_apply`) — the
  standard Möbius function of a locally finite poset (Stanley, EC1 §3.7),
  integer valued. The poset is the whole subspace lattice of `𝔽_p^d`; the
  interval `[0,V]` is the same as in the subspace lattice of `V`.
* `span J` is literally `Submodule.span` of the union of the lines in `J`
  (`spanJ`); `(-1)^{|J|}` is computed in `ℤ`; the sum is over the finite
  powerset of the finset `lines V`.
* `NeZero p` (needed for the finiteness instances) is derived from the
  hypothesis `p.Prime` inside the statement (`haveI`), so it is not an extra
  hypothesis.
* The hypotheses `p` prime, `d ≥ 1`, `dim V = r` are reproduced exactly; the
  hypothesis `dim V = r` is not used by this part's conclusion (it is kept
  verbatim; it is satisfiable for every `V` with `r := dim V`).
PAPER ISSUE: none. (The paper's `d ≥ 1` is not needed — the claim also holds
for `d = 0` — and the lemma holds over every finite field; both are
harmless restrictions, kept as written.) -/
def lemMobiusFEqMuStatement : Prop :=
  ∀ (p d : ℕ) (hp : p.Prime),
    haveI : NeZero p := ⟨hp.ne_zero⟩
    1 ≤ d → ∀ (V : Submodule (ZMod p) (Fin d → ZMod p)) (r : ℕ),
      finrank (ZMod p) V = r →
        signedSpanCount V
          = IncidenceAlgebra.mu ℤ (⊥ : Submodule (ZMod p) (Fin d → ZMod p)) V

/-- **Lemma 4.1, second equality** (paper lines 352–361): the Möbius function
of the subspace lattice of `𝔽_p^d` is `μ(0,V) = (-1)^r p^{\binom r2}` for
`dim V = r`.

Paper (verbatim): see `lemMobiusFEqMuStatement`; the claim here is
"$\mu(0,V)\;=\;(-1)^r p^{\binom r2}$".

Delta: as in `lemMobiusFEqMuStatement`; `\binom r2` = `r.choose 2` (`= 0` for
`r < 2`, matching the paper's convention), the right side is evaluated in `ℤ`.
PAPER ISSUE: none. -/
def lemMobiusMuClosedFormStatement : Prop :=
  ∀ (p d : ℕ) (hp : p.Prime),
    haveI : NeZero p := ⟨hp.ne_zero⟩
    1 ≤ d → ∀ (V : Submodule (ZMod p) (Fin d → ZMod p)) (r : ℕ),
      finrank (ZMod p) V = r →
        IncidenceAlgebra.mu ℤ (⊥ : Submodule (ZMod p) (Fin d → ZMod p)) V
          = (-1 : ℤ) ^ r * (p : ℤ) ^ (r.choose 2)

/-- **Lemma 4.1, eq. `(cr)`** (paper lines 362–367).

Paper (verbatim): "Consequently, classifying subsets of
$\mathrm{lines}(\FF_p^d)$ by their span,
\begin{equation}\label{eq:cr}
  c_r(p)\;:=\!\!\sum_{\substack{J\subseteq\mathrm{lines}(\FF_p^d)\\
  \rk J=r}}\!\!(-1)^{|J|}
  \;=\;(-1)^r p^{\binom r2}\gaussbinom dr_p ,\qquad 0\le r\le d .
\end{equation}"

Delta:
* `lines(𝔽_p^d)` = `lines ⊤`; `rk J` = `finrank (span J)` (`rkJ`; the paper
  defines `rk J` in Lemma 3.3 for sets of order-`p` subgroups of the lattice,
  as "the dimension of the span of the corresponding lines"; for a set of
  lines of `𝔽_p^d` this is `dim span J`).
* `[d r]_p` = `gaussBinom p d r` (project `q`-Pascal definition; fidelity to
  the paper's product formula is frozen in groups 01/02).
* `0 ≤ r` is automatic for `r : ℕ`; `r ≤ d` is kept as a hypothesis (for
  `r > d` both sides are `0`, but the paper does not claim that).
* hypotheses `p` prime and `d ≥ 1` are the lemma's.
PAPER ISSUE: none (minor notation: `rk J` is formally introduced in Lemma 3.3
only for sets of order-`p` cyclic subgroups of `𝒜`; for subsets of
`lines(𝔽_p^d)` the evident meaning `dim span J` is used). -/
def lemMobiusCrStatement : Prop :=
  ∀ (p d : ℕ) (hp : p.Prime),
    haveI : NeZero p := ⟨hp.ne_zero⟩
    1 ≤ d → ∀ r : ℕ, r ≤ d →
      cr p d r = (-1 : ℤ) ^ r * (p : ℤ) ^ (r.choose 2) * (gaussBinom p d r : ℤ)

/-- **Lemma 4.1, whole statement** (paper lines 352–367): the chain
`f(V) = μ(0,V) = (-1)^r p^{C(r,2)}` and eq. `(cr)`. -/
def lemMobiusStatement : Prop :=
  lemMobiusFEqMuStatement ∧ lemMobiusMuClosedFormStatement ∧ lemMobiusCrStatement

/-! ### Proof-internal claims of Lemma 4.1 (supplementary)

The proof of Lemma 4.1 (paper lines 369–386) asserts several intermediate
identities. They are not numbered statements, but they are mathematical
claims of the paper, so they are frozen here as well (each is TRUE and
brute-force checked; see the report). They are NOT part of
`lemMobiusStatement`. -/

/-- **Proof of Lemma 4.1, partition recursion** (paper lines 370–374).

Paper (verbatim): "Every $J\subseteq\mathrm{lines}(V)$ spans exactly one
$W\le V$, so $\sum_{W\le V}f(W)=\sum_{J\subseteq\mathrm{lines}(V)}(-1)^{|J|}
=(1-1)^{|\mathrm{lines}(V)|}=\delta_{V,0}$, since
$\mathrm{lines}(V)\neq\emptyset$ exactly when $V\neq0$."

Formal: the three claims (both equalities of the chain, with
`(1-1)^{|lines V|}` written out, and `lines(V) ≠ ∅ ↔ V ≠ 0`).

Delta: `Σ_{W ≤ V}` = sum over the finset `univ.filter (· ≤ V)` of subspaces;
`δ_{V,0}` = `if V = ⊥ then 1 else 0`; same conventions as Lemma 4.1. -/
def lemMobiusProofPartitionStatement : Prop :=
  ∀ (p d : ℕ) (hp : p.Prime),
    haveI : NeZero p := ⟨hp.ne_zero⟩
    1 ≤ d → ∀ V : Submodule (ZMod p) (Fin d → ZMod p),
      (∑ W ∈ Finset.univ.filter (· ≤ V), signedSpanCount W
          = ∑ J ∈ (lines V).powerset, (-1 : ℤ) ^ J.card) ∧
      (∑ J ∈ (lines V).powerset, (-1 : ℤ) ^ J.card
          = (1 - 1 : ℤ) ^ (lines V).card) ∧
      ((1 - 1 : ℤ) ^ (lines V).card = if V = ⊥ then 1 else 0) ∧
      ((lines V).Nonempty ↔ V ≠ ⊥)

/-- **Proof of Lemma 4.1, `q`-binomial theorem at `x = -1`** (paper lines
377–382).

Paper (verbatim): "$\sum_{r=0}^{R}\gaussbinom Rr_p(-1)^r p^{\binom r2}
=\prod_{i=0}^{R-1}(1-p^i)=\delta_{R,0}$ by the $q$-binomial theorem
\cite[eq.~(1.87)]{stanley2012} at $x=-1$".

Delta: computed in `ℤ`; `δ_{R,0}` = `if R = 0 then 1 else 0`;
`[R r]_p` = `gaussBinom p R r`; `p` prime as throughout the lemma (the
identity holds for every integer `p`). -/
def lemMobiusProofQBinomStatement : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ R : ℕ,
    (∑ r ∈ Finset.range (R + 1),
        (gaussBinom p R r : ℤ) * (-1 : ℤ) ^ r * (p : ℤ) ^ (r.choose 2)
      = ∏ i ∈ Finset.range R, (1 - (p : ℤ) ^ i)) ∧
    (∏ i ∈ Finset.range R, (1 - (p : ℤ) ^ i) = if R = 0 then 1 else 0)

/-- **Proof of Lemma 4.1, the closed form satisfies the recursion** (paper
lines 376–379).

Paper (verbatim): "Self-containedly, the function
$V\mapsto(-1)^{\dim V}p^{\binom{\dim V}2}$ satisfies the same recursion".

Formal: `Σ_{W ≤ V} (-1)^{dim W} p^{C(dim W, 2)} = δ_{V,0}` for every
subspace `V` of `𝔽_p^d`. Delta: as in `lemMobiusProofPartitionStatement`. -/
def lemMobiusProofClosedRecursionStatement : Prop :=
  ∀ (p d : ℕ) (hp : p.Prime),
    haveI : NeZero p := ⟨hp.ne_zero⟩
    1 ≤ d → ∀ V : Submodule (ZMod p) (Fin d → ZMod p),
      ∑ W ∈ Finset.univ.filter (· ≤ V),
          (-1 : ℤ) ^ finrank (ZMod p) W * (p : ℤ) ^ ((finrank (ZMod p) W).choose 2)
        = if V = ⊥ then 1 else 0

/-- **Proof of Lemma 4.1, uniqueness of the solution of the recursion** (paper
lines 382–383).

Paper (verbatim): "and the recursion determines $f$ uniquely by induction on
$\dim V$."

Formal: every `g` on the subspace lattice with `Σ_{W ≤ V} g(W) = δ_{V,0}` for
all `V` equals `f`. Delta: as in `lemMobiusProofPartitionStatement`. -/
def lemMobiusProofUniqueStatement : Prop :=
  ∀ (p d : ℕ) (hp : p.Prime),
    haveI : NeZero p := ⟨hp.ne_zero⟩
    1 ≤ d → ∀ g : Submodule (ZMod p) (Fin d → ZMod p) → ℤ,
      (∀ V : Submodule (ZMod p) (Fin d → ZMod p),
          ∑ W ∈ Finset.univ.filter (· ≤ V), g W = if V = ⊥ then 1 else 0) →
        ∀ V : Submodule (ZMod p) (Fin d → ZMod p), g V = signedSpanCount V

/-- **Proof of Lemma 4.1, classification by span** (paper lines 362–363 and
383–385).

Paper (verbatim): "Consequently, classifying subsets of
$\mathrm{lines}(\FF_p^d)$ by their span, [eq. (cr)]" and "Summing $f$ over
the $\gaussbinom dr_p$ subspaces of dimension $r$ gives \eqref{eq:cr}."

Formal: (a) `c_r(p) = Σ_{dim V = r} f(V)`; (b) there are `[d r]_p`
subspaces of dimension `r` (the count used in "the `[d r]_p` subspaces").

Delta: the count in (b) is `Nat.card` of the subtype of `r`-dimensional
submodules (a finite type); `[d r]_p` = `gaussBinom p d r`; `r ≤ d` as in
`(cr)`. -/
def lemMobiusProofClassifyStatement : Prop :=
  ∀ (p d : ℕ) (hp : p.Prime),
    haveI : NeZero p := ⟨hp.ne_zero⟩
    1 ≤ d → ∀ r : ℕ, r ≤ d →
      cr p d r
          = ∑ V ∈ Finset.univ.filter
              (fun V : Submodule (ZMod p) (Fin d → ZMod p) => finrank (ZMod p) V = r),
              signedSpanCount V ∧
      Nat.card {V : Submodule (ZMod p) (Fin d → ZMod p) // finrank (ZMod p) V = r}
        = gaussBinom p d r

/-! ## Definition 4.2 (Coefficient function, paper lines 390–395) -/

/-- **Definition 4.2, the clause `r_d(p,0) = 1`** (paper lines 390–392).

Paper (verbatim): "For a prime $p$ and $0\le v\le d$ let
$r_d(p,v)=p^{\binom v2}\gaussbinom dv_p$, with $r_d(p,0)=1$."

Formal: the defining formula (`rdCoeff p v d = p^(v choose 2) * [d v]_p`,
`Statement.lean`) indeed gives `1` at `v = 0`, i.e. the extra clause
"with `r_d(p,0) = 1`" is consistent with (not an override of) the formula.

Delta: `r_d(p,v)` = `rdCoeff p v d` (note the argument order `p v d`);
`d ≥ 1` is the standing hypothesis (Definition 2.1).
PAPER ISSUE: none (the clause is redundant: `p^{C(0,2)} [d 0]_p = 1`). -/
def defCoeffZeroStatement : Prop :=
  ∀ (p d : ℕ), p.Prime → 1 ≤ d → rdCoeff p 0 d = 1

/-- **Definition 4.2, the case `d = 2`** (paper lines 392–393).

Paper (verbatim): "For $d=2$ this is $1,\;p+1,\;p$ for $v=0,1,2$".

Delta: values in `ℕ` (no subtraction occurs). PAPER ISSUE: none. -/
def defCoeffD2Statement : Prop :=
  ∀ p : ℕ, p.Prime →
    rdCoeff p 0 2 = 1 ∧ rdCoeff p 1 2 = p + 1 ∧ rdCoeff p 2 2 = p

/-- The coefficient `r(i)` of Theorem E.19 of Banda–Caughman–Cenek–Teuscher
(2019, arXiv:1703.09030v2, p. 14), transcribed from the PDF:
"`r(i) = 1 if v_i = 0; p_i + 1 if v_i = 1; p_i if v_i = 2`" (only
`v ∈ {0,1,2}` occurs there). -/
def banda2019E19Coeff (p v : ℕ) : ℕ :=
  if v = 0 then 1 else if v = 1 then p + 1 else p

/-- **Definition 4.2, agreement with the 2019 coefficients** (paper lines
392–393).

Paper (verbatim): "For $d=2$ this is $1,\;p+1,\;p$ for $v=0,1,2$, the
coefficients of \cite[Thm.~E.19]{banda2019}."

Formal: `r_2(p,v) = r(v)` of Thm E.19 for `v ∈ {0,1,2}`.

Delta: Thm E.19's `r(i)` is transcribed as `banda2019E19Coeff` (verified
against the 2019 PDF, scratchpad/research/references/banda_1703.09030.pdf).
PAPER ISSUE: none. -/
def defCoeffE19Statement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ v : ℕ, v ≤ 2 → rdCoeff p v 2 = banda2019E19Coeff p v

/-- **Definition 4.2, all mathematical claims** (paper lines 390–395). -/
def defCoeffStatement : Prop :=
  defCoeffZeroStatement ∧ defCoeffD2Statement ∧ defCoeffE19Statement

/-! ## Table 1 (paper lines 502–517) -/

/-- **Table 1, row `d = 1`** (paper line 509).

Paper (verbatim): caption "Coefficients $r_d(p,v)=p^{\binom v2}\gaussbinom
dv_p$ for small $d$."; row "1 & 1 & $1$ & & & \\".

Delta: `r_d(p,v)` = `rdCoeff p v d`; `p` ranges over primes (Definition 4.2
defines `r_d(p,v)` for prime `p`); blank cells (`v > d`) are not claims.
PAPER ISSUE: none. -/
def table1Row1Statement : Prop :=
  ∀ p : ℕ, p.Prime → rdCoeff p 0 1 = 1 ∧ rdCoeff p 1 1 = 1

/-- **Table 1, row `d = 2`** (paper line 510).

Paper (verbatim): "2 & 1 & $p+1$ & $p$ & & \\".

Delta: as for row 1. PAPER ISSUE: none. -/
def table1Row2Statement : Prop :=
  ∀ p : ℕ, p.Prime →
    rdCoeff p 0 2 = 1 ∧ rdCoeff p 1 2 = p + 1 ∧ rdCoeff p 2 2 = p

/-- **Table 1, row `d = 3`** (paper line 511).

Paper (verbatim): "3 & 1 & $p^2{+}p{+}1$ & $p(p^2{+}p{+}1)$ & $p^3$ & \\".

Delta: as for row 1. PAPER ISSUE: none. -/
def table1Row3Statement : Prop :=
  ∀ p : ℕ, p.Prime →
    rdCoeff p 0 3 = 1 ∧ rdCoeff p 1 3 = p ^ 2 + p + 1 ∧
    rdCoeff p 2 3 = p * (p ^ 2 + p + 1) ∧ rdCoeff p 3 3 = p ^ 3

/-- **Table 1, row `d = 4`** (paper lines 512–513).

Paper (verbatim): "4 & 1 & $p^3{+}p^2{+}p{+}1$ & $p(p^2{+}1)(p^2{+}p{+}1)$ &
$p^3(p^3{+}p^2{+}p{+}1)$ & $p^6$ \\".

Delta: as for row 1. PAPER ISSUE: none. -/
def table1Row4Statement : Prop :=
  ∀ p : ℕ, p.Prime →
    rdCoeff p 0 4 = 1 ∧ rdCoeff p 1 4 = p ^ 3 + p ^ 2 + p + 1 ∧
    rdCoeff p 2 4 = p * (p ^ 2 + 1) * (p ^ 2 + p + 1) ∧
    rdCoeff p 3 4 = p ^ 3 * (p ^ 3 + p ^ 2 + p + 1) ∧ rdCoeff p 4 4 = p ^ 6

/-- **Table 1, every entry** (paper lines 502–517). -/
def table1Statement : Prop :=
  table1Row1Statement ∧ table1Row2Statement ∧ table1Row3Statement ∧ table1Row4Statement

/-! ## Remark "Duality" (paper lines 1028–1033) -/

/-- **Remark (Duality), Gaussian-binomial symmetry** (paper lines 1028–1029).

Paper (verbatim): "$\gaussbinom dr_p=\gaussbinom d{d-r}_p$, so rank-$r$ and
rank-$(d{-}r)$ symmetry types are equinumerous. We state this purely as the
standard symmetry of Gaussian binomials; we do not attach further structural
claims to it."

Formal: `[d r]_p = [d d-r]_p` for prime `p`, `d ≥ 1`, `r ≤ d`.

Delta:
* `[d r]_p` = `gaussBinom p d r`; `d - r` is `ℕ`-subtraction, exact because of
  the hypothesis `r ≤ d`.
* The range `0 ≤ r ≤ d` is implicit in the paper; it is NECESSARY: for
  `r > d` the truncated `d - r = 0` gives e.g. `[1 2]_2 = 0 ≠ 1 = [1 0]_2`.
* `p` prime and `d ≥ 1` as in the paper's context (the identity holds for
  every integer `q` and every `d`).
PAPER ISSUE: (minor) the range of `r` is not stated; should read
"for `0 ≤ r ≤ d`". -/
def dualityGaussStatement : Prop :=
  ∀ (p d r : ℕ), p.Prime → 1 ≤ d → r ≤ d → gaussBinom p d r = gaussBinom p d (d - r)

/-- **Remark (Duality), "rank-`r` and rank-`(d−r)` symmetry types are
equinumerous" — subspace reading** (paper lines 1029–1030).

Paper (verbatim): "so rank-$r$ and rank-$(d{-}r)$ symmetry types are
equinumerous."

Formal: `𝔽_p^d` has as many `r`-dimensional subspaces as `(d−r)`-dimensional
ones (`0 ≤ r ≤ d`).

Delta: counts are `Nat.card` of subtypes of `Submodule (ZMod p) (Fin d → ZMod p)`
(finite for prime `p`, so `Nat.card` is the true cardinality).
PAPER ISSUE: "symmetry type" is not defined anywhere in the paper. The
evident meaning (via §3–§4: a rank-`r` type at the prime `p` is an
`r`-dimensional subspace of `𝔽_p^d ≅ 𝒜[p]`, counted by `[d r]_p`, line 263) is
formalized here and, at the lattice level, in `dualityLatticeStatement`. The
paper should say e.g. "so `𝔽_p^d` has equally many subspaces of dimensions `r`
and `d−r` (equivalently, `𝒜[p]` has equally many subgroups of order `p^r` and
`p^{d−r}`), `0 ≤ r ≤ d`". -/
def dualitySubspaceStatement : Prop :=
  ∀ (p d r : ℕ), p.Prime → 1 ≤ d → r ≤ d →
    Nat.card {W : Submodule (ZMod p) (Fin d → ZMod p) // finrank (ZMod p) W = r}
      = Nat.card {W : Submodule (ZMod p) (Fin d → ZMod p) // finrank (ZMod p) W = d - r}

/-- **Remark (Duality), "rank-`r` and rank-`(d−r)` symmetry types are
equinumerous" — lattice reading** (paper lines 1029–1030).

Paper (verbatim): see `dualitySubspaceStatement`.

Formal: for `n ≥ 2`, `d ≥ 1`, a prime `p ∣ n` and `0 ≤ r ≤ d`, the subgroups
`H ≤ 𝒜 = (ℤ/nℤ)^d` contained in the `p`-torsion `𝒜[p] = {x : p x = 0}` (the
symmetry groups generated by order-`p` translations, Lemma 3.3) with
`|H| = p^r` (i.e. of rank `r`) are as many as those with `|H| = p^{d−r}`.

Delta: `𝒜` = `Lat n d = Fin d → ZMod n`; "contained in `𝒜[p]`" =
`∀ x ∈ H, p • x = 0`; "rank `r`" = `Nat.card H = p ^ r`; counts are `Nat.card`
of subtypes of `AddSubgroup (Lat n d)` (finite since `n ≥ 2`).
PAPER ISSUE: see `dualitySubspaceStatement` ("symmetry type" undefined). -/
def dualityLatticeStatement : Prop :=
  ∀ (n d p r : ℕ), 2 ≤ n → 1 ≤ d → p.Prime → p ∣ n → r ≤ d →
    Nat.card {H : AddSubgroup (Lat n d) // (∀ x ∈ H, p • x = 0) ∧ Nat.card H = p ^ r}
      = Nat.card {H : AddSubgroup (Lat n d) //
          (∀ x ∈ H, p • x = 0) ∧ Nat.card H = p ^ (d - r)}

/-- **Remark (Duality), whole remark** (paper lines 1028–1033). The final
sentence ("We state this purely as the standard symmetry of Gaussian
binomials; we do not attach further structural claims to it.") is
NON-MATHEMATICAL (a scope disclaimer). -/
def dualityStatement : Prop :=
  dualityGaussStatement ∧ dualitySubspaceStatement ∧ dualityLatticeStatement

/-! ## Sanity checks (non-vacuity and small instances; NOT proofs of the Props) -/

-- hypotheses are satisfiable
example : Nat.Prime 2 ∧ 1 ≤ 3 := ⟨Nat.prime_two, by norm_num⟩
example : 2 ≤ 6 ∧ 1 ≤ 2 ∧ Nat.Prime 3 ∧ 3 ∣ 6 := ⟨by norm_num, by norm_num, Nat.prime_three, by norm_num⟩

-- the incidence-algebra Möbius function elaborates on the subspace lattice
-- (the scoped instances are found) and is normalised: μ(0,0) = 1
example : IncidenceAlgebra.mu ℤ (⊥ : Submodule (ZMod 2) (Fin 3 → ZMod 2)) ⊥ = 1 :=
  IncidenceAlgebra.mu_self _

-- `lines`, `spanJ`, `signedSpanCount`, `cr` elaborate at concrete arguments
example : (signedSpanCount (⊥ : Submodule (ZMod 3) (Fin 2 → ZMod 3)) : ℤ) =
    signedSpanCount (⊥ : Submodule (ZMod 3) (Fin 2 → ZMod 3)) := rfl
example : cr 2 3 1 = cr 2 3 1 := rfl

-- subspaces of every dimension 0..d exist (non-vacuity of `dim V = r`), at the ends:
example : finrank (ZMod 2) (⊥ : Submodule (ZMod 2) (Fin 3 → ZMod 2)) = 0 := finrank_bot _ _

-- Definition 4.2 / Table 1 at p = 2, 3, 5, 7 (kernel evaluation of `rdCoeff`)
example : rdCoeff 2 0 1 = 1 ∧ rdCoeff 2 1 1 = 1 := ⟨rfl, rfl⟩
example : rdCoeff 3 0 2 = 1 ∧ rdCoeff 3 1 2 = 3 + 1 ∧ rdCoeff 3 2 2 = 3 := ⟨rfl, rfl, rfl⟩
example : rdCoeff 5 1 3 = 5 ^ 2 + 5 + 1 ∧ rdCoeff 5 2 3 = 5 * (5 ^ 2 + 5 + 1) ∧
    rdCoeff 5 3 3 = 5 ^ 3 := ⟨rfl, rfl, rfl⟩
example : rdCoeff 3 1 4 = 3 ^ 3 + 3 ^ 2 + 3 + 1 ∧ rdCoeff 3 2 4 = 3 * (3 ^ 2 + 1) * (3 ^ 2 + 3 + 1) ∧
    rdCoeff 3 3 4 = 3 ^ 3 * (3 ^ 3 + 3 ^ 2 + 3 + 1) ∧ rdCoeff 3 4 4 = 3 ^ 6 :=
  ⟨rfl, rfl, rfl, rfl⟩
example : rdCoeff 7 2 4 = 7 * (7 ^ 2 + 1) * (7 ^ 2 + 7 + 1) := rfl
example : ∀ v ≤ 2, rdCoeff 5 v 2 = banda2019E19Coeff 5 v := by decide

-- Duality on small values (and the failure for r > d with truncated d - r)
example : gaussBinom 2 4 1 = gaussBinom 2 4 3 ∧ gaussBinom 3 5 2 = gaussBinom 3 5 3 := ⟨rfl, rfl⟩
example : gaussBinom 2 1 2 ≠ gaussBinom 2 1 (1 - 2) := by decide

-- eq. (cr) right side and the q-binomial identity at -1 (small values)
#eval (List.range 4).map fun r =>
  (-1 : ℤ) ^ r * (2 : ℤ) ^ (r.choose 2) * (gaussBinom 2 3 r : ℤ)   -- [1, -7, 14, -8]
#eval (List.range 6).map fun R => ∑ r ∈ Finset.range (R + 1),
  (gaussBinom 3 R r : ℤ) * (-1 : ℤ) ^ r * (3 : ℤ) ^ (r.choose 2)   -- [1, 0, 0, 0, 0, 0]

-- fidelity of `gaussBinom` to the paper's product formula (line 262), small values
#eval (List.range 6).map fun r =>
  ((∏ i ∈ Finset.range r, (((3 : ℚ) ^ (5 - i) - 1) / ((3 : ℚ) ^ (i + 1) - 1))),
    (gaussBinom 3 5 r : ℚ))

end ShiftSym.P03
