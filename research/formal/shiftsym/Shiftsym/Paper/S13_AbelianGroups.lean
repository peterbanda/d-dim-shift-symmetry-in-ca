/-
Phase H, group 13 (finite abelian groups), 2026-11-06 — paper v10, Section 4.5 (`sec:abelian`,
lines 657–743): the setting, Theorem 4.7 (`thm:abelian`), Corollary 4.8 (`cor:abelian-ranks`) and
Remark 4.9 (`rem:abelian`). FROZEN STATEMENTS ONLY; proofs in
`Shiftsym/Paper/Proofs/P13_AbelianGroups*.lean` as `<X>_proved`, audited by `AuditPaper.lean`
(group "13").

Provenance, stated plainly. The section is follow-up A1 (`research/abelian/`), which went through the
full suite before entering the paper: proof, brute force and an independent subgroup-lattice evaluator
(Run 034), two fresh-context hostile reviews (proof referee: PASS with repairs; numerical
reconstruction: CONFIRMED), and Lean. Eleven statements were frozen on 2026-11-06 in the
extension layer (`Ext/SXA1_AbelianEnum.lean`, from research/abelian/THEOREMS.md), passed a fresh-context
fidelity review there (literal, exploit, numeric: PASS; minor findings applied, re-review PASS) and were
proved there; they move here unchanged except for the namespace (`ShiftSym.XA1` → `ShiftSym.P13`) and
docstrings that now quote the paper, and the extension copy is deleted (ten of them are below; the
eleventh, `card736Statement`, was later replaced, see the note of 2026-11-06 at the end of this
header). `monotoneStatement`,
`cyclicMinStatement`, `stepStrictStatement` (Corollary 4.8(ii)), `rectCardStatement` and
`freeActionStatement` are new here and frozen before their proofs; the proof of
Corollary 4.8(ii) (q-Pascal) was found by a reviewer of v10 and is checked in Run 034's addendum ([9]).
Fidelity review of this file: three fresh-context reviewers (Run 036).

Representation choices (Deltas): alphabet `Fin σ`; a finite abelian group is a type with
`[AddCommGroup G] [Finite G]`, `N = Nat.card G`; shift-symmetric is `IsShiftSymmetricG`; the p-rank is
`pRank G p`, the exponent of `p` in `|G[p]|` (`pRankPowStatement`); the vector-indexed sum is
re-indexed by the divisors `h ≠ 1` of `R = ∏_{p ∣ N} p ^ d_p` (`rankRad`), `|v| = Ω(h)`, as in the
core's `enumerationRHS`; ℕ-division in the exponents is exact; rectangular tori are
`∀ i : Fin d, ZMod (n i)` with all `n i ≥ 1` (the paper's `m` factors are `d` here); orbits are
represented by their sets of translates. Not frozen: the opening sentence "The torus $\ZZ_n^d$ enters the
proof of Theorem~\ref{thm:main-enum} only through its order and its $p$-torsion, which is $\FF_p^d$
… (Lemma~\ref{lem:torsion})" — a remark on the structure of a proof, whose torsion fact is Lemma 3.3
(frozen in group 02); "an $\FF_p$-vector space" — standard structure, whose numerical content is
certified by `pRankPowStatement`; the proof sentences of Theorem 4.7 and Corollary 4.8 (proofs);
"for rectangular tori these are the atranslational necklaces of [adamson2021]" (identification of a
cited notion: an atranslational necklace is a translation orbit of a word with trivial stabilizer).
Review history: round 1 of the fidelity review (Run 036) found the strict increase of Corollary 4.8(ii)
unfrozen without a supplied `G''` (now `stepStrictStatement`), "G acts freely" and "N = ∏ n_i" unfrozen
(now `freeActionStatement`, `rectCardStatement`), the reading of "fewest" undocumented, and wrong line
numbers; repaired, statements frozen before their proofs.
2026-11-06: card736Statement replaced by cardTwoPrimeStatement after the paper's example was replaced
(owner); frozen before its proof. Fidelity review of the re-freeze by three fresh-context reviewers
(literal, exploit, numeric): PASS, PASS, PASS. Their minor findings were applied to the docstrings
only: a run number cited here before that run was logged was removed, the shared order and ranks of
the example's groups are now documented under `cardTwoPrimeStatement`, and the Theorem 4.7 quote is
marked as a display rendered inline. The old example
($\ZZ_2\times\ZZ_8$ and $\ZZ_4\times\ZZ_4$, $736$) concerned 2-groups only; the new one
($\ZZ_2\times\ZZ_{24}$ and $\ZZ_4\times\ZZ_{12}$, $50\,388\,256$ for $\sigma=2$) has two primes. With the
re-freeze, the tex line numbers of every docstring in this file were re-checked against the current
paper source and corrected (later v10 edits had shifted them); no statement other than
`card736Statement` → `cardTwoPrimeStatement` changed.
-/
import Shiftsym.Statement

namespace ShiftSym.P13

open ShiftSym

/-- §4.5, lines 663–665: "Configurations $G\to\Sigma$, translations, stabilizers, and $S_G$ are
defined as in Section~\ref{sec:model} with $\A$ replaced by $G$": `s` is shift-symmetric if some
nonzero translation `v` fixes it, `s (u + v) = s u` for all `u` (the paper's $\tau_v\ssb(\uu)=\ssb(\uu+\vv)$). -/
def IsShiftSymmetricG {G A : Type*} [AddCommGroup G] (s : G → A) : Prop :=
  ∃ v : G, v ≠ 0 ∧ ∀ u : G, s (u + v) = s u

/-- §4.5, lines 662–663: "let $G[p]=\{g\in G: pg=0\}$, an $\FF_p$-vector space, and let
$d_p=\dim_{\FF_p}G[p]$ be the \emph{$p$-rank} of $G$". Delta: the exponent of `p` in `|G[p]|`
(certified by `pRankPowStatement`). -/
noncomputable def pRank (G : Type*) [AddCommGroup G] (p : ℕ) : ℕ :=
  (Nat.card {g : G // p • g = 0}).factorization p

/-- `R = ∏_{p ∣ N} p ^ d_p`. -/
def rankRad (N : ℕ) (dp : ℕ → ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors, p ^ dp p

/-- The coefficient of the divisor `h = ∏ p ^ v_p`:
`(-1)^(1 + Ω(h)) ∏_{p ∣ h} r_{d_p}(p, v_p(h))`. -/
def coeffA (dp : ℕ → ℕ) (h : ℕ) : ℤ :=
  (-1 : ℤ) ^ (1 + bigOmega h) *
    ∏ p ∈ h.primeFactors, (rdCoeff p (h.factorization p) (dp p) : ℤ)

/-- Right-hand side of Theorem 4.7 (divisor form; Delta: the vector index `v` re-indexed by
`h = ∏ p ^ v_p`, as the core's `enumerationRHS`):
`Σ_{h ∣ R, h ≠ 1} (-1)^(1+Ω(h)) ∏_{p ∣ h} r_{d_p}(p, v_p(h)) σ^(N/h)`. -/
def abelianRHS (N : ℕ) (dp : ℕ → ℕ) (σ : ℕ) : ℤ :=
  ∑ h ∈ (rankRad N dp).divisors.erase 1, coeffA dp h * (σ : ℤ) ^ (N / h)

/-- Right-hand side of Remark 4.9(i) (the $k$-active counts of Theorem 5.1 on `G`):
`Σ_{h ∣ R, h ≠ 1, h ∣ k} (-1)^(1+Ω(h)) ∏ r_{d_p}(p, v_p(h)) binom(N/h, k/h) (σ-1)^((N-k)/h)`. -/
def kActiveRHS (N : ℕ) (dp : ℕ → ℕ) (σ k : ℕ) : ℤ :=
  ∑ h ∈ ((rankRad N dp).divisors.erase 1).filter (fun h => h ∣ k),
    coeffA dp h * ((N / h).choose (k / h) : ℤ) * ((σ : ℤ) - 1) ^ ((N - k) / h)

/-- §4.5, lines 665–667: "a rectangular torus $\ZZ_{n_1}\times\dots\times\ZZ_{n_m}$ has $N=\prod_i n_i$
and $d_p=|\{i:p\mid n_i\}|$". -/
def rectRank {d : ℕ} (n : Fin d → ℕ) (p : ℕ) : ℕ :=
  (Finset.univ.filter fun i => p ∣ n i).card

/-- **Theorem 4.7** (`thm:abelian`, lines 669–678): "For every finite abelian group $G$ of order
$N$ and every $\sigma\ge1$, $|S_G| = \sum_{\vv=(v_p)_{p\mid N},\ 0\le v_p\le d_p,\ \vv\neq\mathbf 0}
(-1)^{1+|\vv|}\prod_{p\mid N} r_{d_p}(p,v_p)\,\sigma^{N/\prod_p p^{v_p}}$." (The display, with its
`\substack` index, is rendered inline here.) -/
def abelianEnumStatement (G : Type*) [AddCommGroup G] [Finite G] (σ : ℕ) : Prop :=
  1 ≤ σ →
    (Nat.card {s : G → Fin σ // IsShiftSymmetricG s} : ℤ)
      = abelianRHS (Nat.card G) (pRank G) σ

/-- §4.5, lines 665–667: a rectangular torus has "$d_p=|\{i:p\mid n_i\}|$" (Delta: `n_i ≥ 1`,
since `ZMod 0 = ℤ`). -/
def rectRankStatement (d : ℕ) (n : Fin d → ℕ) (p : ℕ) : Prop :=
  (∀ i, 1 ≤ n i) → p.Prime → pRank (∀ i, ZMod (n i)) p = rectRank n p

/-- Theorem 4.7 on a rectangular torus, with "$N=\prod_i n_i$ and $d_p=|\{i:p\mid n_i\}|$"
(lines 666–667; `rectCardStatement` certifies the order). -/
def rectEnumStatement (d : ℕ) (n : Fin d → ℕ) (σ : ℕ) : Prop :=
  (∀ i, 1 ≤ n i) → 1 ≤ σ →
    (Nat.card {s : (∀ i, ZMod (n i)) → Fin σ // IsShiftSymmetricG s} : ℤ)
      = abelianRHS (∏ i, n i) (rectRank n) σ

/-- Theorem 4.7, lines 676–677: "For $G=\ZZ_n^d$, where $d_p=d$ for every $p\mid n$, this is
Theorem~\ref{thm:main-enum}" — the right-hand sides agree (with `bridgeStatement`, the
left-hand sides too). -/
def squareStatement (n d σ : ℕ) : Prop :=
  1 ≤ n → abelianRHS (n ^ d) (rectRank (fun _ : Fin d => n)) σ = enumerationRHS n d σ

/-- The left-hand sides agree on the square torus: `IsShiftSymmetricG` on `Lat n d` is the
core's `IsShiftSymmetric` (Definitions.lean). -/
def bridgeStatement (n d σ : ℕ) : Prop :=
  ∀ s : Config n d (Fin σ), IsShiftSymmetricG s ↔ IsShiftSymmetric s

/-- **Corollary 4.8(i)** (`cor:abelian-ranks`, lines 699–701): "$|S_G|$ depends on $G$ only through
$N$ and its $p$-ranks". -/
def onlyRanksStatement (G H : Type*) [AddCommGroup G] [Finite G] [AddCommGroup H] [Finite H]
    (σ : ℕ) : Prop :=
  Nat.card G = Nat.card H → (∀ p, p.Prime → pRank G p = pRank H p) →
    Nat.card {s : G → Fin σ // IsShiftSymmetricG s}
      = Nat.card {s : H → Fin σ // IsShiftSymmetricG s}

/-- **Remark 4.9(i)** (`rem:abelian`, lines 737–738): "The $k$-active counts of
Theorem~\ref{thm:kactive} extend to $G$ in the same way, with $r_d$ replaced by $r_{d_p}$ and $n^d$ by
$N$" (Delta: Theorem 5.1's convention $\binom{N/h}{k/h}=0$ unless $h\mid k$; symbol `a : Fin σ`). -/
def kActiveStatement (G : Type*) [AddCommGroup G] [Finite G] (σ k : ℕ) (a : Fin σ) : Prop :=
  k ≤ Nat.card G →
    (Nat.card {s : G → Fin σ // IsShiftSymmetricG s ∧ Nat.card {u : G // s u = a} = k} : ℤ)
      = kActiveRHS (Nat.card G) (pRank G) σ k

/-- **Remark 4.9(ii)**, lines 739–740: "$G$ acts freely on the aperiodic configurations, so
$N\mid\sigma^N-|S_G|$". -/
def freeOrbitsStatement (G : Type*) [AddCommGroup G] [Finite G] (σ : ℕ) : Prop :=
  (Nat.card G : ℤ) ∣ (σ : ℤ) ^ Nat.card G - (Nat.card {s : G → Fin σ // IsShiftSymmetricG s} : ℤ)

/-- Remark 4.9(ii), lines 740–741: "$(\sigma^N-|S_G|)/N$ is the number of $G$-orbits of aperiodic
configurations". Delta: an orbit is represented by its set of translates
`{τ_v s | v ∈ G} = Set.range (fun v u => s (u + v))`; the statement counts these sets for the
aperiodic `s` and multiplies by `N`. -/
def orbitCountStatement (G : Type*) [AddCommGroup G] [Finite G] (σ : ℕ) : Prop :=
  (Nat.card {O : Set (G → Fin σ) //
      ∃ s : G → Fin σ, ¬ IsShiftSymmetricG s ∧ O = Set.range (fun v : G => fun u : G => s (u + v))} : ℤ)
      * Nat.card G
    = (σ : ℤ) ^ Nat.card G - (Nat.card {s : G → Fin σ // IsShiftSymmetricG s} : ℤ)

/-- The `p`-rank Delta: for prime `p`, `|G[p]| = p ^ pRank G p`. -/
def pRankPowStatement (G : Type*) [AddCommGroup G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → Nat.card {g : G // p • g = 0} = p ^ pRank G p

/-- Corollary 4.8(i), lines 699–701: "$|S_G|$ depends on $G$ only through $N$ and its $p$-ranks; for
example, $\ZZ_2\times\ZZ_{24}$ and $\ZZ_4\times\ZZ_{12}$ both have $50\,388\,256$
shift-symmetric configurations for $\sigma=2$." The first clause is `onlyRanksStatement`; this
statement freezes the example (frozen 2026-11-06, replacing `card736Statement`, before its proof).
Deltas: the groups as products of `ZMod`, `∀ i : Fin 2, ZMod (![2, 24] i)` for
$\ZZ_2\times\ZZ_{24}$ and `∀ i : Fin 2, ZMod (![4, 12] i)` for $\ZZ_4\times\ZZ_{12}$ (the rectangular
form used throughout); the alphabet $\sigma=2$ as `Fin 2`; "shift-symmetric" is `IsShiftSymmetricG`,
fixed by some nonzero translation; $50\,388\,256$ is `50388256`. The example illustrates the first
clause because both groups have $N=48$ and the same ranks $d_2=2$, $d_3=1$. That shared order and
those ranks are certified in general by `rectCardStatement` and `rectRankStatement`, so they are not
frozen again here. The text does not claim that the two groups are non-isomorphic, so that is not
frozen either. -/
def cardTwoPrimeStatement : Prop :=
  Nat.card {s : (∀ i : Fin 2, ZMod (![2, 24] i)) → Fin 2 // IsShiftSymmetricG s} = 50388256 ∧
    Nat.card {s : (∀ i : Fin 2, ZMod (![4, 12] i)) → Fin 2 // IsShiftSymmetricG s} = 50388256


/-- **Corollary 4.8(ii)**, lines 702–705: "If $G'$ has the same order as $G$, $d_p(G')=d_p(G)+1$ for
one prime $p$, and the other ranks agree, then $|S_{G'}|-|S_G|=p^{d_p(G)}\,\mathrm{ac}(G'')>0$ for any
abelian group $G''$ of order $N/p$ with the ranks of $G$" ($\sigma\ge2$, $\mathrm{ac}(H)=\sigma^{|H|}-|S_H|$).
Delta: "the ranks of $G$" are compared at every prime. -/
def monotoneStatement (G G' G'' : Type*) [AddCommGroup G] [Finite G] [AddCommGroup G'] [Finite G']
    [AddCommGroup G''] [Finite G''] (σ p : ℕ) : Prop :=
  2 ≤ σ → p.Prime → Nat.card G' = Nat.card G →
    pRank G' p = pRank G p + 1 → (∀ q, q.Prime → q ≠ p → pRank G' q = pRank G q) →
    Nat.card G'' * p = Nat.card G → (∀ q, q.Prime → pRank G'' q = pRank G q) →
      (Nat.card {s : G' → Fin σ // IsShiftSymmetricG s} : ℤ)
          - Nat.card {s : G → Fin σ // IsShiftSymmetricG s}
        = (p : ℤ) ^ pRank G p *
            ((σ : ℤ) ^ Nat.card G'' - Nat.card {s : G'' → Fin σ // IsShiftSymmetricG s})
      ∧ 0 < (σ : ℤ) ^ Nat.card G'' - Nat.card {s : G'' → Fin σ // IsShiftSymmetricG s}

/-- Corollary 4.8(ii), lines 705–707: "among the abelian groups of order $N$, the cyclic group has the
fewest shift-symmetric configurations" ($\sigma\ge2$). Deltas: the cyclic group of order
`N = Nat.card G` is `ZMod N`; "has the fewest" is read as attaining the minimum (`≤` against every
abelian group of order `N`); uniqueness of the minimizer is not claimed by the text and not certified
here (it would follow from `stepStrictStatement` together with the existence of a group with one rank
lowered, which the proof of Corollary 4.8 states and which is not frozen). Round 2 of the fidelity
review (literal, exploit, numeric): PASS. -/
def cyclicMinStatement (G : Type*) [AddCommGroup G] [Finite G] (σ : ℕ) : Prop :=
  2 ≤ σ →
    Nat.card {s : ZMod (Nat.card G) → Fin σ // IsShiftSymmetricG s}
      ≤ Nat.card {s : G → Fin σ // IsShiftSymmetricG s}


/-- Corollary 4.8(ii), line 704: "$|S_{G'}|-|S_G|=p^{d_p(G)}\,\mathrm{ac}(G'')>0$" — the strict
increase along a rank step, with no intermediate group supplied (the existence of `G''` is part of
the claim). -/
def stepStrictStatement (G G' : Type*) [AddCommGroup G] [Finite G] [AddCommGroup G'] [Finite G']
    (σ p : ℕ) : Prop :=
  2 ≤ σ → p.Prime → Nat.card G' = Nat.card G →
    pRank G' p = pRank G p + 1 → (∀ q, q.Prime → q ≠ p → pRank G' q = pRank G q) →
      Nat.card {s : G → Fin σ // IsShiftSymmetricG s}
        < Nat.card {s : G' → Fin σ // IsShiftSymmetricG s}

/-- §4.5, lines 665–666: a rectangular torus "has $N=\prod_i n_i$". -/
def rectCardStatement (d : ℕ) (n : Fin d → ℕ) : Prop :=
  (∀ i, 1 ≤ n i) → Nat.card (∀ i, ZMod (n i)) = ∏ i, n i

/-- Remark 4.9(ii), line 739: "$G$ acts freely on the aperiodic configurations": translates of an
aperiodic configuration are aperiodic, and only `0` fixes one. -/
def freeActionStatement (G : Type*) [AddCommGroup G] (σ : ℕ) : Prop :=
  ∀ (s : G → Fin σ), ¬ IsShiftSymmetricG s → ∀ v : G,
    ¬ IsShiftSymmetricG (fun u => s (u + v)) ∧ ((∀ u, s (u + v) = s u) → v = 0)

end ShiftSym.P13
