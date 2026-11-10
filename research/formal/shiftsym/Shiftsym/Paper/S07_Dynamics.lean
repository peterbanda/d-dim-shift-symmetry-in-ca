/-
Phase H, group 07 — paper Section 8 "Dynamics: irreversibility,
insolvability, rank monotonicity" (`shift_symmetry_d_dimensions.tex`,
lines 725–800, v3.1), frozen as `Prop`s. No statement is proved here.

Contents (paper label → frozen `Prop`s):
* Figure `fig:pattern-flip` caption (L725–736; the figure belongs to
  Observation `obs:extrema`, whose statements are frozen by group 06 —
  the caption repeats three of its numerical claims, frozen here too so
  that no sentence of L725–800 is left out):
  `captionDipsD2Statement`, `captionBoundaryStatement`,
  `captionD3Statement`, `captionD3NotMinStatement`, `captionStatement`.
* Theorem 8.1 `thm:irrev` (L743–748): `irrevStabStatement`,
  `irrevVecStatement`, `irrevSetStatement`, `irrevStatement`.
* Sentence after Theorem 8.1 (L755–756, pointing to Remark 2.4):
  `equivarianceNeededStatement`.
* Corollary 8.2 `cor:insolv` (L758–771): `insolvGeneralStatement`,
  `insolvGeneralCAStatement`, `insolvConstStatement`,
  `insolvTrajStatement`, `leaderAsymStatement`,
  `leaderNeverReachedStatement`, `leaderElectionStatement`,
  `leaderRestrictStatement` (the mathematical core of L767–770),
  `insolvStatement`.
* Proposition 8.3 `prop:rank` (L773–779), with the definition of the
  p-rank: `rankRangeStatement`, `rankMonoStatement`,
  `rankTrajStatement`, `rankStatement`; well-definedness anchors of the
  definition: `rankCardStatement`, `rankIntrinsicStatement`.
* Prose after Proposition 8.3 (L786–794): `rankFullStatement`,
  `rankOneStatement`, `superlevelInvariantStatement`,
  `levelSetInvariantLiteral` (the literal reading — FALSE, see PAPER
  ISSUE) and its refutation target `levelSetInvariantFalseStatement`;
  `rankProseStatement`.
* Everything (paper claims only): `S07Statement`.

Standing conventions (paper §2, L200–203): `n ≥ 2`, `d ≥ 1`, finite
alphabet `Σ` with `σ = |Σ| ≥ 2` (σ = 1 only for counting statements; all
statements here are non-counting, so `2 ≤ σ` is carried as an explicit
hypothesis everywhere). Representation choices shared by every `Prop`:
* alphabet `Σ` = `Fin σ` (every statement here is invariant under
  relabelling the alphabet by a bijection, so this loses nothing);
* lattice `A = (Z/nZ)^d` = `Lat n d = Fin d → ZMod n`, `N = n^d`;
* `τ_v s` = `shift v s` with `(shift v s) u = s (u + v)` (paper L205);
* `Stab(s)` = `stab s : AddSubgroup (Lat n d)` (paper L206);
* "translation-equivariant" = `Equivariant Φ`, i.e.
  `∀ v s, Φ (shift v s) = shift v (Φ s)` (paper Def. 2.3, L231–233);
* `S_{n^d}` = `SS n d σ = {s | IsShiftSymmetric s}`, where
  `IsShiftSymmetric s := ∃ v, v ≠ 0 ∧ shift v s = s` is literally
  membership in `⋃_{0 ≠ v} S_{n^d}(v)` (paper Def. 2.2, L215–218);
* `S_{n^d}(v)` = `SV v = {s | shift v s = s}` (paper Def. 2.2, first
  expression, L212; the identification with `Fix(⟨v⟩)` is Definition
  2.2's own claim, frozen by the group owning §2);
* "trajectory" of `s` = the sequence `k ↦ Φ^[k] s` (synchronous
  iteration of the global map, paper Def. 2.3).
-/
import Shiftsym.Paper.Common
import Shiftsym.Lemmas.Torsion

namespace ShiftSym.P07

open ShiftSym

/-! ## Notation-level definitions -/

/-- `S_{n^d}(v) = {s : τ_v s = s}` (paper Definition 2.2, L212; the paper
uses it for `v ≠ 0`, which every statement below carries as a
hypothesis). -/
def SV {n d σ : ℕ} (v : Lat n d) : Set (Config n d (Fin σ)) :=
  {s | shift v s = s}

/-- `S_{n^d} = ⋃_{0 ≠ v ∈ A} S_{n^d}(v)` (paper Definition 2.2,
L215–218): membership is `IsShiftSymmetric s`, i.e.
`∃ v, v ≠ 0 ∧ shift v s = s`. -/
def SS (n d σ : ℕ) : Set (Config n d (Fin σ)) :=
  {s | IsShiftSymmetric s}

/-! ## Figure 2 caption (`fig:pattern-flip`, L725–736) -/

/-- **Figure 2 caption, left panel** (`fig:pattern-flip`, L729–732;
duplicate of Observation 7.3 `obs:extrema`, L706–709).

Paper (verbatim): "The prime/composite extremal pattern of
Observation~\ref{obs:extrema} ($\sigma=2$, exact arithmetic). Left, $d=2$:
$\log_{10}P^{\mathrm{unif}}$ has local dips at every prime
$5\le n\le40$ (shown here for $n\le30$)".

Formal: for every prime `p` with `5 ≤ p ≤ 40`,
`P^unif_{p^2} < P^unif_{(p-1)^2}` and `P^unif_{p^2} < P^unif_{(p+1)^2}`
at `σ = 2`.

Delta: "local dip" read as STRICT local minimum in `n` (both neighbours
strictly larger; brute force confirms strictness at all ten primes,
`s07/bf_dynamics.py`, part F); `log₁₀` is strictly increasing on the
positive reals and `P^unif > 0` here, so dips of `log₁₀ P` are dips of
`P` and the logarithm is dropped; `P^unif` = `probUnif` (Common.lean,
real division `|S| / σ^N`); `p - 1` is ℕ-subtraction, exact because
`p ≥ 5`. "(shown here for n ≤ 30)" describes the plot only
(NON-MATHEMATICAL).

PAPER ISSUE: none. -/
def captionDipsD2Statement : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → p ≤ 40 →
    probUnif p 2 2 < probUnif (p - 1) 2 2 ∧
      probUnif p 2 2 < probUnif (p + 1) 2 2

/-- **Figure 2 caption, boundary exception** (`fig:pattern-flip`,
L732–733; duplicate of `obs:extrema`, L709–711).

Paper (verbatim): "the boundary case $n=3$ is the audited exception."

Formal: `P^unif_{4^2} < P^unif_{3^2}` at `σ = 2`.

Delta: "exception" (to "local dips at every prime") is made precise by
the reason Observation 7.3 gives for it, `P(3) = 26/2^9 > 736/2^16 =
P(4)`; this implies that `3` is not a local minimum under any reading
(strict or non-strict).

PAPER ISSUE: none. -/
def captionBoundaryStatement : Prop :=
  probUnif 4 2 2 < probUnif 3 2 2

/-- **Figure 2 caption, right panel** (`fig:pattern-flip`, L733–734;
duplicate of `obs:extrema`, L712–716).

Paper (verbatim): "Right, $d=3$: the pattern breaks --- already
$P(5^3)>P(6^3)$, so the prime $5$ is no longer a local minimum."

Formal: `P^unif_{6^3} < P^unif_{5^3}` at `σ = 2`.

Delta: `P(m^3)` = `probUnif m 3 2`; the consequence "so 5 is no longer a
local minimum" is frozen separately as `captionD3NotMinStatement`.

PAPER ISSUE: none. -/
def captionD3Statement : Prop :=
  probUnif 6 3 2 < probUnif 5 3 2

/-- **Figure 2 caption, right panel, consequence** (`fig:pattern-flip`,
L734; duplicate of `obs:extrema`, L716).

Paper (verbatim): "so the prime $5$ is no longer a local minimum."

Formal: `¬ (P^unif_{5^3} ≤ P^unif_{4^3} ∧ P^unif_{5^3} ≤ P^unif_{6^3})`
at `σ = 2`.

Delta: "local minimum" (in `n`, neighbours `4` and `6`) is negated in its
NON-STRICT form; this is the stronger of the two possible negations and
implies `¬ (P(5^3) < P(4^3) ∧ P(5^3) < P(6^3))`, the negation of the
strict "local dip" reading used in `captionDipsD2Statement`, so the
sentence is frozen under both readings. It follows from
`captionD3Statement` alone (`P(5^3) > P(6^3)`, the reason the caption
gives). Added in repair round 1 (reviewer request) so that this sentence
of L725–736 is frozen explicitly. Exact values (`s07/repair_r1_checks.py`):
`log₁₀ P(4^3) = −8.79`, `log₁₀ P(5^3) = −28.61`, `log₁₀ P(6^3) = −31.67`.

PAPER ISSUE: none. -/
def captionD3NotMinStatement : Prop :=
  ¬ (probUnif 5 3 2 ≤ probUnif 4 3 2 ∧ probUnif 5 3 2 ≤ probUnif 6 3 2)

/-- All numerical claims of the Figure 2 caption. -/
def captionStatement : Prop :=
  captionDipsD2Statement ∧ captionBoundaryStatement ∧ captionD3Statement ∧
    captionD3NotMinStatement

/-! ## Theorem 8.1 (Irreversibility), L743–748 -/

/-- **Theorem 8.1, stabilizer form** (`thm:irrev`, L743–746).

Paper (verbatim): "Let $\Phi$ be translation-equivariant
(Definition~\ref{def:ca}). Then
$\Stab(\Phi(\ssb))\supseteq\Stab(\ssb)$ for every configuration $\ssb$".

Delta: `Φ` ranges over ALL maps `Config n d (Fin σ) → Config n d (Fin σ)`
satisfying `Equivariant Φ` (the hypothesis of the theorem; every CA of
Definition 2.3 is one, `caMap_equivariant`); `⊇` of subgroups = `≤` in
the subgroup lattice; standing hypotheses `n ≥ 2`, `d ≥ 1`, `σ ≥ 2`
carried explicitly (the conclusion does not need them).

PAPER ISSUE: none. -/
def irrevStabStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
      ∀ s : Config n d (Fin σ), stab s ≤ stab (Φ s)

/-- **Theorem 8.1, per-vector form** (`thm:irrev`, L746–747).

Paper (verbatim): "in particular, $\ssb\in S_{n^d}(\vv)$ implies
$\Phi(\ssb)\in S_{n^d}(\vv)$".

Delta: `v` ranges over the nonzero vectors (the domain on which
Definition 2.2 defines `S_{n^d}(v)`); `S_{n^d}(v)` = `SV v`.

PAPER ISSUE: none. -/
def irrevVecStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
      ∀ v : Lat n d, v ≠ 0 →
        ∀ s : Config n d (Fin σ), s ∈ SV v → Φ s ∈ SV v

/-- **Theorem 8.1, set form** (`thm:irrev`, L747–748).

Paper (verbatim): "and $\Phi(S_{n^d})\subseteq S_{n^d}$."

Delta: `Φ(S)` is the set image `Φ '' SS n d σ`.

PAPER ISSUE: none. -/
def irrevSetStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
      Φ '' SS n d σ ⊆ SS n d σ

/-- **Theorem 8.1** (`thm:irrev`, L743–748), all three parts. -/
def irrevStatement : Prop :=
  irrevStabStatement ∧ irrevVecStatement ∧ irrevSetStatement

/-! ## The sentence after Theorem 8.1 (L755–756) -/

/-- A global map in which all cells share the local rule `φ` but each
cell `u` reads its own, cell-dependent list of locations
`η u 1, …, η u b`: `Φ(s)(u) = φ(s(η u 1), …, s(η u b))`. This is the
"location-selecting" neighbourhood of Remark 2.4 (L245–250); with
`η u i = u + o_i` it is the CA of Definition 2.3. -/
def locMap {n d σ b : ℕ} (η : Lat n d → Fin b → Lat n d)
    (φ : (Fin b → Fin σ) → Fin σ) :
    Config n d (Fin σ) → Config n d (Fin σ) :=
  fun s u => φ (fun i => s (η u i))

/-- **Equivariance cannot be weakened to a shared local rule**
(L755–756, citing Remark 2.4 `rem:equivariance-needed`).

Paper (verbatim): "By Remark~\ref{rem:equivariance-needed}, the
equivariance hypothesis cannot be weakened to ``all cells share the
local rule.''"

Formal: it is NOT the case that every map with a shared local rule and
cell-dependent location-selecting neighbourhood (`locMap η φ`) satisfies
the conclusion `Φ(S_{n^d}) ⊆ S_{n^d}` of Theorem 8.1 (under the standing
hypotheses).

Delta: of the two weakenings discussed in Remark 2.4 (state-valued
neighbourhood functions, and location-selecting ones), the
location-selecting class is the smaller one, so a failure inside it is
the stronger of the two readings (it implies the state-valued one); the
conclusion that fails is taken to be the set form `Φ(S) ⊆ S` (the
per-vector and stabilizer forms then fail too). The concrete
counterexamples are Remark 2.4's own claims (owned by the §2 group);
here only the existence claim of L755–756 is frozen.

PAPER ISSUE: none. -/
def equivarianceNeededStatement : Prop :=
  ¬ ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
      ∀ (b : ℕ) (η : Lat n d → Fin b → Lat n d)
        (φ : (Fin b → Fin σ) → Fin σ),
        locMap η φ '' SS n d σ ⊆ SS n d σ

/-! ## Corollary 8.2 (Insolvability), L758–771 -/

/-- A *task* on `Z_n^d` over `Fin σ`: a set of admissible inputs, and for
each input the set of acceptable output configurations. (The paper does
not define "task"; this is the most general input/output specification,
and the explicit admissible-input set models the paper's escape clause
"or restrict the admissible inputs, e.g. to asymmetric configurations",
L767–770.) -/
structure Task (n d σ : ℕ) where
  /-- The inputs on which the task must be solved. -/
  admissible : Set (Config n d (Fin σ))
  /-- For each input, the acceptable outputs. -/
  accept : Config n d (Fin σ) → Set (Config n d (Fin σ))

/-- `Φ` *solves* `T`: from every admissible input `x`, the synchronous
trajectory `x, Φ x, Φ (Φ x), …` reaches an acceptable output for `x` at
SOME time step `k ≥ 0`. This is the weakest possible success notion
(no halting signal, no requirement to stay or to be a fixed point), so
unsolvability in this sense implies unsolvability in every stronger
sense (reach-and-stay, fixed point, prescribed time). -/
def Solves {n d σ : ℕ} (Φ : Config n d (Fin σ) → Config n d (Fin σ))
    (T : Task n d σ) : Prop :=
  ∀ x ∈ T.admissible, ∃ k : ℕ, Φ^[k] x ∈ T.accept x

/-- The hypothesis of Corollary 8.2: the task requires, on some
admissible input inside `S_{n^d}`, an output outside `S_{n^d}` — every
acceptable output for that input is asymmetric. -/
def RequiresLeavingS {n d σ : ℕ} (T : Task n d σ) : Prop :=
  ∃ x ∈ T.admissible, x ∈ SS n d σ ∧ T.accept x ⊆ (SS n d σ)ᶜ

/-- **Corollary 8.2, general statement** (`cor:insolv`, L759–761).

Paper (verbatim): "Let $\sigma\ge2$ and $N>1$. Any task requiring, on
some input, an output configuration outside $S_{n^d}$ reachable from an
input inside $S_{n^d}$ is unsolvable by translation-equivariant CA on
$\ZZ_n^d$".

Formal: if `T` satisfies `RequiresLeavingS T`, then no
translation-equivariant global map solves `T` (in the sense of
`Solves`).

Delta: "task" = `Task` (admissible inputs + acceptable outputs per
input); "requiring, on some input, an output … outside S reachable from
an input inside S" = `RequiresLeavingS` (one admissible input `x ∈ S`
ALL of whose acceptable outputs lie outside `S`); "solvable" = `Solves`
(reach an acceptable output at some time step — the weakest notion, so
this is the strongest unsolvability); "translation-equivariant CA" =
any map with `Equivariant Φ` (Definition 2.3 calls the two notions
equivalent; the offset-CA form is `insolvGeneralCAStatement`, which
this statement implies via `caMap_equivariant`); `N > 1` = `1 < n ^ d`
(implied by `n ≥ 2`, `d ≥ 1`, but stated as in the paper).

PAPER ISSUE: none. (The hypotheses `σ ≥ 2` and `N > 1` are not used by
this implication; they are what make it non-degenerate. `N > 1` makes
`S_{n^d}` nonempty — for `N = 1` there is no nonzero `v`, `S` is empty and
`RequiresLeavingS` can never hold. `σ ≥ 2` makes asymmetric
configurations exist, so that a task whose acceptable-output sets are
NONEMPTY can satisfy `RequiresLeavingS` — for `σ = 1` (and `N > 1`) the
only configuration is the constant one, which lies in `S`, so the
hypothesis forces `T.accept x = ∅`, a trivially unsolvable task. See
`insolvConstStatement`, `leaderAsymStatement`, `leaderElectionStatement`;
checks in `s07/repair_r1_checks.py`, part 3. Corrected in repair round 1:
the earlier wording "they are what make the hypothesis satisfiable" was
inaccurate for `σ`.) -/
def insolvGeneralStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 < n ^ d →
    ∀ T : Task n d σ, RequiresLeavingS T →
      ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
        ¬ Solves Φ T

/-- **Corollary 8.2, general statement, offset-CA form** (`cor:insolv`,
L759–761).

Same as `insolvGeneralStatement`, with "CA" read literally as
Definition 2.3: offsets `o_1, …, o_b` and a local rule `φ`, global map
`caMap offs φ`.

Delta: as for `insolvGeneralStatement`; `b` is arbitrary (including
`b = 0`).

PAPER ISSUE: none. -/
def insolvGeneralCAStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 < n ^ d →
    ∀ T : Task n d σ, RequiresLeavingS T →
      ∀ (b : ℕ) (offs : Fin b → Lat n d) (φ : (Fin b → Fin σ) → Fin σ),
        ¬ Solves (caMap offs φ) T

/-- **Corollary 8.2, symmetric inputs exist** (`cor:insolv`, L761–762).

Paper (verbatim): "symmetric inputs exist (all constants lie in
$S_{n^d}$)".

Formal: `S_{n^d}` is nonempty, and every constant configuration lies in
it.

Delta: none beyond the standing conventions.

PAPER ISSUE: none. -/
def insolvConstStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 < n ^ d →
    (∃ x : Config n d (Fin σ), x ∈ SS n d σ) ∧
      ∀ a : Fin σ, (fun _ : Lat n d => a) ∈ SS n d σ

/-- **Corollary 8.2, no trajectory leaves S** (`cor:insolv`, L762–763).

Paper (verbatim): "and by Theorem~\ref{thm:irrev} no trajectory leaves
$S_{n^d}$."

Formal: for equivariant `Φ`, `s ∈ S` implies `Φ^[k] s ∈ S` for every
`k`.

Delta: none beyond the standing conventions.

PAPER ISSUE: none. -/
def insolvTrajStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 < n ^ d →
    ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
      ∀ s ∈ SS n d σ, ∀ k : ℕ, Φ^[k] s ∈ SS n d σ

/-- A configuration with a *unique distinguished cell*: some state `a`
occupies exactly one cell. (For leader election, `a` is the leader
state; the other cells may carry any other states — in particular the
classical "one leader, all others followers" targets are included.) -/
def HasUniqueDistinguishedCell {n d σ : ℕ} (t : Config n d (Fin σ)) :
    Prop :=
  ∃ a : Fin σ, ∃! u : Lat n d, t u = a

/-- **Corollary 8.2, leader-election targets are asymmetric**
(`cor:insolv`, L763–765).

Paper (verbatim): "This covers leader election (the target
configuration with a unique distinguished cell is asymmetric for
$N>1$)".

Formal: every configuration with a unique distinguished cell lies
outside `S_{n^d}`.

Delta: "distinguished" = carrying a state that no other cell carries
(`HasUniqueDistinguishedCell`); the leader state is not fixed in
advance, which makes the class of targets as large as possible.

PAPER ISSUE: none (the claim even holds for `N = 1`, where `S` is
empty; the paper's `N > 1` is kept as stated). -/
def leaderAsymStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 < n ^ d →
    ∀ t : Config n d (Fin σ), HasUniqueDistinguishedCell t → t ∉ SS n d σ

/-- **Corollary 8.2, leader election never reached from a symmetric
input** (`cor:insolv`, L763–765 with L761–763).

Formal: under an equivariant `Φ`, no configuration on the trajectory of
a shift-symmetric input has a unique distinguished cell.

Delta: this is the combination "symmetric input + no trajectory leaves
S + targets asymmetric" that the corollary's "This covers leader
election" asserts; conventions as above.

PAPER ISSUE: none. -/
def leaderNeverReachedStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 < n ^ d →
    ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
      ∀ x ∈ SS n d σ, ∀ k : ℕ, ¬ HasUniqueDistinguishedCell (Φ^[k] x)

/-- The leader-election task with leader state `ℓ` (Smith 1971, as in the
2019 paper §II.C): every input is admissible; an output is acceptable iff
exactly one cell is in state `ℓ`. -/
def leaderTask (n d σ : ℕ) (ℓ : Fin σ) : Task n d σ where
  admissible := Set.univ
  accept := fun _ => {t | ∃! u : Lat n d, t u = ℓ}

/-- **Corollary 8.2, leader election is unsolvable** (`cor:insolv`,
L763–765).

Paper (verbatim): "This covers leader election".

Formal: for every leader state `ℓ`, no translation-equivariant map
solves `leaderTask n d σ ℓ`.

Delta: inputs unrestricted (`Set.univ`; the paper's escape clause of
restricting inputs is exactly what this excludes); acceptable outputs:
exactly one cell in state `ℓ`, others arbitrary (a superset of the
classical "one leader, all others followers" targets, so this is the
stronger unsolvability); "solves" = `Solves` (weakest notion).

PAPER ISSUE: none. -/
def leaderElectionStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 < n ^ d →
    ∀ ℓ : Fin σ,
      ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
        ¬ Solves Φ (leaderTask n d σ ℓ)

/-- The leader-election task with leader state `ℓ` on a prescribed set `X`
of admissible inputs: an output is acceptable iff exactly one cell is in
state `ℓ`. (`leaderTaskOn n d σ ℓ Set.univ = leaderTask n d σ ℓ` by
`rfl`, see the sanity checks.) -/
def leaderTaskOn (n d σ : ℕ) (ℓ : Fin σ) (X : Set (Config n d (Fin σ))) :
    Task n d σ where
  admissible := X
  accept := fun _ => {t | ∃! u : Lat n d, t u = ℓ}

/-- **Corollary 8.2, uniform deterministic synchronous leader election
must exclude every symmetric input** (`cor:insolv`, L766–770).

Paper (verbatim): "$d$-dimensional leader-election algorithms as in
\cite{nichitiu1999,stratmann2002} therefore necessarily break one of the
hypotheses (uniformity, determinism, synchrony) or restrict the
admissible inputs, e.g.\ to asymmetric configurations."

Formal: for every leader state `ℓ`, every set `X` of admissible inputs
and every translation-equivariant `Φ`: if `Φ` solves leader election on
`X` (`Solves Φ (leaderTaskOn n d σ ℓ X)`), then `X` contains no
shift-symmetric configuration (`X ∩ S_{n^d} = ∅`).

Delta: "keeps the hypotheses uniformity, determinism, synchrony" = the
algorithm is the synchronous iteration of one deterministic global map
that is translation-equivariant (`Equivariant Φ`, Definition 2.3; uniform
local rule with translation-invariant neighbourhood); the sentence is
read in its contrapositive form "an algorithm keeping all three
hypotheses must restrict its admissible inputs". "Restrict the admissible
inputs" is made precise as "the admissible set avoids `S_{n^d}`
entirely", i.e. `X ⊆` asymmetric configurations; this is the paper's own
example ("e.g. to asymmetric configurations") and it is what the
argument of the corollary gives. It implies the weakest literal reading
`X ≠ Set.univ` (because `S_{n^d} ≠ ∅`, `insolvConstStatement`), whose
`X = Set.univ` instance is `leaderElectionStatement`; so freezing the
avoidance form is a disclosed strengthening of the literal wording, not
a weakening. The reference to the specific cited algorithms (Nichitiu
1999, Stratmann 2002) is NON-MATHEMATICAL (see `insolvStatement`).
Added in repair round 1 (reviewer request). Non-vacuity: `X =` the
unique-`ℓ` configurations is solved by `Φ = id` (sanity check below).

PAPER ISSUE: none. -/
def leaderRestrictStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 < n ^ d →
    ∀ (ℓ : Fin σ) (X : Set (Config n d (Fin σ))),
      ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
        Solves Φ (leaderTaskOn n d σ ℓ X) → X ∩ SS n d σ = ∅

/-- **Corollary 8.2** (`cor:insolv`, L758–771), all mathematical parts.
NON-MATHEMATICAL (not frozen): "pattern recognition, and image
translation, exactly as in the two-dimensional discussion of [2019]"
(informal task names, not defined in the paper; every concrete instance
that requires a symmetric-to-asymmetric output is covered by
`insolvGeneralStatement` — note that "image translation" in the literal
sense of translating by a lattice vector `w` would be SOLVABLE, by the
one-offset CA `caMap (fun _ => w) (fun x => x 0) = shift w`, so the
paper means the image-processing task of the 2019 paper's Fig. 5); and,
in "d-dimensional leader-election algorithms as in [Nichitiu 1999,
Stratmann 2002] therefore necessarily break one of the hypotheses
(uniformity, determinism, synchrony) or restrict the admissible inputs",
the reference to the specific cited algorithms (whose mathematical core,
for any algorithm, is frozen as `leaderRestrictStatement`). -/
def insolvStatement : Prop :=
  insolvGeneralStatement ∧ insolvGeneralCAStatement ∧ insolvConstStatement ∧
    insolvTrajStatement ∧ leaderAsymStatement ∧
    leaderNeverReachedStatement ∧ leaderElectionStatement ∧
    leaderRestrictStatement

/-! ## Proposition 8.3 (Per-prime rank monotonicity), L773–779 -/

/-- The **`p`-rank** `rk_p(s) = dim_{F_p}(Stab(s) ∩ A[p])`, computed
"via Lemma 3.3" (paper L775–776): `A[p] = latTorsion n d p =
{x | p • x = 0}` is mapped onto `F_p^d = Fin d → ZMod p` by the Lemma 3.3
isomorphism `x = (n/p)·y ↦ y mod p` (`latTorsionEquiv`, built from
`y ↦ y.val * (n/p)`); the image of `Stab(s) ∩ A[p]` is an additive
subgroup of `F_p^d`, i.e. an `F_p`-subspace (`toZModSubmodule`), and
`rk_p(s)` is its `F_p`-dimension (`Module.finrank`).
The proof arguments only supply the `NeZero` instances that
`latTorsionEquiv` needs (and record the paper's "prime `p ∣ n`"). -/
noncomputable def rkP {n d σ p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hpn : p ∣ n) (s : Config n d (Fin σ)) : ℕ :=
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  Module.finrank (ZMod p)
    (AddSubgroup.toZModSubmodule p
      (((stab s ⊓ latTorsion n d p).addSubgroupOf (latTorsion n d p)).map
        (latTorsionEquiv hpn).toAddMonoidHom))

/-- **`p`-rank, cardinality anchor** (well-definedness of the definition
in `prop:rank`, L775–776; not a separate paper claim).

Formal: `|Stab(s) ∩ A[p]| = p^{rk_p(s)}`.

This pins `rkP` down uniquely (`k ↦ p^k` is injective for `p ≥ 2`) by a
quantity that does not mention the isomorphism, and is the form the
brute force checks (`s07/bf_dynamics.py`, part C). -/
def rankCardStatement : Prop :=
  ∀ n d σ : ℕ, ∀ hn : 2 ≤ n, 1 ≤ d → 2 ≤ σ →
    ∀ (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (s : Config n d (Fin σ)),
      Nat.card (stab s ⊓ latTorsion n d p : AddSubgroup (Lat n d))
        = p ^ rkP (by omega) hp hpn s

/-- **`p`-rank, intrinsic-dimension anchor** (well-definedness of the
definition in `prop:rank`, L775–776; not a separate paper claim).

Formal: `rk_p(s)` equals the `F_p`-dimension of the elementary abelian
group `Stab(s) ∩ A[p]` with its own `ZMod p`-module structure
(`AddCommMonoid.zmodModule`, available since `p • x = 0` on it), i.e.
the choice of the Lemma 3.3 isomorphism does not matter. -/
def rankIntrinsicStatement : Prop :=
  ∀ n d σ : ℕ, ∀ hn : 2 ≤ n, 1 ≤ d → 2 ≤ σ →
    ∀ (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (s : Config n d (Fin σ)),
      haveI : NeZero p := ⟨hp.ne_zero⟩
      letI : Module (ZMod p) (stab s ⊓ latTorsion n d p : AddSubgroup (Lat n d)) :=
        AddCommMonoid.zmodModule (fun x => Subtype.ext x.2.2)
      rkP (by omega) hp hpn s
        = Module.finrank (ZMod p)
            (stab s ⊓ latTorsion n d p : AddSubgroup (Lat n d))

/-- **Proposition 8.3, range of the `p`-rank** (`prop:rank`, L774–776).

Paper (verbatim): "For a prime $p\mid n$ define the \emph{$p$-rank} of
$\ssb$ as
$\rk_p(\ssb)=\dim_{\FF_p}\bigl(\Stab(\ssb)\cap\A[p]\bigr)\in\{0,\dots,d\}$
(via Lemma~\ref{lem:torsion})."

Formal: `rk_p(s) ∈ {0, …, d}` (`Finset.Icc 0 d`).

Delta: `rk_p` = `rkP` (Lemma 3.3 transport, see its docstring and the
anchors `rankCardStatement`, `rankIntrinsicStatement`); "prime `p ∣ n`"
= hypotheses `p.Prime`, `p ∣ n`.

PAPER ISSUE: none. -/
def rankRangeStatement : Prop :=
  ∀ n d σ : ℕ, ∀ hn : 2 ≤ n, 1 ≤ d → 2 ≤ σ →
    ∀ (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (s : Config n d (Fin σ)),
      rkP (by omega) hp hpn s ∈ Finset.Icc 0 d

/-- **Proposition 8.3, one-step monotonicity** (`prop:rank`, L776–778).

Paper (verbatim): "Under any translation-equivariant $\Phi$, every
$p$-rank is non-decreasing along every trajectory:
$\rk_p(\Phi(\ssb))\ge\rk_p(\ssb)$ for all $p\mid n$ simultaneously."

Formal: for equivariant `Φ`, every configuration `s` and EVERY prime
`p ∣ n`, `rk_p(s) ≤ rk_p(Φ s)`.

Delta: "simultaneously" = the conclusion is quantified over all primes
`p ∣ n` for the same `Φ` and `s`.

PAPER ISSUE: none. -/
def rankMonoStatement : Prop :=
  ∀ n d σ : ℕ, ∀ hn : 2 ≤ n, 1 ≤ d → 2 ≤ σ →
    ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
      ∀ s : Config n d (Fin σ), ∀ (p : ℕ) (hp : p.Prime) (hpn : p ∣ n),
        rkP (by omega) hp hpn s ≤ rkP (by omega) hp hpn (Φ s)

/-- **Proposition 8.3, monotonicity along trajectories** (`prop:rank`,
L776–778).

Paper (verbatim): "every $p$-rank is non-decreasing along every
trajectory".

Formal: for equivariant `Φ`, every `s` and every prime `p ∣ n`, the
sequence `k ↦ rk_p(Φ^[k] s)` is monotone (non-decreasing) in `k`.

Delta: none beyond the conventions above.

PAPER ISSUE: none. -/
def rankTrajStatement : Prop :=
  ∀ n d σ : ℕ, ∀ hn : 2 ≤ n, 1 ≤ d → 2 ≤ σ →
    ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
      ∀ s : Config n d (Fin σ), ∀ (p : ℕ) (hp : p.Prime) (hpn : p ∣ n),
        Monotone (fun k : ℕ => rkP (by omega) hp hpn (Φ^[k] s))

/-- **Proposition 8.3** (`prop:rank`, L773–779): range, one-step and
trajectory monotonicity, together with the two well-definedness anchors
of the definition of `rk_p`. -/
def rankStatement : Prop :=
  rankCardStatement ∧ rankIntrinsicStatement ∧ rankRangeStatement ∧
    rankMonoStatement ∧ rankTrajStatement

/-! ## Prose after Proposition 8.3 (L786–794) -/

/-- **Fully `p`-periodic configurations** (prose after `prop:rank`,
L790).

Paper (verbatim): "$\rk_p=d$ configurations are fully $p$-periodic".

Formal: `rk_p(s) = d ↔ A[p] ≤ Stab(s)`, i.e. `s` is invariant under every
translation of order dividing `p`; equivalently (since
`A[p] = ((n/p)Z/nZ)^d` is generated by the vectors `(n/p)·e_i`), `s` has
period `n/p` along every coordinate axis.

Delta: "fully `p`-periodic" read as "fixed by the whole `p`-torsion
`A[p]`", i.e. invariant under every period of ORDER `p` — the reading
that parallels the preceding clause "periodic along one direction of the
`p`-torsion" (`rankOneStatement`) and the only one under which the
sentence is true; the biconditional is the descriptive reading of "are"
(the level set IS the set of fully `p`-periodic configurations).

PAPER ISSUE: "fully `p`-periodic" is ambiguous, and false under the
standard reading "period `p` along every coordinate axis"
(`s(u + p·e_i) = s(u)` for all `i`). Translations by `p·e_i` are nonzero
elements of `Z_n^d` whenever `p < n`, but they have order `n/p`, not
`p`; the two readings agree only for `n = p^2`. Counterexamples
(exhaustive, reviewers' `G07_*_periodic.py` and `s07/repair_r1_checks.py`,
part 1): `n = 6, d = 1, p = 3, s = (0,1,0,1,0,1)` has
`Stab(s) = {0,2,4} = A[3]`, so `rk_3(s) = 1 = d`, but `s(u+3) ≠ s(u)`;
`n = 6, d = 1, p = 2, s = (0,0,1,0,0,1)` has `Stab(s) = {0,3} = A[2]`,
`rk_2(s) = 1 = d`, but no period `2`; conversely for `n = p` every
configuration has period `p`, but `rk_p = d` only for constants
(`n = 3, d = 1, s = (0,0,1)`: `rk_3 = 0`). The paper should say
"`rk_p = d` configurations are exactly those invariant under the whole
`p`-torsion `A[p]`, i.e. with period `n/p` in every coordinate
direction". The Lean body (unchanged in repair round 1) formalizes this
intended reading; the earlier justification "the only `p`-periods
available on `Z_n^d`" was wrong and has been removed. -/
def rankFullStatement : Prop :=
  ∀ n d σ : ℕ, ∀ hn : 2 ≤ n, 1 ≤ d → 2 ≤ σ →
    ∀ (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (s : Config n d (Fin σ)),
      rkP (by omega) hp hpn s = d ↔ latTorsion n d p ≤ stab s

/-- **Rank-one configurations** (prose after `prop:rank`, L788–789).

Paper (verbatim): "Geometrically, $\rk_p=1$ configurations are periodic
along one direction of the $p$-torsion (``stripes''/``slabs'')".

Formal: `rk_p(s) = 1 ↔` there is `w` of order `p` with
`Stab(s) ∩ A[p] = ⟨w⟩`.

Delta: "periodic along one direction of the `p`-torsion" read as "the
`p`-torsion periods form exactly one line" (one cyclic subgroup of order
`p`, Lemma 3.3's correspondence lines ↔ order-`p` subgroups); the
biconditional is the descriptive reading of "are"; "stripes/slabs" is
imagery (NON-MATHEMATICAL).

PAPER ISSUE: none. -/
def rankOneStatement : Prop :=
  ∀ n d σ : ℕ, ∀ hn : 2 ≤ n, 1 ≤ d → 2 ≤ σ →
    ∀ (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (s : Config n d (Fin σ)),
      rkP (by omega) hp hpn s = 1 ↔
        ∃ w : Lat n d, addOrderOf w = p ∧
          stab s ⊓ latTorsion n d p = AddSubgroup.zmultiples w

/-- The LITERAL reading of "each level set is an irreversible attractor"
(L790–791): every level set `{s : rk_p(s) = k}` is forward invariant
under every equivariant `Φ`. This is FALSE (see
`levelSetInvariantFalseStatement`); it is recorded only to make the
PAPER ISSUE precise and is not a target. -/
def levelSetInvariantLiteral : Prop :=
  ∀ n d σ : ℕ, ∀ hn : 2 ≤ n, 1 ≤ d → 2 ≤ σ →
    ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
      ∀ (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (s : Config n d (Fin σ)),
        rkP (by omega) hp hpn (Φ s) = rkP (by omega) hp hpn s

/-- **PAPER ISSUE witness** for L790–791 (not a paper claim): the literal
reading `levelSetInvariantLiteral` fails.

Evidence: `n = 2, d = 1, σ = 2, p = 2`, `s = (0, 1)` has
`Stab(s) = {0}`, `rk_2(s) = 0`, while the constant CA `Φ ≡ (0, 0)`
(equivariant; offsets `(0)`, rule `φ ≡ 0`) gives `Φ(s) = (0, 0)` with
`rk_2 = 1` (brute force `s07/bf_dynamics.py`, part D). -/
def levelSetInvariantFalseStatement : Prop :=
  ¬ levelSetInvariantLiteral

/-- **Superlevel sets are absorbing** (prose after `prop:rank`, L790–791,
corrected reading).

Paper (verbatim): "each level set is an irreversible attractor by
Proposition~\ref{prop:rank}."

Formal (intended reading): for every `k`, the superlevel set
`{s : rk_p(s) ≥ k}` is forward invariant under every equivariant `Φ`:
once a trajectory reaches `p`-rank `≥ k` it never drops below `k`.

Delta: "irreversible attractor" (undefined in the paper) read as
"forward-invariant set that cannot be left downwards".

PAPER ISSUE: as written ("each LEVEL set"), the claim is false: the
level sets `{rk_p = k}` with `k < d` are not forward invariant (see
`levelSetInvariantFalseStatement`: a constant CA moves `rk_2 = 0` to
`rk_2 = 1`); only the top level set `{rk_p = d}` is. The paper should
say "each superlevel set `{rk_p ≥ k}` is absorbing (an irreversible
trap)" — which is what is frozen here. -/
def superlevelInvariantStatement : Prop :=
  ∀ n d σ : ℕ, ∀ hn : 2 ≤ n, 1 ≤ d → 2 ≤ σ →
    ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ →
      ∀ (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (k : ℕ) (s : Config n d (Fin σ)),
        k ≤ rkP (by omega) hp hpn s →
          ∀ t : ℕ, k ≤ rkP (by omega) hp hpn (Φ^[t] s)

/-- All mathematical claims of the prose after Proposition 8.3, in the
corrected reading. NON-MATHEMATICAL (not frozen): "This replaces the
informal ``symmetry rank (for the dominant prime)'' of earlier drafts"
(history; its mathematical content "one rank per prime factor, all
monotone" is `rankMonoStatement`); "Kornyak's observation … is the
general heuristic; the proposition is its exact translation-stabilizer
form" (attribution/interpretation). -/
def rankProseStatement : Prop :=
  rankFullStatement ∧ rankOneStatement ∧ superlevelInvariantStatement

/-- Every mathematical claim of paper lines 725–800 (corrected reading
where a PAPER ISSUE is recorded). The issue witness
`levelSetInvariantFalseStatement` is deliberately NOT part of this
conjunction (it is not a paper claim). -/
def S07Statement : Prop :=
  captionStatement ∧ irrevStatement ∧ equivarianceNeededStatement ∧
    insolvStatement ∧ rankStatement ∧ rankProseStatement

/-! ## Non-vacuity and small-instance sanity checks (no main `Prop` is
proved here) -/

/-- The standing hypotheses of every statement are satisfiable
(`n = 2, d = 1, σ = 2`, `N = 2`). -/
example : 2 ≤ 2 ∧ 1 ≤ 1 ∧ 2 ≤ 2 ∧ 1 < 2 ^ 1 := by decide

/-- The rank hypotheses are satisfiable (`p = 2 ∣ n = 2`, `p = 3 ∣ 6`). -/
example : (Nat.Prime 2 ∧ 2 ∣ 2) ∧ (Nat.Prime 3 ∧ 3 ∣ 6) :=
  ⟨⟨Nat.prime_two, dvd_refl 2⟩, ⟨Nat.prime_three, ⟨2, rfl⟩⟩⟩

/-- Equivariant maps exist (the identity, and every offset CA). -/
example : Equivariant (id : Config 2 1 (Fin 2) → Config 2 1 (Fin 2)) :=
  fun _ _ => rfl

/-- The hypothesis `RequiresLeavingS` is satisfiable: the task "from the
constant input `0`, output any asymmetric configuration". -/
example : RequiresLeavingS
    (⟨Set.univ, fun _ => (SS 2 1 2)ᶜ⟩ : Task 2 1 2) :=
  ⟨fun _ => 0, Set.mem_univ _, ⟨fun _ => 1, by decide, rfl⟩, le_rfl⟩

/-- Leader-election targets exist on `Z_2` (`(1, 0)` has a unique cell
in state `1`), so `leaderTask` is not trivially unsolvable. -/
example : ∃ t : Config 2 1 (Fin 2), ∃! u : Lat 2 1, t u = 1 :=
  ⟨fun u => if u = 0 then 1 else 0, 0, by simp, fun y hy => by
    by_contra h; simp [h] at hy⟩

/-- `leaderTaskOn` with all inputs admissible is `leaderTask`. -/
example (ℓ : Fin 2) : leaderTaskOn 3 2 2 ℓ Set.univ = leaderTask 3 2 2 ℓ :=
  rfl

/-- Non-vacuity of `leaderRestrictStatement`: its hypothesis `Solves` is
satisfiable — the identity map (equivariant) solves leader election on
`X =` the configurations with exactly one cell in state `1` (at time
`k = 0`); this `X` is nonempty (example above) and avoids `S`. -/
example : Solves (id : Config 2 1 (Fin 2) → Config 2 1 (Fin 2))
    (leaderTaskOn 2 1 2 1 {t | ∃! u : Lat 2 1, t u = 1}) :=
  fun _ hx => ⟨0, hx⟩

/-- The `rankFullStatement` PAPER ISSUE witness on `Z_6`, `p = 3`:
`s = (0,1,0,1,0,1)` is fixed by every `v` with `3 • v = 0` (i.e.
`A[3] ≤ Stab(s)`, so `rk_3(s) = d = 1`), but not by the translation by
`3` (no period `3`). -/
example :
    (∀ v : Lat 6 1, 3 • v = 0 →
        shift v (fun u : Lat 6 1 => if (u 0).val % 2 = 1 then (1 : Fin 2) else 0)
          = (fun u : Lat 6 1 => if (u 0).val % 2 = 1 then (1 : Fin 2) else 0)) ∧
      shift (fun _ => (3 : ZMod 6))
          (fun u : Lat 6 1 => if (u 0).val % 2 = 1 then (1 : Fin 2) else 0)
        ≠ (fun u : Lat 6 1 => if (u 0).val % 2 = 1 then (1 : Fin 2) else 0) := by
  decide

/-- Literal "image translation" by a lattice vector is an offset CA:
`caMap (fun _ => w) (fun x => x 0) = shift w` (so it is solvable, which
is why the paper's "image translation" must mean the 2019 paper's
image-processing task; see `insolvStatement`). -/
example (w : Lat 3 2) :
    caMap (fun _ : Fin 1 => w) (fun x : Fin 1 → Fin 2 => x 0) = shift w :=
  rfl

/-- The `S(v)` and `S` used here agree with the shared definitions
(`IsShiftSymmetric`, `shift`) by `Iff.rfl`. -/
example (s : Config 2 1 (Fin 2)) : s ∈ SS 2 1 2 ↔ ∃ v, v ≠ 0 ∧ s ∈ SV v :=
  Iff.rfl

/-- Small-instance check of `leaderAsymStatement` (`n = 2, 3`, `d = 1`,
`σ = 2`, ALL configurations — written as `u ↦ ![b₀, …](u 0)` so that the
kernel `decide` only enumerates `Fin 2`-tuples; `∃!` unfolded since
mathlib has no `Fintype` decision procedure for it). -/
example : ∀ b₀ b₁ a : Fin 2, ∀ u : Lat 2 1,
    (fun w : Lat 2 1 => ![b₀, b₁] (w 0)) u = a →
    (∀ y, (fun w : Lat 2 1 => ![b₀, b₁] (w 0)) y = a → y = u) →
    ¬ IsShiftSymmetric (fun w : Lat 2 1 => ![b₀, b₁] (w 0)) := by
  unfold IsShiftSymmetric; decide

example : ∀ b₀ b₁ b₂ a : Fin 2, ∀ u : Lat 3 1,
    (fun w : Lat 3 1 => ![b₀, b₁, b₂] (w 0)) u = a →
    (∀ y, (fun w : Lat 3 1 => ![b₀, b₁, b₂] (w 0)) y = a → y = u) →
    ¬ IsShiftSymmetric (fun w : Lat 3 1 => ![b₀, b₁, b₂] (w 0)) := by
  unfold IsShiftSymmetric; decide

/-- Small-instance check behind `equivarianceNeededStatement` (Remark
2.4's location-selecting example, `n = 4, d = 1, σ = 2, b = 1`,
`φ = id`, every cell reads itself except cell `2`, which reads cell `1`):
`(0,1,0,1)` is shift-symmetric, its image `(0,1,1,1)` is not. -/
example :
    IsShiftSymmetric
        (fun u : Lat 4 1 => if (u 0).val % 2 = 1 then (1 : Fin 2) else 0) ∧
      ¬ IsShiftSymmetric
        (locMap (fun (u : Lat 4 1) (_ : Fin 1) => if u 0 = 2 then (fun _ => 1) else u)
          (fun x : Fin 1 → Fin 2 => x 0)
          (fun u : Lat 4 1 => if (u 0).val % 2 = 1 then (1 : Fin 2) else 0)) := by
  unfold IsShiftSymmetric locMap; decide

/-- Small-instance check of the PAPER ISSUE witness data
(`levelSetInvariantFalseStatement`): on `Z_2`, `s = (0, 1)` has trivial
stabilizer while its image under the constant CA is the constant `0`,
which is shift-symmetric. (On `Z_2`, `A[2]` is the whole lattice, so
`rk_2 = 0` iff asymmetric and `rk_2 = 1` iff shift-symmetric: this is the
rank jump `0 → 1`.) -/
example :
    ¬ IsShiftSymmetric (fun u : Lat 2 1 => if u = 0 then (0 : Fin 2) else 1) ∧
      IsShiftSymmetric (caMap (fun _ : Fin 1 => (0 : Lat 2 1))
        (fun _ : Fin 1 → Fin 2 => (0 : Fin 2))
        (fun u : Lat 2 1 => if u = 0 then (0 : Fin 2) else 1)) := by
  unfold IsShiftSymmetric caMap; decide

end ShiftSym.P07
