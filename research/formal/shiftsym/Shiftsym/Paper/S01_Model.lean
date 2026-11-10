/-
Phase H, group 01 (Model): frozen statements for §2 "Model" of
`shift_symmetry_d_dimensions.tex` (v3.1), paper lines 196–262
(Definitions 2.1–2.3, Remark 2.4) plus the boundary sentence of the §3
preamble that starts inside this range (lines 261–264, the
Gaussian-binomial convention).

Statements only: every claim is a `def …Statement : Prop`; nothing here is
proved except `rfl`-level literalness checks of the definitions and
satisfiability checks of hypotheses (`example`s), and display-only `#eval`
sanity runs of computable instances. Proofs belong in
`Shiftsym/Paper/Proofs/P01_Model.lean`.

Reused project definitions (all literal, see `Shiftsym/Definitions.lean`):
* `Lat n d := Fin d → ZMod n`                        — the lattice `𝔸 = (ℤ/nℤ)^d`;
* `Config n d A := Lat n d → A`                       — configurations `s : 𝔸 → Σ`;
* `shift v s := fun u => s (u + v)`                   — the translation `τ_v`;
* `stab s` (carrier `{v | shift v s = s}`)            — `Stab(s)`;
* `fixedBy A H := {s | ∀ h ∈ H, shift h s = s}`        — `Fix(H)`;
* `IsShiftSymmetric s := ∃ v, v ≠ 0 ∧ shift v s = s`  — membership in `S_{n^d}`;
* `Equivariant Φ := ∀ v s, Φ (shift v s) = shift v (Φ s)`;
* `caMap o φ := fun s u => φ (fun i => s (u + o i))`  — the offset-CA global map.
The paper-literal set-level objects (`stabSet`, `sOf`, `shiftSymSet`) are
introduced below, and their agreement with the project's `stab`,
`IsShiftSymmetric`, `numSS` is itself frozen as a fidelity `Prop` (to be
proved), so that no later group silently relies on an unchecked identification.

Global representation choices (Delta, apply to every statement below):
* The paper's arbitrary finite alphabet `Σ` is an arbitrary `A : Type` with
  `[Fintype A]` and `σ = Fintype.card A` (universe 0 suffices: every finite set
  has a `Type 0` copy). Only the concrete examples of Remark 2.4 use
  `Σ = {0,1}`, encoded as `Fin 2`.
* `ℤ/nℤ` is `ZMod n`; the paper's standing hypotheses `n ≥ 2`, `d ≥ 1` are
  explicit antecedents (so `ZMod 0 = ℤ` and the one-point lattice never occur).
* `σ ≥ 2` vs `σ ≥ 1`: Definition 2.1 fixes `σ ≥ 2` and allows `σ = 1` "for
  counting statements". Definitions 2.1/2.2 define the objects that the
  counting theorems count (also at `σ = 1`), so their embedded claims are
  frozen over the whole stated setting `σ ≥ 1` (this implies the `σ ≥ 2`
  reading). The claims of Definition 2.3 and Remark 2.4 are not counting
  statements, so they carry `σ ≥ 2`.
* "Does not support the irreversibility theorem" (Remark 2.4) has a strong and a
  weak formal reading (`BreaksIrreversibility`: `Φ(S) ⊄ S`; `ViolatesThm81`: the
  conclusion of Theorem 8.1 fails in some clause), and "location-selecting" has a
  narrow and a broad one (`locMap`: read locations depend on the cell;
  `locMapDep`: on the cell and the configuration). Every EXISTENCE claim is
  stated with (at least) the strong failure notion and the narrow class (the
  strongest reading), and every NON-EXISTENCE claim with the weak notion and the
  broad class (again the strongest reading), so each frozen `Prop` implies all of
  its readings (repair round 1, see the S01 report).

NON-MATHEMATICAL items of the range (not frozen; one-line reasons):
* "(for counting statements $\sigma=1$ is also allowed)" — a convention; it fixes
  the `σ`-ranges above.
* "updates all cells synchronously" — descriptive (the global map is a function
  of the whole configuration).
* "(and this is the property all dynamical results use)" — a meta-claim about the
  later proofs; the §8 groups check it through the hypotheses they freeze.
* "because $\eta$ may depend on the cell arbitrarily" — an explanation.
* "All cells share $\phi$" — true by construction of `etaMap`/`locMap`.
* "The two-dimensional source avoids this pitfall only inside its proofs, where
  the neighborhood is explicitly assumed to be given by shared relative offsets
  [banda2019, Lemma A.5]" — a bibliographic claim about the 2019 paper (checked by
  the round-1 fidelity reviewer against the 2019 text: the proof of Lemma A.5 does
  assume shared relative vectors `u_1, …, u_m`).
* "Definition 2.3 makes the hypothesis explicit from the start" — editorial.
* "Throughout, $n=\prod p_i^{\alpha_i}$ with $p_1<\dots<p_k$ prime and
  $k=\omega(n)$" (line 261) — notation (unique factorization).
-/
import Shiftsym.Paper.Common

namespace ShiftSym.P01

open ShiftSym

/-! ## Paper-literal objects -/

/-- `Stab(s) = {v ∈ 𝔸 : τ_v s = s}` as the literal SET (paper Def. 2.1, line 207).
(The project's `stab s` is a bundled `AddSubgroup` with this carrier; that the
set is a subgroup is the claim `stabSubgroupStatement`.) -/
def stabSet {n d : ℕ} {A : Type*} (s : Config n d A) : Set (Lat n d) :=
  {v | shift v s = s}

/-- `S_{n^d}(v) = {s : τ_v s = s}` (paper Def. 2.2, line 212). -/
def sOf {n d : ℕ} (A : Type*) (v : Lat n d) : Set (Config n d A) :=
  {s | shift v s = s}

/-- `S_{n^d} = ⋃_{0 ≠ v ∈ 𝔸} S_{n^d}(v)` — the literal union of Def. 2.2
(line 217). -/
def shiftSymSet (n d : ℕ) (A : Type*) : Set (Config n d A) :=
  ⋃ (v : Lat n d) (_ : v ≠ 0), sOf A v

/-- Remark 2.4 (line 238–240): the global map of "a neighborhood function
`η : 𝔸 × Σ^𝔸 → Σ^b` together with a shared local rule `φ`", namely
`Φ(s)(u) = φ(η(u, s))` (every cell applies the same `φ` to what `η` hands it).
Delta: `η` is curried, `η u s = η(u, s)`; `Σ^b` is `Fin b → A`. -/
def etaMap {n d b : ℕ} {A : Type*} (η : Lat n d → Config n d A → (Fin b → A))
    (φ : (Fin b → A) → A) : Config n d A → Config n d A :=
  fun s u => φ (η u s)

/-- Remark 2.4 (lines 246–247): `η` "only select[s] locations (each cell reads
actual cells, just not translation-uniform ones)": cell `u` reads the cells
`λ_1(u), …, λ_b(u)`, i.e. `η(u, s) = (s(λ_1 u), …, s(λ_b u))`.
Delta: here the read locations `λ_i : 𝔸 → 𝔸` depend on the cell only (the
narrow class: a fixed, cell-dependent wiring, as in the paper's example "every
cell read[s] itself except that cell 2 reads cell 1"). Existence claims use this
class (the stronger claims); non-existence claims use the broad class `locMapDep`
below, which contains this one (`rfl` check below). -/
def locMap {n d b : ℕ} {A : Type*} (lam : Fin b → Lat n d → Lat n d)
    (φ : (Fin b → A) → A) : Config n d A → Config n d A :=
  etaMap (fun u s i => s (lam i u)) φ

/-- Remark 2.4, the broad reading of "`η` only select[s] locations": since
`η : 𝔸 × Σ^𝔸 → Σ^b` may see the configuration, the location read in slot `i` by
cell `u` may depend on `u` AND on `s`: `η(u, s) = (s(λ_1(u,s)), …, s(λ_b(u,s)))`.
Used in every non-existence claim (the stronger claims). -/
def locMapDep {n d b : ℕ} {A : Type*} (lam : Fin b → Lat n d → Config n d A → Lat n d)
    (φ : (Fin b → A) → A) : Config n d A → Config n d A :=
  etaMap (fun u s i => s (lam i u s)) φ

/-- `Φ` is the global map of an offset cellular automaton (paper Def. 2.3,
lines 223–230): there are `b ≥ 1` offsets `o_1, …, o_b ∈ 𝔸` and a local rule
`φ : Σ^b → Σ` with `Φ(s)(u) = φ(s(u + o_1), …, s(u + o_b))`.
Delta: `b ≥ 1` as the notation `o_1, …, o_b` suggests (a constant map, the only
`b = 0` case, is also a `b = 1` CA whose rule ignores its input, so the class of
maps is the same either way). -/
def IsOffsetCA {n d : ℕ} {A : Type*} (Φ : Config n d A → Config n d A) : Prop :=
  ∃ b : ℕ, 1 ≤ b ∧ ∃ (o : Fin b → Lat n d) (φ : (Fin b → A) → A), Φ = caMap o φ

/-- The conclusion of Theorem 8.1 (`thm:irrev`, paper lines 743–748) for a map
`Φ`, transcribed clause by clause with the paper-literal objects:
"$\Stab(\Phi(\ssb))\supseteq\Stab(\ssb)$ for every configuration $\ssb$;
in particular, $\ssb\in S_{n^d}(\vv)$ implies $\Phi(\ssb)\in S_{n^d}(\vv)$, and
$\Phi(S_{n^d})\subseteq S_{n^d}$."
"`Φ` supports the irreversibility theorem" (Remark 2.4, lines 240–241) means
that this conclusion holds for `Φ`.
Delta: the per-vector clause ranges over `v ≠ 0` (where `S_{n^d}(v)` is defined,
Def. 2.2); the two "in particular" clauses are kept although they follow from
the first. -/
def Thm81Conclusion {n d : ℕ} {A : Type*} (Φ : Config n d A → Config n d A) : Prop :=
  (∀ s : Config n d A, stabSet s ⊆ stabSet (Φ s)) ∧
    (∀ (v : Lat n d) (s : Config n d A), v ≠ 0 → s ∈ sOf A v → Φ s ∈ sOf A v) ∧
    Φ '' shiftSymSet n d A ⊆ shiftSymSet n d A

/-- "`Φ` does not support the irreversibility theorem" (Remark 2.4, line 240–241),
WEAK (literal) reading: the conclusion of Theorem 8.1 fails for `Φ` (in some
clause; equivalently in its main clause `Stab(Φ s) ⊇ Stab(s)`, which implies the
other two). Used in every NON-existence claim (repair round 1: the fidelity
review showed that negating the strong notion `BreaksIrreversibility` there
certifies only `Φ(S) ⊆ S`, not Theorem 8.1). -/
def ViolatesThm81 {n d : ℕ} {A : Type*} (Φ : Config n d A → Config n d A) : Prop :=
  ¬ Thm81Conclusion Φ

/-- "`Φ` does not support the irreversibility theorem" (Remark 2.4, line 240),
STRONG reading: the weakest conclusion of Theorem 8.1, `Φ(S_{n^d}) ⊆ S_{n^d}`,
fails — some shift-symmetric configuration is mapped to a non-shift-symmetric
one. It implies `ViolatesThm81` (check below). Used ONLY in existence claims,
where it is the stronger reading (the paper's own counterexamples are of this
kind). -/
def BreaksIrreversibility {n d : ℕ} {A : Type*} (Φ : Config n d A → Config n d A) :
    Prop :=
  ∃ s : Config n d A, IsShiftSymmetric s ∧ ¬ IsShiftSymmetric (Φ s)

/-- On `(n, d, Σ)` some location-selecting map (narrow class `locMap`) with a
shared local rule and `b ≥ 1` read locations per cell breaks irreversibility
(strong notion). Existence uses only. -/
def LocBreaks (n d : ℕ) (A : Type) : Prop :=
  ∃ b : ℕ, 1 ≤ b ∧ ∃ (lam : Fin b → Lat n d → Lat n d) (φ : (Fin b → A) → A),
    BreaksIrreversibility (locMap lam φ)

/-- On `(n, d, Σ)` some location-selecting map (narrow class `locMap`, `b ≥ 1`)
with a shared local rule violates Theorem 8.1 (weak notion). -/
def LocViolates (n d : ℕ) (A : Type) : Prop :=
  ∃ b : ℕ, 1 ≤ b ∧ ∃ (lam : Fin b → Lat n d → Lat n d) (φ : (Fin b → A) → A),
    ViolatesThm81 (locMap lam φ)

/-- On `(n, d, Σ)` some location-selecting map in the BROAD class `locMapDep`
(read locations depending on cell and configuration, `b ≥ 1`) with a shared local
rule violates Theorem 8.1 (weak notion). This is the weakest existence notion of
the file; its negation is the strongest non-existence claim. -/
def LocDepViolates (n d : ℕ) (A : Type) : Prop :=
  ∃ b : ℕ, 1 ≤ b ∧ ∃ (lam : Fin b → Lat n d → Config n d A → Lat n d)
    (φ : (Fin b → A) → A), ViolatesThm81 (locMapDep lam φ)

/-- On `(n, d, Σ)` some location-selecting map with a shared local rule is not
translation-equivariant. -/
def LocNonEquivariant (n d : ℕ) (A : Type) : Prop :=
  ∃ b : ℕ, 1 ≤ b ∧ ∃ (lam : Fin b → Lat n d → Lat n d) (φ : (Fin b → A) → A),
    ¬ Equivariant (locMap lam φ)

/-! ### Concrete objects of Remark 2.4 (`d = 1`, `Σ = {0,1}` as `Fin 2`, `b = 1`) -/

/-- Cell `k` of the one-dimensional lattice `ℤ_n^1` (`Lat n 1 = Fin 1 → ZMod n`). -/
def cell1 {n : ℕ} (k : ZMod n) : Lat n 1 := fun _ => k

/-- Tuple notation `(x_0, …, x_{n-1})` for a configuration on `ℤ_n^1`: cell `u`
carries `x_k` where `k ∈ {0, …, n-1}` is the residue of `u`. -/
def tup1 {n : ℕ} [NeZero n] {A : Type*} (x : Fin n → A) : Config n 1 A :=
  fun u => x ⟨(u 0).val, ZMod.val_lt (u 0)⟩

/-- `φ = id` for `b = 1`: `Σ^1 → Σ`, `(x) ↦ x` (Delta: `Σ^1` identified with `Σ`
through the single coordinate). -/
def phiId : (Fin 1 → Fin 2) → Fin 2 := fun x => x 0

/-- The state-valued neighbourhood function of Remark 2.4 (`d = 1`, `n = 2`,
`b = 1`): `η_0(s) = (s_0)`, `η_1(s) = (0)`. -/
def etaState : Lat 2 1 → Config 2 1 (Fin 2) → (Fin 1 → Fin 2) :=
  fun u s => if u = cell1 0 then (fun _ => s (cell1 0)) else (fun _ => 0)

/-- Its global map `Φ(s)(u) = φ(η_u(s))` with `φ = id`. -/
def PhiState : Config 2 1 (Fin 2) → Config 2 1 (Fin 2) := etaMap etaState phiId

/-- The location selector of Remark 2.4 (`d = 1`, `n = 4`, `b = 1`): "every cell
read[s] itself except that cell 2 reads cell 1". -/
def lamLoc : Fin 1 → Lat 4 1 → Lat 4 1 :=
  fun _ u => if u = cell1 2 then cell1 1 else u

/-- Its global map with `φ = id`. -/
def PhiLoc : Config 4 1 (Fin 2) → Config 4 1 (Fin 2) := locMap lamLoc phiId

/-! ### Literalness checks (definitional unfolding only) -/

example {n d : ℕ} {A : Type*} (v : Lat n d) (s : Config n d A) (u : Lat n d) :
    shift v s u = s (u + v) := rfl
example {n d : ℕ} {A : Type*} (s : Config n d A) :
    (stab s : Set (Lat n d)) = stabSet s := rfl
example {n d : ℕ} {A : Type*} (H : AddSubgroup (Lat n d)) :
    fixedBy A H = {s : Config n d A | ∀ h ∈ H, shift h s = s} := rfl
example {n d b : ℕ} {A : Type*} (o : Fin b → Lat n d) (φ : (Fin b → A) → A)
    (s : Config n d A) (u : Lat n d) : caMap o φ s u = φ (fun i => s (u + o i)) := rfl
example {n d b : ℕ} {A : Type*} (lam : Fin b → Lat n d → Lat n d)
    (φ : (Fin b → A) → A) (s : Config n d A) (u : Lat n d) :
    locMap lam φ s u = φ (fun i => s (lam i u)) := rfl
example {n d : ℕ} {A : Type*} (Φ : Config n d A → Config n d A) :
    Equivariant Φ ↔ ∀ (v : Lat n d) (s : Config n d A), Φ (shift v s) = shift v (Φ s) :=
  Iff.rfl
example {n d : ℕ} {A : Type*} (s : Config n d A) :
    IsShiftSymmetric s ↔ ∃ v : Lat n d, v ≠ 0 ∧ shift v s = s := Iff.rfl
-- An offset CA is in particular a location-selecting map (`λ_i u = u + o_i`):
example {n d b : ℕ} {A : Type*} (o : Fin b → Lat n d) (φ : (Fin b → A) → A) :
    caMap o φ = locMap (fun i u => u + o i) φ := rfl
-- The narrow location class is contained in the broad one:
example {n d b : ℕ} {A : Type*} (lam : Fin b → Lat n d → Lat n d) (φ : (Fin b → A) → A) :
    locMap lam φ = locMapDep (fun i u _ => lam i u) φ := rfl
example {n d b : ℕ} {A : Type*} (lam : Fin b → Lat n d → Config n d A → Lat n d)
    (φ : (Fin b → A) → A) (s : Config n d A) (u : Lat n d) :
    locMapDep lam φ s u = φ (fun i => s (lam i u s)) := rfl

/-! ### Monotonicity of the readings (why the chosen reading is the strongest)

Strong failure implies weak failure, and the narrow class embeds in the broad one,
so `LocBreaks → LocViolates → LocDepViolates`: existence claims stated with
`LocBreaks` and non-existence claims stated with `¬ LocDepViolates` imply every
other combination. (Small bridging checks, not paper claims.) -/
example {n d : ℕ} {A : Type*} (Φ : Config n d A → Config n d A) :
    BreaksIrreversibility Φ → ViolatesThm81 Φ := by
  rintro ⟨s, ⟨v, hv0, hv⟩, hΦ⟩ ⟨_, _, hC⟩
  have hs : s ∈ shiftSymSet n d A := Set.mem_iUnion₂.mpr ⟨v, hv0, hv⟩
  obtain ⟨w, hw0, hw⟩ := Set.mem_iUnion₂.mp (hC ⟨s, hs, rfl⟩)
  exact hΦ ⟨w, hw0, hw⟩
example (n d : ℕ) (A : Type) : LocViolates n d A → LocDepViolates n d A :=
  fun ⟨b, hb, lam, φ, h⟩ => ⟨b, hb, fun i u _ => lam i u, φ, h⟩

/-! ## Definition 2.1 (Lattice and configurations), lines 200–208 -/

/-- **Def. 2.1, finiteness** (lines 201–204).
Paper: "Fix integers $n\ge2$, $d\ge1$ … The lattice is the finite abelian group
$\A=(\ZZ/n\ZZ)^d$ with $N=n^d$ cells."
Delta: `𝔸 = Lat n d = Fin d → ZMod n`; "finite" is `Finite (Lat n d)`.
No alphabet enters. -/
def latFiniteStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d → Finite (Lat n d)

/-- **Def. 2.1, abelian group** (line 203): "$\A=(\ZZ/n\ZZ)^d$ … the finite
abelian group".
Delta: the group structure is mathlib's componentwise `ZMod n` addition on the
Pi type (the one `shift` uses); "abelian" is the literal commutativity law. -/
def latAbelianStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d → ∀ a b : Lat n d, a + b = b + a

/-- **Def. 2.1, cell count** (line 203): "with $N=n^d$ cells".
Delta: `Nat.card` (which would be `0` for an infinite type; finiteness is the
separate claim `latFiniteStatement`). -/
def latCardStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d → Nat.card (Lat n d) = n ^ d

/-- **Def. 2.1, translations act** (lines 204–206): "For $\vv\in\A$, the
\emph{translation} $\tau_\vv$ acts by $(\tau_\vv\ssb)(\uu)=\ssb(\uu+\vv)$".
Delta: "acts" read as an action of the group `𝔸` on `Σ^𝔸`: `τ_0 = id` and
`τ_{v+w} = τ_v ∘ τ_w` (with this convention `(τ_v(τ_w s))(u) = s(u + v + w)`;
`𝔸` is abelian, so the order is immaterial). Setting `σ ≥ 1` (see header). -/
def translationActsStatement : Prop :=
  ∀ (n d : ℕ) (A : Type) [Fintype A], 2 ≤ n → 1 ≤ d → 1 ≤ Fintype.card A →
    (∀ s : Config n d A, shift 0 s = s) ∧
    (∀ (v w : Lat n d) (s : Config n d A), shift (v + w) s = shift v (shift w s))

/-- **Def. 2.1, the stabilizer is a subgroup** (line 207):
"$\Stab(\ssb)=\{\vv\in\A:\tau_\vv\ssb=\ssb\}$ is a subgroup of $\A$."
Delta: "is a subgroup" = there is an `AddSubgroup` of `Lat n d` whose carrier is
exactly the literal set `stabSet s`. (The project's `stab s` was built with
this carrier; this `Prop` re-asserts the closure laws as a claim rather than
trusting the construction.) Setting `σ ≥ 1` (see header). -/
def stabSubgroupStatement : Prop :=
  ∀ (n d : ℕ) (A : Type) [Fintype A], 2 ≤ n → 1 ≤ d → 1 ≤ Fintype.card A →
    ∀ s : Config n d A, ∃ H : AddSubgroup (Lat n d), (H : Set (Lat n d)) = stabSet s

/-- **Definition 2.1, all embedded claims** (conjunction). -/
def def21Statement : Prop :=
  latFiniteStatement ∧ latAbelianStatement ∧ latCardStatement ∧
    translationActsStatement ∧ stabSubgroupStatement

/-! ## Definition 2.2 (Shift-symmetry), lines 210–220 -/

/-- **Def. 2.2, `S(v) = Fix(⟨v⟩)`** (lines 211–214): "For $\vv\neq\mathbf 0$ let
$S_{n^d}(\vv)=\{\ssb:\tau_\vv\ssb=\ssb\}=\Fix(\langle\vv\rangle)$, where for a
subgroup $H\le\A$ we write
$\Fix(H)=\{\ssb:\tau_{\mathbf h}\ssb=\ssb\ \forall\,\mathbf h\in H\}$."
Delta: `⟨v⟩` is `AddSubgroup.closure {v}` (literally the subgroup generated by
`v`); `Fix(H)` is the project's literal `fixedBy A H`; the hypothesis `v ≠ 0`
is kept although the equality also holds for `v = 0`. Setting `σ ≥ 1`. -/
def sOfEqFixStatement : Prop :=
  ∀ (n d : ℕ) (A : Type) [Fintype A], 2 ≤ n → 1 ≤ d → 1 ≤ Fintype.card A →
    ∀ v : Lat n d, v ≠ 0 → sOf A v = fixedBy A (AddSubgroup.closure {v})

/-- **Def. 2.2, union = nontrivial stabilizer** (lines 215–218): "The set of
\emph{shift-symmetric configurations} is
$S_{n^d}=\bigcup_{\mathbf 0\neq\vv\in\A}S_{n^d}(\vv)=\{\ssb:\Stab(\ssb)\neq\{\mathbf 0\}\}$."
The first equality is the definition (`shiftSymSet`); the second is the claim.
Delta: `Stab(s) ≠ {0}` compares the literal set `stabSet s` with the singleton
set `{0}`. Setting `σ ≥ 1`. -/
def unionEqStabStatement : Prop :=
  ∀ (n d : ℕ) (A : Type) [Fintype A], 2 ≤ n → 1 ≤ d → 1 ≤ Fintype.card A →
    shiftSymSet n d A = {s | stabSet s ≠ {0}}

/-- **Definition 2.2, all embedded claims** (conjunction). -/
def def22Statement : Prop :=
  sOfEqFixStatement ∧ unionEqStabStatement

/-! ### Fidelity links to the project-wide definitions (not paper claims)

These are frozen so that every later group that counts or reasons with the
project's `IsShiftSymmetric` / `numSS` provably talks about the paper's
`S_{n^d}`. They are stated without the paper's standing hypotheses because they
hold for all parameters (they are identifications of definitions, not results). -/

/-- **Fidelity: `IsShiftSymmetric` is membership in the paper's union
`S_{n^d}`** (Def. 2.2, line 217). Any `n, d` and any alphabet type. -/
def isShiftSymmetricFidelityStatement : Prop :=
  ∀ (n d : ℕ) (A : Type), {s : Config n d A | IsShiftSymmetric s} = shiftSymSet n d A

/-- **Fidelity: `numSS n d σ = |S_{n^d}|`** for the alphabet `Fin σ`, with
`S_{n^d}` the paper's literal union (Common.lean's `numSS` is
`Nat.card {s // IsShiftSymmetric s}`). Any `n, d, σ`. -/
def numSSFidelityStatement : Prop :=
  ∀ n d σ : ℕ, numSS n d σ = Nat.card (shiftSymSet n d (Fin σ))

/-! ## Definition 2.3 (Equivariant cellular automaton), lines 222–234 -/

/-- **Def. 2.3, offset CA ⇒ equivariant** (lines 223–233): "A \emph{cellular
automaton} on $\A$ over $\Sigma$ is given by a finite list of \emph{offsets}
$\mathbf o_1,\dots,\mathbf o_b\in\A$ and a \emph{local rule}
$\phi:\Sigma^b\to\Sigma$; the \emph{global map} $\Phi:\Sigma^{\A}\to\Sigma^{\A}$
updates all cells synchronously:
$\Phi(\ssb)(\uu)=\phi\bigl(\ssb(\uu+\mathbf o_1),\dots,\ssb(\uu+\mathbf o_b)\bigr)$.
Equivalently (and this is the property all dynamical results use), $\Phi$ is
\emph{translation-equivariant}: $\Phi(\tau_\vv\ssb)=\tau_\vv\Phi(\ssb)$ for all
$\vv\in\A$."
This `Prop` is the direction "offset CA ⇒ equivariant".
Delta: global map = project's literal `caMap o φ`; offsets `o : Fin b → Lat n d`
(a list, repetitions allowed), `b ≥ 1`; `Σ^b = Fin b → A`. Setting `σ ≥ 2`. -/
def caEquivariantStatement : Prop :=
  ∀ (n d : ℕ) (A : Type) [Fintype A], 2 ≤ n → 1 ≤ d → 2 ≤ Fintype.card A →
    ∀ b : ℕ, 1 ≤ b → ∀ (o : Fin b → Lat n d) (φ : (Fin b → A) → A),
      Equivariant (caMap o φ)

/-- **Def. 2.3, equivariant ⇒ offset CA** (line 231, "Equivalently"): every
translation-equivariant map `Φ : Σ^𝔸 → Σ^𝔸` on the finite torus is the global
map of some offset CA. (Same quotation as `caEquivariantStatement`.)
Delta: "Equivalently" is read as equality of the two classes of maps
`Σ^𝔸 → Σ^𝔸`; this is the converse direction, with an arbitrary (unbounded)
finite number `b ≥ 1` of offsets as the definition allows — no locality
bound is claimed (with a bounded neighbourhood the converse would be false).
Setting `σ ≥ 2`. -/
def equivariantCAStatement : Prop :=
  ∀ (n d : ℕ) (A : Type) [Fintype A], 2 ≤ n → 1 ≤ d → 2 ≤ Fintype.card A →
    ∀ Φ : Config n d A → Config n d A, Equivariant Φ → IsOffsetCA Φ

/-- **Def. 2.3, the equivalence** ("Equivalently …", line 231) as a single
biconditional: a map `Σ^𝔸 → Σ^𝔸` is an offset-CA global map iff it is
translation-equivariant. Setting `σ ≥ 2`. -/
def caIffEquivariantStatement : Prop :=
  ∀ (n d : ℕ) (A : Type) [Fintype A], 2 ≤ n → 1 ≤ d → 2 ≤ Fintype.card A →
    ∀ Φ : Config n d A → Config n d A, IsOffsetCA Φ ↔ Equivariant Φ

/-- **Definition 2.3, all embedded claims** (conjunction of both directions and
the biconditional form). -/
def def23Statement : Prop :=
  caEquivariantStatement ∧ equivariantCAStatement ∧ caIffEquivariantStatement

/-! ## Remark 2.4 (Equivariance is necessary, not cosmetic), lines 236–255 -/

/-- **Rem. 2.4, η-style maps need not be equivariant** (lines 238–242):
"Definitions in the style of ``a neighborhood function
$\eta:\A\times\Sigma^{\A}\to\Sigma^b$ together with a shared local rule
$\phi$'' do \emph{not} imply equivariance and do \emph{not} support the
irreversibility theorem, because $\eta$ may depend on the cell arbitrarily."
This `Prop` is the first half ("do not imply equivariance").
Delta: read inside the paper's fixed setting ("Fix integers $n\ge2$, $d\ge1$ and
a finite alphabet …", Def. 2.1): for EVERY such `(n, d, Σ)` there are `b ≥ 1`,
`η` and `φ` whose global map `Φ(s)(u) = φ(η(u,s))` is not equivariant. The
weaker purely existential reading (some setting admits such a map) is implied,
and is also witnessed by `stateExampleNotEquivariantStatement`. Setting `σ ≥ 2`. -/
def etaNotEquivariantStatement : Prop :=
  ∀ (n d : ℕ) (A : Type) [Fintype A], 2 ≤ n → 1 ≤ d → 2 ≤ Fintype.card A →
    ∃ b : ℕ, 1 ≤ b ∧ ∃ (η : Lat n d → Config n d A → (Fin b → A)) (φ : (Fin b → A) → A),
      ¬ Equivariant (etaMap η φ)

/-- **Rem. 2.4, η-style maps break irreversibility** (same quotation, second
half: "do \emph{not} support the irreversibility theorem").
Delta: as in `etaNotEquivariantStatement` (universal over the setting, `b ≥ 1`);
"not support" = `BreaksIrreversibility`, the failure of the weakest conclusion
`Φ(S_{n^d}) ⊆ S_{n^d}` of Theorem 8.1 — the strong reading, which implies the
weak one (`ViolatesThm81`); this is an existence claim, so the strong reading is
the stronger statement. Setting `σ ≥ 2`. -/
def etaBreaksStatement : Prop :=
  ∀ (n d : ℕ) (A : Type) [Fintype A], 2 ≤ n → 1 ≤ d → 2 ≤ Fintype.card A →
    ∃ b : ℕ, 1 ≤ b ∧ ∃ (η : Lat n d → Config n d A → (Fin b → A)) (φ : (Fin b → A) → A),
      BreaksIrreversibility (etaMap η φ)

/-- **Rem. 2.4, the state-valued counterexample** (lines 242–245):
"Counterexample for state-valued $\eta$ ($d=1$, $n=2$, $\Sigma=\{0,1\}$, $b=1$):
let $\eta_0(\ssb)=(s_0)$, $\eta_1(\ssb)=(0)$, and $\phi=\mathrm{id}$. All cells
share $\phi$, yet the shift-symmetric configuration $(1,1)$ maps to $(1,0)$,
which is not shift-symmetric."
Delta: `Σ = Fin 2`; `PhiState = etaMap etaState phiId`; tuples via `tup1`
(`(x_0, x_1)` = value `x_k` at cell `k`). "All cells share `φ`" holds by
construction of `etaMap` (non-mathematical). -/
def stateExampleStatement : Prop :=
  PhiState (tup1 ![1, 1]) = tup1 ![1, 0] ∧
    IsShiftSymmetric (tup1 (n := 2) ![(1 : Fin 2), 1]) ∧
    ¬ IsShiftSymmetric (tup1 (n := 2) ![(1 : Fin 2), 0])

/-- **Rem. 2.4, the state-valued counterexample is not equivariant** (implicit:
the example is offered as the counterexample to "imply equivariance" as well,
lines 240–242). Delta: `PhiState` as in `stateExampleStatement`. -/
def stateExampleNotEquivariantStatement : Prop :=
  ¬ Equivariant PhiState

/-- **Rem. 2.4, the location-selecting counterexample** (lines 248–250):
"with $d=1$, $n=4$, $\phi=\mathrm{id}$, let every cell read itself except that
cell $2$ reads cell $1$; then $(0,1,0,1)$, fixed by the shift $2$, maps to
$(0,1,1,1)$, which is not."
Delta: `Σ = Fin 2` (the paper leaves `Σ` implicit; the tuples use only 0, 1,
as in the first example); `b = 1`; `PhiLoc = locMap lamLoc phiId`.
"which is not" is elliptical — it is frozen in both readings: not fixed by the
shift 2, and (what the remark needs) not shift-symmetric at all. -/
def locExampleStatement : Prop :=
  shift (cell1 2) (tup1 (n := 4) ![(0 : Fin 2), 1, 0, 1]) = tup1 ![0, 1, 0, 1] ∧
    PhiLoc (tup1 ![0, 1, 0, 1]) = tup1 ![0, 1, 1, 1] ∧
    shift (cell1 2) (tup1 (n := 4) ![(0 : Fin 2), 1, 1, 1]) ≠ tup1 ![0, 1, 1, 1] ∧
    ¬ IsShiftSymmetric (tup1 (n := 4) ![(0 : Fin 2), 1, 1, 1])

/-- **Rem. 2.4, the location-selecting counterexample is not equivariant**
(implicit: "the conclusion is the same", where the conclusion includes "do not
imply equivariance"). -/
def locExampleNotEquivariantStatement : Prop :=
  ¬ Equivariant PhiLoc

/-- **Rem. 2.4, location-selecting maps need not be equivariant, from `n = 4` on**
(lines 245–248): "If one insists that $\eta$ only select \emph{locations} (each
cell reads actual cells, just not translation-uniform ones), the conclusion is
the same from $n=4$ on".
This `Prop` is the "do not imply equivariance" half of "the conclusion", in the
paper's literal range `n ≥ 4`, universal over the setting as in
`etaNotEquivariantStatement` (all `d ≥ 1`, all `Σ` with `σ ≥ 2`). This half is
TRUE as written (see `locNotEquivariantFromTwoStatement` for the sharper truth).
Delta: location-selecting maps = `locMap` (`b ≥ 1` cell-dependent read
locations, shared `φ`). -/
def locNotEquivariantStatement : Prop :=
  ∀ (n d : ℕ) (A : Type) [Fintype A], 4 ≤ n → 1 ≤ d → 2 ≤ Fintype.card A →
    LocNonEquivariant n d A

/-- **Rem. 2.4, PAPER ISSUE — the literal "from `n = 4` on" is false for the
irreversibility half.** (Same quotation as `locNotEquivariantStatement`.)
The literal reading "for every `n ≥ 4` (in the remark's own setting `d = 1`,
`Σ = {0,1}`) some location-selecting map does not support the irreversibility
theorem" fails at `n = 5` (indeed at every prime `n` in `d = 1`): on `ℤ_p^1` every
nonzero translation generates the whole group, so every stabilizer is `{0}` or
all of `ℤ_p`, and in the second case `s` is constant; a location-selecting map
with a shared `φ` sends a constant configuration to a constant one (all read cells
carry the same value), so the full conclusion of Theorem 8.1 holds
(`locPrimeThm81Statement`).
This `Prop` refutes the literal reading in its WEAKEST form, hence in every form:
"does not support" is the weak notion `ViolatesThm81` (some clause of
Theorem 8.1 fails) and the class is the broad `locMapDep` — so the refuted
universal claim is the weakest available, and its refutation implies the
refutations for `BreaksIrreversibility` and for the narrow class `locMap`
(monotonicity checks above). The readings universal over `d` or over `Σ` are
refuted a fortiori.
Evidence: Python (`bf/S01_repair_r1.py`, literal definitions, all clauses of
Theorem 8.1): exhaustive over all `λ`, `φ` with `b ≤ 2` at (n,d,σ) =
(2,1,2),(3,1,2),(2,1,3) and `b = 1` at (5,1,2),(3,1,3), and `b = 1` at
(7,1,2),(5,1,3) with the witness `s` restricted to `S_{n^d}` (exact: a failure of
any clause of Theorem 8.1 is witnessed by a configuration with a nonzero
period): no violating narrow map; FULL enumeration of the broad class (all `s`-dependent
`λ`) at (2,1,2) with `b ≤ 2` and (2,1,3) with `b = 1`: no violating map. Lean
`#eval` of the `b = 1` slices below.
Repair round 1 (fidelity review, exploit lens): the previous version refuted only
`∀ n ≥ 4, LocBreaks n 1 (Fin 2)` (strong notion), a strictly weaker refutation;
the reviewer's kernel-checked witness on `ℤ_6` (cell `u` reads cell `u mod 2`)
violates Theorem 8.1 without breaking `Φ(S) ⊆ S` (reproduced by `#eval` below). -/
def locFromFourRefutedStatement : Prop :=
  ¬ (∀ n : ℕ, 4 ≤ n → LocDepViolates n 1 (Fin 2))

/-- **Rem. 2.4, PAPER ISSUE — location-selecting maps DO support Theorem 8.1 on
every prime cycle `ℤ_p^1`** (the positive content behind
`locFromFourRefutedStatement`; reviewer's "missing" item, repair round 1). For
every prime `p`, every alphabet with `σ ≥ 2`, every number `b` of read slots
(`b = 0` included: then `Φ` is constant), every choice of read locations
`λ_i(u, s)` depending on the cell AND the configuration (the broad class
`locMapDep`, which contains `locMap`) and every shared `φ`, the full conclusion of
Theorem 8.1 holds (`Thm81Conclusion`: stabilizer, per-vector and set clauses).
Delta: `d = 1` as in the remark's setting (in `d ≥ 2` it fails, see
`locIffStatement`); `ℤ_p^1 = Lat p 1`. Evidence as in
`locFromFourRefutedStatement`. -/
def locPrimeThm81Statement : Prop :=
  ∀ (p : ℕ) (A : Type) [Fintype A], p.Prime → 2 ≤ Fintype.card A →
    ∀ (b : ℕ) (lam : Fin b → Lat p 1 → Config p 1 A → Lat p 1) (φ : (Fin b → A) → A),
      Thm81Conclusion (locMapDep lam φ)

/-- **Rem. 2.4, corrected claim (PAPER ISSUE repair) — exact range of the
location-selecting counterexamples.** For every `n ≥ 2`, `d ≥ 1` and alphabet
with `σ ≥ 2`, under EVERY reading of "location-selecting" and of "does not
support the irreversibility theorem": a location-selecting map with a shared
local rule that does not support Theorem 8.1 exists iff NOT (`d = 1` and `n`
prime). Equivalently: in `d = 1` exactly for composite `n` (the least being
`n = 4`, so none for `n ∈ {2, 3}`), and in every dimension `d ≥ 2` for every
`n ≥ 2`.
The three conjuncts are the strongest existence notion (`LocBreaks`: narrow
class, `Φ(S) ⊄ S`), the main faithful reading (`LocViolates`: narrow class,
Theorem 8.1 fails), and the weakest existence notion (`LocDepViolates`: broad
class, Theorem 8.1 fails); since `LocBreaks → LocViolates → LocDepViolates`, the
first and last pin down every intermediate reading (e.g. broad class with
`Φ(S) ⊄ S`).
What the paper should say instead of "the conclusion is the same from $n=4$ on":
"…the conclusion is the same whenever $\ZZ_n^d$ is not of prime order (in
$d=1$: for every composite $n$, the smallest being $n=4$)".
Brute-force evidence (Python, literal definitions, all `λ`, all `φ`): round 0
(`bf/S01_remark.py`, strong notion) and round 1 (`bf/S01_repair_r1.py`, both
notions, all three clauses): exhaustive with `b ≤ 2` at (n,d,σ) ∈
{(2,1,2),(3,1,2),(2,1,3)} and with `b = 1` at {(4,1,2),(5,1,2),(6,1,2),(2,2,2),
(3,1,3)} (plus witnesses-in-`S` scans at (7,1,2),(5,1,3)) — the existence
pattern of both notions equals `¬(d = 1 ∧ n prime)` in every case; at (6,1,2),
`b = 1`: 92652 breaking vs 93096 violating maps; at (2,2,2): 384 vs 496;
explicit witnesses for d = 1, n ∈ {4,6,8,9,10,12,15} and d ≥ 2,
(n,d) ∈ {(3,2),(5,2),(2,3),(3,3)}. Structural cross-check: a violating broad map
exists iff a non-constant configuration with nontrivial stabilizer exists, which
matches `¬(d = 1 ∧ n prime)` for d = 1, n ≤ 16 and (n,d) ∈ {(2,2),(3,2),(4,2),(2,3)}.
Repair round 1: previously only the `LocBreaks` conjunct (whose `→` direction
certified only `Φ(S) ⊆ S` at prime `n`, not Theorem 8.1). -/
def locIffStatement : Prop :=
  ∀ (n d : ℕ) (A : Type) [Fintype A], 2 ≤ n → 1 ≤ d → 2 ≤ Fintype.card A →
    (LocBreaks n d A ↔ ¬ (d = 1 ∧ n.Prime)) ∧
      (LocViolates n d A ↔ ¬ (d = 1 ∧ n.Prime)) ∧
      (LocDepViolates n d A ↔ ¬ (d = 1 ∧ n.Prime))

/-- **Rem. 2.4, the evidently intended content of "from `n = 4` on"** (in the
remark's own setting `d = 1`): `n = 4` is the least lattice size at which a
location-selecting map fails to support the irreversibility theorem — for
`n = 2, 3` every location-selecting map (broad class, any `b ≥ 1`) satisfies the
full conclusion of Theorem 8.1 (`¬ LocDepViolates`, the strongest
non-existence form), and for `n = 4` one maps a shift-symmetric configuration to
a non-shift-symmetric one (`LocBreaks`, the strongest existence form). Any
alphabet with `σ ≥ 2`.
Reading: "the conclusion is the same from $n=4$ on" is offered as the threshold
of the phenomenon, i.e. it implicates that it does not occur below `n = 4`; in
`d = 1` this implicature is true (the literal "for all `n ≥ 4`" is not, see
`locFromFourRefutedStatement`). A consequence of `locIffStatement`, frozen
separately because it is the closest true reading of the paper's sentence.
Repair round 1: the non-existence conjuncts were `¬ LocBreaks` (certifying only
`Φ(S) ⊆ S`); now `¬ LocDepViolates`. -/
def locLeastFourStatement : Prop :=
  ∀ (A : Type) [Fintype A], 2 ≤ Fintype.card A →
    ¬ LocDepViolates 2 1 A ∧ ¬ LocDepViolates 3 1 A ∧ LocBreaks 4 1 A

/-- **Rem. 2.4, sharper truth for the equivariance half** (PAPER ISSUE note:
the restriction `n ≥ 4` is unnecessary for "do not imply equivariance"):
location-selecting maps with a shared rule need not be equivariant on ANY
`ℤ_n^d` with `n ≥ 2`, `d ≥ 1`, `σ ≥ 2` (e.g. every cell reads cell `0`).
Python: a `b = 1`, `φ = id` search finds one at (2,1,2),(3,1,2),(4,1,2),(2,2,2),(3,1,3),
and the "every cell reads cell 0" witness works at (2,1,2),(3,1,2),(5,1,2),(2,2,2),(3,2,3). -/
def locNotEquivariantFromTwoStatement : Prop :=
  ∀ (n d : ℕ) (A : Type) [Fintype A], 2 ≤ n → 1 ≤ d → 2 ≤ Fintype.card A →
    LocNonEquivariant n d A

/-- **Remark 2.4, all mathematical claims** (literal-true parts, the two concrete
counterexamples, the refutation of the false literal range, the positive prime
case behind it, and the repair). -/
def rem24Statement : Prop :=
  etaNotEquivariantStatement ∧ etaBreaksStatement ∧
    stateExampleStatement ∧ stateExampleNotEquivariantStatement ∧
    locExampleStatement ∧ locExampleNotEquivariantStatement ∧
    locNotEquivariantStatement ∧ locFromFourRefutedStatement ∧
    locPrimeThm81Statement ∧ locIffStatement ∧ locLeastFourStatement ∧
    locNotEquivariantFromTwoStatement

/-! ## Boundary: §3 preamble, lines 261–264 (Gaussian-binomial convention)

This sentence starts inside the assigned range (lines 261–262) and ends at
line 264; it is frozen here so that it is not lost between groups (a duplicate
in group 02 would be harmless). -/

/-- **§3 preamble, Gaussian binomial = number of subspaces** (lines 261–264):
"Throughout, $n=\prod_{i=1}^{k}p_i^{\alpha_i}$ with $p_1<\dots<p_k$ prime and
$k=\omega(n)$, and $\gaussbinom dr_p=\prod_{i=0}^{r-1}\frac{p^{d-i}-1}{p^{i+1}-1}$
is the Gaussian binomial, the number of $r$-dimensional subspaces of $\FF_p^d$."
Delta: the product is evaluated in `ℚ` (each factor is a ratio of positive
integers; the exponent `d - i` is exact since `i < r ≤ d`); "the number of
`r`-dimensional subspaces" is `Nat.card` of the subtype of `ZMod p`-submodules of
`Fin d → ZMod p` of `finrank r`; quantified over all primes `p` (the convention
applies it to the primes `p_i ∣ n`), `d ≥ 1`, `0 ≤ r ≤ d` (the range in which the
paper uses it; for `r > d` the product is `0` and so is the count). -/
def gaussBinomCountStatement : Prop :=
  ∀ p d r : ℕ, p.Prime → 1 ≤ d → r ≤ d →
    (∏ i ∈ Finset.range r, (((p : ℚ) ^ (d - i) - 1) / ((p : ℚ) ^ (i + 1) - 1))) =
      (Nat.card {W : Submodule (ZMod p) (Fin d → ZMod p) // Module.finrank (ZMod p) W = r} : ℚ)

/-- **Fidelity (not a paper claim): the paper's product formula is the project's
`gaussBinom`** (the recursive `q`-Pascal definition used in `Statement.lean`,
`rdCoeff`, `sopfD`). Same quantifiers as `gaussBinomCountStatement`. -/
def gaussBinomProductFidelityStatement : Prop :=
  ∀ p d r : ℕ, p.Prime → 1 ≤ d → r ≤ d →
    (∏ i ∈ Finset.range r, (((p : ℚ) ^ (d - i) - 1) / ((p : ℚ) ^ (i + 1) - 1))) =
      (gaussBinom p d r : ℚ)

/-- **All frozen statements of group 01** (paper claims and fidelity links). -/
def group01Statement : Prop :=
  def21Statement ∧ def22Statement ∧ isShiftSymmetricFidelityStatement ∧
    numSSFidelityStatement ∧ def23Statement ∧ rem24Statement ∧
    gaussBinomCountStatement ∧ gaussBinomProductFidelityStatement

/-! ## Non-vacuity checks (hypotheses satisfiable) -/

example : 2 ≤ (2 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ 2 ≤ Fintype.card (Fin 2) := by decide
example : 4 ≤ (4 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ 1 ≤ Fintype.card (Fin 1) := by decide
example : ∃ v : Lat 2 1, v ≠ 0 := ⟨cell1 1, by decide⟩
example : Nat.Prime 2 ∧ 1 ≤ (3 : ℕ) ∧ (2 : ℕ) ≤ 3 := by norm_num

/-! ## Display-only sanity runs (`#eval`, no proofs) -/

-- Def. 2.1: |𝔸| = n^d on small instances (expect 9, 8, 16).
#eval (Fintype.card (Lat 3 2), Fintype.card (Lat 2 3), Fintype.card (Lat 4 2))

-- Rem. 2.4, state-valued example (expect true, true, false, true = "not equivariant").
#eval decide (PhiState (tup1 ![1, 1]) = tup1 ![1, 0])
#eval decide (∃ v : Lat 2 1, v ≠ 0 ∧ shift v (tup1 (n := 2) ![(1 : Fin 2), 1]) = tup1 ![1, 1])
#eval decide (∃ v : Lat 2 1, v ≠ 0 ∧ shift v (tup1 (n := 2) ![(1 : Fin 2), 0]) = tup1 ![1, 0])
#eval decide (¬ ∀ (v : Lat 2 1) (s : Config 2 1 (Fin 2)), PhiState (shift v s) = shift v (PhiState s))

-- Rem. 2.4, location example (expect true, true, true, false, true).
#eval decide (shift (cell1 2) (tup1 (n := 4) ![(0 : Fin 2), 1, 0, 1]) = tup1 ![0, 1, 0, 1])
#eval decide (PhiLoc (tup1 ![0, 1, 0, 1]) = tup1 ![0, 1, 1, 1])
#eval decide (shift (cell1 2) (tup1 (n := 4) ![(0 : Fin 2), 1, 1, 1]) ≠ tup1 ![0, 1, 1, 1])
#eval decide (∃ v : Lat 4 1, v ≠ 0 ∧ shift v (tup1 (n := 4) ![(0 : Fin 2), 1, 1, 1]) = tup1 ![0, 1, 1, 1])
#eval decide (¬ ∀ (v : Lat 4 1) (s : Config 4 1 (Fin 2)), PhiLoc (shift v s) = shift v (PhiLoc s))

-- Def. 2.3 (b = 1 slices): an offset CA on ℤ_3^1 is equivariant (expect true).
#eval decide (∀ (v : Lat 3 1) (s : Config 3 1 (Fin 2)),
  caMap (b := 1) (fun _ => cell1 1) phiId (shift v s) = shift v (caMap (b := 1) (fun _ => cell1 1) phiId s))

-- Def. 2.2: union = nontrivial stabilizer, pointwise on ℤ_2^2 over Fin 2 (expect true).
#eval decide (∀ s : Config 2 2 (Fin 2),
  (∃ v : Lat 2 2, v ≠ 0 ∧ shift v s = s) ↔ (∃ v : Lat 2 2, v ≠ 0 ∧ v ∈ {w | shift w s = s}))

-- Rem. 2.4, the exact `b = 1` slice of `LocBreaks n 1 (Fin 2)` at n = 2, 3, 4, 5
-- (expect false, false, true, false — consistent with the corrected claim
-- "d = 1: exactly composite n", and with the refutation of "from n = 4 on" at n = 5).
section Sanity
local instance decBreaksIrr {n : ℕ} [NeZero n] (Φ : Config n 1 (Fin 2) → Config n 1 (Fin 2)) :
    Decidable (BreaksIrreversibility Φ) := by
  unfold BreaksIrreversibility IsShiftSymmetric; infer_instance
#eval decide (∃ (lam : Fin 1 → Lat 2 1 → Lat 2 1) (φ : (Fin 1 → Fin 2) → Fin 2),
  BreaksIrreversibility (locMap lam φ))
#eval decide (∃ (lam : Fin 1 → Lat 3 1 → Lat 3 1) (φ : (Fin 1 → Fin 2) → Fin 2),
  BreaksIrreversibility (locMap lam φ))
#eval decide (∃ (lam : Fin 1 → Lat 4 1 → Lat 4 1) (φ : (Fin 1 → Fin 2) → Fin 2),
  BreaksIrreversibility (locMap lam φ))
#eval decide (∃ (lam : Fin 1 → Lat 5 1 → Lat 5 1) (φ : (Fin 1 → Fin 2) → Fin 2),
  BreaksIrreversibility (locMap lam φ))
-- the concrete witness at n = 4 (expect true)
#eval decide (BreaksIrreversibility PhiLoc)

-- Repair round 1: the weak (faithful) notion. `Thm81Conclusion` is decided through
-- its per-vector clause (`v ≠ 0`), which is equivalent to the whole conclusion
-- (the equivalence is PROVED inside the instance, not assumed; this form keeps the
-- `#eval`s fast because `Φ s` is only evaluated when `s` has a nonzero period).
local instance decThm81 {n d : ℕ} [NeZero n] (Φ : Config n d (Fin 2) → Config n d (Fin 2)) :
    Decidable (Thm81Conclusion Φ) :=
  decidable_of_iff
    (∀ (s : Config n d (Fin 2)) (v : Lat n d), v ≠ 0 → shift v s = s → shift v (Φ s) = Φ s)
    (by
      constructor
      · intro h
        have h1 : ∀ s : Config n d (Fin 2), stabSet s ⊆ stabSet (Φ s) := by
          intro s v hv
          by_cases h0 : v = 0
          · subst h0; exact shift_zero _
          · exact h s v h0 hv
        refine ⟨h1, fun v s _ hs => h1 s hs, ?_⟩
        rintro _ ⟨s, hs, rfl⟩
        obtain ⟨v, hv0, hv⟩ := Set.mem_iUnion₂.mp hs
        exact Set.mem_iUnion₂.mpr ⟨v, hv0, h1 s hv⟩
      · intro h s v h0 hv
        exact h.2.1 v s h0 hv)
local instance decViol {n d : ℕ} [NeZero n] (Φ : Config n d (Fin 2) → Config n d (Fin 2)) :
    Decidable (ViolatesThm81 Φ) :=
  inferInstanceAs (Decidable (¬ Thm81Conclusion Φ))
-- `b = 1` slices of `LocViolates n 1 (Fin 2)`, n = 2, 3, 4, 5 (expect false, false, true, false).
#eval decide (∃ (lam : Fin 1 → Lat 2 1 → Lat 2 1) (φ : (Fin 1 → Fin 2) → Fin 2),
  ViolatesThm81 (locMap lam φ))
#eval decide (∃ (lam : Fin 1 → Lat 3 1 → Lat 3 1) (φ : (Fin 1 → Fin 2) → Fin 2),
  ViolatesThm81 (locMap lam φ))
#eval decide (∃ (lam : Fin 1 → Lat 4 1 → Lat 4 1) (φ : (Fin 1 → Fin 2) → Fin 2),
  ViolatesThm81 (locMap lam φ))
#eval decide (∃ (lam : Fin 1 → Lat 5 1 → Lat 5 1) (φ : (Fin 1 → Fin 2) → Fin 2),
  ViolatesThm81 (locMap lam φ))
-- `b = 1` slice of the BROAD class at n = 2: all 256 configuration-dependent
-- selectors, all 4 rules (expect false).
local instance : Fintype (Config 2 1 (Fin 2) → Lat 2 1) := inferInstance
local instance : Fintype (Lat 2 1 → Config 2 1 (Fin 2) → Lat 2 1) := inferInstance
local instance : Fintype (Fin 1 → Lat 2 1 → Config 2 1 (Fin 2) → Lat 2 1) := inferInstance
#eval decide (∃ (lam : Fin 1 → Lat 2 1 → Config 2 1 (Fin 2) → Lat 2 1)
  (φ : (Fin 1 → Fin 2) → Fin 2), ViolatesThm81 (locMapDep lam φ))
-- the concrete witness at n = 4 also violates in the weak sense (expect true)
#eval decide (ViolatesThm81 PhiLoc)
-- The fidelity reviewer's gap witness on ℤ_6: cell `u` reads cell `u mod 2`
-- (`b = 1`, `φ = id`); it keeps `Φ(S) ⊆ S` but violates Theorem 8.1
-- (s = (0,1,1,0,1,1), Stab {0,3} ↦ (0,1,0,1,0,1), Stab {0,2,4}).
-- Expect: false (does not break), true (violates), true (3 ∈ Stab s), false (3 ∈ Stab Φ s).
#eval decide (BreaksIrreversibility (locMap (b := 1)
  (fun _ (u : Lat 6 1) => cell1 (((u 0).val % 2 : ℕ) : ZMod 6)) phiId))
#eval decide (ViolatesThm81 (locMap (b := 1)
  (fun _ (u : Lat 6 1) => cell1 (((u 0).val % 2 : ℕ) : ZMod 6)) phiId))
#eval decide (shift (cell1 3) (tup1 (n := 6) ![(0 : Fin 2), 1, 1, 0, 1, 1]) =
  tup1 ![0, 1, 1, 0, 1, 1])
#eval decide (shift (cell1 3) (locMap (b := 1)
  (fun _ (u : Lat 6 1) => cell1 (((u 0).val % 2 : ℕ) : ZMod 6)) phiId
  (tup1 ![0, 1, 1, 0, 1, 1])) = locMap (b := 1)
  (fun _ (u : Lat 6 1) => cell1 (((u 0).val % 2 : ℕ) : ZMod 6)) phiId
  (tup1 ![0, 1, 1, 0, 1, 1]))
end Sanity

-- §3 preamble: product formula vs project `gaussBinom` (expect equal pairs).
#eval ((∏ i ∈ Finset.range 2, (((3 : ℚ) ^ (4 - i) - 1) / ((3 : ℚ) ^ (i + 1) - 1))), gaussBinom 3 4 2)
#eval ((∏ i ∈ Finset.range 1, (((2 : ℚ) ^ (3 - i) - 1) / ((2 : ℚ) ^ (i + 1) - 1))), gaussBinom 2 3 1)

end ShiftSym.P01
