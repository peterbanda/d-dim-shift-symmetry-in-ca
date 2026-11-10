/-
C_reconstruction: Lean-side comparison of the Phase-1 reading with the frozen
`insolvSymBreakStatement`. No proof of the frozen statement is attempted here;
only (1) definitional unfolding, (2) non-vacuity/strictness of the hypothesis
on the Z_4 example of the docstring, (3) inclusion-direction sanity.
Run: cd research/formal/shiftsym && flock /tmp/claude-1000/symbreak_lean.lock \
       lake env lean ../../experiments/symbreak_fidelity/C_reconstruction/reconstruction_check.lean
-/
import Shiftsym.Paper.S07_Dynamics_SymmetryBreaking

open ShiftSym ShiftSym.P07

/-- Phase-1 statement, in the repository's vocabulary, WITHOUT side conditions. -/
def phase1Statement : Prop :=
  ∀ n d σ : ℕ, ∀ T : Task n d σ,
    (∃ x ∈ T.admissible, ∀ y ∈ T.accept x, ¬ stab x ≤ stab y) →
    ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ → ¬ Solves Φ T

/-- (1) The frozen statement is, by definitional unfolding, the Phase-1
statement restricted to the paper's parameter domain. -/
example : insolvSymBreakStatement ↔
    ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 < n ^ d → ∀ T : Task n d σ,
      (∃ x ∈ T.admissible, ∀ y ∈ T.accept x, ¬ stab x ≤ stab y) →
      ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ → ¬ Solves Φ T :=
  Iff.rfl

/-- Phase-1 statement implies the frozen one (trivially: drop the guards). -/
example (h : phase1Statement) : insolvSymBreakStatement :=
  fun n d σ _ _ _ _ T hT Φ hΦ => h n d σ T hT Φ hΦ

/-- The Z_4 example: constant 0 input, the only acceptable output is 0101. -/
def c0 : Config 4 1 (Fin 2) := fun _ => 0
def p01 : Config 4 1 (Fin 2) := fun u => if (u 0).val % 2 = 0 then 0 else 1
def T4 : Task 4 1 2 := ⟨{c0}, fun _ => {p01}⟩

/-- (2a) Non-vacuity with a nonempty accept set. -/
example : RequiresSymmetryBreaking T4 := by
  refine ⟨c0, rfl, ?_⟩
  rintro y rfl h
  have h1 : (fun _ => (1 : ZMod 4) : Lat 4 1) ∈ stab c0 := by
    show shift _ c0 = c0
    funext u; rfl
  have h2 := congrFun (h h1) 0
  revert h2
  decide

/-- (2b) Strictness: the same task is NOT covered by `RequiresLeavingS`
(0101 is itself shift-symmetric, period 2). -/
example : ¬ RequiresLeavingS T4 := by
  rintro ⟨x, hx, -, hacc⟩
  have hx' : x = c0 := hx
  subst hx'
  have hp : p01 ∈ SS 4 1 2 := by
    refine ⟨fun _ => 2, ?_, ?_⟩
    · intro h0; have := congrFun h0 0; revert this; decide
    · funext u; revert u; decide
  exact hacc (show p01 ∈ T4.accept c0 from rfl) hp

/-- (3) Direction sanity: the REVERSE inclusion `stab y ≤ stab x` is not
preserved by equivariant maps — the constant map sends the asymmetric
single-cell indicator to c0; were the hypothesis written with
`stab y ≤ stab x` it would not express symmetry breaking. Here: stab c0 is
not ≤ stab of the indicator. -/
def e0 : Config 4 1 (Fin 2) := fun u => if u = 0 then 1 else 0
example : ¬ stab c0 ≤ stab e0 := by
  intro h
  have h1 : (fun _ => (1 : ZMod 4) : Lat 4 1) ∈ stab c0 := by
    show shift _ c0 = c0
    funext u; rfl
  have h2 := congrFun (h h1) (fun _ => 3)
  revert h2
  decide

