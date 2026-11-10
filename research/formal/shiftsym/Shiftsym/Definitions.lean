/-
Shift-symmetric configurations on the discrete torus (Z/nZ)^d:
formal definitions.

Mirrors research/problem.md (frozen contract) and the revised paper's
Section 2. See research/formal/STATEMENT_PRESERVATION.md for the
informal-to-formal mapping.
-/
import Mathlib

namespace ShiftSym

/-- The lattice / translation group `(Z/nZ)^d`. -/
abbrev Lat (n d : ℕ) := Fin d → ZMod n

/-- Configurations: functions from the lattice to an alphabet `A`. -/
abbrev Config (n d : ℕ) (A : Type*) := Lat n d → A

variable {n d : ℕ} {A : Type*}

/-- Translation of a configuration by a lattice vector:
`(shift v s) u = s (u + v)`. -/
def shift (v : Lat n d) (s : Config n d A) : Config n d A :=
  fun u => s (u + v)

@[simp] theorem shift_apply (v : Lat n d) (s : Config n d A) (u : Lat n d) :
    shift v s u = s (u + v) := rfl

theorem shift_zero (s : Config n d A) : shift (0 : Lat n d) s = s := by
  funext u; simp

theorem shift_add (v w : Lat n d) (s : Config n d A) :
    shift (v + w) s = shift v (shift w s) := by
  funext u
  simp only [shift_apply]
  rw [add_assoc]

/-- The stabilizer of a configuration, as an additive subgroup of the
translation group. -/
def stab (s : Config n d A) : AddSubgroup (Lat n d) where
  carrier := {v | shift v s = s}
  zero_mem' := shift_zero s
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [shift_add, hb, ha]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h : shift (-a + a) s = shift (-a) s := by rw [shift_add, ha]
    rw [neg_add_cancel, shift_zero] at h
    exact h.symm

@[simp] theorem mem_stab {s : Config n d A} {v : Lat n d} :
    v ∈ stab s ↔ shift v s = s := Iff.rfl

/-- A configuration is shift-symmetric if some nonzero translation fixes
it, i.e. its stabilizer is nontrivial. -/
def IsShiftSymmetric (s : Config n d A) : Prop :=
  ∃ v : Lat n d, v ≠ 0 ∧ shift v s = s

/-- The set of configurations fixed by every element of a subgroup `H`. -/
def fixedBy (A : Type*) (H : AddSubgroup (Lat n d)) : Set (Config n d A) :=
  {s | ∀ h ∈ H, shift h s = s}

/-- Translation-equivariant global maps: `Φ (shift v s) = shift v (Φ s)`. -/
def Equivariant (Φ : Config n d A → Config n d A) : Prop :=
  ∀ (v : Lat n d) (s : Config n d A), Φ (shift v s) = shift v (Φ s)

/-- The global map of a cellular automaton given by `b` fixed neighborhood
offsets and a shared local rule `φ` (paper Definition 2.3). -/
def caMap {b : ℕ} (offs : Fin b → Lat n d) (φ : (Fin b → A) → A) :
    Config n d A → Config n d A :=
  fun s u => φ (fun i => s (u + offs i))

/-- Cellular automata with fixed offsets are translation-equivariant
(the hypothesis all dynamical results use; paper Definition 2.3). -/
theorem caMap_equivariant {b : ℕ} (offs : Fin b → Lat n d)
    (φ : (Fin b → A) → A) : Equivariant (caMap offs φ) := by
  intro v s
  funext u
  simp only [caMap, shift_apply]
  congr 1
  funext i
  rw [add_right_comm]

end ShiftSym
