/-
Fidelity reviewer A (literal comparison), 2026-10-27. Probes of the FROZEN statements in
`Shiftsym/Paper/S07_Dynamics_SymmetryBreaking.lean` (sha256 dbe24aa3…). Nothing here proves
`insolvSymBreakStatement` itself; only implications between statements and small instances.
Run from research/formal/shiftsym:
  flock /tmp/claude-1000/symbreak_lean.lock lake env lean \
    ../../experiments/symbreak_fidelity/A_literal/probe_A.lean
-/
import Shiftsym.Paper.S07_Dynamics_SymmetryBreaking

namespace FidelityA
open ShiftSym ShiftSym.P07

-- (0) The frozen objects elaborate with the expected types.
#check @RequiresSymmetryBreaking
#print RequiresSymmetryBreaking
#print insolvSymBreakStatement
#print insolvFullStatement

-- (1) Post-composition by a cellwise map never loses a translation symmetry.
theorem stab_comp_le {n d : ℕ} {A B : Type*} (f : A → B) (s : Config n d A) :
    stab s ≤ stab (f ∘ s) := by
  intro v hv
  have hv' : shift v s = s := hv
  show shift v (f ∘ s) = f ∘ s
  funext u
  have := congrFun hv' u
  simp only [shift_apply, Function.comp] at this ⊢
  rw [this]

-- (2) Docstring claim "an asymmetric output of a symmetric input always breaks a symmetry
-- of it": RequiresLeavingS → RequiresSymmetryBreaking (no hypotheses on n, d, σ needed).
theorem RLS_to_RSB {n d σ : ℕ} (T : Task n d σ) (h : RequiresLeavingS T) :
    RequiresSymmetryBreaking T := by
  obtain ⟨x, hx, hxS, hacc⟩ := h
  obtain ⟨v, hv0, hvx⟩ := hxS
  refine ⟨x, hx, fun y hy hle => ?_⟩
  have hvy : v ∈ stab y := hle (show v ∈ stab x from hvx)
  exact hacc hy ⟨v, hv0, hvy⟩

-- (3) Docstring claim "strictly extends insolvGeneralStatement": the new Prop implies it.
theorem symBreak_implies_general : insolvSymBreakStatement → insolvGeneralStatement := by
  intro h n d σ hn hd hσ hN T hT Φ hΦ
  exact h n d σ hn hd hσ hN T (RLS_to_RSB T hT) Φ hΦ

-- (4) The offset-CA form of the new clause (literal Definition 2.3) follows.
theorem symBreak_implies_CA : insolvSymBreakStatement →
    ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 < n ^ d →
      ∀ T : Task n d σ, RequiresSymmetryBreaking T →
        ∀ (b : ℕ) (offs : Fin b → Lat n d) (φ : (Fin b → Fin σ) → Fin σ),
          ¬ Solves (caMap offs φ) T := by
  intro h n d σ hn hd hσ hN T hT b offs φ
  exact h n d σ hn hd hσ hN T hT _ (caMap_equivariant offs φ)

-- (5) The narrower reading "ONE translation of x is broken by every acceptable output"
-- implies the frozen hypothesis (docstring: "a special case").
def RSBone {n d σ : ℕ} (T : Task n d σ) : Prop :=
  ∃ x ∈ T.admissible, ∃ v ∈ stab x, ∀ y ∈ T.accept x, v ∉ stab y

theorem RSBone_to_RSB {n d σ : ℕ} (T : Task n d σ) :
    RSBone T → RequiresSymmetryBreaking T := by
  rintro ⟨x, hx, v, hv, h⟩
  exact ⟨x, hx, fun y hy hle => h y hy (hle hv)⟩

-- (5b) ... and it is STRICTLY narrower: on Z_2^2, constant input, acceptable outputs the
-- three stripe patterns u ↦ u₁, u ↦ u₀, u ↦ u₀ + u₁ (stabilizers the three lines of F_2^2).
-- Every output breaks a symmetry of the input, but every translation is kept by one output.
def c0 : Config 2 2 (Fin 2) := fun _ => 0
def yA : Config 2 2 (Fin 2) := fun u => if u 1 = 0 then 0 else 1
def yB : Config 2 2 (Fin 2) := fun u => if u 0 = 0 then 0 else 1
def yC : Config 2 2 (Fin 2) := fun u => if u 0 + u 1 = 0 then 0 else 1

def linesTask : Task 2 2 2 where
  admissible := {c0}
  accept := fun _ => {yA, yB, yC}

-- every translation fixes c0
theorem c0_stab (v : Lat 2 2) : v ∈ stab c0 := by
  show shift v c0 = c0
  rfl

-- each output misses a translation; each translation is kept by some output
theorem yA_miss : shift (![1, 1] : Lat 2 2) yA ≠ yA := by
  intro h; have := congrFun h 0; revert this; decide
theorem yB_miss : shift (![1, 1] : Lat 2 2) yB ≠ yB := by
  intro h; have := congrFun h 0; revert this; decide
theorem yC_miss : shift (![1, 0] : Lat 2 2) yC ≠ yC := by
  intro h; have := congrFun h 0; revert this; decide

theorem every_v_kept (v : Lat 2 2) :
    shift v yA = yA ∨ shift v yB = yB ∨ shift v yC = yC := by
  revert v
  unfold yA yB yC shift
  decide

theorem linesTask_RSB : RequiresSymmetryBreaking linesTask := by
  refine ⟨c0, rfl, fun y hy hle => ?_⟩
  rcases hy with rfl | rfl | rfl
  · exact yA_miss (hle (c0_stab _))
  · exact yB_miss (hle (c0_stab _))
  · exact yC_miss (hle (c0_stab _))

theorem linesTask_not_RSBone : ¬ RSBone linesTask := by
  rintro ⟨x, hx, v, -, h⟩
  have hx' : x = c0 := hx
  subst hx'
  rcases every_v_kept v with hA | hB | hC
  · exact h yA (Or.inl rfl) hA
  · exact h yB (Or.inr (Or.inl rfl)) hB
  · exact h yC (Or.inr (Or.inr rfl)) hC

-- (6) Non-vacuity beyond RequiresLeavingS (Z_4: constant → 0101), with NONEMPTY accept.
def zero4 : Config 4 1 (Fin 2) := fun _ => 0
def alt4 : Config 4 1 (Fin 2) := fun u => if (u 0).val % 2 = 0 then 0 else 1
def stripeTask : Task 4 1 2 where
  admissible := {zero4}
  accept := fun _ => {alt4}

theorem stripe_RSB_not_RLS :
    RequiresSymmetryBreaking stripeTask ∧ ¬ RequiresLeavingS stripeTask := by
  have hfix : shift (fun _ => 2) alt4 = alt4 := by
    funext u; revert u; decide
  refine ⟨⟨zero4, rfl, fun y hy hle => ?_⟩, fun ⟨x, hx, _, hacc⟩ => ?_⟩
  · have hy' : y = alt4 := hy
    subst hy'
    have h1 : (fun _ => (1 : ZMod 4)) ∈ stab zero4 := rfl
    have := congrFun (hle h1) 0
    revert this; decide
  · have hx' : x = zero4 := hx
    subst hx'
    exact hacc (rfl : alt4 ∈ stripeTask.accept zero4) ⟨fun _ => 2, by decide, hfix⟩

-- (7) A broader reading: the CA computes over a LARGER alphabet σ' (auxiliary states),
-- inputs are encoded cellwise by an injective ι, outputs decoded cellwise by π. The frozen
-- statement (instantiated at σ') already covers this reading.
theorem symBreak_aux_states : insolvSymBreakStatement →
    ∀ n d σ σ' : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ' → 1 < n ^ d →
      ∀ (ι : Fin σ → Fin σ') (π : Fin σ' → Fin σ), Function.Injective ι →
        ∀ T : Task n d σ, RequiresSymmetryBreaking T →
          ∀ Φ : Config n d (Fin σ') → Config n d (Fin σ'), Equivariant Φ →
            ¬ ∀ x ∈ T.admissible, ∃ k : ℕ, π ∘ (Φ^[k] (ι ∘ x)) ∈ T.accept x := by
  intro h n d σ σ' hn hd hσ' hN ι π hι T hT Φ hΦ hsol
  obtain ⟨x₀, hx₀, hbr⟩ := hT
  let T' : Task n d σ' :=
    { admissible := (fun x => ι ∘ x) '' T.admissible
      accept := fun x' => {y' | ∀ x, ι ∘ x = x' → π ∘ y' ∈ T.accept x} }
  have hinj : ∀ x₁ x₂ : Config n d (Fin σ), ι ∘ x₁ = ι ∘ x₂ → x₁ = x₂ := by
    intro x₁ x₂ he; funext u; exact hι (congrFun he u)
  have hRSB' : RequiresSymmetryBreaking T' := by
    refine ⟨ι ∘ x₀, ⟨x₀, hx₀, rfl⟩, fun y' hy' hle => ?_⟩
    have hy0 : π ∘ y' ∈ T.accept x₀ := hy' x₀ rfl
    exact hbr _ hy0 ((stab_comp_le ι x₀).trans (hle.trans (stab_comp_le π y')))
  have hSolves : Solves Φ T' := by
    rintro x' ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := hsol x hx
    refine ⟨k, fun x₁ he => ?_⟩
    rw [hinj x₁ x he]; exact hk
  exact h n d σ' hn hd hσ' hN T' hRSB' Φ hΦ hSolves

#print axioms symBreak_implies_general
#print axioms symBreak_implies_CA
#print axioms linesTask_RSB
#print axioms linesTask_not_RSBone
#print axioms stripe_RSB_not_RLS
#print axioms symBreak_aux_states

end FidelityA
