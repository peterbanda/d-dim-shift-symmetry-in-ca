/-
Machine-checked dynamics core (paper Section 8; claims C004, C015, C018
in research/claims.yaml):

* equivariant maps enlarge stabilizers (irreversibility, Thm 8.1);
* hence shift-symmetry is preserved, per vector and globally;
* hence the intersection with ANY fixed subgroup (e.g. the p-torsion,
  giving per-prime rank monotonicity at subgroup level) is monotone.
-/
import Shiftsym.Definitions

namespace ShiftSym

variable {n d : ℕ} {A : Type*}

/-- **Irreversibility, stabilizer form** (paper Theorem 8.1): under a
translation-equivariant global map, the stabilizer can only grow. -/
theorem stab_le_stab_apply {Φ : Config n d A → Config n d A}
    (hΦ : Equivariant Φ) (s : Config n d A) :
    stab s ≤ stab (Φ s) := by
  intro v hv
  simp only [mem_stab] at hv ⊢
  rw [← hΦ, hv]

/-- Per-vector irreversibility: if `v` fixes `s`, it fixes `Φ s`. -/
theorem shift_apply_eq_of_shift_eq {Φ : Config n d A → Config n d A}
    (hΦ : Equivariant Φ) {s : Config n d A} {v : Lat n d}
    (hv : shift v s = s) : shift v (Φ s) = Φ s :=
  stab_le_stab_apply hΦ s hv

/-- **Irreversibility, set form**: equivariant maps preserve
shift-symmetry. -/
theorem isShiftSymmetric_apply {Φ : Config n d A → Config n d A}
    (hΦ : Equivariant Φ) {s : Config n d A}
    (hs : IsShiftSymmetric s) : IsShiftSymmetric (Φ s) := by
  obtain ⟨v, hv0, hv⟩ := hs
  exact ⟨v, hv0, shift_apply_eq_of_shift_eq hΦ hv⟩

/-- Subgroup-level rank monotonicity (paper Proposition 8.3, subgroup
form): for ANY subgroup `T` (in particular the `p`-torsion), the part of
the stabilizer inside `T` is monotone along equivariant dynamics. -/
theorem stab_inf_mono {Φ : Config n d A → Config n d A}
    (hΦ : Equivariant Φ) (s : Config n d A) (T : AddSubgroup (Lat n d)) :
    stab s ⊓ T ≤ stab (Φ s) ⊓ T :=
  inf_le_inf_right T (stab_le_stab_apply hΦ s)

/-- Constant configurations are shift-symmetric whenever a nonzero vector
exists (`n ≥ 2`, `d ≥ 1`) — the input-existence half of the insolvability
corollary (paper Corollary 8.2). -/
theorem isShiftSymmetric_const (a : A) (v : Lat n d) (hv : v ≠ 0) :
    IsShiftSymmetric (fun _ : Lat n d => a) :=
  ⟨v, hv, rfl⟩

/-- Shift-symmetry is preserved along entire trajectories. -/
theorem isShiftSymmetric_iterate {Φ : Config n d A → Config n d A}
    (hΦ : Equivariant Φ) {s : Config n d A} (hs : IsShiftSymmetric s) :
    ∀ k : ℕ, IsShiftSymmetric (Φ^[k] s) := by
  intro k
  induction k with
  | zero => exact hs
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact isShiftSymmetric_apply hΦ ih

/-- **Insolvability** (paper Corollary 8.2, machine-checked core): from a
shift-symmetric input, no translation-equivariant CA ever reaches a
non-shift-symmetric target, at any time step. -/
theorem iterate_ne_of_not_isShiftSymmetric
    {Φ : Config n d A → Config n d A} (hΦ : Equivariant Φ)
    {s t : Config n d A} (hs : IsShiftSymmetric s)
    (ht : ¬ IsShiftSymmetric t) (k : ℕ) :
    Φ^[k] s ≠ t :=
  fun h => ht (h ▸ isShiftSymmetric_iterate hΦ hs k)

end ShiftSym
