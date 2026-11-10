import Shiftsym.AuditPaper

/- Independent v8 review: conclusions written in cell values, without the
   project's Task, Solves, RequiresSymmetryBreaking or stabilizer definitions.
   The proof must bridge these literal statements to the new frozen theorem. -/
namespace V8Review
open ShiftSym

theorem symmetry_breaking_literal
    (n d σ : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 2 ≤ σ) (hN : 1 < n ^ d)
    (admissible : Set ((Fin d → ZMod n) → Fin σ))
    (accept : ((Fin d → ZMod n) → Fin σ) → Set ((Fin d → ZMod n) → Fin σ))
    (hbreak : ∃ x ∈ admissible, ∀ y ∈ accept x,
      ∃ v : Fin d → ZMod n, v ≠ 0 ∧
        (∀ u, x (u + v) = x u) ∧ ∃ u, y (u + v) ≠ y u)
    (Φ : ((Fin d → ZMod n) → Fin σ) → ((Fin d → ZMod n) → Fin σ))
    (heq : ∀ x v u, Φ (fun w => x (w + v)) u = Φ x (u + v)) :
    ¬ (∀ x ∈ admissible, ∃ k : ℕ, Φ^[k] x ∈ accept x) := by
  let T : P07.Task n d σ := ⟨admissible, accept⟩
  have hT : P07.RequiresSymmetryBreaking T := by
    obtain ⟨x, hx, hb⟩ := hbreak
    refine ⟨x, hx, fun y hy hle => ?_⟩
    obtain ⟨v, _, hv, u, hu⟩ := hb y hy
    have hvin : v ∈ stab x := funext hv
    exact hu (congrFun (hle hvin) u)
  have hΦ : Equivariant Φ := by
    intro v x
    exact funext (heq x v)
  exact P07.insolvSymBreak_proved n d σ hn hd hσ hN T hT Φ hΦ

-- The negated subgroup inclusion really is loss of an actual NONZERO shift.
-- The output-dependent witness is intentionally inside the output quantifier.
theorem loss_of_shift_iff {n d σ : ℕ} (x y : (Fin d → ZMod n) → Fin σ) :
    (¬ stab x ≤ stab y) ↔
      ∃ v : Fin d → ZMod n, v ≠ 0 ∧
        (∀ u, x (u + v) = x u) ∧ ∃ u, y (u + v) ≠ y u := by
  classical
  constructor
  · intro h
    have hex : ∃ v, v ∈ stab x ∧ v ∉ stab y := by
      by_contra hn
      apply h
      intro v hv
      by_contra hny
      exact hn ⟨v, hv, hny⟩
    obtain ⟨v, hx, hy⟩ := hex
    refine ⟨v, ?_, fun u => congrFun hx u, ?_⟩
    · intro hv
      subst v
      exact hy (AddSubgroup.zero_mem _)
    · by_contra hn
      apply hy
      apply funext
      intro u
      by_contra hu
      exact hn ⟨u, hu⟩
  · rintro ⟨v, _, hx, u, hy⟩ hle
    exact hy (congrFun (hle (show v ∈ stab x from funext hx)) u)

#print axioms symmetry_breaking_literal
#print axioms loss_of_shift_iff
end V8Review
