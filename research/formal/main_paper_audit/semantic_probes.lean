import Shiftsym.AuditPaper

/- Independent audit probes for the main manuscript. These do not change
   the frozen statements or production proofs. -/
namespace MainPaperAudit
open ShiftSym

-- The displayed rank-vector formula counts actual configurations.
theorem main_formula (n d σ : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hs : 1 ≤ σ) :
    (Nat.card {s : Config n d (Fin σ) // ∃ v, v ≠ 0 ∧ shift v s = s} : ℤ) =
      P04.mainFormulaRHS n d σ := by
  rw [P04.rankVectorReindex_proved]
  exact enumeration_proved n d σ hn hd hs

-- A literal image-translation task is solvable, including symmetric inputs.
def translationTask (n d σ : ℕ) (w : Lat n d) : P07.Task n d σ where
  admissible := Set.univ
  accept := fun s => {shift w s}

theorem translation_is_CA (n d σ : ℕ) (w : Lat n d) :
    caMap (fun _ : Fin 1 => w) (fun x : Fin 1 → Fin σ => x 0) = shift w := rfl

theorem translation_solves (n d σ : ℕ) (w : Lat n d) :
    Equivariant (shift w : Config n d (Fin σ) → Config n d (Fin σ)) ∧
      P07.Solves (shift w) (translationTask n d σ w) := by
  constructor
  · rw [← translation_is_CA]
    exact caMap_equivariant _ _
  · intro s _
    exact ⟨1, by simp [translationTask]⟩

-- Reading one fixed absolute location and copying it everywhere preserves
-- every stabilizer, although the map is not translation-equivariant.
def copyOrigin (s : Config 2 1 (Fin 2)) : Config 2 1 (Fin 2) :=
  fun _ => s 0

theorem equivariance_not_necessary_for_each_map :
    (¬ Equivariant copyOrigin) ∧
      (∀ s : Config 2 1 (Fin 2), stab s ≤ stab (copyOrigin s)) := by
  constructor
  · intro h
    have hh := congrFun (h (fun _ => 1) (fun u => u 0)) 0
    norm_num [copyOrigin, shift] at hh
    exact (by decide : (1 : Fin 2) ≠ 0) hh
  · intro s v _
    rfl

#print axioms main_formula
#print axioms translation_solves
#print axioms equivariance_not_necessary_for_each_map
end MainPaperAudit
