/-
Phase H, group 08 (Detection), SUPPLEMENT of 2026-11-06 — proofs of the frozen statements of
`Shiftsym/Paper/S08_Detection_Reads.lean` (Remark 9.4, Read complexity, and the paragraph after it). Each
`def <X>Statement` there has `ShiftSym.P08.<X>_proved : ∀ params, <X>Statement params` here.

The first five proofs were written for the extension-layer copy of these statements
(`Ext/Proofs/PXA3_DetectionReads.lean`, 2026-11-06) and are moved here unchanged except for the
namespace and the helper name `collect` → `collectTree`:
* `oneDefect_proved`  — evaluate the fixed-point equation at `u - v`;
* `readOnce_proved`   — the tree `collectTree` reads the cells in the order of
  `Finset.univ.toList`, records the values, and answers by testing the assembled configuration
  (classical decision at the leaves);
* `readAll_proved`    — from `readOnce_proved`;
* `readLower_proved`  — inputs that agree on the cells read on the first get the same answer
  (`ReadTree.run_path_eq_of_agree`); on a constant configuration a correct tree must read every
  cell, else the one-defect configuration at an unread cell gets the answer `true`;
* `readWorst_proved`  — from `readLower_proved` at the constant configuration `0`.
New: `stabCorr_proved` — `Σ_a I_a(u) I_a(u+w) = [s(u+w) = s(u)]`, and a sum of `N` terms in
{0, 1} equals `N` iff every term is `1`.
-/
import Shiftsym.Paper.S08_Detection_Reads

namespace ShiftSym.P08

open ShiftSym

/-! ### Generic facts about read trees -/

/-- The number of reads is the length of the read path. -/
theorem ReadTree.reads_eq_length {L A : Type*} (T : ReadTree L A) (s : L → A) :
    T.reads s = (T.path s).length := by
  induction T with
  | done b => rfl
  | read u k ih => simp [ReadTree.reads, ReadTree.path, ih]

/-- Two inputs that agree on every cell read on the first have the same answer and the same
read path. -/
theorem ReadTree.run_path_eq_of_agree {L A : Type*} (T : ReadTree L A) (s s' : L → A)
    (h : ∀ u ∈ T.path s, s u = s' u) : T.run s = T.run s' ∧ T.path s = T.path s' := by
  induction T with
  | done b => exact ⟨rfl, rfl⟩
  | read u k ih =>
    simp only [ReadTree.path, List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨hu, hrest⟩ := h
    obtain ⟨h1, h2⟩ := ih (s u) hrest
    simp only [ReadTree.run, ReadTree.path, ← hu]
    exact ⟨h1, by rw [h2]⟩

/-- The tree that reads the cells of `l` in order, recording the values read in `acc`, and
answers `f` of the final record. -/
def collectTree {L A : Type*} [DecidableEq L] (f : (L → Option A) → Bool) :
    List L → (L → Option A) → ReadTree L A
  | [], acc => .done (f acc)
  | u :: l, acc => .read u (fun x => collectTree f l (Function.update acc u (some x)))

theorem collectTree_run {L A : Type*} [DecidableEq L] (f : (L → Option A) → Bool) (l : List L)
    (acc : L → Option A) (s : L → A) :
    (collectTree f l acc).run s = f (fun w => if w ∈ l then some (s w) else acc w) := by
  induction l generalizing acc with
  | nil => simp [collectTree, ReadTree.run]
  | cons u l ih =>
    simp only [collectTree, ReadTree.run, ih]
    congr 1
    funext w
    by_cases hw : w ∈ l
    · simp [hw]
    · by_cases hwu : w = u
      · subst hwu; simp [hw]
      · simp [hw, hwu]

theorem collectTree_path {L A : Type*} [DecidableEq L] (f : (L → Option A) → Bool) (l : List L)
    (acc : L → Option A) (s : L → A) : (collectTree f l acc).path s = l := by
  induction l generalizing acc with
  | nil => rfl
  | cons u l ih => simp [collectTree, ReadTree.path, ih]

/-! ### The statements -/

theorem oneDefect_proved (n d σ : ℕ) : oneDefectStatement n d σ := by
  intro _ _ a b u hab ⟨v, hv0, hv⟩
  have h := congrFun hv (u - v)
  simp only [shift_apply, sub_add_cancel, Function.update_self] at h
  by_cases huv : u - v = u
  · apply hv0
    have : u - (u - v) = u - u := by rw [huv]
    simpa using this
  · rw [Function.update_of_ne huv] at h
    exact hab h.symm

theorem readOnce_proved (n d σ : ℕ) : readOnceStatement n d σ := by
  intro hn
  classical
  have : NeZero n := ⟨by omega⟩
  let f : (Lat n d → Option (Fin σ)) → Bool := fun g =>
    decide (∃ s : Config n d (Fin σ), (∀ u, g u = some (s u)) ∧ IsShiftSymmetric s)
  let l : List (Lat n d) := (Finset.univ : Finset (Lat n d)).toList
  refine ⟨collectTree f l (fun _ => none), ?_, ?_⟩
  · intro s
    have hl : (fun w => if w ∈ l then some (s w) else (none : Option (Fin σ))) =
        fun w => some (s w) := by
      funext w; simp [l]
    rw [collectTree_run, hl]
    simp only [f, decide_eq_true_iff, Option.some.injEq]
    constructor
    · rintro ⟨s', hs', hsym⟩
      have : s = s' := funext hs'
      rw [this]; exact hsym
    · intro hsym
      exact ⟨s, fun _ => rfl, hsym⟩
  · intro s
    have hlen : l.length = n ^ d := by
      simp [l, Finset.length_toList, Finset.card_univ, ZMod.card]
    refine ⟨?_, ?_, ?_⟩
    · rw [collectTree_path]; exact Finset.nodup_toList _
    · rw [collectTree_path, hlen]
    · rw [ReadTree.reads_eq_length, collectTree_path, hlen]

theorem readAll_proved (n d σ : ℕ) : readAllStatement n d σ := by
  intro hn
  obtain ⟨T, hT, h⟩ := readOnce_proved n d σ hn
  exact ⟨T, hT, fun s => (h s).2.2.le⟩

theorem readLower_proved (n d σ : ℕ) : readLowerStatement n d σ := by
  intro hn hd hσ T hT a
  classical
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < n) := ⟨by omega⟩
  have : Nontrivial (Fin σ) := Fin.nontrivial_iff_two_le.mpr hσ
  obtain ⟨b, hb⟩ := exists_ne a
  let c : Config n d (Fin σ) := fun _ => a
  -- the constant configuration is shift-symmetric
  have hc : IsShiftSymmetric c := by
    refine ⟨fun _ => 1, ?_, rfl⟩
    intro h
    have := congrFun h ⟨0, by omega⟩
    exact one_ne_zero this
  have hrun : T.run c = true := (hT c).mpr hc
  -- every cell is read on `c`
  have hall : ∀ u : Lat n d, u ∈ T.path c := by
    intro u
    by_contra hu
    let t : Config n d (Fin σ) := Function.update c u b
    have hagree : ∀ w ∈ T.path c, c w = t w := by
      intro w hw
      have hwu : w ≠ u := fun h => hu (h ▸ hw)
      simp [t, Function.update_of_ne hwu]
    have hrt : T.run t = true := by
      rw [← (T.run_path_eq_of_agree c t hagree).1]; exact hrun
    exact oneDefect_proved n d σ hn hd a b u (Ne.symm hb) ((hT t).mp hrt)
  have hsub : (Finset.univ : Finset (Lat n d)) ⊆ (T.path c).toFinset := by
    intro u _; simpa using hall u
  have hcard : (Finset.univ : Finset (Lat n d)).card = n ^ d := by
    simp [Finset.card_univ, ZMod.card]
  rw [ReadTree.reads_eq_length, ← hcard]
  exact (Finset.card_le_card hsub).trans (List.toFinset_card_le _)

theorem readWorst_proved (n d σ : ℕ) : readWorstStatement n d σ := by
  intro hn hd hσ T hT
  exact ⟨fun _ => ⟨0, by omega⟩, readLower_proved n d σ hn hd hσ T hT _⟩


theorem stabCorr_proved (n d σ : ℕ) [NeZero n] : stabCorrStatement n d σ := by
  intro s w
  classical
  have hinner : ∀ u : Lat n d,
      (∑ a : Fin σ, (if s u = a then 1 else 0) * (if s (u + w) = a then 1 else 0) : ℕ)
        = if s (u + w) = s u then 1 else 0 := by
    intro u
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ (s u) (fun a => if s (u + w) = a then 1 else 0)]
    simp
  rw [Finset.sum_comm]
  simp only [hinner, Finset.sum_boole, Nat.cast_id]
  have hcard : Fintype.card (Lat n d) = n ^ d := by simp [ZMod.card]
  rw [mem_stab, funext_iff]
  simp only [shift_apply]
  constructor
  · intro h
    rw [← hcard, ← Finset.card_univ]
    congr 1
    ext u; simp [h u]
  · intro h u
    have h' : (Finset.univ.filter fun u => s (u + w) = s u) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [h, hcard]
    have : u ∈ Finset.univ.filter fun u => s (u + w) = s u := by rw [h']; exact Finset.mem_univ u
    simpa using this

end ShiftSym.P08
