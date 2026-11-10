/-
Phase D groundwork: the certified inclusion–exclusion form of |S|.

Main result: `card_shiftSymmetric_IE` — the number of shift-symmetric
configurations equals the alternating sum, over nonempty sets `J` of
prime-order subgroups, of `σ^(N / |sup J|)`. This is the paper's
Theorem 4.3 proof skeleton with every ingredient certified; what remains
for `enumerationStatement` (Phase D2) is evaluating this sum via rank
regrouping into the divisor-indexed closed form.
-/
import Shiftsym.Lemmas.Completeness
import Shiftsym.Lemmas.FixedCount
import Shiftsym.Lemmas.Lines

open scoped Classical

namespace ShiftSym

variable {n d : ℕ}

instance [NeZero n] : Finite (AddSubgroup (Lat n d)) :=
  Finite.of_injective (fun H => (H : Set (Lat n d))) SetLike.coe_injective

noncomputable instance [NeZero n] : Fintype (AddSubgroup (Lat n d)) :=
  Fintype.ofFinite _

/-- Membership in `fixedBy` is containment in the stabilizer. -/
theorem mem_fixedBy_iff_le_stab {A : Type*} {H : AddSubgroup (Lat n d)}
    {s : Config n d A} : s ∈ fixedBy A H ↔ H ≤ stab s :=
  Iff.rfl

/-- The finset of prime-order (cyclic) subgroups of the translation
group. Their orders automatically divide `n`. -/
noncomputable def primeOrderSubs (n d : ℕ) [NeZero n] :
    Finset (AddSubgroup (Lat n d)) :=
  Finset.univ.filter fun C => (Nat.card C).Prime

theorem mem_primeOrderSubs [NeZero n] {C : AddSubgroup (Lat n d)} :
    C ∈ primeOrderSubs n d ↔ (Nat.card C).Prime := by
  simp [primeOrderSubs]

section Fixed

variable (σ : ℕ) [NeZero n]

/-- `Fix(H)` as a finset of configurations over the alphabet `Fin σ`. -/
noncomputable def fixedByF (H : AddSubgroup (Lat n d)) :
    Finset (Config n d (Fin σ)) :=
  Finset.univ.filter fun s => ∀ h ∈ H, shift h s = s

theorem mem_fixedByF {H : AddSubgroup (Lat n d)}
    {s : Config n d (Fin σ)} : s ∈ fixedByF σ H ↔ H ≤ stab s := by
  simp only [fixedByF, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

theorem card_fixedByF (H : AddSubgroup (Lat n d)) :
    (fixedByF σ H).card = σ ^ (n ^ d / Nat.card H) := by
  have h1 : (fixedByF σ H).card
      = Fintype.card {s : Config n d (Fin σ) // ∀ h ∈ H, shift h s = s} :=
    (Fintype.card_subtype _).symm
  have h2 : Fintype.card {s : Config n d (Fin σ) // ∀ h ∈ H, shift h s = s}
      = Nat.card (fixedBy (Fin σ) H) := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [h1, h2, card_fixedBy_div, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Intersections of fixed-sets are the fixed-set of the join. -/
theorem inf'_fixedByF {t : Finset (AddSubgroup (Lat n d))}
    (ht : t.Nonempty) :
    t.inf' ht (fixedByF σ) = fixedByF σ (t.sup id) := by
  ext s
  rw [← Finset.singleton_subset_iff, Finset.le_inf'_iff]
  simp only [Finset.singleton_subset_iff]
  constructor
  · intro h
    rw [mem_fixedByF]
    apply Finset.sup_le
    intro C hC
    exact (mem_fixedByF σ).mp (h C hC)
  · intro h C hC
    rw [mem_fixedByF]
    exact le_trans (Finset.le_sup (f := id) hC) ((mem_fixedByF σ).mp h)

/-- **Set-form completeness**: a configuration is shift-symmetric iff it
lies in the fixed-set of some prime-order subgroup. -/
theorem isShiftSymmetric_iff_mem_biUnion (s : Config n d (Fin σ)) :
    IsShiftSymmetric s
      ↔ s ∈ (primeOrderSubs n d).biUnion (fun C => fixedByF σ C) := by
  rw [Finset.mem_biUnion]
  constructor
  · intro hs
    obtain ⟨v, hvp, -, hvfix⟩ :=
      (isShiftSymmetric_iff_prime_order s).mp hs
    refine ⟨AddSubgroup.zmultiples v, ?_, ?_⟩
    · rw [mem_primeOrderSubs, Nat.card_zmultiples]
      exact hvp
    · rw [mem_fixedByF]
      exact AddSubgroup.zmultiples_le.mpr (mem_stab.mpr hvfix)
  · rintro ⟨C, hC, hsC⟩
    rw [mem_primeOrderSubs] at hC
    have hCbot : C ≠ ⊥ := by
      intro hbot
      rw [hbot, AddSubgroup.card_bot] at hC
      exact Nat.not_prime_one hC
    obtain ⟨v, hvC, hv0⟩ := AddSubgroup.bot_or_exists_ne_zero C |>.resolve_left hCbot
    exact ⟨v, hv0, (mem_fixedByF σ).mp hsC hvC⟩

/-- **The certified inclusion–exclusion form of |S|** (paper Theorem 4.3,
proof skeleton): the count of shift-symmetric configurations is the
alternating sum over nonempty sets of prime-order subgroups of
`σ^(N / |sup J|)`. -/
theorem card_shiftSymmetric_IE :
    ((Finset.univ.filter
        (fun s : Config n d (Fin σ) => IsShiftSymmetric s)).card : ℤ)
      = ∑ t : ((primeOrderSubs n d).powerset.filter (·.Nonempty)),
          (-1 : ℤ) ^ (t.1.card + 1)
            * (σ : ℤ) ^ (n ^ d / Nat.card ((t.1.sup id : AddSubgroup (Lat n d)))) := by
  have hunion : Finset.univ.filter
      (fun s : Config n d (Fin σ) => IsShiftSymmetric s)
      = (primeOrderSubs n d).biUnion (fun C => fixedByF σ C) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isShiftSymmetric_iff_mem_biUnion σ s
  rw [hunion, Finset.inclusion_exclusion_card_biUnion]
  apply Finset.sum_congr rfl
  intro t _
  have hne : t.1.Nonempty :=
    (Finset.mem_filter.mp t.2).2
  rw [Finset.inf'_congr hne rfl (fun C _ => rfl)]
  rw [inf'_fixedByF σ hne, card_fixedByF]
  push_cast
  ring

/-- Bridge to the frozen statement's `Nat.card` form. -/
theorem natCard_shiftSymmetric_eq_filterCard :
    Nat.card {s : Config n d (Fin σ) // IsShiftSymmetric s}
      = (Finset.univ.filter
          (fun s : Config n d (Fin σ) => IsShiftSymmetric s)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Fixed

end ShiftSym
