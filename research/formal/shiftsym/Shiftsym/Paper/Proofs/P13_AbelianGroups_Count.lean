/-
Paper group 13 (Section 4.5; moved from extension group A1) (AbelianEnum) — proof module 4: the fixed-set counts and the
two frozen theorems `abelianEnum_proved` (Theorem A1) and `kActive_proved`
(Corollary (d)).

Step 2's count on `G`: `Fix(H) ≃ (G ⧸ H → A)` (`fixEquivG`), so
`|Fix(H)| = σ^(N/|H|)`; its `k`-active part has
`binom(N/h, k/h)(σ−1)^((N−k)/h)` elements if `h = |H|` divides `k`, and none
otherwise (every coset has `h` elements; the count of maps with a prescribed
number of preimages is the certified `ShiftSym.P05.natCard_fun_preimage`). Both
weights depend only on `|H|`, so `relative_divisorG` evaluates the relative
inclusion–exclusion formula into the frozen right-hand sides.
-/
import Shiftsym.Paper.Proofs.P13_AbelianGroups_Eval
import Shiftsym.Paper.Proofs.P05_KActive_Fix

open scoped Classical

namespace ShiftSym.P13.Gen

open ShiftSym ShiftSym.P13

variable {G : Type*} [AddCommGroup G]

/-- A configuration fixed by `H` is a labelling of the cosets of `H`. -/
def fixEquivG {A : Type*} (H : AddSubgroup G) : {s : G → A // H ≤ stabG s} ≃ (G ⧸ H → A) where
  toFun s := Quotient.lift s.1 (by
    intro u v huv
    have hmem : -u + v ∈ H := QuotientAddGroup.leftRel_apply.mp huv
    have h1 : s.1 (u + (-u + v)) = s.1 u := mem_stabG.mp (s.2 hmem) u
    rw [← add_assoc, add_neg_cancel, zero_add] at h1
    exact h1.symm)
  invFun f := ⟨fun u => f (QuotientAddGroup.mk u), by
    intro h hh
    rw [mem_stabG]
    intro u
    have hq : (QuotientAddGroup.mk (u + h) : G ⧸ H) = QuotientAddGroup.mk u := by
      rw [QuotientAddGroup.eq]
      have : -(u + h) + u = -h := by abel
      rw [this]
      exact H.neg_mem hh
    rw [hq]⟩
  left_inv s := Subtype.ext (funext fun _ => rfl)
  right_inv f := funext fun q => Quotient.inductionOn q fun _ => rfl

variable [Finite G]

theorem card_quotientG (H : AddSubgroup G) : Nat.card (G ⧸ H) = Nat.card G / Nat.card H := by
  have hmul : H.index * Nat.card H = Nat.card G := H.index_mul_card
  have hpos : 0 < Nat.card H := Nat.card_pos
  rw [← hmul, Nat.mul_div_cancel _ hpos, AddSubgroup.index_eq_card]

/-- `|Fix(H)| = σ^(N/|H|)`. -/
theorem card_fixA_fin [Fintype G] (σ : ℕ) (H : AddSubgroup G) :
    ((Finset.univ ∩ fixA (Fin σ) H).card : ℤ) = (σ : ℤ) ^ (Nat.card G / Nat.card H) := by
  rw [Finset.univ_inter]
  have h1 : (fixA (Fin σ) H).card = Nat.card {s : G → Fin σ // H ≤ stabG s} := by
    rw [fixA, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, Nat.card_congr (fixEquivG H), Nat.card_fun, card_quotientG,
    Nat.card_eq_fintype_card (α := Fin σ), Fintype.card_fin]
  push_cast
  rfl

omit [Finite G] in
/-- The `k`-active part of `Fix(H)` as maps on the coset space. -/
theorem natCard_fixK_eq_mapsG (σ : ℕ) (a : Fin σ) (k : ℕ) (H : AddSubgroup G) :
    Nat.card {s : G → Fin σ // H ≤ stabG s ∧ Nat.card {u // s u = a} = k}
      = Nat.card {f : G ⧸ H → Fin σ //
          Nat.card H * Nat.card {q : G ⧸ H // f q = a} = k} := by
  have hcells : ∀ s : {s : G → Fin σ // H ≤ stabG s},
      Nat.card {u // s.1 u = a}
        = Nat.card H * Nat.card {q : G ⧸ H // fixEquivG H s q = a} := by
    intro s
    rw [← P05.natCard_preimage_mk H (fixEquivG H s) a]
    rfl
  refine Nat.card_congr ?_
  refine (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun s : G → Fin σ => H ≤ stabG s)
    (fun s => Nat.card {u // s u = a} = k)).symm.trans ?_
  exact Equiv.subtypeEquiv (fixEquivG H) (fun s => by rw [hcells s])

/-- `|Fix_k(H)| = binom(N/h, k/h)(σ−1)^((N−k)/h)` if `h = |H|` divides `k`, else `0`. -/
theorem natCard_fixKG (σ : ℕ) (hσ : 1 ≤ σ) (a : Fin σ) (k : ℕ) (H : AddSubgroup G) :
    (Nat.card {s : G → Fin σ // H ≤ stabG s ∧ Nat.card {u // s u = a} = k} : ℤ)
      = if Nat.card H ∣ k then
          ((Nat.card G / Nat.card H).choose (k / Nat.card H) : ℤ)
            * ((σ : ℤ) - 1) ^ ((Nat.card G - k) / Nat.card H)
        else 0 := by
  rw [natCard_fixK_eq_mapsG]
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hdvdN : Nat.card H ∣ Nat.card G := AddSubgroup.card_addSubgroup_dvd_card H
  by_cases hk : Nat.card H ∣ k
  · rw [if_pos hk]
    obtain ⟨j, rfl⟩ := hk
    have hcond : ∀ f : G ⧸ H → Fin σ,
        (Nat.card H * Nat.card {q : G ⧸ H // f q = a} = Nat.card H * j)
          ↔ Nat.card {q : G ⧸ H // f q = a} = j :=
      fun f => ⟨fun h => Nat.eq_of_mul_eq_mul_left hpos h, fun h => by rw [h]⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight hcond), P05.natCard_fun_preimage,
      card_quotientG, Nat.card_eq_fintype_card (α := Fin σ), Fintype.card_fin,
      Nat.mul_div_cancel_left _ hpos]
    obtain ⟨M, hM⟩ := hdvdN
    have hMj : (Nat.card G - Nat.card H * j) / Nat.card H = Nat.card G / Nat.card H - j := by
      rw [hM, ← Nat.mul_sub, Nat.mul_div_cancel_left _ hpos, Nat.mul_div_cancel_left _ hpos]
    rw [hMj]
    push_cast [Nat.cast_sub hσ]
    ring
  · rw [if_neg hk]
    have hempty : IsEmpty {f : G ⧸ H → Fin σ //
        Nat.card H * Nat.card {q : G ⧸ H // f q = a} = k} :=
      ⟨fun ⟨f, hf⟩ => hk ⟨_, hf.symm⟩⟩
    rw [Nat.card_of_isEmpty]
    simp

/-- The relativised count for `X` = the configurations with exactly `k` cells in state `a`. -/
theorem card_fixA_kActive [Fintype G] (σ : ℕ) (hσ : 1 ≤ σ) (a : Fin σ) (k : ℕ)
    (H : AddSubgroup G) :
    (((Finset.univ.filter fun s : G → Fin σ => Nat.card {u // s u = a} = k)
        ∩ fixA (Fin σ) H).card : ℤ)
      = if Nat.card H ∣ k then
          ((Nat.card G / Nat.card H).choose (k / Nat.card H) : ℤ)
            * ((σ : ℤ) - 1) ^ ((Nat.card G - k) / Nat.card H)
        else 0 := by
  rw [← natCard_fixKG σ hσ a k H]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, fixA, ← Finset.filter_and]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

end ShiftSym.P13.Gen

namespace ShiftSym.P13

open ShiftSym.P13.Gen

/-- **Theorem A1, machine-checked** (frozen `abelianEnumStatement`): for every
finite abelian group `G` and every `σ ≥ 1`, the number of shift-symmetric
configurations `G → Fin σ` is `abelianRHS (Nat.card G) (pRank G) σ`. -/
theorem abelianEnum_proved (G : Type*) [AddCommGroup G] [Finite G] (σ : ℕ) :
    abelianEnumStatement G σ := by
  intro _
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    relative_divisorG Finset.univ (fun h => (σ : ℤ) ^ (Nat.card G / h)) (card_fixA_fin σ)]
  rfl

/-- **Corollary (d), machine-checked** (frozen `kActiveStatement`): the `k`-active
counts on every finite abelian group. -/
theorem kActive_proved (G : Type*) [AddCommGroup G] [Finite G] (σ k : ℕ) (a : Fin σ) :
    kActiveStatement G σ k a := by
  intro _
  have := Fintype.ofFinite G
  have hσ : 1 ≤ σ := Nat.one_le_iff_ne_zero.mpr fun h => by subst h; exact a.elim0
  have hcard : Nat.card {s : G → Fin σ // IsShiftSymmetricG s ∧ Nat.card {u // s u = a} = k}
      = ((Finset.univ.filter fun s : G → Fin σ => Nat.card {u // s u = a} = k).filter
          IsShiftSymmetricG).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hcard, relative_divisorG _
    (fun h => if h ∣ k then ((Nat.card G / h).choose (k / h) : ℤ)
      * ((σ : ℤ) - 1) ^ ((Nat.card G - k) / h) else 0)
    (card_fixA_kActive (G := G) σ hσ a k), kActiveRHS, Finset.sum_filter]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs <;> ring

end ShiftSym.P13
