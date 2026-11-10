/-
Phase H, group 05 (KActive) — proof helper module 1 of 3.

The counting step of Theorem 5.1 (paper lines 544–550): for every subgroup
`H ≤ Z_n^d` and EVERY `k ∈ ℕ` (no `k ≤ N` needed),
`#{s ∈ Fix(H) : exactly k cells in state a} = convTerm (n^d) k |H| σ`,
i.e. `binom(N/h, k/h)(σ−1)^{(N−k)/h}` under the §5 convention, `0` unless
`h ∣ k` (and `0` for `k > N`).  Route: `Fix(H) ≃ (Z_n^d ⧸ H → Fin σ)`
(certified `fixedByEquiv`), every coset has `|H|` elements
(`preimageMkEquivAddSubgroupProdSet`), and the number of maps `Q → B` with
exactly `j` preimages of `a` is `binom(|Q|, j)(|B|−1)^{|Q|−j}`.
Also: `cellsInState s a ≤ N` and the partition of `S_{n^d}` by `k`.
-/
import Shiftsym.Paper.S05_KActive
import Shiftsym.Lemmas.FixedCount

namespace ShiftSym.P05

open ShiftSym

/-! ### Maps with a prescribed number of preimages of `a` -/

theorem card_filter_fun_preimage {Q B : Type*} [Fintype Q] [DecidableEq Q] [Fintype B]
    [DecidableEq B] (a : B) (j : ℕ) :
    (Finset.univ.filter fun f : Q → B =>
        (Finset.univ.filter fun q => f q = a).card = j).card
      = (Fintype.card Q).choose j * (Fintype.card B - 1) ^ (Fintype.card Q - j) := by
  set S := Finset.univ.filter fun f : Q → B =>
        (Finset.univ.filter fun q => f q = a).card = j with hS
  have hmaps : ∀ f ∈ S, (Finset.univ.filter fun q => f q = a)
      ∈ (Finset.univ : Finset Q).powersetCard j := by
    intro f hf
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (Finset.mem_filter.mp hf).2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ T ∈ (Finset.univ : Finset Q).powersetCard j,
      (S.filter fun f => (Finset.univ.filter fun q => f q = a) = T).card
        = (Fintype.card B - 1) ^ (Fintype.card Q - j) := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    have heq : S.filter (fun f => (Finset.univ.filter fun q => f q = a) = T)
        = Fintype.piFinset (fun q => if q ∈ T then ({a} : Finset B)
            else Finset.univ.erase a) := by
      ext f
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro ⟨-, hf⟩ q
        have hq : f q = a ↔ q ∈ T := by
          rw [← hf]; simp
        split_ifs with hqT
        · exact Finset.mem_singleton.mpr (hq.mpr hqT)
        · exact Finset.mem_erase.mpr ⟨fun h => hqT (hq.mp h), Finset.mem_univ _⟩
      · intro hf
        have hT' : (Finset.univ.filter fun q => f q = a) = T := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have h := hf q
          by_cases hqT : q ∈ T
          · rw [if_pos hqT, Finset.mem_singleton] at h
            exact ⟨fun _ => hqT, fun _ => h⟩
          · rw [if_neg hqT, Finset.mem_erase] at h
            exact ⟨fun h' => absurd h' h.1, fun h' => absurd h' hqT⟩
        exact ⟨by rw [hT', hT.2], hT'⟩
    rw [heq, Fintype.card_piFinset]
    have hc1 : ∀ q, (if q ∈ T then ({a} : Finset B) else Finset.univ.erase a).card
        = if q ∈ T then 1 else Fintype.card B - 1 := by
      intro q
      split_ifs
      · exact Finset.card_singleton a
      · rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
    simp only [hc1]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have hc : (Finset.univ.filter fun q : Q => q ∉ T) = Tᶜ := by
      ext q; simp
    rw [hc, Finset.card_compl, hT.2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, smul_eq_mul]

theorem natCard_fun_preimage {Q B : Type*} [Finite Q] [Finite B] (a : B) (j : ℕ) :
    Nat.card {f : Q → B // Nat.card {q // f q = a} = j}
      = (Nat.card Q).choose j * (Nat.card B - 1) ^ (Nat.card Q - j) := by
  classical
  have := Fintype.ofFinite Q
  have := Fintype.ofFinite B
  have h1 : ∀ f : Q → B,
      Nat.card {q // f q = a} = (Finset.univ.filter fun q => f q = a).card := by
    intro f; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun f => by rw [h1 f]) :
      {f : Q → B // Nat.card {q // f q = a} = j}
        ≃ {f : Q → B // (Finset.univ.filter fun q => f q = a).card = j})]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  convert card_filter_fun_preimage (Q := Q) (B := B) a j using 2

/-! ### Cosets have `|H|` elements -/

theorem natCard_preimage_mk {G : Type*} [AddGroup G] (H : AddSubgroup G) {B : Type*}
    (f : G ⧸ H → B) (a : B) :
    Nat.card {u : G // f (QuotientAddGroup.mk u) = a}
      = Nat.card H * Nat.card {q : G ⧸ H // f q = a} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (QuotientAddGroup.preimageMkEquivAddSubgroupProdSet H {q | f q = a})

/-! ### `|Fix_k(H)|` for every `k` -/

theorem natCard_quotient_lat (n d : ℕ) [NeZero n] (H : AddSubgroup (Lat n d)) :
    Nat.card (Lat n d ⧸ H) = n ^ d / Nat.card H := by
  have hmul : H.index * Nat.card H = Nat.card (Lat n d) := H.index_mul_card
  have hpos : 0 < Nat.card H := Nat.card_pos
  rw [ShiftSym.card_lat] at hmul
  rw [← hmul, Nat.mul_div_cancel _ hpos, AddSubgroup.index_eq_card]

/-- The count of `Fix_k(H)` as maps on the coset space. -/
theorem natCard_fixK_eq_maps (n d σ : ℕ) (a : Fin σ) (k : ℕ) (H : AddSubgroup (Lat n d)) :
    Nat.card {s : Config n d (Fin σ) // s ∈ fixedBy (Fin σ) H ∧ cellsInState s a = k}
      = Nat.card {f : Lat n d ⧸ H → Fin σ //
          Nat.card H * Nat.card {q : Lat n d ⧸ H // f q = a} = k} := by
  have hcells : ∀ s : fixedBy (Fin σ) H,
      cellsInState s.1 a
        = Nat.card H * Nat.card {q : Lat n d ⧸ H // fixedByEquiv H s q = a} := by
    intro s
    unfold cellsInState
    rw [← natCard_preimage_mk H (fixedByEquiv H s) a]
    rfl
  refine Nat.card_congr ?_
  refine (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun s : Config n d (Fin σ) => s ∈ fixedBy (Fin σ) H)
    (fun s => cellsInState s a = k)).symm.trans ?_
  exact Equiv.subtypeEquiv (fixedByEquiv H) (fun s => by rw [hcells s])

theorem natCard_fixK (n d σ : ℕ) [NeZero n] (hσ : 1 ≤ σ) (a : Fin σ) (k : ℕ)
    (H : AddSubgroup (Lat n d)) :
    (Nat.card {s : Config n d (Fin σ) // s ∈ fixedBy (Fin σ) H ∧ cellsInState s a = k} : ℤ)
      = convTerm (n ^ d) k (Nat.card H) σ := by
  rw [natCard_fixK_eq_maps]
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hdvdN : Nat.card H ∣ n ^ d := card_addSubgroup_dvd_pow n d H
  unfold convTerm
  by_cases hk : Nat.card H ∣ k
  · obtain ⟨j, rfl⟩ := hk
    have hcond : ∀ f : Lat n d ⧸ H → Fin σ,
        (Nat.card H * Nat.card {q : Lat n d ⧸ H // f q = a} = Nat.card H * j)
          ↔ Nat.card {q : Lat n d ⧸ H // f q = a} = j :=
      fun f => ⟨fun h => Nat.eq_of_mul_eq_mul_left hpos h, fun h => by rw [h]⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight hcond), natCard_fun_preimage,
      natCard_quotient_lat, Nat.card_eq_fintype_card (α := Fin σ), Fintype.card_fin,
      Nat.mul_div_cancel_left _ hpos]
    by_cases hj : j ≤ n ^ d / Nat.card H
    · rw [if_pos ⟨dvd_mul_right _ _, hj⟩]
      obtain ⟨M, hM⟩ := hdvdN
      have hMj : (n ^ d - Nat.card H * j) / Nat.card H = n ^ d / Nat.card H - j := by
        rw [hM, ← Nat.mul_sub, Nat.mul_div_cancel_left _ hpos, Nat.mul_div_cancel_left _ hpos]
      rw [hMj]
      push_cast [Nat.cast_sub hσ]
      ring
    · rw [if_neg (fun h => hj h.2), Nat.choose_eq_zero_of_lt (by omega)]
      simp
  · rw [if_neg (fun h => hk h.1)]
    have hempty : IsEmpty {f : Lat n d ⧸ H → Fin σ //
        Nat.card H * Nat.card {q : Lat n d ⧸ H // f q = a} = k} :=
      ⟨fun ⟨f, hf⟩ => hk ⟨_, hf.symm⟩⟩
    rw [Nat.card_of_isEmpty]
    simp

/-- `|Fix_k(⊥)| = |C^a_k|` (all configurations with exactly `k` cells in state `a`). -/
theorem natCard_cells_eq (n d σ : ℕ) [NeZero n] (hσ : 1 ≤ σ) (a : Fin σ) (k : ℕ) :
    (Nat.card {s : Config n d (Fin σ) // cellsInState s a = k} : ℤ)
      = convTerm (n ^ d) k 1 σ := by
  have h := natCard_fixK n d σ hσ a k ⊥
  rw [AddSubgroup.card_bot] at h
  rw [← h]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun s => ?_)
  constructor
  · intro hs
    refine ⟨fun x hx => ?_, hs⟩
    rw [AddSubgroup.mem_bot] at hx
    rw [hx]
    exact shift_zero s
  · exact fun hs => hs.2

theorem convTerm_one_of_le {N k σ : ℕ} (hk : k ≤ N) :
    convTerm N k 1 σ = (N.choose k : ℤ) * ((σ : ℤ) - 1) ^ (N - k) := by
  unfold convTerm
  rw [if_pos ⟨one_dvd k, by simpa using hk⟩]
  simp

/-! ### Cell counts and the partition by `k` -/

theorem cellsInState_le (n d σ : ℕ) [NeZero n] (s : Config n d (Fin σ)) (a : Fin σ) :
    cellsInState s a ≤ n ^ d := by
  unfold cellsInState
  calc Nat.card {u : Lat n d // s u = a} ≤ Nat.card (Lat n d) := Finite.card_subtype_le _
    _ = n ^ d := ShiftSym.card_lat

theorem sum_numKActive (n d σ : ℕ) [NeZero n] (a : Fin σ) :
    ∑ k ∈ Finset.range (n ^ d + 1), numKActive n d σ a k = numSS n d σ := by
  classical
  have hmaps : ∀ s ∈ (Finset.univ.filter fun s : Config n d (Fin σ) => IsShiftSymmetric s),
      cellsInState s a ∈ Finset.range (n ^ d + 1) :=
    fun s _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (cellsInState_le n d σ s a))
  have hS : numSS n d σ
      = (Finset.univ.filter fun s : Config n d (Fin σ) => IsShiftSymmetric s).card := by
    rw [numSS, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hS, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [numKActive, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]

end ShiftSym.P05
