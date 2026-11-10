/-
The signed spanning-set count (paper Lemma 4.1; Phase C item 6; the
referees' top formalization target):

  f(W) := Σ_{J ⊆ lines(W), sup J = W} (−1)^{|J|} = (−1)^{dim W} q^{C(dim W, 2)}.

Route (the paper's self-contained one): the partition recursion
Σ_{U ≤ W} f(U) = [W = ⊥] (binomial theorem on the powerset of lines),
the alternating subspace identity Σ_{U ≤ W} (−1)^{dim U} q^{C(dim U,2)}
= [dim W = 0] (Grassmannian count + q-binomial theorem at −1, proved by
telescoping), and strong induction on the rank.
-/
import Shiftsym.Lemmas.GaussCount

open scoped Classical

namespace ShiftSym

open Module

/-! ### The q-binomial theorem at x = −1 (telescoping) -/

theorem gaussBinom_alt_sum (q R : ℕ) :
    ∑ r ∈ Finset.range (R + 1),
        (-1 : ℤ) ^ r * (q : ℤ) ^ (r.choose 2) * gaussBinom q R r
      = if R = 0 then 1 else 0 := by
  cases R with
  | zero => simp [gaussBinom]
  | succ R =>
    simp only [Nat.succ_ne_zero, if_false]
    rw [Finset.sum_range_succ']
    have hf0 : (-1 : ℤ) ^ 0 * (q : ℤ) ^ ((0 : ℕ).choose 2)
        * gaussBinom q (R + 1) 0 = 1 := by simp [gaussBinom]
    rw [hf0]
    -- expand the recurrence in each term
    have hexp : ∀ r : ℕ, (gaussBinom q (R + 1) (r + 1) : ℤ)
        = gaussBinom q R r + (q : ℤ) ^ (r + 1) * gaussBinom q R (r + 1) := by
      intro r
      have h : gaussBinom q (R + 1) (r + 1)
          = gaussBinom q R r + q ^ (r + 1) * gaussBinom q R (r + 1) := by
        simp [gaussBinom]
      exact_mod_cast h
    have hchoose : ∀ r : ℕ, (r + 1).choose 2 + (r + 1) = (r + 2).choose 2 := by
      intro r
      rw [Nat.choose_succ_succ (r + 1) 1, Nat.choose_one_right]
      exact Nat.add_comm _ _
    -- f s := the generic term at index s
    set f : ℕ → ℤ :=
      fun s => (-1 : ℤ) ^ s * (q : ℤ) ^ ((s + 1).choose 2) * gaussBinom q R s
      with hf
    have hsplit : ∀ r ∈ Finset.range (R + 1),
        (-1 : ℤ) ^ (r + 1) * (q : ℤ) ^ ((r + 1).choose 2)
            * gaussBinom q (R + 1) (r + 1)
          = -((-1 : ℤ) ^ r * (q : ℤ) ^ ((r + 1).choose 2) * gaussBinom q R r)
            + f (r + 1) := by
      intro r _
      rw [hexp r, hf]
      simp only
      rw [← hchoose r, pow_add]
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    -- first piece: −T with T := Σ_{r ∈ range (R+1)} (−1)^r q^{C(r+1,2)} G(R,r)
    set T : ℤ := ∑ r ∈ Finset.range (R + 1),
        (-1 : ℤ) ^ r * (q : ℤ) ^ ((r + 1).choose 2) * gaussBinom q R r with hT
    have hpc1 : ∑ r ∈ Finset.range (R + 1),
        -((-1 : ℤ) ^ r * (q : ℤ) ^ ((r + 1).choose 2) * gaussBinom q R r)
          = -T := by rw [hT, ← Finset.sum_neg_distrib]
    -- second piece: Σ_{r ∈ range (R+1)} f (r+1) = T − f 0, since the shifted
    -- sum's last term vanishes (G (R, R+1) = 0)
    have hlast : f (R + 1) = 0 := by
      rw [hf]
      simp [gaussBinom_eq_zero_of_lt (Nat.lt_succ_self R)]
    have hpc2 : ∑ r ∈ Finset.range (R + 1), f (r + 1) = T - 1 := by
      rw [Finset.sum_range_succ, hlast, add_zero]
      have hT' : T = (∑ r ∈ Finset.range R, f (r + 1)) + f 0 := by
        rw [hT, Finset.sum_range_succ']
      have hf0' : f 0 = 1 := by
        rw [hf]; simp [gaussBinom]
      rw [hT', hf0']
      ring
    rw [hpc1, hpc2]
    ring

/-! ### Counting subspaces below a fixed subspace -/

section SubLe

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
  [Finite V]

/-- Submodules contained in `W` with a given rank correspond to
submodules of `W` of that rank. -/
noncomputable def subLeEquiv (W : Submodule K V) (r : ℕ) :
    {U : Submodule K V // U ≤ W ∧ finrank K U = r}
      ≃ {U' : Submodule K W // finrank K U' = r} where
  toFun U := ⟨Submodule.comap W.subtype U.1, by
    have h1 : Submodule.map W.subtype (Submodule.comap W.subtype U.1)
        = U.1 := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr U.2.1]
    have h2 : finrank K (Submodule.comap W.subtype U.1)
        = finrank K (Submodule.map W.subtype
            (Submodule.comap W.subtype U.1)) :=
      (Submodule.equivMapOfInjective _
        (Submodule.injective_subtype W) _).finrank_eq
    rw [h2, h1]
    exact U.2.2⟩
  invFun U' := ⟨Submodule.map W.subtype U'.1,
    ⟨Submodule.map_subtype_le _ _, by
      have h2 : finrank K (Submodule.map W.subtype U'.1)
          = finrank K U'.1 :=
        ((Submodule.equivMapOfInjective _
          (Submodule.injective_subtype W) _).finrank_eq).symm
      rw [h2]
      exact U'.2⟩⟩
  left_inv U := Subtype.ext (by
    simp only
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr U.2.1])
  right_inv U' := Subtype.ext (by
    simp only
    rw [Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq])

/-- Count of rank-`r` submodules below `W`: `[dim W, r]_q`. -/
theorem card_finrank_le (W : Submodule K V) {r : ℕ}
    (hr : r ≤ finrank K W) :
    Nat.card {U : Submodule K V // U ≤ W ∧ finrank K U = r}
      = gaussBinom (Fintype.card K) (finrank K W) r := by
  rw [Nat.card_congr (subLeEquiv W r)]
  exact card_finrank_submodule_generic hr

end SubLe

/-! ### The alternating subspace identity and the spanning-set count -/

section Mobius

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
  [Finite V] [Fintype (Submodule K V)]

/-- Alternating Möbius-weight sum over the subspaces below `W`. -/
theorem alt_sum_le (W : Submodule K V) :
    ∑ U ∈ Finset.univ.filter (· ≤ W),
        (-1 : ℤ) ^ (finrank K U) * (Fintype.card K : ℤ) ^ ((finrank K U).choose 2)
      = if finrank K W = 0 then 1 else 0 := by
  haveI : Module.Finite K W := Module.Finite.of_finite
  set R := finrank K W with hR
  set g : ℕ → ℤ :=
    fun r => (-1 : ℤ) ^ r * (Fintype.card K : ℤ) ^ (r.choose 2) with hg
  have hmap : ∀ U ∈ Finset.univ.filter (· ≤ W),
      finrank K U ∈ Finset.range (R + 1) := by
    intro U hU
    rw [Finset.mem_range, Nat.lt_succ_iff, hR]
    exact Submodule.finrank_mono (Finset.mem_filter.mp hU).2
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun U : Submodule K V => g (finrank K U))]
  have hinner : ∀ r ∈ Finset.range (R + 1),
      (∑ U ∈ (Finset.univ.filter (· ≤ W)).filter
          (fun U : Submodule K V => finrank K U = r), g (finrank K U))
        = (gaussBinom (Fintype.card K) R r : ℤ) * g r := by
    intro r hrmem
    have hconst : ∀ U ∈ (Finset.univ.filter (· ≤ W)).filter
        (fun U : Submodule K V => finrank K U = r),
        g (finrank K U) = g r := by
      intro U hU
      rw [(Finset.mem_filter.mp hU).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Finset.filter_filter]
    have hcards : (Finset.univ.filter
        (fun U : Submodule K V => U ≤ W ∧ finrank K U = r)).card
        = Nat.card {U : Submodule K V // U ≤ W ∧ finrank K U = r} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcards, card_finrank_le W (Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hrmem))]
  rw [Finset.sum_congr rfl hinner, ← gaussBinom_alt_sum (Fintype.card K) R]
  apply Finset.sum_congr rfl
  intro r _
  rw [hg]
  ring

/-- The finset of lines (1-dimensional submodules) below `W`. -/
noncomputable def linesF (W : Submodule K V) : Finset (Submodule K V) :=
  Finset.univ.filter fun L => finrank K L = 1 ∧ L ≤ W

theorem mem_linesF {W L : Submodule K V} :
    L ∈ linesF W ↔ finrank K L = 1 ∧ L ≤ W := by
  simp [linesF]

theorem linesF_mono {U W : Submodule K V} (h : U ≤ W) :
    linesF U ⊆ linesF W := by
  intro L hL
  rw [mem_linesF] at hL ⊢
  exact ⟨hL.1, hL.2.trans h⟩

theorem linesF_bot : linesF (⊥ : Submodule K V) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro L hL
  rw [mem_linesF] at hL
  have := hL.1
  rw [le_bot_iff.mp hL.2] at this
  simp [finrank_bot] at this

theorem linesF_nonempty {W : Submodule K V} (hW : W ≠ ⊥) :
    (linesF W).Nonempty := by
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hW
  refine ⟨Submodule.span K {w}, ?_⟩
  rw [mem_linesF]
  exact ⟨finrank_span_singleton hw0,
    (Submodule.span_singleton_le_iff_mem w W).mpr hwW⟩

/-- The signed spanning-set count `f(W)` of the paper's Lemma 4.1. -/
noncomputable def spanSum (W : Submodule K V) : ℤ :=
  ∑ J ∈ (linesF W).powerset, if J.sup id = W then (-1 : ℤ) ^ J.card else 0

theorem spanSum_bot : spanSum (⊥ : Submodule K V) = 1 := by
  simp [spanSum, linesF_bot]

/-- **Partition recursion**: Σ_{U ≤ W} f(U) = [W = ⊥]. -/
theorem sum_spanSum_le (W : Submodule K V) :
    ∑ U ∈ Finset.univ.filter (· ≤ W), spanSum U
      = if W = ⊥ then 1 else 0 := by
  -- widen every spanSum U to a sum over the powerset of lines(W)
  have hcong : ∀ U ∈ Finset.univ.filter (· ≤ W),
      spanSum U = ∑ J ∈ (linesF W).powerset,
        if J.sup id = U then (-1 : ℤ) ^ J.card else 0 := by
    intro U hU
    have hUW : U ≤ W := (Finset.mem_filter.mp hU).2
    unfold spanSum
    apply Finset.sum_subset (Finset.powerset_mono.mpr (linesF_mono hUW))
    intro J hJ hJU
    rw [Finset.mem_powerset] at hJ hJU
    rw [if_neg]
    intro hsup
    apply hJU
    intro L hL
    rw [mem_linesF]
    have hLW := mem_linesF.mp (hJ hL)
    exact ⟨hLW.1, hsup ▸ Finset.le_sup (f := id) hL⟩
  rw [Finset.sum_congr rfl hcong, Finset.sum_comm]
  have hinner : ∀ J ∈ (linesF W).powerset,
      (∑ U ∈ Finset.univ.filter (· ≤ W),
          if J.sup id = U then (-1 : ℤ) ^ J.card else 0)
        = (-1 : ℤ) ^ J.card := by
    intro J hJ
    rw [Finset.mem_powerset] at hJ
    rw [Finset.sum_ite_eq]
    rw [if_pos]
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      Finset.sup_le fun L hL => (mem_linesF.mp (hJ hL)).2⟩
  rw [Finset.sum_congr rfl hinner, Finset.sum_powerset_neg_one_pow_card]
  by_cases hW : W = ⊥
  · rw [if_pos hW, if_pos]
    rw [hW, linesF_bot]
  · rw [if_neg hW, if_neg]
    exact Finset.nonempty_iff_ne_empty.mp (linesF_nonempty hW)

/-- **The signed spanning-set count** (paper Lemma 4.1, machine-checked):
`f(W) = (−1)^{dim W} q^{dim W choose 2}`. -/
theorem spanSum_eq_mobius (W : Submodule K V) :
    spanSum W = (-1 : ℤ) ^ (finrank K W)
      * (Fintype.card K : ℤ) ^ ((finrank K W).choose 2) := by
  haveI : Module.Finite K V := Module.Finite.of_finite
  suffices H : ∀ N : ℕ, ∀ W : Submodule K V, finrank K W = N →
      spanSum W = (-1 : ℤ) ^ (finrank K W)
        * (Fintype.card K : ℤ) ^ ((finrank K W).choose 2) from H _ W rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro W hWN
    by_cases hbot : W = ⊥
    · subst hbot
      rw [spanSum_bot]
      simp [finrank_bot]
    · have hne0 : finrank K W ≠ 0 := by
        obtain ⟨L, hL⟩ := linesF_nonempty hbot
        rw [mem_linesF] at hL
        haveI : Module.Finite K W := Module.Finite.of_finite
        have hmono := Submodule.finrank_mono hL.2
        rw [hL.1] at hmono
        omega
      have hrec := sum_spanSum_le W
      have halt := alt_sum_le W
      have hsplit : Finset.univ.filter (· ≤ W)
          = insert W (Finset.univ.filter (· < W)) := by
        ext U
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert]
        constructor
        · intro h
          rcases lt_or_eq_of_le h with h' | h'
          · exact Or.inr h'
          · exact Or.inl h'
        · rintro (rfl | h')
          · exact le_refl _
          · exact le_of_lt h'
      have hWnotin : W ∉ Finset.univ.filter (· < W) := by
        simp [lt_irrefl]
      rw [hsplit, Finset.sum_insert hWnotin] at hrec halt
      have hIH : ∀ U ∈ Finset.univ.filter (· < W),
          spanSum U = (-1 : ℤ) ^ (finrank K U)
            * (Fintype.card K : ℤ) ^ ((finrank K U).choose 2) := by
        intro U hU
        have hlt : U < W := (Finset.mem_filter.mp hU).2
        haveI : FiniteDimensional K W := Module.Finite.of_finite
        have hrk : finrank K U < N :=
          hWN ▸ Submodule.finrank_lt_finrank_of_lt hlt
        exact IH _ hrk U rfl
      rw [Finset.sum_congr rfl hIH] at hrec
      rw [if_neg hbot] at hrec
      rw [if_neg hne0] at halt
      linarith [hrec, halt]

end Mobius

section Classified

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
  [Finite V] [Fintype (Submodule K V)]

/-- **Classified coefficient** (claim C007's exact statement): summing the
signed spanning-set count over all rank-`r` subspaces gives
`(−1)^r q^{r choose 2} [dim V, r]_q`. -/
theorem spanSum_rank_classified {r : ℕ} (hr : r ≤ finrank K V) :
    ∑ W ∈ Finset.univ.filter
        (fun W : Submodule K V => finrank K W = r), spanSum W
      = (-1 : ℤ) ^ r * (Fintype.card K : ℤ) ^ (r.choose 2)
          * gaussBinom (Fintype.card K) (finrank K V) r := by
  have hconst : ∀ W ∈ Finset.univ.filter
      (fun W : Submodule K V => finrank K W = r),
      spanSum W = (-1 : ℤ) ^ r * (Fintype.card K : ℤ) ^ (r.choose 2) := by
    intro W hW
    rw [spanSum_eq_mobius, (Finset.mem_filter.mp hW).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcards : (Finset.univ.filter
      (fun W : Submodule K V => finrank K W = r)).card
      = Nat.card {W : Submodule K V // finrank K W = r} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcards, card_finrank_submodule_generic hr]
  push_cast
  ring

end Classified

end ShiftSym
