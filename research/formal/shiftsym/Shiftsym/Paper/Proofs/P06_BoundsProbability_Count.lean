/-
Phase H, group 06 (BoundsProbability), proof helper 2: counting arguments.

* `numSS_le_unionRHS` — Theorem 6.3(i), the union bound over the prime-order
  subgroups (completeness `isShiftSymmetric_iff_mem_biUnion`), grouped by the
  prime `p = |C|` and counted with `card_orderP_subgroups`;
* `numSS_le_gjs` — `|S| ≤ σ^{N-1}`: restriction to the nonzero cells is
  injective on shift-symmetric configurations;
* `numSS_le_cg` — `|S| ≤ (N-1) σ^{N/p₁}`: union over the nonzero translations;
* `sopf_count` — `sopf_d(n)` counts the cyclic subgroups of prime order;
* `numSS_le_naive_sub_one` — for prime `p`, `d ≥ 3`: `|S| ≤ naive − 1`;
* `single_subgroup` and `pow_le_numSS` — one order-`p₁` subgroup.
-/
import Shiftsym.Paper.S06_BoundsProbability
import Shiftsym.Lemmas.LowerBound

open scoped Classical

namespace ShiftSym.P06

open ShiftSym

variable {n d : ℕ}

theorem numSS_eq_filter_card (σ : ℕ) [NeZero n] :
    numSS n d σ = (Finset.univ.filter
      (fun s : Config n d (Fin σ) => IsShiftSymmetric s)).card :=
  natCard_shiftSymmetric_eq_filterCard σ

theorem filter_SS_eq_biUnion (σ : ℕ) [NeZero n] :
    Finset.univ.filter (fun s : Config n d (Fin σ) => IsShiftSymmetric s)
      = (primeOrderSubs n d).biUnion (fun C => fixedByF σ C) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isShiftSymmetric_iff_mem_biUnion σ s

/-- Prime-order subgroups have order a prime factor of `n`. -/
theorem card_mem_primeFactors [NeZero n] {C : AddSubgroup (Lat n d)}
    (hC : C ∈ primeOrderSubs n d) : Nat.card C ∈ n.primeFactors := by
  have hp : (Nat.card C).Prime := mem_primeOrderSubs.mp hC
  have hdvd : Nat.card C ∣ n ^ d := by
    have := AddSubgroup.card_addSubgroup_dvd_card C
    rwa [card_lat] at this
  exact Nat.mem_primeFactors.mpr ⟨hp, hp.dvd_of_dvd_pow hdvd, NeZero.ne n⟩

/-- The number of subgroups of prime order `p` as a filter card. -/
theorem card_filter_card_eq [NeZero n] {p : ℕ} (pp : p.Prime) (hpn : p ∣ n) :
    (Finset.univ.filter (fun C : AddSubgroup (Lat n d) => Nat.card C = p)).card
      = gaussBinom p d 1 := by
  rw [← card_orderP_subgroups (n := n) (d := d) pp hpn, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-! ### Theorem 6.3(i): the union bound -/

theorem numSS_le_unionRHS {σ : ℕ} (hn : 2 ≤ n) :
    numSS n d σ ≤ unionRHS n d σ := by
  have : NeZero n := ⟨by omega⟩
  rw [numSS_eq_filter_card, filter_SS_eq_biUnion]
  calc ((primeOrderSubs n d).biUnion (fun C => fixedByF σ C)).card
      ≤ ∑ C ∈ primeOrderSubs n d, (fixedByF σ C).card := Finset.card_biUnion_le
    _ = ∑ C ∈ primeOrderSubs n d, σ ^ (n ^ d / Nat.card C) := by
        simp only [card_fixedByF]
    _ = ∑ p ∈ n.primeFactors, ∑ C ∈ (primeOrderSubs n d).filter
          (fun C : AddSubgroup (Lat n d) => Nat.card C = p), σ ^ (n ^ d / Nat.card C) :=
        (Finset.sum_fiberwise_of_maps_to (fun C hC => card_mem_primeFactors hC) _).symm
    _ = unionRHS n d σ := by
        rw [unionRHS]
        refine Finset.sum_congr rfl fun p hp => ?_
        have pp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
        have hfil : (primeOrderSubs n d).filter (fun C : AddSubgroup (Lat n d) => Nat.card C = p)
            = Finset.univ.filter (fun C : AddSubgroup (Lat n d) => Nat.card C = p) := by
          ext C
          simp only [Finset.mem_filter, mem_primeOrderSubs, Finset.mem_univ, true_and]
          constructor
          · exact fun h => h.2
          · intro h; exact ⟨h ▸ pp, h⟩
        rw [Finset.sum_congr rfl (fun C hC => by
            rw [(Finset.mem_filter.mp hC).2]), Finset.sum_const, hfil,
          card_filter_card_eq pp hpn, smul_eq_mul]

/-! ### The Gao–Jackson–Seward bound -/

private theorem card_ne_zero_subtype' (G : Type*) [Zero G] [Fintype G] :
    Nat.card {w : G // w ≠ 0} = Fintype.card G - 1 := by
  simp only [ne_eq]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- Two shift-symmetric configurations that agree off the origin agree. -/
theorem SS_eq_of_agree {A : Type*} {s s' : Config n d A}
    (hs : IsShiftSymmetric s) (hs' : IsShiftSymmetric s')
    (h : ∀ u : Lat n d, u ≠ 0 → s u = s' u) : s = s' := by
  obtain ⟨v, hv0, hv⟩ := hs
  obtain ⟨w, hw0, hw⟩ := hs'
  have hv' : ∀ x, s (x + v) = s x := fun x => congrFun hv x
  have hw' : ∀ x, s' (x + w) = s' x := fun x => congrFun hw x
  funext u
  by_cases hu : u = 0
  · subst hu
    have e1 : s' 0 = s' w := by have := hw' 0; rw [zero_add] at this; exact this.symm
    by_cases hvw : w = v
    · subst hvw
      have e2 : s w = s 0 := by have := hv' 0; rwa [zero_add] at this
      rw [e1, ← h w hw0, e2]
    · have e2 : s w = s (w - v) := by
        have := hv' (w - v); rwa [sub_add_cancel] at this
      have e3 : s' (w - v) = s' (-v) := by
        have := hw' (-v); rwa [neg_add_eq_sub] at this
      have e4 : s (-v) = s 0 := by
        have := hv' (-v); rw [neg_add_cancel] at this; exact this.symm
      rw [e1, ← h w hw0, e2, h (w - v) (sub_ne_zero.mpr hvw), e3,
        ← h (-v) (neg_ne_zero.mpr hv0), e4]
  · exact h u hu

theorem numSS_le_gjs {σ : ℕ} (hn : 2 ≤ n) : numSS n d σ ≤ σ ^ (n ^ d - 1) := by
  have : NeZero n := ⟨by omega⟩
  let f : {s : Config n d (Fin σ) // IsShiftSymmetric s}
      → ({u : Lat n d // u ≠ 0} → Fin σ) := fun s u => s.1 u.1
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply SS_eq_of_agree a.2 b.2
    intro u hu
    exact congrFun hab ⟨u, hu⟩
  have h1 := Nat.card_le_card_of_injective f hf
  have hfin : Nat.card (Fin σ) = σ := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Nat.card_fun, card_ne_zero_subtype', hfin] at h1
  have hc : Fintype.card (Lat n d) = n ^ d := by simp
  rw [hc] at h1
  exact h1

/-! ### The Castillo-Ramirez–Gadouleau bound -/

theorem two_le_addOrderOf [NeZero n] {v : Lat n d} (hv : v ≠ 0) : 2 ≤ addOrderOf v := by
  have h0 : addOrderOf v ≠ 0 := by
    intro h
    have := addOrderOf_lat_dvd v
    rw [h] at this
    exact NeZero.ne n (Nat.eq_zero_of_zero_dvd this)
  have h1 : addOrderOf v ≠ 1 := fun h => hv (AddMonoid.addOrderOf_eq_one_iff.mp h)
  omega

theorem numSS_le_cg {σ : ℕ} (hn : 2 ≤ n) (hσ : 1 ≤ σ) :
    numSS n d σ ≤ (n ^ d - 1) * σ ^ (n ^ d / n.minFac) := by
  have : NeZero n := ⟨by omega⟩
  rw [numSS_eq_filter_card]
  have hsub : Finset.univ.filter (fun s : Config n d (Fin σ) => IsShiftSymmetric s)
      ⊆ (Finset.univ.filter (fun v : Lat n d => v ≠ 0)).biUnion
          (fun v => fixedByF σ (AddSubgroup.zmultiples v)) := by
    intro s hs
    obtain ⟨v, hv0, hv⟩ := (Finset.mem_filter.mp hs).2
    refine Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv0⟩, ?_⟩
    rw [mem_fixedByF]
    exact AddSubgroup.zmultiples_le.mpr (mem_stab.mpr hv)
  have hcard : (Finset.univ.filter (fun v : Lat n d => v ≠ 0)).card = n ^ d - 1 := by
    rw [Finset.filter_ne' Finset.univ (0 : Lat n d), Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ]
    simp
  have hmf : 0 < n.minFac := Nat.minFac_pos n
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v : Lat n d => v ≠ 0),
          (fixedByF σ (AddSubgroup.zmultiples v)).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v : Lat n d => v ≠ 0),
          σ ^ (n ^ d / n.minFac) := by
        apply Finset.sum_le_sum
        intro v hv
        have hv0 : v ≠ 0 := (Finset.mem_filter.mp hv).2
        rw [card_fixedByF, Nat.card_zmultiples]
        apply Nat.pow_le_pow_right hσ
        apply Nat.div_le_div_left _ hmf
        exact Nat.minFac_le_of_dvd (two_le_addOrderOf hv0) (addOrderOf_lat_dvd v)
    _ = (n ^ d - 1) * σ ^ (n ^ d / n.minFac) := by
        rw [Finset.sum_const, hcard, smul_eq_mul]

/-! ### `sopf_d` counts the cyclic subgroups of prime order -/

theorem sopf_count (hn : 2 ≤ n) :
    Nat.card {C : AddSubgroup (Lat n d) //
        IsAddCyclic C ∧ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ Nat.card C = p}
      = sopfD n d := by
  have : NeZero n := ⟨by omega⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hset : Finset.univ.filter (fun C : AddSubgroup (Lat n d) =>
        IsAddCyclic C ∧ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ Nat.card C = p)
      = n.primeFactors.biUnion
          (fun p => Finset.univ.filter (fun C : AddSubgroup (Lat n d) => Nat.card C = p)) := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨-, p, pp, hpn, hC⟩
      exact ⟨p, Nat.mem_primeFactors.mpr ⟨pp, hpn, NeZero.ne n⟩, hC⟩
    · rintro ⟨p, hp, hC⟩
      have pp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have : Fact p.Prime := ⟨pp⟩
      exact ⟨isAddCyclic_of_prime_card hC, p, pp, Nat.dvd_of_mem_primeFactors hp, hC⟩
  rw [hset, Finset.card_biUnion]
  · rw [sopfD]
    refine Finset.sum_congr rfl fun p hp => ?_
    exact card_filter_card_eq (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  · intro p _ q _ hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro C hC hC'
    exact hpq ((Finset.mem_filter.mp hC).2.symm.trans (Finset.mem_filter.mp hC').2)

/-! ### One subgroup of order `p₁` -/

theorem single_subgroup (σ : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    ∃ C : AddSubgroup (Lat n d),
      IsAddCyclic C ∧ Nat.card C = n.minFac
        ∧ fixedBy (Fin σ) C ⊆ {s | IsShiftSymmetric s}
        ∧ Nat.card (fixedBy (Fin σ) C) = σ ^ (n ^ d / n.minFac) := by
  have : NeZero n := ⟨by omega⟩
  have pp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have : Fact n.minFac.Prime := ⟨pp⟩
  obtain ⟨C, hC⟩ := exists_orderP_subgroup (n := n) (d := d) pp (Nat.minFac_dvd n) hd
  refine ⟨C, isAddCyclic_of_prime_card hC, hC, ?_, ?_⟩
  · intro s hs
    have hCbot : C ≠ ⊥ := by
      intro hbot
      rw [hbot, AddSubgroup.card_bot] at hC
      exact pp.one_lt.ne hC
    obtain ⟨v, hvC, hv0⟩ := (AddSubgroup.bot_or_exists_ne_zero C).resolve_left hCbot
    exact ⟨v, hv0, hs v hvC⟩
  · rw [card_fixedBy_div, Nat.card_eq_fintype_card, Fintype.card_fin, hC]

theorem pow_le_numSS (σ : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    σ ^ (n ^ d / n.minFac) ≤ numSS n d σ := by
  have : NeZero n := ⟨by omega⟩
  rw [numSS_eq_filter_card]
  exact card_SS_ge_fix σ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n) hd

theorem numSS_pos (σ : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 1 ≤ σ) : 0 < numSS n d σ :=
  lt_of_lt_of_le (pow_pos (by omega : 0 < σ) _) (pow_le_numSS σ hn hd)

/-! ### Remark 6.2: the naive expression strictly exceeds the count (`d ≥ 3`) -/

theorem numSS_le_naive_sub_one {p d σ : ℕ} (pp : p.Prime) (hd : 3 ≤ d) (hσ : 2 ≤ σ) :
    (numSS p d σ : ℤ)
      ≤ (gaussBinom p d 1 : ℤ) * (σ : ℤ) ^ (p ^ (d - 1))
        - ((gaussBinom p d 1 : ℤ) - 1) * σ - 1 := by
  have : NeZero p := ⟨pp.ne_zero⟩
  have : Fact p.Prime := ⟨pp⟩
  set T := primeOrderSubs p d with hT
  set A : AddSubgroup (Lat p d) → Finset (Config p d (Fin σ)) := fun C => fixedByF σ C
    with hA
  set g : ℕ := σ ^ (p ^ (d - 1)) with hg
  -- every prime-order subgroup has order `p`
  have hcardT : ∀ C ∈ T, Nat.card C = p := by
    intro C hC
    have := card_mem_primeFactors hC
    rw [pp.primeFactors, Finset.mem_singleton] at this
    exact this
  have hAcard : ∀ C ∈ T, (A C).card = g := by
    intro C hC
    simp only [hA, card_fixedByF, hcardT C hC, hg]
    rw [Nat.div_eq_of_eq_mul_left pp.pos (by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)])]
  have hTcard : T.card = gaussBinom p d 1 := by
    rw [← card_filter_card_eq (n := p) (d := d) pp dvd_rfl]
    congr 1
    ext C
    simp only [hT, mem_primeOrderSubs, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have := card_mem_primeFactors (mem_primeOrderSubs.mpr h)
      rw [pp.primeFactors, Finset.mem_singleton] at this
      exact this
    · intro h; rw [h]; exact pp
  -- two explicit lines
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  let i2 : Fin d := ⟨2, by omega⟩
  let e : Fin d → Lat p d := fun i => Pi.single i 1
  have he0 : ∀ i, e i ≠ 0 := by
    intro i h
    have := congrFun h i
    simp [e] at this
  have heord : ∀ i, addOrderOf (e i) = p := fun i =>
    addOrderOf_eq_prime (nsmul_self_lat (e i)) (he0 i)
  set C0 := AddSubgroup.zmultiples (e i0) with hC0def
  set C1 := AddSubgroup.zmultiples (e i1) with hC1def
  have hC0 : C0 ∈ T := mem_primeOrderSubs.mpr (by rw [Nat.card_zmultiples, heord]; exact pp)
  have hC1 : C1 ∈ T := mem_primeOrderSubs.mpr (by rw [Nat.card_zmultiples, heord]; exact pp)
  have hne : C1 ≠ C0 := by
    intro h
    have hmem : e i1 ∈ C0 := h ▸ AddSubgroup.mem_zmultiples (e i1)
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have := congrFun hk i1
    simp [e, i0, i1] at this
  -- constants
  let K : Finset (Config p d (Fin σ)) := Finset.univ.image (fun a : Fin σ => fun _ => a)
  have hK : K.card = σ := by
    rw [Finset.card_image_of_injective _ (fun a b h => congrFun h 0), Finset.card_univ,
      Fintype.card_fin]
  have hKA : ∀ C, K ⊆ A C := by
    intro C s hs
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hs
    simp only [hA]
    rw [mem_fixedByF]
    intro h _
    rfl
  -- a nonconstant configuration fixed by both lines
  let w : Config p d (Fin σ) := fun u => if u i2 = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩
  have hwfix : ∀ i : Fin d, i ≠ i2 → w ∈ A (AddSubgroup.zmultiples (e i)) := by
    intro i hi
    simp only [hA]
    rw [mem_fixedByF]
    apply AddSubgroup.zmultiples_le.mpr
    rw [mem_stab]
    funext u
    simp only [shift_apply, w, e, Pi.add_apply, Pi.single_apply, if_neg (Ne.symm hi),
      add_zero]
  have hw0 : w ∈ A C0 := hwfix i0 (by simp [i0, i2])
  have hw1 : w ∈ A C1 := hwfix i1 (by simp [i1, i2])
  have hwK : w ∉ K := by
    intro hwK
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hwK
    have h1 := congrFun ha 0
    have h2 := congrFun ha (e i2)
    have hp1 : (1 : ZMod p) ≠ 0 := one_ne_zero
    simp [w, e, hp1] at h1 h2
    have h3 := h1.symm.trans h2
    exact absurd (congrArg Fin.val h3) (by simp)
  -- the union is controlled by `A C0` and the differences
  have hsub : T.biUnion A ⊆ A C0 ∪ (T.erase C0).biUnion (fun C => A C \ A C0) := by
    intro s hs
    obtain ⟨C, hC, hsC⟩ := Finset.mem_biUnion.mp hs
    by_cases h0 : s ∈ A C0
    · exact Finset.mem_union_left _ h0
    · apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr ⟨C, Finset.mem_erase.mpr ⟨?_, hC⟩,
        Finset.mem_sdiff.mpr ⟨hsC, h0⟩⟩
      rintro rfl
      exact h0 hsC
  have hdiff : ∀ C ∈ T, ((A C \ A C0).card : ℤ) + σ ≤ g := by
    intro C hC
    have h1 := Finset.card_sdiff_add_card_inter (A C) (A C0)
    have h2 : σ ≤ (A C ∩ A C0).card := by
      have := Finset.card_le_card (Finset.subset_inter (hKA C) (hKA C0))
      rw [hK] at this
      exact this
    rw [hAcard C hC] at h1
    have : ((A C \ A C0).card : ℤ) + (A C ∩ A C0).card = g := by exact_mod_cast h1
    have h2' : (σ : ℤ) ≤ (A C ∩ A C0).card := by exact_mod_cast h2
    linarith
  have hdiff1 : ((A C1 \ A C0).card : ℤ) + σ + 1 ≤ g := by
    have h1 := Finset.card_sdiff_add_card_inter (A C1) (A C0)
    have h2 : σ + 1 ≤ (A C1 ∩ A C0).card := by
      have := Finset.card_le_card (show insert w K ⊆ A C1 ∩ A C0 by
        intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact Finset.mem_inter.mpr ⟨hw1, hw0⟩
        · exact Finset.subset_inter (hKA C1) (hKA C0) hs)
      rw [Finset.card_insert_of_notMem hwK, hK] at this
      exact this
    rw [hAcard C1 hC1] at h1
    have : ((A C1 \ A C0).card : ℤ) + (A C1 ∩ A C0).card = g := by exact_mod_cast h1
    have h2' : (σ : ℤ) + 1 ≤ (A C1 ∩ A C0).card := by exact_mod_cast h2
    linarith
  have hC1mem : C1 ∈ T.erase C0 := Finset.mem_erase.mpr ⟨hne, hC1⟩
  have hsum : (∑ C ∈ T.erase C0, ((A C \ A C0).card : ℤ))
      ≤ ((T.card : ℤ) - 1) * ((g : ℤ) - σ) - 1 := by
    rw [← Finset.add_sum_erase _ _ hC1mem]
    have hrest : (∑ C ∈ (T.erase C0).erase C1, ((A C \ A C0).card : ℤ))
        ≤ (((T.erase C0).erase C1).card : ℤ) * ((g : ℤ) - σ) := by
      have := Finset.sum_le_card_nsmul ((T.erase C0).erase C1)
        (fun C => ((A C \ A C0).card : ℤ)) ((g : ℤ) - σ) (by
          intro C hC
          have hCT : C ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC)
          have := hdiff C hCT
          linarith)
      rwa [nsmul_eq_mul] at this
    have hc : (((T.erase C0).erase C1).card : ℤ) = (T.card : ℤ) - 2 := by
      rw [Finset.card_erase_of_mem hC1mem, Finset.card_erase_of_mem hC0]
      have : 2 ≤ T.card := by
        have := Finset.card_le_card (show ({C0, C1} : Finset _) ⊆ T by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hC0
          · rw [Finset.mem_singleton.mp hx]; exact hC1)
        rwa [Finset.card_pair hne.symm] at this
      push_cast [Nat.sub_sub, Nat.cast_sub this]
      ring
    rw [hc] at hrest
    linarith
  have hmain : ((T.biUnion A).card : ℤ)
      ≤ (A C0).card + ∑ C ∈ T.erase C0, ((A C \ A C0).card : ℤ) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (A C0) ((T.erase C0).biUnion (fun C => A C \ A C0))
    have h3 := Finset.card_biUnion_le (s := T.erase C0) (t := fun C => A C \ A C0)
    have : (T.biUnion A).card
        ≤ (A C0).card + ∑ C ∈ T.erase C0, (A C \ A C0).card := by omega
    exact_mod_cast this
  have hS : numSS p d σ = (T.biUnion A).card := by
    rw [numSS_eq_filter_card, filter_SS_eq_biUnion]
  rw [hS]
  rw [hAcard C0 hC0] at hmain
  rw [hTcard] at hsum
  have hgσ : (g : ℤ) = (σ : ℤ) ^ (p ^ (d - 1)) := by rw [hg]; push_cast; ring
  rw [← hgσ]
  linarith

end ShiftSym.P06
