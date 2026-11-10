/-
Phase H, group 01 (Model): proofs of every frozen statement of
`Shiftsym/Paper/S01_Model.lean` (paper §2, lines 196–262, and the §3-preamble
Gaussian-binomial convention, lines 261–264).

Blueprint: the paper's own (mostly definitional) arguments; for Remark 2.4
the repaired claims frozen in S01 (prime cycles: every stabilized
configuration is constant; otherwise a non-constant periodic configuration
is read into a "delta" configuration).
-/
import Shiftsym.Paper.S01_Model
import Shiftsym.Lemmas.GaussCount

namespace ShiftSym.P01

open ShiftSym

/-! ## Definition 2.1 -/

theorem latFinite_proved : latFiniteStatement := by
  intro n d hn _
  have : NeZero n := ⟨by omega⟩
  infer_instance

theorem latAbelian_proved : latAbelianStatement := by
  intro n d _ _ a b
  exact add_comm a b

theorem latCard_proved : latCardStatement := by
  intro n d hn _
  have : NeZero n := ⟨by omega⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem translationActs_proved : translationActsStatement := by
  intro n d A _ _ _ _
  exact ⟨fun s => shift_zero s, fun v w s => shift_add v w s⟩

theorem stabSubgroup_proved : stabSubgroupStatement := by
  intro n d A _ _ _ _ s
  exact ⟨stab s, rfl⟩

theorem def21_proved : def21Statement :=
  ⟨latFinite_proved, latAbelian_proved, latCard_proved, translationActs_proved,
    stabSubgroup_proved⟩

/-! ## Definition 2.2 -/

/-- `S(v) = Fix(⟨v⟩)` for every `v` (the paper needs it only for `v ≠ 0`). -/
theorem sOf_eq_fixedBy {n d : ℕ} {A : Type*} (v : Lat n d) :
    sOf A v = fixedBy A (AddSubgroup.closure {v}) := by
  ext s
  constructor
  · intro hs h hh
    have hle : AddSubgroup.closure {v} ≤ stab s := by
      rw [AddSubgroup.closure_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hs
    exact hle hh
  · intro hs
    exact hs v (AddSubgroup.subset_closure (Set.mem_singleton v))

theorem sOfEqFix_proved : sOfEqFixStatement := by
  intro n d A _ _ _ _ v _
  exact sOf_eq_fixedBy v

/-- Membership in the paper's literal union is the project's `IsShiftSymmetric`. -/
theorem mem_shiftSymSet_iff {n d : ℕ} {A : Type*} (s : Config n d A) :
    s ∈ shiftSymSet n d A ↔ IsShiftSymmetric s := by
  constructor
  · intro h
    obtain ⟨v, hv0, hv⟩ := Set.mem_iUnion₂.mp h
    exact ⟨v, hv0, hv⟩
  · rintro ⟨v, hv0, hv⟩
    exact Set.mem_iUnion₂.mpr ⟨v, hv0, hv⟩

theorem unionEqStab_proved : unionEqStabStatement := by
  intro n d A _ _ _ _
  ext s
  rw [mem_shiftSymSet_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv0, hv⟩ h
    have hmem : v ∈ stabSet s := hv
    rw [h, Set.mem_singleton_iff] at hmem
    exact hv0 hmem
  · intro h
    by_contra hne
    apply h
    ext v
    rw [Set.mem_singleton_iff]
    constructor
    · intro hv
      by_contra hv0
      exact hne ⟨v, hv0, hv⟩
    · intro hv
      subst hv
      exact shift_zero s

theorem def22_proved : def22Statement :=
  ⟨sOfEqFix_proved, unionEqStab_proved⟩

/-! ## Fidelity links -/

theorem isShiftSymmetricFidelity_proved : isShiftSymmetricFidelityStatement := by
  intro n d A
  ext s
  exact (mem_shiftSymSet_iff s).symm

theorem numSSFidelity_proved : numSSFidelityStatement := by
  intro n d σ
  unfold numSS
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun s => (mem_shiftSymSet_iff s).symm))

/-! ## Definition 2.3 -/

theorem caEquivariant_proved : caEquivariantStatement := by
  intro n d A _ _ _ _ b _ o φ
  exact caMap_equivariant o φ

/-- Every translation-equivariant map on the finite torus is an offset CA:
take all lattice points as offsets and let `φ` read off `Φ(·)(0)`. -/
theorem equivariant_isOffsetCA {n d : ℕ} [NeZero n] {A : Type*}
    (Φ : Config n d A → Config n d A) (hΦ : Equivariant Φ) : IsOffsetCA Φ := by
  let e : Fin (Fintype.card (Lat n d)) ≃ Lat n d := (Fintype.equivFin (Lat n d)).symm
  refine ⟨Fintype.card (Lat n d), Fintype.card_pos, e,
    fun x => Φ (fun w => x (e.symm w)) 0, ?_⟩
  funext s u
  have h := congrFun (hΦ u s) 0
  simp only [shift_apply, zero_add] at h
  simp only [caMap, Equiv.apply_symm_apply]
  rw [← h]
  congr 1
  funext w
  rw [shift_apply, add_comm]

theorem equivariantCA_proved : equivariantCAStatement := by
  intro n d A _ hn _ _ Φ hΦ
  have : NeZero n := ⟨by omega⟩
  exact equivariant_isOffsetCA Φ hΦ

theorem caIffEquivariant_proved : caIffEquivariantStatement := by
  intro n d A _ hn hd hA Φ
  constructor
  · rintro ⟨b, _, o, φ, rfl⟩
    exact caMap_equivariant o φ
  · exact equivariantCA_proved n d A hn hd hA Φ

theorem def23_proved : def23Statement :=
  ⟨caEquivariant_proved, equivariantCA_proved, caIffEquivariant_proved⟩

/-! ## Remark 2.4: generic tools -/

/-- A nonzero lattice vector exists for `n ≥ 2`, `d ≥ 1`. -/
theorem exists_ne_zero_lat {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    ∃ v : Lat n d, v ≠ 0 := by
  have : Fact (1 < n) := ⟨by omega⟩
  refine ⟨fun _ => 1, fun h => ?_⟩
  have h1 := congrFun h ⟨0, hd⟩
  simp at h1

/-- The "delta" configuration (`a` at `0`, `c` elsewhere, `a ≠ c`) is not
shift-symmetric. -/
theorem not_isShiftSymmetric_delta {n d : ℕ} {A : Type*} {a c : A} (hac : a ≠ c) :
    ¬ IsShiftSymmetric (fun u : Lat n d => if u = 0 then a else c) := by
  rintro ⟨v, hv0, hv⟩
  have h := congrFun hv 0
  simp only [shift_apply, zero_add, if_neg hv0] at h
  exact hac h.symm

/-- A constant configuration is shift-symmetric (`n ≥ 2`, `d ≥ 1`). -/
theorem isShiftSymmetric_const {n d : ℕ} {A : Type*} (hn : 2 ≤ n) (hd : 1 ≤ d) (a : A) :
    IsShiftSymmetric (fun _ : Lat n d => a) := by
  obtain ⟨v, hv⟩ := exists_ne_zero_lat hn hd
  exact ⟨v, hv, rfl⟩

/-- "Every cell reads cell `0`" (`b = 1`, `φ = id`) is not equivariant. -/
theorem readZero_not_equivariant {n d : ℕ} {A : Type*} (hn : 2 ≤ n) (hd : 1 ≤ d)
    {a c : A} (hac : a ≠ c) :
    ¬ Equivariant (locMap (b := 1) (fun _ _ => (0 : Lat n d)) (fun x : Fin 1 → A => x 0)) := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne_zero_lat hn hd
  have h1 := congrFun (h v (fun u => if u = 0 then a else c)) 0
  simp only [locMap, etaMap, shift_apply, zero_add, if_neg hv] at h1
  exact hac h1.symm

/-- A non-constant shift-symmetric configuration yields a location-selecting
map (`b = 1`, `φ = id`, cell `0` reads `z`, every other cell reads `w`) that
breaks irreversibility. -/
theorem locBreaks_of {n d : ℕ} {A : Type} (s : Config n d A) (hs : IsShiftSymmetric s)
    {z w : Lat n d} (hzw : s z ≠ s w) : LocBreaks n d A := by
  refine ⟨1, le_rfl, fun _ u => if u = 0 then z else w, fun x => x 0, s, hs, ?_⟩
  have hΦ : locMap (fun (_ : Fin 1) (u : Lat n d) => if u = 0 then z else w)
      (fun x : Fin 1 → A => x 0) s = fun u => if u = 0 then s z else s w := by
    funext u
    simp only [locMap, etaMap]
    split_ifs <;> rfl
  rw [hΦ]
  exact not_isShiftSymmetric_delta hzw

theorem breaks_violates {n d : ℕ} {A : Type*} (Φ : Config n d A → Config n d A) :
    BreaksIrreversibility Φ → ViolatesThm81 Φ := by
  rintro ⟨s, ⟨v, hv0, hv⟩, hΦ⟩ ⟨_, _, hC⟩
  have hs : s ∈ shiftSymSet n d A := Set.mem_iUnion₂.mpr ⟨v, hv0, hv⟩
  obtain ⟨w, hw0, hw⟩ := Set.mem_iUnion₂.mp (hC ⟨s, hs, rfl⟩)
  exact hΦ ⟨w, hw0, hw⟩

theorem locBreaks_locViolates {n d : ℕ} {A : Type} : LocBreaks n d A → LocViolates n d A :=
  fun ⟨b, hb, lam, φ, h⟩ => ⟨b, hb, lam, φ, breaks_violates _ h⟩

theorem locViolates_locDepViolates {n d : ℕ} {A : Type} :
    LocViolates n d A → LocDepViolates n d A :=
  fun ⟨b, hb, lam, φ, h⟩ => ⟨b, hb, fun i u _ => lam i u, φ, h⟩

/-! ### Prime cycles: stabilized configurations are constant -/

theorem const_of_stab_prime {p : ℕ} (hp : p.Prime) {A : Type*} (s : Config p 1 A)
    (v : Lat p 1) (hv0 : v ≠ 0) (hv : shift v s = s) : ∀ u, s u = s 0 := by
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hv0' : v 0 ≠ 0 := by
    intro h
    apply hv0
    funext i
    rw [Fin.fin_one_eq_zero i]
    exact h
  intro u
  have hmem : v ∈ stab s := hv
  have hk : ((u 0 / v 0).val) • v = u := by
    funext i
    rw [Fin.fin_one_eq_zero i, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val,
      div_mul_cancel₀ _ hv0']
  have hmem' : ((u 0 / v 0).val) • v ∈ stab s := AddSubgroup.nsmul_mem _ hmem _
  rw [hk] at hmem'
  have h := congrFun (hmem' : shift u s = s) 0
  simpa using h

/-- On a prime cycle `ℤ_p^1`, every location-selecting map (broad class, any
`b`) satisfies the whole conclusion of Theorem 8.1. -/
theorem locMapDep_thm81_prime {p : ℕ} (hp : p.Prime) {A : Type*} {b : ℕ}
    (lam : Fin b → Lat p 1 → Config p 1 A → Lat p 1) (φ : (Fin b → A) → A) :
    Thm81Conclusion (locMapDep lam φ) := by
  have h1 : ∀ s : Config p 1 A, stabSet s ⊆ stabSet (locMapDep lam φ s) := by
    intro s v hv
    by_cases h0 : v = 0
    · subst h0
      exact shift_zero _
    · have hc := const_of_stab_prime hp s v h0 hv
      show shift v (locMapDep lam φ s) = locMapDep lam φ s
      funext u
      simp only [shift_apply, locMapDep, etaMap]
      congr 1
      funext i
      rw [hc (lam i (u + v) s), hc (lam i u s)]
  refine ⟨h1, fun v s _ hs => h1 s hs, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨v, hv0, hv⟩ := Set.mem_iUnion₂.mp hs
  exact Set.mem_iUnion₂.mpr ⟨v, hv0, h1 s hv⟩

theorem not_locDepViolates_prime {p : ℕ} (hp : p.Prime) (A : Type) :
    ¬ LocDepViolates p 1 A := by
  rintro ⟨b, _, lam, φ, h⟩
  exact h (locMapDep_thm81_prime hp lam φ)

/-! ### Non-prime-order lattices: an explicit breaking map -/

/-- Composite `n` (any `d ≥ 1`): the configuration "`a` where the first
coordinate is `0 mod m`, else `c`" (`m ∣ n`, `1 < m < n`) has period `m e_0`
and is not constant. -/
theorem locBreaks_composite {n d : ℕ} {A : Type} (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hnp : ¬ n.Prime) {a c : A} (hac : a ≠ c) : LocBreaks n d A := by
  obtain ⟨m, hmn, hm2, hmlt⟩ := Nat.exists_dvd_of_not_prime2 hn hnp
  have : Fact (1 < m) := ⟨by omega⟩
  have : NeZero n := ⟨by omega⟩
  let i0 : Fin d := ⟨0, hd⟩
  let f := ZMod.castHom hmn (ZMod m)
  let s : Config n d A := fun u => if f (u i0) = 0 then a else c
  have hs : IsShiftSymmetric s := by
    refine ⟨fun _ => (m : ZMod n), ?_, ?_⟩
    · intro h
      have h1 := congrFun h i0
      simp only [Pi.zero_apply] at h1
      rw [ZMod.natCast_eq_zero_iff] at h1
      exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
    · funext u
      simp only [s, shift_apply, Pi.add_apply, map_add, map_natCast, ZMod.natCast_self,
        add_zero]
  refine locBreaks_of s hs (z := 0) (w := fun _ => 1) ?_
  simpa [s] using hac

/-- `d ≥ 2` (any `n ≥ 2`): the configuration "`a` where the second coordinate
is `0`, else `c`" has period `e_0` and is not constant. -/
theorem locBreaks_dim_two {n d : ℕ} {A : Type} (hn : 2 ≤ n) (hd : 2 ≤ d)
    {a c : A} (hac : a ≠ c) : LocBreaks n d A := by
  have : Fact (1 < n) := ⟨by omega⟩
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have h01 : i1 ≠ i0 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  let s : Config n d A := fun u => if u i1 = 0 then a else c
  have hs : IsShiftSymmetric s := by
    refine ⟨fun i => if i = i0 then 1 else 0, ?_, ?_⟩
    · intro h
      have h1 := congrFun h i0
      simp at h1
    · funext u
      simp only [s, shift_apply, Pi.add_apply, if_neg h01, add_zero]
  refine locBreaks_of s hs (z := 0) (w := fun i => if i = i1 then 1 else 0) ?_
  simpa [s] using hac

theorem locBreaks_of_not {n d : ℕ} {A : Type} [Fintype A] (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hA : 2 ≤ Fintype.card A) (h : ¬ (d = 1 ∧ n.Prime)) : LocBreaks n d A := by
  obtain ⟨a, c, hac⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  by_cases hp : n.Prime
  · have hd2 : 2 ≤ d := by
      by_contra hlt
      exact h ⟨by omega, hp⟩
    exact locBreaks_dim_two hn hd2 hac
  · exact locBreaks_composite hn hd hp hac

/-! ## Remark 2.4: the frozen statements -/

theorem etaNotEquivariant_proved : etaNotEquivariantStatement := by
  intro n d A _ hn hd hA
  obtain ⟨a, c, hac⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  exact ⟨1, le_rfl, fun _ s _ => s 0, fun x => x 0, readZero_not_equivariant hn hd hac⟩

theorem etaBreaks_proved : etaBreaksStatement := by
  intro n d A _ hn hd hA
  obtain ⟨a, c, hac⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  exact ⟨1, le_rfl, fun u _ _ => if u = 0 then a else c, fun x => x 0,
    fun _ => a, isShiftSymmetric_const hn hd a, not_isShiftSymmetric_delta hac⟩

theorem stateExample_proved : stateExampleStatement := by
  refine ⟨by decide, ⟨cell1 1, by decide, by decide⟩, ?_⟩
  unfold IsShiftSymmetric
  decide

theorem stateExampleNotEquivariant_proved : stateExampleNotEquivariantStatement := by
  intro h
  -- `s = (0,1)`, `v = 1`: `Φ(τ_1 s) = (1,0)` but `τ_1 Φ(s) = (0,0)`.
  exact absurd (h (cell1 1) (tup1 ![0, 1])) (by decide)

theorem locExample_proved : locExampleStatement := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  unfold IsShiftSymmetric
  decide

theorem locExampleNotEquivariant_proved : locExampleNotEquivariantStatement := by
  intro h
  -- `s = (0,1,0,1)`, `v = 2`: `Φ(τ_2 s) = (0,1,1,1)` but `τ_2 Φ(s) = (1,1,0,1)`.
  exact absurd (h (cell1 2) (tup1 ![0, 1, 0, 1])) (by decide)

theorem locNotEquivariantFromTwo_proved : locNotEquivariantFromTwoStatement := by
  intro n d A _ hn hd hA
  obtain ⟨a, c, hac⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  exact ⟨1, le_rfl, fun _ _ => 0, fun x => x 0, readZero_not_equivariant hn hd hac⟩

theorem locNotEquivariant_proved : locNotEquivariantStatement := by
  intro n d A _ hn hd hA
  exact locNotEquivariantFromTwo_proved n d A (by omega) hd hA

theorem locPrimeThm81_proved : locPrimeThm81Statement := by
  intro p A _ hp _ b lam φ
  exact locMapDep_thm81_prime hp lam φ

theorem locFromFourRefuted_proved : locFromFourRefutedStatement := by
  intro h
  exact not_locDepViolates_prime (by norm_num : Nat.Prime 5) (Fin 2) (h 5 (by norm_num))

theorem locIff_proved : locIffStatement := by
  intro n d A _ hn hd hA
  have hfwd : ¬ (d = 1 ∧ n.Prime) → LocBreaks n d A := locBreaks_of_not hn hd hA
  have hback : LocDepViolates n d A → ¬ (d = 1 ∧ n.Prime) := by
    rintro hV ⟨rfl, hp⟩
    exact not_locDepViolates_prime hp A hV
  refine ⟨⟨fun h => hback (locViolates_locDepViolates (locBreaks_locViolates h)), hfwd⟩,
    ⟨fun h => hback (locViolates_locDepViolates h), fun h => locBreaks_locViolates (hfwd h)⟩,
    ⟨hback, fun h => locViolates_locDepViolates (locBreaks_locViolates (hfwd h))⟩⟩

theorem locLeastFour_proved : locLeastFourStatement := by
  intro A _ hA
  refine ⟨not_locDepViolates_prime Nat.prime_two A, not_locDepViolates_prime Nat.prime_three A,
    locBreaks_of_not (by norm_num) le_rfl hA (by norm_num)⟩

theorem rem24_proved : rem24Statement :=
  ⟨etaNotEquivariant_proved, etaBreaks_proved, stateExample_proved,
    stateExampleNotEquivariant_proved, locExample_proved, locExampleNotEquivariant_proved,
    locNotEquivariant_proved, locFromFourRefuted_proved, locPrimeThm81_proved, locIff_proved,
    locLeastFour_proved, locNotEquivariantFromTwo_proved⟩

/-! ## §3 preamble: the Gaussian binomial -/

/-- The paper's product `∏_{i<r} (p^{d-i}-1)/(p^{i+1}-1)` equals the project's
recursive `gaussBinom p d r` (in `ℚ`), for `p ≥ 2` and `r ≤ d`. -/
theorem prod_ratio_eq_gaussBinom {p d r : ℕ} (hp : 2 ≤ p) (hrd : r ≤ d) :
    (∏ i ∈ Finset.range r, (((p : ℚ) ^ (d - i) - 1) / ((p : ℚ) ^ (i + 1) - 1))) =
      (gaussBinom p d r : ℚ) := by
  have hx1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 1 < p)
  have hx0 : (p : ℚ) ≠ 0 := by positivity
  have hZ := gaussBinom_mul_prod_int p d r
  have hQ : (gaussBinom p d r : ℚ) * ∏ i : Fin r, ((p : ℚ) ^ r - (p : ℚ) ^ (i : ℕ)) =
      ∏ i : Fin r, ((p : ℚ) ^ d - (p : ℚ) ^ (i : ℕ)) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) hZ
    push_cast at h
    exact h
  rw [Fin.prod_univ_eq_prod_range (fun i => (p : ℚ) ^ r - (p : ℚ) ^ i),
    Fin.prod_univ_eq_prod_range (fun i => (p : ℚ) ^ d - (p : ℚ) ^ i)] at hQ
  have hA : ∀ i ∈ Finset.range r,
      (p : ℚ) ^ d - (p : ℚ) ^ i = (p : ℚ) ^ i * ((p : ℚ) ^ (d - i) - 1) := by
    intro i hi
    have hid : i ≤ d := by rw [Finset.mem_range] at hi; omega
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hid]
  have hB : ∀ i ∈ Finset.range r,
      (p : ℚ) ^ r - (p : ℚ) ^ i = (p : ℚ) ^ i * ((p : ℚ) ^ (r - i) - 1) := by
    intro i hi
    have hir : i ≤ r := by rw [Finset.mem_range] at hi; omega
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hir]
  rw [Finset.prod_congr rfl hA, Finset.prod_congr rfl hB, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib] at hQ
  have hP0 : ∏ i ∈ Finset.range r, (p : ℚ) ^ i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ hx0)
  have hrefl : ∏ i ∈ Finset.range r, ((p : ℚ) ^ (r - i) - 1) =
      ∏ i ∈ Finset.range r, ((p : ℚ) ^ (i + 1) - 1) := by
    rw [← Finset.prod_range_reflect (fun i => (p : ℚ) ^ (i + 1) - 1) r]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    show _ = (p : ℚ) ^ (r - 1 - i + 1) - 1
    rw [show r - 1 - i + 1 = r - i by omega]
  have hD0 : ∏ i ∈ Finset.range r, ((p : ℚ) ^ (i + 1) - 1) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
    have : (1 : ℚ) < (p : ℚ) ^ (i + 1) := one_lt_pow₀ hx1 (Nat.succ_ne_zero i)
    linarith
  rw [hrefl] at hQ
  rw [Finset.prod_div_distrib, eq_comm, eq_div_iff hD0]
  apply mul_left_cancel₀ hP0
  linear_combination hQ

theorem gaussBinomProductFidelity_proved : gaussBinomProductFidelityStatement := by
  intro p d r hp _ hrd
  exact prod_ratio_eq_gaussBinom hp.two_le hrd

theorem gaussBinomCount_proved : gaussBinomCountStatement := by
  intro p d r hp hd hrd
  rw [gaussBinomProductFidelity_proved p d r hp hd hrd, card_submodule_finrank hp hrd]

/-! ## Whole group -/

theorem group01_proved : group01Statement :=
  ⟨def21_proved, def22_proved, isShiftSymmetricFidelity_proved, numSSFidelity_proved,
    def23_proved, rem24_proved, gaussBinomCount_proved, gaussBinomProductFidelity_proved⟩

end ShiftSym.P01
