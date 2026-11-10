/-
Paper group 13 (Section 4.5; moved from extension group A1) (AbelianEnum) — proof helper module 1: the setting on an
arbitrary finite abelian group `G` (THEOREMS.md, Theorem A1, Steps 1–2).

* `torsG G p` = `G[p] = {g | p • g = 0}` as an additive subgroup, with its
  `ZMod p`-module structure (`AddCommGroup.zmodModule`, scoped instance);
  `pRank G p = finrank (ZMod p) G[p]` for prime `p` and the frozen
  `pRankPowStatement` (`pRankPow_proved`);
* the subgroup ↔ submodule dictionary `ofModG` / `toModG` at a prime `p`
  (the core's `Bridge.lean` with `Lat n d` replaced by `G`);
* prime-order subgroups, the stabilizer `stabG`, completeness (Step 1), fixed
  sets over an arbitrary finite alphabet and their intersections (Step 2), and
  the relative inclusion–exclusion formula (Step 3, IE form);
* the order of a join of subgroups in pairwise-coprime torsions (Bézout; the
  core's `Primary.lean` for `G`).

Helpers live in `ShiftSym.P13.Gen`; instances are scoped there.
-/
import Shiftsym.Lemmas.MobiusSum
import Shiftsym.Paper.S13_AbelianGroups

open scoped Classical

namespace ShiftSym.P13.Gen

open ShiftSym ShiftSym.P13 Module

/-! ### `G[p]` and its `F_p`-structure -/

section Tors

variable (G : Type*) [AddCommGroup G]

/-- `G[p] = {g ∈ G | p • g = 0}`. -/
def torsG (p : ℕ) : AddSubgroup G where
  carrier := {g | p • g = 0}
  add_mem' := by
    intro a b ha hb
    change p • a = 0 at ha
    change p • b = 0 at hb
    change p • (a + b) = 0
    rw [nsmul_add, ha, hb, add_zero]
  zero_mem' := nsmul_zero p
  neg_mem' := by
    intro a ha
    change p • a = 0 at ha
    change p • (-a) = 0
    rw [smul_neg, ha, neg_zero]

variable {G}

theorem mem_torsG {p : ℕ} {g : G} : g ∈ torsG G p ↔ p • g = 0 := Iff.rfl

theorem nsmul_torsG (p : ℕ) (x : torsG G p) : p • x = 0 :=
  Subtype.ext (by
    rw [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero]
    exact x.2)

/-- The `F_p`-vector-space structure of `G[p]`. -/
scoped instance torsModule (p : ℕ) : Module (ZMod p) (torsG G p) :=
  AddCommGroup.zmodModule (nsmul_torsG p)

/-- `Nat.card G[p]` is the frozen statement's `Nat.card {g // p • g = 0}`. -/
theorem card_torsG (p : ℕ) :
    Nat.card (torsG G p) = Nat.card {g : G // p • g = 0} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

variable [Finite G]

scoped instance torsSubFinite (p : ℕ) : Finite (Submodule (ZMod p) (torsG G p)) :=
  Finite.of_injective (fun U => (U : Set (torsG G p))) SetLike.coe_injective

noncomputable scoped instance torsSubFintype (p : ℕ) :
    Fintype (Submodule (ZMod p) (torsG G p)) :=
  Fintype.ofFinite _

theorem card_torsG_pow (p : ℕ) [Fact p.Prime] :
    Nat.card (torsG G p) = p ^ finrank (ZMod p) (torsG G p) := by
  have := Fintype.ofFinite (torsG G p)
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

/-- For prime `p`, the frozen `pRank` is the `F_p`-dimension of `G[p]`. -/
theorem pRank_eq_finrank (p : ℕ) [hp : Fact p.Prime] :
    pRank G p = finrank (ZMod p) (torsG G p) := by
  rw [pRank, ← card_torsG, card_torsG_pow, Nat.factorization_pow,
    Finsupp.smul_apply, hp.out.factorization_self, smul_eq_mul, mul_one]

theorem card_submodule_pow (p : ℕ) [Fact p.Prime]
    (U : Submodule (ZMod p) (torsG G p)) :
    Nat.card U = p ^ finrank (ZMod p) U := by
  have := Fintype.ofFinite U
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

theorem finrank_eq_one_of_card_eq {p : ℕ} [hp : Fact p.Prime]
    {U : Submodule (ZMod p) (torsG G p)} (hU : Nat.card U = p) :
    finrank (ZMod p) U = 1 := by
  have h := card_submodule_pow p U
  rw [hU] at h
  nth_rewrite 1 [← pow_one p] at h
  exact (Nat.pow_right_injective hp.out.two_le h).symm

end Tors

/-- **The `p`-rank Delta** (frozen `pRankPowStatement`): for prime `p`,
`|G[p]| = p ^ pRank G p`. -/
theorem pRankPow_aux (G : Type*) [AddCommGroup G] [Finite G] (p : ℕ) (hp : p.Prime) :
    Nat.card {g : G // p • g = 0} = p ^ pRank G p := by
  have := Fact.mk hp
  rw [← card_torsG, card_torsG_pow, pRank_eq_finrank]

end ShiftSym.P13.Gen

namespace ShiftSym.P13

/-- **Frozen `pRankPowStatement`, machine-checked.** -/
theorem pRankPow_proved (G : Type*) [AddCommGroup G] [Finite G] (p : ℕ) :
    pRankPowStatement G p :=
  fun hp => Gen.pRankPow_aux G p hp

end ShiftSym.P13

namespace ShiftSym.P13.Gen

open ShiftSym ShiftSym.P13 Module

/-! ### The subgroup ↔ submodule dictionary at `p` -/

section Dict

variable {G : Type*} [AddCommGroup G]

/-- From `F_p`-submodules of `G[p]` to additive subgroups of `G`. -/
def ofModG (p : ℕ) (U : Submodule (ZMod p) (torsG G p)) : AddSubgroup G :=
  U.toAddSubgroup.map (torsG G p).subtype

/-- From additive subgroups of `G` to `F_p`-submodules of `G[p]`. -/
def toModG (p : ℕ) (H : AddSubgroup G) : Submodule (ZMod p) (torsG G p) :=
  AddSubgroup.toZModSubmodule p (H.addSubgroupOf (torsG G p))

theorem toModG_ofModG (p : ℕ) (U : Submodule (ZMod p) (torsG G p)) :
    toModG p (ofModG p U) = U := by
  unfold toModG ofModG
  have h : (U.toAddSubgroup.map (torsG G p).subtype).addSubgroupOf (torsG G p)
      = U.toAddSubgroup :=
    AddSubgroup.comap_map_eq_self_of_injective (torsG G p).subtype_injective _
  rw [h, Submodule.toAddSubgroup_toZModSubmodule]

theorem ofModG_toModG (p : ℕ) {H : AddSubgroup G} (hH : H ≤ torsG G p) :
    ofModG p (toModG p H) = H := by
  unfold toModG ofModG
  rw [AddSubgroup.toZModSubmodule_toAddSubgroup, AddSubgroup.addSubgroupOf_map_subtype]
  exact inf_eq_left.mpr hH

theorem ofModG_le_torsG (p : ℕ) (U : Submodule (ZMod p) (torsG G p)) :
    ofModG p U ≤ torsG G p :=
  AddSubgroup.map_subtype_le _

theorem toModG_mono (p : ℕ) : Monotone (toModG (G := G) p) := by
  intro H K hHK
  exact (AddSubgroup.toZModSubmodule p).monotone (AddSubgroup.comap_mono hHK)

theorem ofModG_injective (p : ℕ) : Function.Injective (ofModG (G := G) p) :=
  fun U V h => by rw [← toModG_ofModG p U, h, toModG_ofModG]

theorem ofModG_bot (p : ℕ) : ofModG (G := G) p ⊥ = ⊥ := by
  unfold ofModG
  have h : (⊥ : Submodule (ZMod p) (torsG G p)).toAddSubgroup = ⊥ :=
    (AddSubgroup.toZModSubmodule p).symm.map_bot
  rw [h, AddSubgroup.map_bot]

theorem ofModG_sup (p : ℕ) (U V : Submodule (ZMod p) (torsG G p)) :
    ofModG p (U ⊔ V) = ofModG p U ⊔ ofModG p V := by
  unfold ofModG
  have h : (U ⊔ V).toAddSubgroup = U.toAddSubgroup ⊔ V.toAddSubgroup :=
    map_sup ((AddSubgroup.toZModSubmodule p).symm
      : Submodule (ZMod p) (torsG G p) ≃o AddSubgroup _) U V
  rw [h, AddSubgroup.map_sup]

theorem ofModG_finset_sup {α : Type*} (p : ℕ) (J : Finset α)
    (f : α → Submodule (ZMod p) (torsG G p)) :
    ofModG p (J.sup f) = J.sup (fun a => ofModG p (f a)) := by
  induction J using Finset.cons_induction with
  | empty => simpa using ofModG_bot (G := G) p
  | cons a s ha ih => rw [Finset.sup_cons, Finset.sup_cons, ofModG_sup, ih]

theorem toModG_finset_sup (p : ℕ) {t : Finset (AddSubgroup G)}
    (ht : ∀ C ∈ t, C ≤ torsG G p) :
    toModG p (t.sup id) = t.sup (fun C => toModG p C) := by
  apply ofModG_injective p
  rw [ofModG_toModG p (Finset.sup_le (f := id) ht), ofModG_finset_sup]
  exact (Finset.sup_congr rfl fun C hC => (ofModG_toModG p (ht C hC))).symm

theorem card_ofModG (p : ℕ) (U : Submodule (ZMod p) (torsG G p)) :
    Nat.card (ofModG p U) = Nat.card U := by
  unfold ofModG
  rw [← Nat.card_congr (AddSubgroup.equivMapOfInjective _ _
    ((torsG G p).subtype_injective)).toEquiv]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)

theorem card_toModG (p : ℕ) {H : AddSubgroup G} (hH : H ≤ torsG G p) :
    Nat.card (toModG p H) = Nat.card H := by
  conv_rhs => rw [← ofModG_toModG p hH]
  rw [card_ofModG]

end Dict

/-! ### Torsion arithmetic and the order of a join across coprime torsions -/

section Primary

open Function

variable {G : Type*} [AddCommGroup G]

theorem torsG_mono {a b : ℕ} (hab : a ∣ b) : torsG G a ≤ torsG G b := by
  intro v hv
  rw [mem_torsG] at hv ⊢
  obtain ⟨c, rfl⟩ := hab
  rw [mul_nsmul, hv, smul_zero]

theorem torsG_inf_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    torsG G a ⊓ torsG G b = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hva, hvb⟩ := AddSubgroup.mem_inf.mp hv
  rw [mem_torsG] at hva hvb
  rw [AddSubgroup.mem_bot]
  have hcop : IsCoprime (a : ℤ) (b : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact hab
  obtain ⟨u, w, huw⟩ := hcop
  have hva' : (a : ℤ) • v = 0 := by rw [natCast_zsmul]; exact hva
  have hvb' : (b : ℤ) • v = 0 := by rw [natCast_zsmul]; exact hvb
  calc v = (1 : ℤ) • v := (one_zsmul v).symm
    _ = (u * a + w * b : ℤ) • v := by rw [huw]
    _ = u • ((a : ℤ) • v) + w • ((b : ℤ) • v) := by
        rw [add_zsmul, mul_zsmul, mul_zsmul]
    _ = 0 := by rw [hva', hvb', smul_zero, smul_zero, add_zero]

variable {ι : Type*} [Fintype ι]

/-- The summation homomorphism out of a product of subgroups. -/
def sumHomG (L : ι → AddSubgroup G) : (∀ i, L i) →+ G :=
  AddMonoidHom.mk' (fun y => ∑ i, (y i : G)) (by
    intro y z
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => rfl)

theorem sumHomG_range (L : ι → AddSubgroup G) :
    (sumHomG L).range = Finset.univ.sup L := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact AddSubgroup.sum_mem _ fun i _ =>
      Finset.le_sup (f := L) (Finset.mem_univ i) (y i).2
  · apply Finset.sup_le
    intro i _ x hx
    refine ⟨Pi.single i ⟨x, hx⟩, ?_⟩
    change ∑ j, ((Pi.single i (⟨x, hx⟩ : L i) : ∀ j, L j) j : G) = x
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji]
      rfl
    · intro hi
      exact absurd (Finset.mem_univ i) hi

theorem sumHomG_injective (m : ι → ℕ) (L : ι → AddSubgroup G)
    (hm : ∀ i, L i ≤ torsG G (m i))
    (hcop : Pairwise (Nat.Coprime on m)) :
    Function.Injective (sumHomG L) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  change ∑ i, (y i : G) = 0 at hy
  funext i
  refine Subtype.ext ?_
  show (y i : G) = 0
  have hsplit : (y i : G) = -∑ j ∈ Finset.univ.erase i, (y j : G) := by
    have h := Finset.add_sum_erase Finset.univ (fun j => (y j : G)) (Finset.mem_univ i)
    rw [hy] at h
    exact eq_neg_of_add_eq_zero_left h
  have hmem_i : (y i : G) ∈ torsG G (m i) := hm i (y i).2
  have hmem_rest : (y i : G) ∈ torsG G (∏ j ∈ Finset.univ.erase i, m j) := by
    rw [hsplit]
    exact AddSubgroup.neg_mem _ (AddSubgroup.sum_mem _ fun j hj =>
      torsG_mono (Finset.dvd_prod_of_mem m hj) (hm j (y j).2))
  have hcop' : Nat.Coprime (m i) (∏ j ∈ Finset.univ.erase i, m j) :=
    Nat.Coprime.prod_right fun j hj => hcop (Ne.symm (Finset.ne_of_mem_erase hj))
  have := torsG_inf_coprime (G := G) hcop'
  have hbot : (y i : G) ∈ (⊥ : AddSubgroup G) := by
    rw [← this]
    exact AddSubgroup.mem_inf.mpr ⟨hmem_i, hmem_rest⟩
  exact AddSubgroup.mem_bot.mp hbot

/-- **Order of a join across coprime torsions.** -/
theorem card_univ_sup_of_torsG (m : ι → ℕ) (L : ι → AddSubgroup G)
    (hm : ∀ i, L i ≤ torsG G (m i)) (hcop : Pairwise (Nat.Coprime on m)) :
    Nat.card ((Finset.univ.sup L : AddSubgroup G)) = ∏ i, Nat.card (L i) := by
  rw [← sumHomG_range]
  rw [← Nat.card_congr
    (AddMonoidHom.ofInjective (sumHomG_injective m L hm hcop)).toEquiv]
  rw [Nat.card_pi]

end Primary

end ShiftSym.P13.Gen

namespace ShiftSym.P13.Gen

open ShiftSym ShiftSym.P13 Module

/-! ### Step 1: stabilizers, prime-order subgroups, completeness -/

section Complete

variable {G : Type*} [AddCommGroup G]

/-- The stabilizer `Stab(s) = {v | ∀ u, s (u + v) = s u}`. -/
def stabG {A : Type*} (s : G → A) : AddSubgroup G where
  carrier := {v | ∀ u, s (u + v) = s u}
  add_mem' := by
    intro a b ha hb u
    change ∀ u, s (u + a) = s u at ha
    change ∀ u, s (u + b) = s u at hb
    rw [← add_assoc, hb, ha]
  zero_mem' := fun u => by rw [add_zero]
  neg_mem' := by
    intro a ha u
    change ∀ u, s (u + a) = s u at ha
    have h := ha (u + -a)
    rw [add_assoc, neg_add_cancel, add_zero] at h
    exact h.symm

theorem mem_stabG {A : Type*} {s : G → A} {v : G} :
    v ∈ stabG s ↔ ∀ u, s (u + v) = s u := Iff.rfl

variable [Finite G]

noncomputable scoped instance addSubgroupFintype : Fintype (AddSubgroup G) := Fintype.ofFinite _

variable (G) in
/-- The prime-order subgroups of `G`. -/
noncomputable def primeOrderSubsG : Finset (AddSubgroup G) :=
  Finset.univ.filter fun C => (Nat.card C).Prime

variable (G) in
/-- The order-`p` subgroups of `G`. -/
noncomputable def linesPG (p : ℕ) : Finset (AddSubgroup G) :=
  (primeOrderSubsG G).filter fun C => Nat.card C = p

theorem mem_primeOrderSubsG {C : AddSubgroup G} :
    C ∈ primeOrderSubsG G ↔ (Nat.card C).Prime := by
  simp [primeOrderSubsG]

theorem mem_linesPG {p : ℕ} {C : AddSubgroup G} (hp : p.Prime) :
    C ∈ linesPG G p ↔ Nat.card C = p := by
  simp only [linesPG, Finset.mem_filter, mem_primeOrderSubsG]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hp, h⟩⟩

omit [Finite G] in
theorem le_torsG_of_card {p : ℕ} {C : AddSubgroup G} (hC : Nat.card C = p) :
    C ≤ torsG G p := by
  intro x hx
  rw [mem_torsG, ← addOrderOf_dvd_iff_nsmul_eq_zero]
  have h := AddSubgroup.addOrderOf_dvd_natCard C hx
  rwa [hC] at h

theorem card_mem_primeFactorsG {C : AddSubgroup G} (hC : (Nat.card C).Prime) :
    Nat.card C ∈ (Nat.card G).primeFactors :=
  Nat.mem_primeFactors.mpr ⟨hC, AddSubgroup.card_addSubgroup_dvd_card C,
    Nat.card_pos.ne'⟩

/-- **Step 1 (completeness), element form**: a nonzero period yields a period
of prime order. -/
theorem exists_prime_order_of_ne_zero {A : Type*} {s : G → A} {v : G}
    (hv0 : v ≠ 0) (hv : v ∈ stabG s) :
    ∃ w : G, (addOrderOf w).Prime ∧ w ∈ stabG s := by
  set o := addOrderOf v with ho
  have ho1 : o ≠ 1 := fun h => hv0 (AddMonoid.addOrderOf_eq_one_iff.mp (ho ▸ h))
  have hopos : 0 < o := addOrderOf_pos v
  set p := o.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime ho1
  have hpd : p ∣ o := Nat.minFac_dvd o
  have hdivpos : 0 < o / p := Nat.div_pos (Nat.minFac_le hopos) hp.pos
  refine ⟨(o / p) • v, ?_, (stabG s).nsmul_mem hv (o / p)⟩
  have hzero : p • ((o / p) • v) = 0 := by
    rw [← mul_nsmul, Nat.div_mul_cancel hpd, ho]
    exact addOrderOf_nsmul_eq_zero v
  have hdvd : addOrderOf ((o / p) • v) ∣ p := addOrderOf_dvd_of_nsmul_eq_zero hzero
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | hself
  · exfalso
    have hw0 : (o / p) • v = 0 := AddMonoid.addOrderOf_eq_one_iff.mp h1
    have : o ∣ o / p := ho ▸ addOrderOf_dvd_of_nsmul_eq_zero hw0
    have hlt : o / p < o := Nat.div_lt_self hopos hp.one_lt
    exact absurd (Nat.le_of_dvd hdivpos this) (not_le.mpr hlt)
  · rw [hself]; exact hp

/-- **Step 1 (completeness), subgroup form.** -/
theorem isShiftSymmetricG_iff_exists {A : Type*} (s : G → A) :
    IsShiftSymmetricG s ↔ ∃ C ∈ primeOrderSubsG G, C ≤ stabG s := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    obtain ⟨w, hwp, hw⟩ := exists_prime_order_of_ne_zero hv0 (mem_stabG.mpr hv)
    refine ⟨AddSubgroup.zmultiples w, ?_, AddSubgroup.zmultiples_le.mpr hw⟩
    rw [mem_primeOrderSubsG, Nat.card_zmultiples]
    exact hwp
  · rintro ⟨C, hC, hsC⟩
    rw [mem_primeOrderSubsG] at hC
    have hCbot : C ≠ ⊥ := by
      intro hbot
      rw [hbot, AddSubgroup.card_bot] at hC
      exact Nat.not_prime_one hC
    obtain ⟨v, hvC, hv0⟩ := AddSubgroup.bot_or_exists_ne_zero C |>.resolve_left hCbot
    exact ⟨v, hv0, mem_stabG.mp (hsC hvC)⟩

end Complete

/-! ### Step 2: fixed sets; Step 3 (IE form) -/

section Fixed

variable {G : Type*} [AddCommGroup G] [Fintype G] {A : Type*} [Fintype A]

variable (A) in
/-- `Fix(H)` over the alphabet `A`, as a finset of configurations. -/
noncomputable def fixA (H : AddSubgroup G) : Finset (G → A) :=
  Finset.univ.filter fun s => H ≤ stabG s

theorem mem_fixA {H : AddSubgroup G} {s : G → A} : s ∈ fixA A H ↔ H ≤ stabG s := by
  simp [fixA]

theorem fixA_bot : fixA A (⊥ : AddSubgroup G) = Finset.univ := by
  ext s
  simp only [mem_fixA, Finset.mem_univ, iff_true]
  exact bot_le

theorem inf'_inter_fixA [DecidableEq A] (X : Finset (G → A)) {t : Finset (AddSubgroup G)}
    (ht : t.Nonempty) :
    t.inf' ht (fun C => X ∩ fixA A C) = X ∩ fixA A (t.sup id) := by
  ext s
  rw [← Finset.singleton_subset_iff, Finset.le_inf'_iff]
  simp only [Finset.singleton_subset_iff, Finset.mem_inter]
  constructor
  · intro h
    obtain ⟨C₀, hC₀⟩ := ht
    refine ⟨(h C₀ hC₀).1, ?_⟩
    rw [mem_fixA]
    apply Finset.sup_le
    intro C hC
    exact mem_fixA.mp (h C hC).2
  · rintro ⟨hX, hfix⟩ C hC
    exact ⟨hX, mem_fixA.mpr (le_trans (Finset.le_sup (f := id) hC) (mem_fixA.mp hfix))⟩

theorem filter_shiftSymmetricG_eq_biUnion [DecidableEq A] (X : Finset (G → A)) :
    X.filter IsShiftSymmetricG
      = (primeOrderSubsG G).biUnion (fun C => X ∩ fixA A C) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_inter, mem_fixA]
  constructor
  · rintro ⟨hX, hs⟩
    obtain ⟨C, hC, hle⟩ := (isShiftSymmetricG_iff_exists s).mp hs
    exact ⟨C, hC, hX, hle⟩
  · rintro ⟨C, hC, hX, hle⟩
    exact ⟨hX, (isShiftSymmetricG_iff_exists s).mpr ⟨C, hC, hle⟩⟩

/-- **The relative inclusion–exclusion formula on `G`.** -/
theorem card_filter_shiftSymmetricG_IE [DecidableEq A] (X : Finset (G → A)) :
    ((X.filter IsShiftSymmetricG).card : ℤ)
      = ∑ t : ((primeOrderSubsG G).powerset.filter (·.Nonempty)),
          (-1 : ℤ) ^ (t.1.card + 1) * ((X ∩ fixA A (t.1.sup id)).card : ℤ) := by
  rw [filter_shiftSymmetricG_eq_biUnion, Finset.inclusion_exclusion_card_biUnion]
  apply Finset.sum_congr rfl
  intro t _
  have hne : t.1.Nonempty := (Finset.mem_filter.mp t.2).2
  rw [Finset.inf'_congr hne rfl (fun C _ => rfl), inf'_inter_fixA X hne]

end Fixed

end ShiftSym.P13.Gen
