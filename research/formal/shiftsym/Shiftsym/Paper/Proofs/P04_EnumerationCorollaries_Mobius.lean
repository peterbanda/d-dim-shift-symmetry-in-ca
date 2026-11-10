/-
Phase H, group 04 — proofs, part 4: Möbius functions of subgroup lattices
(§4.3 of the paper).

* generic facts on the Möbius function of a finite poset (`cmu`, built
  exactly as the frozen `subgroupMu` / `addSubgroupMu` / `subgroupMuG`);
* the Möbius count `#{x : st x = ⊥} = ∑_b μ(⊥,b) #{x : b ≤ st x}` and
  CG Lemma 7(i) for every finite group, and its instance `G = A`;
* multiplicativity of `μ` across the primary decomposition (two-variable
  form);
* Hall's evaluation of `μ(0,K)` for `K ≤ A_p`, and the count of elementary
  abelian subgroups of rank `r`.
-/
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Lattice

open Finset

namespace ShiftSym.P04

open ShiftSym

/-! ### The Möbius function of a finite poset -/

/-- Möbius function of a finite partial order, built exactly as the frozen
`subgroupMu`, `addSubgroupMu`, `subgroupMuG` (so that those are `rfl`-instances). -/
noncomputable def cmu {α : Type*} [PartialOrder α] [Finite α] (a b : α) : ℤ :=
  letI : Fintype α := Fintype.ofFinite _
  letI : DecidableLE α := Classical.decRel _
  letI : DecidableLT α := Classical.decRel _
  letI : DecidableEq α := Classical.decEq _
  letI : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  IncidenceAlgebra.mu ℤ a b

theorem subgroupMu_eq_cmu (n d : ℕ) [NeZero n] (H K : AddSubgroup (Lat n d)) :
    subgroupMu n d H K = cmu H K := rfl

theorem addSubgroupMu_eq_cmu (B : Type*) [AddGroup B] [Finite B] (H K : AddSubgroup B) :
    addSubgroupMu B H K = cmu H K := rfl

theorem subgroupMuG_eq_cmu (G : Type*) [Group G] [Finite G] (H K : Subgroup G) :
    subgroupMuG G H K = cmu H K := rfl

theorem mu_inst_congr {α : Type*} [Preorder α] (l1 l2 : LocallyFiniteOrder α)
    (e1 e2 : DecidableEq α) (a b : α) :
    @IncidenceAlgebra.mu ℤ α _ _ _ l1 e1 a b = @IncidenceAlgebra.mu ℤ α _ _ _ l2 e2 a b := by
  obtain rfl := Subsingleton.elim l1 l2
  obtain rfl := Subsingleton.elim e1 e2
  rfl

section Generic

open scoped Classical

variable {α : Type*} [PartialOrder α] [Fintype α]

theorem cmu_eq_mu [LocallyFiniteOrder α] [DecidableEq α] (a b : α) :
    cmu a b = IncidenceAlgebra.mu ℤ a b := by
  unfold cmu
  exact mu_inst_congr _ _ _ _ a b

theorem cmu_self (a : α) : cmu a a = 1 := by
  letI : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  rw [cmu_eq_mu]
  exact IncidenceAlgebra.mu_self a

theorem cmu_of_not_le {a b : α} (h : ¬ a ≤ b) : cmu a b = 0 := by
  letI : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  rw [cmu_eq_mu]
  exact IncidenceAlgebra.apply_eq_zero_of_not_le h _

/-- `∑_{a ≤ x ≤ b} μ(a,x) = δ(a,b)`. -/
theorem sum_cmu (a b : α) :
    ∑ x ∈ univ.filter (fun x => a ≤ x ∧ x ≤ b), cmu a x = if a = b then 1 else 0 := by
  letI : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  have h := IncidenceAlgebra.sum_Icc_mu_right (𝕜 := ℤ) a b
  have hI : Finset.Icc a b = univ.filter (fun x => a ≤ x ∧ x ≤ b) := by
    ext x; simp [Finset.mem_Icc]
  rw [hI] at h
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact cmu_eq_mu a x

/-- Uniqueness of the Möbius function on a down-closed set `D`: any `g`
satisfying `∑_{a ≤ x ≤ b} g x = δ(a,b)` for all `b ∈ D` agrees with `μ(a,·)`
on `D ∩ [a, ∞)`. -/
theorem eq_cmu_of_sum (a : α) (D : α → Prop) (hD : ∀ b x, D b → x ≤ b → D x)
    (g : α → ℤ)
    (hg : ∀ b, D b → ∑ x ∈ univ.filter (fun x => a ≤ x ∧ x ≤ b), g x = if a = b then 1 else 0) :
    ∀ b, D b → a ≤ b → g b = cmu a b := by
  intro b
  induction b using WellFoundedLT.induction with
  | _ b ih =>
    intro hb hab
    have h1 := hg b hb
    have h2 := sum_cmu a b
    have hsplit : ∀ f : α → ℤ, ∑ x ∈ univ.filter (fun x => a ≤ x ∧ x ≤ b), f x
        = f b + ∑ x ∈ univ.filter (fun x => a ≤ x ∧ x < b), f x := by
      intro f
      have hmem : b ∈ univ.filter (fun x => a ≤ x ∧ x ≤ b) := by simp [hab]
      rw [← Finset.add_sum_erase _ _ hmem]
      congr 1
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext x
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hne, h1, h2⟩; exact ⟨h1, lt_of_le_of_ne h2 hne⟩
      · rintro ⟨h1, h2⟩; exact ⟨ne_of_lt h2, h1, le_of_lt h2⟩
    rw [hsplit] at h1 h2
    have hrest : ∑ x ∈ univ.filter (fun x => a ≤ x ∧ x < b), g x
        = ∑ x ∈ univ.filter (fun x => a ≤ x ∧ x < b), cmu a x := by
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain ⟨hax, hxb⟩ := (Finset.mem_filter.mp hx).2
      exact ih x hxb (hD b x hb (le_of_lt hxb)) hax
    rw [hrest] at h1
    linarith

/-- **The Möbius count**: `#{x : st x = ⊥} = ∑_b μ(⊥,b) · #{x : b ≤ st x}`. -/
theorem natCard_eq_sum_cmu [OrderBot α] {X : Type*} [Finite X] (st : X → α) :
    (Nat.card {x // st x = ⊥} : ℤ)
      = ∑ b, cmu ⊥ b * (Nat.card {x // b ≤ st x} : ℤ) := by
  haveI : Fintype X := Fintype.ofFinite X
  have hcard : ∀ P : X → Prop, (Nat.card {x // P x} : ℤ) = ∑ x, if P x then 1 else 0 := by
    intro P
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    push_cast
    rw [Finset.sum_boole]
  rw [hcard]
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := sum_cmu (⊥ : α) (st x)
  rw [Finset.sum_filter] at h
  simp only [bot_le, true_and] at h
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [h]
  simp only [eq_comm]

end Generic

/-! ### CG Lemma 7(i) for an arbitrary finite group -/

section Group

variable {G : Type*} [Group G] {β : Type*}

/-- The stabilizer of `x : G → β` under right translation `(x·g)(h) = x(hg)`. -/
def rstab (x : G → β) : Subgroup G where
  carrier := {g | ∀ h, x (h * g) = x h}
  one_mem' := fun h => by simp
  mul_mem' := by
    intro a b ha hb h
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [← mul_assoc, hb (h * a), ha h]
  inv_mem' := by
    intro a ha h
    simp only [Set.mem_setOf_eq] at ha ⊢
    have := ha (h * a⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

theorem mem_rstab {x : G → β} {g : G} : g ∈ rstab x ↔ ∀ h, x (h * g) = x h := Iff.rfl

/-- Configurations fixed by `K` ≃ labelings of the coset space `G ⧸ K`. -/
def rfixEquiv (K : Subgroup G) : {x : G → β // K ≤ rstab x} ≃ (G ⧸ K → β) where
  toFun x := Quotient.lift x.1 (by
    intro a b hab
    have hmem : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
    have h1 := x.2 hmem a
    rw [mul_inv_cancel_left] at h1
    exact h1.symm)
  invFun y := ⟨fun g => y (QuotientGroup.mk g), by
    intro k hk h
    show y (QuotientGroup.mk (h * k)) = y (QuotientGroup.mk h)
    congr 1
    rw [QuotientGroup.eq, mul_inv_rev, inv_mul_cancel_right]
    exact K.inv_mem hk⟩
  left_inv x := Subtype.ext (funext fun _ => rfl)
  right_inv y := funext fun q => Quotient.inductionOn q fun _ => rfl

theorem natCard_rfix [Finite G] (K : Subgroup G) (q : ℕ) :
    Nat.card {x : G → Fin q // K ≤ rstab x} = q ^ (Nat.card G / Nat.card K) := by
  rw [Nat.card_congr (rfixEquiv K), Nat.card_fun, Nat.card_eq_fintype_card (α := Fin q),
    Fintype.card_fin]
  congr 1
  have h := K.card_mul_index
  have hpos : 0 < Nat.card K := Nat.card_pos
  rw [← h, Nat.mul_div_cancel_left _ hpos]
  rfl

theorem acG_eq (q : ℕ) : acG G q = Nat.card {x : G → Fin q // rstab x = ⊥} := by
  unfold acG
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Subgroup.eq_bot_iff_forall]
  rfl

end Group

/-- **CG Lemma 7(i)** (for every finite group and every `q`). -/
theorem cgLemma7i (G : Type) [Group G] [Finite G] (q : ℕ) :
    (acG G q : ℤ) = ∑ K ∈ allSubgroupsG G,
      subgroupMuG G ⊥ K * (q : ℤ) ^ (Nat.card G / Nat.card K) := by
  letI : Fintype (Subgroup G) := Fintype.ofFinite _
  rw [acG_eq, natCard_eq_sum_cmu (rstab (G := G) (β := Fin q))]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [natCard_rfix, subgroupMuG_eq_cmu]
  push_cast
  rfl

/-- **The Möbius count on `A = (ZMod n)^d`** (CG Lemma 7(i) for `G = A`, any `σ`). -/
theorem acount_mobius (n d σ : ℕ) [NeZero n] :
    (acount n d σ : ℤ) = ∑ K ∈ allSubgroups n d,
      subgroupMu n d ⊥ K * (σ : ℤ) ^ (n ^ d / Nat.card K) := by
  unfold acount
  rw [natCard_eq_sum_cmu (stab (n := n) (d := d) (A := Fin σ))]
  refine Finset.sum_congr rfl fun K _ => ?_
  have h : Nat.card {s : Config n d (Fin σ) // K ≤ stab s} = σ ^ (n ^ d / Nat.card K) := by
    have := card_fixedBy_div (A := Fin σ) K
    rw [Nat.card_eq_fintype_card (α := Fin σ), Fintype.card_fin] at this
    rw [← this]
    rfl
  rw [h, subgroupMu_eq_cmu]
  push_cast
  rfl

/-! ### Multiplicativity of `μ` across the primary decomposition -/

section Mult

open scoped Classical

variable {n d : ℕ} [NeZero n]

/-- `Fintype` structure on the primary lattices `L(A_p)` (a local instance only). -/
noncomputable def fintypeAddSubgroupPrimComp (p : ℕ) :
    Fintype (AddSubgroup ↥(primComp n d p)) := Fintype.ofFinite _

attribute [local instance] fintypeAddSubgroupPrimComp

/-- `X ↦ X ∩ A_p`, viewed as a subgroup of `A_p`. -/
def proj (X : AddSubgroup (Lat n d)) (p : ℕ) : AddSubgroup ↥(primComp n d p) :=
  (X ⊓ primComp n d p).addSubgroupOf (primComp n d p)

theorem map_proj (X : AddSubgroup (Lat n d)) (p : ℕ) :
    (proj X p).map (primComp n d p).subtype = X ⊓ primComp n d p := by
  rw [proj, AddSubgroup.addSubgroupOf_map_subtype, inf_assoc, inf_idem]

/-- The join of the images of a family `Y_p ≤ A_p`. -/
noncomputable def emb (Y : ∀ p : n.primeFactors, AddSubgroup ↥(primComp n d (p : ℕ))) :
    AddSubgroup (Lat n d) :=
  ⨆ p : n.primeFactors, (Y p).map (primComp n d (p : ℕ)).subtype

theorem emb_proj (hn : 2 ≤ n) (X : AddSubgroup (Lat n d)) :
    emb (fun p : n.primeFactors => proj X (p : ℕ)) = X := by
  unfold emb
  simp_rw [map_proj]
  exact (split_eq' hn X).symm

theorem emb_inf (hn : 2 ≤ n) (Y : ∀ p : n.primeFactors, AddSubgroup ↥(primComp n d (p : ℕ)))
    (p : n.primeFactors) :
    emb Y ⊓ primComp n d (p : ℕ) = (Y p).map (primComp n d (p : ℕ)).subtype := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxK, hxp⟩ := AddSubgroup.mem_inf.mp hx
    have hle : emb Y ≤ ((Y p).map (primComp n d (p : ℕ)).subtype).comap
        (smulHom (n := n) (d := d) (crtCoeff n p)) := by
      refine iSup_le fun q => ?_
      intro y hy
      have hyq : y ∈ primComp n d (q : ℕ) := AddSubgroup.map_subtype_le _ hy
      rw [AddSubgroup.mem_comap, smulHom_apply]
      by_cases hqp : q = p
      · subst hqp
        rw [crt_smul_self hn q.2 hyq]
        exact hy
      · rw [crt_smul_eq_zero hn q.2 p.2 (fun h => hqp (Subtype.ext h).symm) hyq]
        exact AddSubgroup.zero_mem _
    have := hle hxK
    rw [AddSubgroup.mem_comap, smulHom_apply, crt_smul_self hn p.2 hxp] at this
    exact this
  · exact le_inf (le_iSup (fun q : n.primeFactors => (Y q).map (primComp n d (q : ℕ)).subtype) p)
      (AddSubgroup.map_subtype_le _)

theorem proj_emb (hn : 2 ≤ n) (Y : ∀ p : n.primeFactors, AddSubgroup ↥(primComp n d (p : ℕ)))
    (p : n.primeFactors) : proj (emb Y) (p : ℕ) = Y p := by
  rw [proj, emb_inf hn Y p]
  exact AddSubgroup.comap_map_eq_self_of_injective (primComp n d (p : ℕ)).subtype_injective _

theorem proj_le_iff (hn : 2 ≤ n) (X X' : AddSubgroup (Lat n d)) :
    X ≤ X' ↔ ∀ p : n.primeFactors, proj X (p : ℕ) ≤ proj X' (p : ℕ) := by
  constructor
  · intro h p
    exact AddSubgroup.comap_mono (inf_le_inf_right _ h)
  · intro h
    rw [le_iff_inf_le hn]
    intro p hp
    rw [← map_proj, ← map_proj]
    exact AddSubgroup.map_mono (h ⟨p, hp⟩)

theorem proj_eq_iff (hn : 2 ≤ n) (X X' : AddSubgroup (Lat n d)) :
    X = X' ↔ ∀ p : n.primeFactors, proj X (p : ℕ) = proj X' (p : ℕ) := by
  constructor
  · rintro rfl p; rfl
  · intro h
    exact le_antisymm ((proj_le_iff hn X X').mpr fun p => (h p).le)
      ((proj_le_iff hn X' X).mpr fun p => (h p).ge)

theorem sum_interval_prod (hn : 2 ≤ n) (H b : AddSubgroup (Lat n d)) :
    ∑ X ∈ univ.filter (fun X => H ≤ X ∧ X ≤ b),
        ∏ p : n.primeFactors, cmu (proj H (p : ℕ)) (proj X (p : ℕ))
      = ∏ p : n.primeFactors, ∑ y ∈ univ.filter
          (fun y => proj H (p : ℕ) ≤ y ∧ y ≤ proj b (p : ℕ)), cmu (proj H (p : ℕ)) y := by
  rw [Finset.prod_univ_sum]
  refine Finset.sum_nbij' (fun X => fun p : n.primeFactors => proj X (p : ℕ)) emb
    ?_ ?_ ?_ ?_ ?_
  · intro X hX
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hX).2
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (proj_le_iff hn H X).mp h1 p, (proj_le_iff hn X b).mp h2 p⟩
  · intro Y hY
    rw [Fintype.mem_piFinset] at hY
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (proj_le_iff hn H (emb Y)).mpr fun p => ?_,
      (proj_le_iff hn (emb Y) b).mpr fun p => ?_⟩
    · rw [proj_emb hn Y p]; exact (Finset.mem_filter.mp (hY p)).2.1
    · rw [proj_emb hn Y p]; exact (Finset.mem_filter.mp (hY p)).2.2
  · intro X _
    exact emb_proj hn X
  · intro Y _
    funext p
    exact proj_emb hn Y p
  · intro X _
    rfl

/-- **Multiplicativity**: `μ_{L(A)}(H,K) = ∏_p μ_{L(A_p)}(H ∩ A_p, K ∩ A_p)`. -/
theorem cmu_mult (hn : 2 ≤ n) (H K : AddSubgroup (Lat n d)) :
    cmu H K = ∏ p : n.primeFactors, cmu (proj H (p : ℕ)) (proj K (p : ℕ)) := by
  by_cases hHK : H ≤ K
  · symm
    refine eq_cmu_of_sum H (fun _ => True) (fun _ _ _ _ => trivial)
      (fun X => ∏ p : n.primeFactors, cmu (proj H (p : ℕ)) (proj X (p : ℕ))) ?_ K trivial hHK
    intro b _
    by_cases hHb : H ≤ b
    · rw [sum_interval_prod hn H b]
      simp_rw [sum_cmu]
      rw [Finset.prod_boole]
      simp only [Finset.mem_univ, true_implies]
      congr 1
      exact propext (proj_eq_iff hn H b).symm
    · have hempty : univ.filter (fun x => H ≤ x ∧ x ≤ b) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro x - ⟨h1, h2⟩
        exact hHb (h1.trans h2)
      rw [hempty, Finset.sum_empty, if_neg (fun h : H = b => hHb (h ▸ le_rfl))]
  · rw [cmu_of_not_le hHK]
    obtain ⟨p, hp⟩ : ∃ p : n.primeFactors, ¬ proj H (p : ℕ) ≤ proj K (p : ℕ) := by
      by_contra h
      push Not at h
      exact hHK ((proj_le_iff hn H K).mpr h)
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ p) (cmu_of_not_le hp)

end Mult

/-! ### Hall's evaluation on `A_p` and the elementary abelian count -/

section Hall

open scoped Classical

open Module

variable {n d p : ℕ} [NeZero n] [NeZero p] [Fact p.Prime]

theorem isElemAbelian_iff (K : AddSubgroup (Lat n d)) :
    IsElemAbelian p K ↔ K ≤ latTorsion n d p := Iff.rfl

theorem latTorsion_le_primComp : latTorsion n d p ≤ primComp n d p := by
  intro x hx
  unfold primComp
  rw [AddCommGroup.mem_primaryComponent]
  exact ⟨1, by rw [pow_one]; exact hx⟩

theorem inf_torsion_eq_bot_iff {K : AddSubgroup (Lat n d)} (hK : K ≤ primComp n d p) :
    K ⊓ latTorsion n d p = ⊥ ↔ K = ⊥ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨x, hxK, hx0⟩ := (AddSubgroup.bot_or_exists_ne_zero K).resolve_left hne
    have hxp := hK hxK
    unfold primComp at hxp
    rw [AddCommGroup.mem_primaryComponent] at hxp
    have hk : p ^ (Nat.find hxp) • x = 0 := Nat.find_spec hxp
    have hk0 : Nat.find hxp ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_smul] at hk
      exact hx0 hk
    have hmin : ¬ p ^ (Nat.find hxp - 1) • x = 0 := Nat.find_min hxp (by omega)
    have hy : p ^ (Nat.find hxp - 1) • x ∈ K ⊓ latTorsion n d p := by
      refine AddSubgroup.mem_inf.mpr ⟨AddSubgroup.nsmul_mem _ hxK _, ?_⟩
      rw [mem_latTorsion, smul_smul, ← pow_succ', Nat.sub_add_cancel (by omega)]
      exact hk
    rw [h] at hy
    exact hmin ((AddSubgroup.mem_bot).mp hy)
  · rintro rfl
    exact bot_inf_eq _

/-- The candidate value of `μ(0,X)` on subgroups of `A_p`. -/
noncomputable def hallW (hpn : p ∣ n) (X : AddSubgroup (Lat n d)) : ℤ :=
  if X ≤ latTorsion n d p then
    (-1 : ℤ) ^ (finrank (ZMod p) (toMod hpn X)) * (p : ℤ) ^ ((finrank (ZMod p) (toMod hpn X)).choose 2)
  else 0

theorem toMod_eq_bot_iff (hpn : p ∣ n) {W : AddSubgroup (Lat n d)} (hW : W ≤ latTorsion n d p) :
    toMod hpn W = ⊥ ↔ W = ⊥ := by
  constructor
  · intro h
    rw [← ofMod_toMod hpn hW, h, ofMod_bot]
  · rintro rfl
    rw [← ofMod_bot (n := n) (d := d) hpn, toMod_ofMod]

theorem sum_hallW (hpn : p ∣ n) (K : AddSubgroup (Lat n d)) (hK : K ≤ primComp n d p) :
    ∑ X ∈ univ.filter (fun X => ⊥ ≤ X ∧ X ≤ K), hallW hpn X = if ⊥ = K then 1 else 0 := by
  have step1 : ∑ X ∈ univ.filter (fun X => ⊥ ≤ X ∧ X ≤ K), hallW hpn X
      = ∑ X ∈ univ.filter (fun X => X ≤ K ⊓ latTorsion n d p),
          (-1 : ℤ) ^ (finrank (ZMod p) (toMod hpn X))
            * (p : ℤ) ^ ((finrank (ZMod p) (toMod hpn X)).choose 2) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun X _ => ?_
    unfold hallW
    by_cases h1 : X ≤ K <;> by_cases h2 : X ≤ latTorsion n d p <;> simp [h1, h2, le_inf_iff]
  have step2 : ∑ X ∈ univ.filter (fun X => X ≤ K ⊓ latTorsion n d p),
        (-1 : ℤ) ^ (finrank (ZMod p) (toMod hpn X))
          * (p : ℤ) ^ ((finrank (ZMod p) (toMod hpn X)).choose 2)
      = ∑ U ∈ univ.filter (· ≤ toMod hpn (K ⊓ latTorsion n d p)),
          (-1 : ℤ) ^ (finrank (ZMod p) U)
            * (Fintype.card (ZMod p) : ℤ) ^ ((finrank (ZMod p) U).choose 2) := by
    refine Finset.sum_nbij' (toMod hpn) (ofMod hpn) ?_ ?_ ?_ ?_ ?_
    · intro X hX
      rw [Finset.mem_filter] at hX ⊢
      exact ⟨Finset.mem_univ _, toMod_mono hpn hX.2⟩
    · intro U hU
      rw [Finset.mem_filter] at hU ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have := ofMod_mono hpn hU.2
      rwa [ofMod_toMod hpn inf_le_right] at this
    · intro X hX
      rw [Finset.mem_filter] at hX
      exact ofMod_toMod hpn (hX.2.trans inf_le_right)
    · intro U _
      exact toMod_ofMod hpn U
    · intro X _
      rw [ZMod.card]
  rw [step1, step2, alt_sum_le]
  have e : finrank (ZMod p) (toMod hpn (K ⊓ latTorsion n d p)) = 0 ↔ ⊥ = K := by
    rw [Submodule.finrank_eq_zero, toMod_eq_bot_iff hpn inf_le_right,
      inf_torsion_eq_bot_iff hK, eq_comm]
  exact if_congr e rfl rfl

/-- **Hall**: for `K ≤ A_p`, `μ(0,K) = hallW K`. -/
theorem cmu_bot_eq_hallW (hpn : p ∣ n) (K : AddSubgroup (Lat n d)) (hK : K ≤ primComp n d p) :
    cmu ⊥ K = hallW hpn K :=
  (eq_cmu_of_sum ⊥ (· ≤ primComp n d p) (fun _ _ hb hxb => hxb.trans hb) (hallW hpn)
    (fun b hb => sum_hallW hpn b hb) K hK bot_le).symm

theorem finrank_toMod_eq (hpn : p ∣ n) {K : AddSubgroup (Lat n d)} (hKT : K ≤ latTorsion n d p)
    {r : ℕ} (hr : Nat.card K = p ^ r) : finrank (ZMod p) (toMod hpn K) = r := by
  have h1 := card_toMod hpn hKT
  rw [card_submodule_pow, hr] at h1
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h1

theorem hall (hpn : p ∣ n) (K : AddSubgroup (Lat n d)) (hK : K ≤ primComp n d p) :
    (¬ IsElemAbelian p K → subgroupMu n d ⊥ K = 0) ∧
      (IsElemAbelian p K → ∀ r : ℕ, Nat.card K = p ^ r →
        subgroupMu n d ⊥ K = (-1 : ℤ) ^ r * (p : ℤ) ^ (r.choose 2)) := by
  rw [subgroupMu_eq_cmu, cmu_bot_eq_hallW hpn K hK]
  constructor
  · intro h
    unfold hallW
    rw [if_neg ((isElemAbelian_iff K).not.mp h)]
  · intro h r hr
    unfold hallW
    rw [if_pos ((isElemAbelian_iff K).mp h), finrank_toMod_eq hpn ((isElemAbelian_iff K).mp h) hr]

theorem elemAbelian_count (hpn : p ∣ n) {r : ℕ} (hr : r ≤ d) :
    (@Finset.filter _ (fun K => K ≤ primComp n d p ∧ IsElemAbelian p K ∧ Nat.card K = p ^ r)
        (Classical.decPred _) (allSubgroups n d)).card = gaussBinom p d r := by
  rw [Finset.filter_congr_decidable]
  have hset : (allSubgroups n d).filter
      (fun K => K ≤ primComp n d p ∧ IsElemAbelian p K ∧ Nat.card K = p ^ r)
      = Finset.univ.filter (fun K => K ≤ latTorsion n d p ∧ Nat.card K = p ^ r) := by
    ext K
    simp only [Finset.mem_filter, allSubgroups, Finset.mem_univ, true_and, isElemAbelian_iff]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.trans latTorsion_le_primComp, h1, h2⟩
  rw [hset, ← card_submodule_finrank (Fact.out : p.Prime) hr, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  refine Finset.card_nbij' (toMod hpn) (ofMod hpn) ?_ ?_ ?_ ?_
  · intro K hK
    rw [Finset.mem_coe, Finset.mem_filter] at hK
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, finrank_toMod_eq hpn hK.2.1 hK.2.2⟩
  · intro U hU
    rw [Finset.mem_coe, Finset.mem_filter] at hU
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ofMod_le_torsion hpn U, ?_⟩
    rw [card_ofMod, card_submodule_pow, hU.2]
  · intro K hK
    rw [Finset.mem_coe, Finset.mem_filter] at hK
    exact ofMod_toMod hpn hK.2.1
  · intro U _
    exact toMod_ofMod hpn U

end Hall

end ShiftSym.P04
