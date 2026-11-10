/-
Phase D2, part 2: the subgroup ↔ submodule dictionary at a prime `p ∣ n`.

`ofMod` embeds the submodule lattice of `F_p^d` into the subgroup lattice
of `(Z/nZ)^d` (image: the subgroups inside the `p`-torsion); `toMod` is
its inverse there. The dictionary preserves order, joins, `⊥`, and
cardinality, matches order-`p` subgroups with lines, and transports the
machine-checked signed spanning-set count `spanSum` to the subgroup side.
-/
import Shiftsym.Lemmas.Primary
import Shiftsym.Lemmas.MobiusSum
import Shiftsym.Lemmas.Assembly

open scoped Classical

namespace ShiftSym

open Module

/-- A prime in a `Fact` is nonzero (harmless if mathlib also provides
this: `NeZero` is a `Prop` class). -/
instance (priority := 90) {q : ℕ} [hq : Fact q.Prime] : NeZero q :=
  ⟨hq.out.pos.ne'⟩

instance {q k : ℕ} [NeZero q] :
    Finite (Submodule (ZMod q) (Fin k → ZMod q)) :=
  Finite.of_injective
    (fun U => (U : Set (Fin k → ZMod q))) SetLike.coe_injective

noncomputable instance {q k : ℕ} [NeZero q] :
    Fintype (Submodule (ZMod q) (Fin k → ZMod q)) :=
  Fintype.ofFinite _

variable {n d p : ℕ}

section Dict

variable [NeZero n] [NeZero p]

/-- From submodules of `F_p^d` to additive subgroups of `(Z/nZ)^d`. -/
noncomputable def ofMod (hpn : p ∣ n)
    (U : Submodule (ZMod p) (Fin d → ZMod p)) : AddSubgroup (Lat n d) :=
  (U.toAddSubgroup.map
      (latTorsionEquiv hpn).symm.toAddMonoidHom).map
    (latTorsion n d p).subtype

/-- From additive subgroups of `(Z/nZ)^d` to submodules of `F_p^d`
(restrict to the `p`-torsion, then transport). -/
noncomputable def toMod (hpn : p ∣ n)
    (H : AddSubgroup (Lat n d)) : Submodule (ZMod p) (Fin d → ZMod p) :=
  AddSubgroup.toZModSubmodule p
    ((H.addSubgroupOf (latTorsion n d p)).map
      (latTorsionEquiv hpn).toAddMonoidHom)

private theorem equiv_comp_symm (hpn : p ∣ n) :
    (latTorsionEquiv (n := n) (d := d) hpn).toAddMonoidHom.comp
        (latTorsionEquiv hpn).symm.toAddMonoidHom
      = AddMonoidHom.id _ := by
  ext x
  simp

private theorem symm_comp_equiv (hpn : p ∣ n) :
    (latTorsionEquiv (n := n) (d := d) hpn).symm.toAddMonoidHom.comp
        (latTorsionEquiv hpn).toAddMonoidHom
      = AddMonoidHom.id _ := by
  ext x
  simp

private theorem addSubgroupOf_map_subtype {T : AddSubgroup (Lat n d)}
    (X : AddSubgroup T) : (X.map T.subtype).addSubgroupOf T = X :=
  AddSubgroup.comap_map_eq_self_of_injective T.subtype_injective X

theorem toMod_ofMod (hpn : p ∣ n)
    (U : Submodule (ZMod p) (Fin d → ZMod p)) :
    toMod hpn (ofMod hpn U) = U := by
  unfold toMod ofMod
  rw [addSubgroupOf_map_subtype, AddSubgroup.map_map, equiv_comp_symm,
    AddSubgroup.map_id, Submodule.toAddSubgroup_toZModSubmodule]

theorem ofMod_toMod (hpn : p ∣ n) {H : AddSubgroup (Lat n d)}
    (hH : H ≤ latTorsion n d p) : ofMod hpn (toMod hpn H) = H := by
  unfold toMod ofMod
  rw [AddSubgroup.toZModSubmodule_toAddSubgroup, AddSubgroup.map_map,
    AddSubgroup.map_map, AddMonoidHom.comp_assoc, symm_comp_equiv,
    AddMonoidHom.comp_id, AddSubgroup.addSubgroupOf_map_subtype]
  exact inf_eq_left.mpr hH

theorem ofMod_le_torsion (hpn : p ∣ n)
    (U : Submodule (ZMod p) (Fin d → ZMod p)) :
    ofMod hpn U ≤ latTorsion n d p :=
  AddSubgroup.map_subtype_le _

theorem toMod_mono (hpn : p ∣ n) :
    Monotone (toMod (n := n) (d := d) hpn) := by
  intro H K hHK
  exact (AddSubgroup.toZModSubmodule p).monotone
    (AddSubgroup.map_mono (AddSubgroup.comap_mono hHK))

theorem ofMod_mono (hpn : p ∣ n) :
    Monotone (ofMod (n := n) (d := d) hpn) := by
  intro U V hUV
  refine AddSubgroup.map_mono (AddSubgroup.map_mono ?_)
  exact (AddSubgroup.toZModSubmodule p).symm.monotone hUV

theorem ofMod_injective (hpn : p ∣ n) :
    Function.Injective (ofMod (n := n) (d := d) hpn) := fun U V h => by
  rw [← toMod_ofMod hpn U, h, toMod_ofMod]

theorem ofMod_bot (hpn : p ∣ n) : ofMod (n := n) (d := d) hpn ⊥ = ⊥ := by
  unfold ofMod
  have h : (⊥ : Submodule (ZMod p) (Fin d → ZMod p)).toAddSubgroup = ⊥ :=
    (AddSubgroup.toZModSubmodule p).symm.map_bot
  rw [h, AddSubgroup.map_bot, AddSubgroup.map_bot]

theorem ofMod_sup (hpn : p ∣ n)
    (U V : Submodule (ZMod p) (Fin d → ZMod p)) :
    ofMod hpn (U ⊔ V) = ofMod hpn U ⊔ ofMod hpn V := by
  unfold ofMod
  have h : (U ⊔ V).toAddSubgroup = U.toAddSubgroup ⊔ V.toAddSubgroup :=
    map_sup ((AddSubgroup.toZModSubmodule p).symm
      : Submodule (ZMod p) (Fin d → ZMod p) ≃o AddSubgroup _) U V
  rw [h, AddSubgroup.map_sup, AddSubgroup.map_sup]

theorem ofMod_finset_sup {α : Type*} (hpn : p ∣ n) (J : Finset α)
    (f : α → Submodule (ZMod p) (Fin d → ZMod p)) :
    ofMod hpn (J.sup f) = J.sup (fun a => ofMod hpn (f a)) := by
  induction J using Finset.cons_induction with
  | empty => simpa using ofMod_bot hpn
  | cons a s ha ih => rw [Finset.sup_cons, Finset.sup_cons, ofMod_sup, ih]

theorem toMod_finset_sup (hpn : p ∣ n)
    {t : Finset (AddSubgroup (Lat n d))}
    (ht : ∀ C ∈ t, C ≤ latTorsion n d p) :
    toMod hpn (t.sup id) = t.sup (fun C => toMod hpn C) := by
  apply ofMod_injective hpn
  rw [ofMod_toMod hpn (Finset.sup_le (f := id) ht), ofMod_finset_sup]
  exact (Finset.sup_congr rfl fun C hC =>
    (ofMod_toMod hpn (ht C hC))).symm

theorem card_ofMod (hpn : p ∣ n)
    (U : Submodule (ZMod p) (Fin d → ZMod p)) :
    Nat.card (ofMod hpn U) = Nat.card U := by
  unfold ofMod
  rw [← Nat.card_congr (AddSubgroup.equivMapOfInjective _ _
    ((latTorsion n d p).subtype_injective)).toEquiv]
  rw [← Nat.card_congr (AddSubgroup.equivMapOfInjective _ _
    ((latTorsionEquiv (n := n) (d := d) hpn).symm.injective)).toEquiv]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)

theorem card_toMod (hpn : p ∣ n) {H : AddSubgroup (Lat n d)}
    (hH : H ≤ latTorsion n d p) :
    Nat.card (toMod hpn H) = Nat.card H := by
  conv_rhs => rw [← ofMod_toMod hpn hH]
  rw [card_ofMod]

end Dict

/-! ### The prime-field side: ranks, cardinalities, and the transport of
the signed spanning-set count -/

/-- Order-`p` subgroups of the translation group, as a finset. -/
noncomputable def linesP (n d p : ℕ) [NeZero n] :
    Finset (AddSubgroup (Lat n d)) :=
  (primeOrderSubs n d).filter fun C => Nat.card C = p

theorem mem_linesP [NeZero n] {C : AddSubgroup (Lat n d)}
    (hp : p.Prime) : C ∈ linesP n d p ↔ Nat.card C = p := by
  simp only [linesP, Finset.mem_filter, mem_primeOrderSubs]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hp, h⟩⟩

section PrimeField

variable [NeZero n] [Fact p.Prime]

theorem card_submodule_pow (U : Submodule (ZMod p) (Fin d → ZMod p)) :
    Nat.card U = p ^ finrank (ZMod p) U := by
  haveI := Fintype.ofFinite U
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

theorem finrank_eq_one_of_card_eq
    {U : Submodule (ZMod p) (Fin d → ZMod p)} (hU : Nat.card U = p) :
    finrank (ZMod p) U = 1 := by
  have h := card_submodule_pow U
  rw [hU] at h
  nth_rewrite 1 [← pow_one p] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm

theorem finrank_pi_d : finrank (ZMod p) (Fin d → ZMod p) = d := by
  rw [Module.finrank_pi, Fintype.card_fin]

/-- `spanSum_rank_classified`, specialized to `F_p^d` with the `p` and
`d` spelled out. -/
theorem spanSum_rank_classified_pd {r : ℕ} (hr : r ≤ d) :
    ∑ U ∈ Finset.univ.filter
        (fun U : Submodule (ZMod p) (Fin d → ZMod p) =>
          finrank (ZMod p) U = r),
      spanSum U
      = (-1 : ℤ) ^ r * (p : ℤ) ^ (r.choose 2) * gaussBinom p d r := by
  have hd : finrank (ZMod p) (Fin d → ZMod p) = d := finrank_pi_d
  have h := spanSum_rank_classified (K := ZMod p) (V := Fin d → ZMod p)
    (r := r) (by rw [hd]; exact hr)
  rw [ZMod.card, hd] at h
  exact h

/-- **Transport of the signed spanning-set count** to the subgroup side:
summing `(−1)^{|t|}` over the sets `t` of order-`p` subgroups of
`(Z/nZ)^d` whose join is `ofMod U` gives `spanSum U`. -/
theorem spanSum_transport (hpn : p ∣ n)
    (U : Submodule (ZMod p) (Fin d → ZMod p)) :
    ∑ t ∈ (linesP n d p).powerset.filter
        (fun t => t.sup id = ofMod hpn U),
      (-1 : ℤ) ^ t.card
      = spanSum U := by
  have hp : p.Prime := Fact.out
  rw [spanSum, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun t => t.image (toMod hpn))
    (fun J => J.image (ofMod hpn)) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro t ht
    obtain ⟨htsub, htsup⟩ := Finset.mem_filter.mp ht
    rw [Finset.mem_powerset] at htsub
    have hmemT : ∀ C ∈ t, C ≤ latTorsion n d p := fun C hC =>
      le_torsion_of_card_prime ((mem_linesP hp).mp (htsub hC))
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · -- image lands in linesF U
      intro L hL
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hL
      rw [mem_linesF]
      constructor
      · exact finrank_eq_one_of_card_eq
          (by rw [card_toMod hpn (hmemT C hC)]
              exact (mem_linesP hp).mp (htsub hC))
      · have h1 : C ≤ ofMod hpn U := htsup ▸ Finset.le_sup (f := id) hC
        have h2 := toMod_mono hpn h1
        rwa [toMod_ofMod] at h2
    · -- the join of the image is U
      rw [Finset.sup_image]
      have hcomp : t.sup (id ∘ toMod hpn)
          = t.sup (fun C => toMod hpn C) := rfl
      rw [hcomp, ← toMod_finset_sup hpn hmemT, htsup, toMod_ofMod]
  · -- backward membership
    intro J hJ
    obtain ⟨hJsub, hJsup⟩ := Finset.mem_filter.mp hJ
    rw [Finset.mem_powerset] at hJsub
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro C hC
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hC
      have hline := mem_linesF.mp (hJsub hL)
      rw [mem_linesP hp, card_ofMod, card_submodule_pow, hline.1, pow_one]
    · rw [Finset.sup_image]
      have hcomp : J.sup (id ∘ ofMod hpn)
          = J.sup (fun L => ofMod hpn (id L)) := rfl
      rw [hcomp, ← ofMod_finset_sup hpn J id, hJsup]
  · -- left inverse
    intro t ht
    obtain ⟨htsub, _⟩ := Finset.mem_filter.mp ht
    rw [Finset.mem_powerset] at htsub
    rw [Finset.image_image]
    refine (Finset.image_congr ?_).trans Finset.image_id
    intro C hC
    exact ofMod_toMod hpn
      (le_torsion_of_card_prime ((mem_linesP hp).mp (htsub hC)))
  · -- right inverse
    intro J _
    rw [Finset.image_image]
    refine (Finset.image_congr ?_).trans Finset.image_id
    intro L _
    exact toMod_ofMod hpn L
  · -- values agree
    intro t ht
    obtain ⟨htsub, _⟩ := Finset.mem_filter.mp ht
    rw [Finset.mem_powerset] at htsub
    congr 1
    refine (Finset.card_image_of_injOn ?_).symm
    intro C₁ h₁ C₂ h₂ heq
    have hT₁ := le_torsion_of_card_prime ((mem_linesP hp).mp (htsub h₁))
    have hT₂ := le_torsion_of_card_prime ((mem_linesP hp).mp (htsub h₂))
    rw [← ofMod_toMod hpn hT₁, ← ofMod_toMod hpn hT₂, heq]

end PrimeField

end ShiftSym
