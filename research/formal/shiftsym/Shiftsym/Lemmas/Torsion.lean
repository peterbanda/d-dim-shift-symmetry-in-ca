/-
Torsion ↔ lines, part (a) (paper Lemma 3.3 core; Phase B item 3):
for `p ∣ n`, the `p`-torsion of `(Z/nZ)^d` is additively equivalent to
`(Z/pZ)^d`; hence it has `p^d` elements, and for prime `p` the elements
of order exactly `p` number `p^d - 1`.

The ZMod-level embedding is elementary: `y ↦ (y.val * (n/p) : ZMod n)`.
-/
import Shiftsym.Definitions

namespace ShiftSym

variable {n d p : ℕ}

/-- `p`-torsion of `ZMod n` as an additive subgroup. -/
def zmodTorsion (n p : ℕ) : AddSubgroup (ZMod n) where
  carrier := {x | p • x = 0}
  zero_mem' := smul_zero p
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [smul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [smul_neg, ha, neg_zero]

@[simp] theorem mem_zmodTorsion {x : ZMod n} :
    x ∈ zmodTorsion n p ↔ p • x = 0 := Iff.rfl

/-- `p`-torsion of the translation group `(Z/nZ)^d`. -/
def latTorsion (n d p : ℕ) : AddSubgroup (Lat n d) where
  carrier := {v | p • v = 0}
  zero_mem' := smul_zero p
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [smul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [smul_neg, ha, neg_zero]

@[simp] theorem mem_latTorsion {v : Lat n d} :
    v ∈ latTorsion n d p ↔ p • v = 0 := Iff.rfl

theorem mem_latTorsion_iff_addOrderOf_dvd {v : Lat n d} :
    v ∈ latTorsion n d p ↔ addOrderOf v ∣ p :=
  (addOrderOf_dvd_iff_nsmul_eq_zero).symm

section ZModLevel

variable [NeZero n] [NeZero p]

/-- The key cast identity: multiples of `n/p` only depend on the
multiplier mod `p`. -/
private theorem cast_mod_mul (hp : p ∣ n) (a : ℕ) :
    (((a % p) * (n / p) : ℕ) : ZMod n) = ((a * (n / p) : ℕ) : ZMod n) := by
  conv_rhs => rw [← Nat.div_add_mod a p]
  push_cast
  rw [add_mul]
  have h0 : ((p : ZMod n) * (a / p : ℕ)) * ((n / p : ℕ) : ZMod n) = 0 := by
    rw [mul_comm (p : ZMod n) _, mul_assoc, ← Nat.cast_mul,
      Nat.mul_div_cancel' hp, ZMod.natCast_self, mul_zero]
  rw [mul_assoc] at h0
  rw [mul_assoc, h0, zero_add]

/-- The embedding `ZMod p →+ ZMod n`, `y ↦ y.val * (n/p)`. -/
def zmodEmbed (hp : p ∣ n) : ZMod p →+ ZMod n :=
  AddMonoidHom.mk' (fun y => ((y.val * (n / p) : ℕ) : ZMod n)) (by
    intro y z
    rw [ZMod.val_add, cast_mod_mul hp, Nat.add_mul, Nat.cast_add])

theorem zmodEmbed_apply (hp : p ∣ n) (y : ZMod p) :
    zmodEmbed hp y = ((y.val * (n / p) : ℕ) : ZMod n) := rfl

theorem zmodEmbed_mem_torsion (hp : p ∣ n) (y : ZMod p) :
    zmodEmbed hp y ∈ zmodTorsion n p := by
  rw [mem_zmodTorsion, zmodEmbed_apply hp, nsmul_eq_mul, ← Nat.cast_mul,
    ← Nat.mul_assoc, Nat.mul_comm p y.val, Nat.mul_assoc,
    Nat.mul_div_cancel' hp, Nat.cast_mul, ZMod.natCast_self, mul_zero]

theorem zmodEmbed_injective (hp : p ∣ n) :
    Function.Injective (zmodEmbed hp) := by
  intro y z hyz
  have hnp : 0 < n / p :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hp)
      (Nat.pos_of_ne_zero (NeZero.ne p))
  -- reduce to: p ∣ y.val - z.val style argument via injectivity on vals
  have key : ∀ w : ZMod p, zmodEmbed hp w = 0 → w = 0 := by
    intro w hw
    rw [zmodEmbed_apply hp, ZMod.natCast_eq_zero_iff] at hw
    have hw' : p * (n / p) ∣ w.val * (n / p) := by
      rw [Nat.mul_div_cancel' hp]; exact hw
    have hpw : p ∣ w.val := (Nat.mul_dvd_mul_iff_right hnp).mp hw'
    exact (ZMod.val_eq_zero w).mp (Nat.eq_zero_of_dvd_of_lt hpw w.val_lt)
  have : zmodEmbed hp (y - z) = 0 := by
    rw [map_sub, hyz, sub_self]
  have hz := key _ this
  exact sub_eq_zero.mp hz

theorem zmodEmbed_surjOn_torsion (hp : p ∣ n) (x : ZMod n)
    (hx : x ∈ zmodTorsion n p) :
    ∃ y : ZMod p, zmodEmbed hp y = x := by
  have hnp : 0 < n / p :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hp)
      (Nat.pos_of_ne_zero (NeZero.ne p))
  rw [mem_zmodTorsion, nsmul_eq_mul] at hx
  have hx' : ((p * x.val : ℕ) : ZMod n) = 0 := by
    rw [Nat.cast_mul, ← hx]
    congr 1
    exact ZMod.natCast_rightInverse x
  rw [ZMod.natCast_eq_zero_iff] at hx'
  have hx2 : p * (n / p) ∣ p * x.val := by
    rw [Nat.mul_div_cancel' hp]; exact hx'
  have hx3 : (n / p) ∣ x.val :=
    (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (NeZero.ne p))).mp hx2
  obtain ⟨m, hm⟩ := hx3
  have hmlt : m < p := by
    have hvlt : x.val < n := x.val_lt
    by_contra hle
    push_neg at hle
    have : n / p * p ≤ n / p * m := Nat.mul_le_mul_left _ hle
    rw [Nat.div_mul_cancel hp] at this
    exact absurd (hm ▸ this) (not_le.mpr hvlt)
  refine ⟨(m : ZMod p), ?_⟩
  rw [zmodEmbed_apply hp, ZMod.val_cast_of_lt hmlt]
  rw [Nat.mul_comm m (n / p), ← hm]
  exact ZMod.natCast_rightInverse x

/-- The `p`-torsion of `ZMod n` is additively `ZMod p` (for `p ∣ n`). -/
noncomputable def zmodTorsionEquiv (hp : p ∣ n) :
    ZMod p ≃+ zmodTorsion n p :=
  AddEquiv.ofBijective
    ((zmodEmbed hp).codRestrict (zmodTorsion n p) (zmodEmbed_mem_torsion hp))
    ⟨fun y z h => zmodEmbed_injective hp (congrArg Subtype.val h),
     fun x => by
      obtain ⟨y, hy⟩ := zmodEmbed_surjOn_torsion hp x.1 x.2
      exact ⟨y, Subtype.ext hy⟩⟩

end ZModLevel

section LatLevel

variable [NeZero n] [NeZero p]

/-- The lattice torsion is the product of the coordinate torsions. -/
def latTorsionPi :
    latTorsion n d p ≃+ (Fin d → zmodTorsion n p) where
  toFun v i := ⟨v.1 i, by
    have hv : p • (v : Lat n d) = 0 := v.2
    have h := congrFun hv i
    simp only [Pi.smul_apply, Pi.zero_apply] at h
    exact h⟩
  invFun f := ⟨fun i => (f i).1, by
    have : p • (fun i => ((f i : ZMod n))) = (0 : Lat n d) := by
      funext i
      simp only [Pi.smul_apply, Pi.zero_apply]
      exact (f i).2
    exact this⟩
  left_inv v := Subtype.ext rfl
  right_inv f := funext fun i => Subtype.ext rfl
  map_add' v w := funext fun i => Subtype.ext rfl

/-- **Torsion ≅ F_p^d** (paper Lemma 3.3 core): for `p ∣ n`, the
`p`-torsion of `(Z/nZ)^d` is additively `(Z/pZ)^d`. -/
noncomputable def latTorsionEquiv (hp : p ∣ n) :
    latTorsion n d p ≃+ (Fin d → ZMod p) :=
  latTorsionPi.trans
    (AddEquiv.piCongrRight fun _ => (zmodTorsionEquiv hp).symm)

/-- The `p`-torsion has exactly `p^d` elements. -/
theorem card_latTorsion (hp : p ∣ n) :
    Nat.card (latTorsion n d p) = p ^ d := by
  rw [Nat.card_congr (latTorsionEquiv (d := d) hp).toEquiv, Nat.card_fun]
  simp

/-- **Order-p elements number `p^d - 1`** (paper Lemma 3.3, second half):
for prime `p ∣ n`, the elements of order exactly `p` in `(Z/nZ)^d` are the
nonzero `p`-torsion elements. -/
theorem card_addOrderOf_eq_prime (hpp : p.Prime) (hp : p ∣ n) :
    Nat.card {v : Lat n d // addOrderOf v = p} = p ^ d - 1 := by
  -- order-p elements ≃ nonzero torsion elements
  have e1 : {v : Lat n d // addOrderOf v = p} ≃
      {w : latTorsion n d p // w ≠ 0} :=
    { toFun := fun v => ⟨⟨v.1, mem_latTorsion_iff_addOrderOf_dvd.mpr
        (dvd_of_eq v.2)⟩, by
        intro h
        have hv0 : v.1 = 0 := congrArg Subtype.val h
        have := v.2
        rw [hv0, addOrderOf_zero] at this
        exact hpp.one_lt.ne this⟩
      invFun := fun w => ⟨w.1.1, by
        have hdvd : addOrderOf w.1.1 ∣ p :=
          mem_latTorsion_iff_addOrderOf_dvd.mp w.1.2
        rcases (Nat.Prime.eq_one_or_self_of_dvd hpp _ hdvd) with h1 | h
        · exfalso
          have : w.1.1 = 0 := AddMonoid.addOrderOf_eq_one_iff.mp h1
          exact w.2 (Subtype.ext this)
        · exact h⟩
      left_inv := fun v => Subtype.ext rfl
      right_inv := fun w => Subtype.ext (Subtype.ext rfl) }
  -- transport along the torsion equivalence
  have e2 : {w : latTorsion n d p // w ≠ 0} ≃
      {y : Fin d → ZMod p // y ≠ 0} := by
    have hz : latTorsionEquiv (d := d) hp 0 = 0 := map_zero _
    refine Equiv.subtypeEquiv (latTorsionEquiv hp).toEquiv (fun w => ?_)
    constructor
    · intro hw h0
      exact hw ((latTorsionEquiv (d := d) hp).injective
        ((show latTorsionEquiv (d := d) hp w = 0 from h0).trans hz.symm))
    · intro hw h0
      exact hw (show latTorsionEquiv (d := d) hp w = 0 from by
        rw [h0]; exact hz)
  rw [Nat.card_congr (e1.trans e2), Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  simp [ZMod.card]

end LatLevel

end ShiftSym
