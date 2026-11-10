/-
Phase H, group 02 — proofs of the frozen statements of
`Shiftsym/Paper/S02_LatticeLemmas.lean` (paper §3, Lemmas 3.1–3.5 and the
Gaussian-binomial sentence of the §3 preamble).

Every frozen `def <X>Statement : Prop` gets a theorem `<X>_proved`.
The proofs reuse the certified development: `card_fixedBy_div`
(FixedCount), `isShiftSymmetric_iff_prime_order` (Completeness),
`latTorsionEquiv`/`zmodEmbed` (Torsion), `card_orderP_subgroups` (Lines),
`card_submodule_finrank`/`gaussBinom_mul_prod_int` (GaussCount),
`card_univ_sup_of_torsion` (Primary), `ofMod`/`toMod` (Bridge).
-/
import Shiftsym.Paper.S02_LatticeLemmas
import Shiftsym.Lemmas.Bridge

namespace ShiftSym.P02

open ShiftSym

/-! ## The Gaussian binomial: project recursion = paper product formula -/

/-- `∏_{i<r} (x^e − x^i) = (∏_{i<r} x^i) · ∏_{i<r} (x^{e−i} − 1)` for `r ≤ e`. -/
private theorem prod_pow_sub_pow (x : ℚ) {e r : ℕ} (h : r ≤ e) :
    ∏ i : Fin r, (x ^ e - x ^ (i : ℕ))
      = (∏ i ∈ Finset.range r, x ^ i) * ∏ i ∈ Finset.range r, (x ^ (e - i) - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => x ^ e - x ^ i) r, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hie : i ≤ e := le_trans (Finset.mem_range.mp hi).le h
  rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hie]

theorem gaussBinomDef_proved : gaussBinomDefStatement := by
  intro q d r hq
  by_cases hrd : r ≤ d
  · have hq1 : (1 : ℚ) < q := by exact_mod_cast hq
    have hq0 : (q : ℚ) ≠ 0 := by positivity
    have hZ := gaussBinom_mul_prod_int q d r
    have hQ : (gaussBinom q d r : ℚ) * ∏ i : Fin r, ((q : ℚ) ^ r - (q : ℚ) ^ (i : ℕ))
        = ∏ i : Fin r, ((q : ℚ) ^ d - (q : ℚ) ^ (i : ℕ)) := by exact_mod_cast hZ
    rw [prod_pow_sub_pow _ le_rfl, prod_pow_sub_pow _ hrd] at hQ
    -- reflect the denominator product
    have hrefl : ∏ i ∈ Finset.range r, ((q : ℚ) ^ (r - i) - 1)
        = ∏ i ∈ Finset.range r, ((q : ℚ) ^ (i + 1) - 1) := by
      rw [← Finset.prod_range_reflect (fun i => (q : ℚ) ^ (i + 1) - 1) r]
      refine Finset.prod_congr rfl fun i hi => ?_
      have hir : i < r := Finset.mem_range.mp hi
      congr 2
      omega
    rw [hrefl] at hQ
    have hA : ∏ i ∈ Finset.range r, (q : ℚ) ^ i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hq0
    have hB : ∏ i ∈ Finset.range r, ((q : ℚ) ^ (i + 1) - 1) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
      have : (1 : ℚ) < (q : ℚ) ^ (i + 1) := one_lt_pow₀ hq1 (Nat.succ_ne_zero i)
      exact sub_ne_zero.mpr this.ne'
    have hG : (gaussBinom q d r : ℚ)
        = (∏ i ∈ Finset.range r, ((q : ℚ) ^ (d - i) - 1))
          / ∏ i ∈ Finset.range r, ((q : ℚ) ^ (i + 1) - 1) := by
      rw [eq_div_iff hB]
      apply mul_left_cancel₀ hA
      rw [← hQ]
      ring
    rw [hG, gaussProd, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hid : i ≤ d := le_trans (Finset.mem_range.mp hi).le hrd
    rw [← Nat.cast_sub hid, zpow_natCast]
  · push Not at hrd
    rw [gaussBinom_eq_zero_of_lt hrd, gaussProd,
      Finset.prod_eq_zero (Finset.mem_range.mpr hrd)]
    · simp
    · simp

theorem gaussianCount_proved : gaussianCountStatement := by
  intro p d r hp _hd
  rw [← gaussBinomDef_proved p d r hp.two_le]
  by_cases hrd : r ≤ d
  · rw [card_submodule_finrank hp hrd]
  · push Not at hrd
    rw [gaussBinom_eq_zero_of_lt hrd]
    have := Fact.mk hp
    have : IsEmpty {W : Submodule (ZMod p) (Fin d → ZMod p) //
        Module.finrank (ZMod p) W = r} := ⟨fun W => by
      have h1 := Submodule.finrank_le W.1
      rw [Module.finrank_fin_fun, W.2] at h1
      omega⟩
    simp

/-! ## Lemma 3.1 -/

/-- `n ∣ t·a ↔ n / gcd(a, n) ∣ t` (coprime cofactors). -/
private theorem dvd_mul_iff_div_gcd_dvd {n a t : ℕ} (hn : 0 < n) :
    n ∣ t * a ↔ n / Nat.gcd a n ∣ t := by
  have hg : 0 < Nat.gcd a n := Nat.gcd_pos_of_pos_right a hn
  have hcop : Nat.Coprime (n / Nat.gcd a n) (a / Nat.gcd a n) :=
    (Nat.coprime_div_gcd_div_gcd hg).symm
  have hn' : n = n / Nat.gcd a n * Nat.gcd a n :=
    (Nat.div_mul_cancel (Nat.gcd_dvd_right a n)).symm
  have ha' : a = a / Nat.gcd a n * Nat.gcd a n :=
    (Nat.div_mul_cancel (Nat.gcd_dvd_left a n)).symm
  calc n ∣ t * a ↔ n / Nat.gcd a n * Nat.gcd a n
        ∣ t * (a / Nat.gcd a n) * Nat.gcd a n := by
          rw [← hn', Nat.mul_assoc, ← ha']
    _ ↔ n / Nat.gcd a n ∣ t * (a / Nat.gcd a n) := Nat.mul_dvd_mul_iff_right hg
    _ ↔ n / Nat.gcd a n ∣ t := hcop.dvd_mul_right

/-- Coordinatewise: `t • (l : ZMod n) = 0 ↔ n ∣ t·|l|`. -/
private theorem nsmul_intCast_eq_zero_iff {n : ℕ} (t : ℕ) (l : ℤ) :
    t • ((l : ℤ) : ZMod n) = 0 ↔ n ∣ t * l.natAbs := by
  rw [nsmul_eq_mul, show ((t : ZMod n) * ((l : ℤ) : ZMod n)) = (((t : ℤ) * l : ℤ) : ZMod n) by
    push_cast; ring, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd, Int.natAbs_mul,
    Int.natAbs_natCast]

/-- On the lattice: `t • v = 0 ↔ ∀ i, n ∣ t·|l_i|` for any integer lift `l` of `v`. -/
private theorem nsmul_eq_zero_iff_lift {n d : ℕ} (v : Lat n d) (l : Fin d → ℤ)
    (hl : ∀ i, ((l i : ℤ) : ZMod n) = v i) (t : ℕ) :
    t • v = 0 ↔ ∀ i, n ∣ t * (l i).natAbs := by
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  rw [Pi.smul_apply, Pi.zero_apply, ← hl i, nsmul_intCast_eq_zero_iff]

theorem orderLcm_proved : orderLcmStatement := by
  intro n d hn _hd v _hv l hl
  have hn0 : 0 < n := by omega
  rw [Nat.card_zmultiples]
  have key : ∀ t : ℕ, addOrderOf v ∣ t ↔
      (Finset.univ.lcm fun i => n / Int.gcd (l i) (n : ℤ)) ∣ t := by
    intro t
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_eq_zero_iff_lift v l hl, Finset.lcm_dvd_iff]
    simp only [Finset.mem_univ, true_implies]
    refine forall_congr' fun i => ?_
    rw [dvd_mul_iff_div_gcd_dvd hn0]
    rfl
  exact Nat.dvd_antisymm ((key _).mpr dvd_rfl) ((key _).mp dvd_rfl)

theorem orderGcd_proved : orderGcdStatement := by
  intro n d hn _hd v _hv l hl
  have hn0 : 0 < n := by omega
  rw [Nat.card_zmultiples]
  have key : ∀ t : ℕ, addOrderOf v ∣ t ↔ n / gcdAll l n ∣ t := by
    intro t
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_eq_zero_iff_lift v l hl, gcdAll,
      ← dvd_mul_iff_div_gcd_dvd hn0]
    constructor
    · intro h
      have h1 : n ∣ Finset.univ.gcd (fun i => t * (l i).natAbs) :=
        Finset.dvd_gcd_iff.mpr fun i _ => h i
      rwa [Finset.gcd_mul_left, normalize_eq] at h1
    · intro h i
      exact h.trans (Nat.mul_dvd_mul_left t (Finset.gcd_dvd (Finset.mem_univ i)))
  exact Nat.dvd_antisymm ((key _).mpr dvd_rfl) ((key _).mp dvd_rfl)

/-- The configurations fixed by `v` are those fixed by `⟨v⟩`. -/
private theorem setOf_shift_eq_fixedBy {n d σ : ℕ} (v : Lat n d) :
    {s : Config n d (Fin σ) | shift v s = s}
      = fixedBy (Fin σ) (AddSubgroup.zmultiples v) := by
  ext s
  simp only [Set.mem_ofPred_eq, fixedBy]
  constructor
  · intro h x hx
    exact (AddSubgroup.zmultiples_le.mpr (show v ∈ stab s from h)) hx
  · intro h
    exact h v (AddSubgroup.mem_zmultiples v)

theorem orderCount_proved : orderCountStatement := by
  intro n d σ hn hd _hσ v hv l hl
  have : NeZero n := ⟨by omega⟩
  have hfin : Nat.card (Fin σ) = σ := Nat.card_eq_fintype_card.trans (Fintype.card_fin σ)
  refine ⟨?_, ?_, ?_⟩
  · rw [← card_lat (n := n) (d := d)]
    exact AddSubgroup.card_addSubgroup_dvd_card _
  · rw [setOf_shift_eq_fixedBy, card_fixedBy_div, hfin]
  · rw [setOf_shift_eq_fixedBy, card_fixedBy_div, hfin, orderGcd_proved n d hn hd v hv l hl]
    congr 1
    have hn0 : 0 < n := by omega
    set g := gcdAll l n with hgdef
    have hgn : g ∣ n := Nat.gcd_dvd_right _ _
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hn0
    have hng0 : 0 < n / g := Nat.div_pos (Nat.le_of_dvd hn0 hgn) hg0
    apply Nat.div_eq_of_eq_mul_left hng0
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    have h2 : n ^ d' * n = n ^ d' * (g * (n / g)) := by rw [Nat.mul_div_cancel' hgn]
    rw [h2]
    ring

theorem orderLemma_proved : orderLemmaStatement :=
  ⟨orderLcm_proved, orderGcd_proved, orderCount_proved⟩

/-! ## Lemma 3.2 -/

theorem fixCount_proved : fixCountStatement := by
  intro n d σ hn _hd _hσ H
  have : NeZero n := ⟨by omega⟩
  refine ⟨?_, ?_⟩
  · rw [← card_lat (n := n) (d := d)]
    exact AddSubgroup.card_addSubgroup_dvd_card _
  · rw [card_fixedBy_div, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- `s ∈ Fix(H) ↔ H ≤ Stab(s)`. -/
private theorem mem_fixedBy_iff_le_stab {n d : ℕ} {A : Type*} (H : AddSubgroup (Lat n d))
    (s : Config n d A) : s ∈ fixedBy A H ↔ H ≤ stab s :=
  Iff.rfl

theorem fixJoin_proved : fixJoinStatement := by
  intro n d σ _hn _hd _hσ ℓ H
  ext s
  rw [Set.mem_iInter, mem_fixedBy_iff_le_stab, AddSubgroup.closure_le, Set.iUnion_subset_iff]
  exact forall_congr' fun a => (mem_fixedBy_iff_le_stab (H a) s).trans Iff.rfl

theorem fixLemma_proved : fixLemmaStatement :=
  ⟨fixCount_proved, fixJoin_proved⟩

/-! ## Lemma 3.3 -/

theorem torsionEq_proved : torsionEqStatement := by
  intro n d p hn _hd hp hpn
  have : NeZero n := ⟨by omega⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hx i
    have hxi : p • x i = 0 := by
      have := congrFun hx i
      simpa using this
    obtain ⟨y, hy⟩ := zmodEmbed_surjOn_torsion hpn (x i) hxi
    refine ⟨(y.val : ℤ), ?_⟩
    rw [← hy, zmodEmbed_apply, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Nat.cast_mul,
      mul_comm]
  · intro h
    funext i
    obtain ⟨y, hy⟩ := h i
    simp only [Pi.smul_apply, Pi.zero_apply]
    rw [hy, nsmul_eq_mul]
    have h0 : ((p : ZMod n) * ((n / p : ℕ) : ZMod n)) = 0 := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hpn, ZMod.natCast_self]
    calc (p : ZMod n) * ((((n / p : ℕ) : ℤ) * y : ℤ) : ZMod n)
        = ((p : ZMod n) * ((n / p : ℕ) : ZMod n)) * (y : ZMod n) := by
          rw [Int.cast_mul, Int.cast_natCast]; ring
      _ = 0 := by rw [h0, zero_mul]

/-- Part (1) of the isomorphism: the paper's formula `x = (n/p)·y ↦ y mod p`
determines `torsionCoord`. -/
private theorem torsionCoord_of_rep {n d p : ℕ} [NeZero n] (hp : p.Prime) (hpn : p ∣ n)
    (x : Lat n d) (y : Fin d → ℤ)
    (hxy : ∀ i, x i = ((((n / p : ℕ) : ℤ) * y i : ℤ) : ZMod n)) :
    torsionCoord n p d x = fun i => ((y i : ℤ) : ZMod p) := by
  funext i
  unfold torsionCoord
  rw [hxy i]
  set m := n / p with hm
  have hm0 : 0 < m := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hpn) hp.pos
  have hnZ : (n : ℤ) = (m : ℤ) * (p : ℤ) := by
    rw [hm]; exact_mod_cast (Nat.div_mul_cancel hpn).symm
  have hval : (((((m : ℤ) * y i : ℤ) : ZMod n)).val : ℤ) = (m : ℤ) * (y i % (p : ℤ)) := by
    rw [ZMod.val_intCast, hnZ, Int.mul_emod_mul_of_pos _ _ (by exact_mod_cast hm0)]
  have hdiv : ((((((m : ℤ) * y i : ℤ) : ZMod n)).val / m : ℕ) : ℤ) = y i % (p : ℤ) := by
    rw [Int.natCast_div, hval, Int.mul_ediv_cancel_left _ (by exact_mod_cast hm0.ne')]
  rw [← Int.cast_natCast, hdiv, ZMod.intCast_mod]

/-- The certified `latTorsionEquiv` is exactly the paper's map `torsionCoord`. -/
private theorem latTorsionEquiv_eq_torsionCoord {n d p : ℕ} [NeZero n] [NeZero p]
    (hp : p.Prime) (hpn : p ∣ n) (x : latTorsion n d p) :
    latTorsionEquiv hpn x = torsionCoord n p d (x : Lat n d) := by
  set z := latTorsionEquiv hpn x with hz
  have hx : x = (latTorsionEquiv hpn).symm z := by rw [hz, AddEquiv.symm_apply_apply]
  have hcoord : ∀ i, (x : Lat n d) i = ((((n / p : ℕ) : ℤ) * ((z i).val : ℤ) : ℤ) : ZMod n) := by
    intro i
    rw [hx]
    show zmodEmbed hpn (z i) = _
    rw [zmodEmbed_apply, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Nat.cast_mul,
      mul_comm]
  rw [torsionCoord_of_rep hp hpn _ _ hcoord]
  funext i
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem torsionIso_proved : torsionIsoStatement := by
  intro n d p hn _hd hp hpn
  have : NeZero n := ⟨by omega⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  exact ⟨fun x y hxy => torsionCoord_of_rep hp hpn x y hxy,
    latTorsionEquiv hpn, fun x => latTorsionEquiv_eq_torsionCoord hp hpn x⟩

theorem torsionOrder_proved : torsionOrderStatement := by
  intro n d p hn _hd hp hpn
  have : NeZero n := ⟨by omega⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  refine ⟨fun x hx => hx ▸ addOrderOf_nsmul_eq_zero x, fun x hx => ?_⟩
  have hdvd : addOrderOf x ∣ p := addOrderOf_dvd_of_nsmul_eq_zero hx
  have h1 : addOrderOf x = p ↔ x ≠ 0 := by
    constructor
    · intro h h0
      rw [h0, addOrderOf_zero] at h
      exact hp.one_lt.ne h
    · intro hx0
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h
      · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hx0
      · exact h
  rw [h1, ← latTorsionEquiv_eq_torsionCoord hp hpn ⟨x, mem_latTorsion.mpr hx⟩]
  rw [Ne, Ne, AddEquiv.map_eq_zero_iff]
  simp

/-- `𝓛_p` is exactly the set of subgroups of cardinality `p` (cyclicity is
automatic for prime cardinality). -/
private theorem mem_orderPCyc_iff {n d p : ℕ} [NeZero n] (hp : p.Prime)
    (C : AddSubgroup (Lat n d)) : C ∈ orderPCyc n d p ↔ Nat.card C = p := by
  constructor
  · exact fun h => h.2
  · intro hC
    refine ⟨?_, hC⟩
    have hne : C ≠ ⊥ := by
      intro hbot
      rw [hbot, AddSubgroup.card_bot] at hC
      exact hp.one_lt.ne hC
    obtain ⟨⟨w, hw⟩, hw0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hne
    have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
    exact ⟨w, (zmultiples_eq_of_mem_card_prime hp hC hw hw0').symm⟩

/-- `lineOf C` is the Bridge dictionary image `toMod C`, for EVERY subgroup `C`. -/
private theorem lineOf_eq_toMod {n d p : ℕ} [NeZero n] [NeZero p] (hp : p.Prime)
    (hpn : p ∣ n) (C : AddSubgroup (Lat n d)) :
    lineOf n d p C = toMod hpn C := by
  unfold lineOf
  have hset : torsionCoord n p d '' {x : Lat n d | p • x = 0 ∧ x ∈ C}
      = (toMod hpn C : Set (Fin d → ZMod p)) := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxC⟩, rfl⟩
      rw [← latTorsionEquiv_eq_torsionCoord hp hpn ⟨x, mem_latTorsion.mpr hx⟩]
      show _ ∈ ((C.addSubgroupOf (latTorsion n d p)).map
        (latTorsionEquiv hpn).toAddMonoidHom)
      exact ⟨⟨x, hx⟩, hxC, rfl⟩
    · intro hy
      change y ∈ ((C.addSubgroupOf (latTorsion n d p)).map
        (latTorsionEquiv hpn).toAddMonoidHom) at hy
      obtain ⟨⟨x, hx⟩, hxC, rfl⟩ := hy
      exact ⟨x, ⟨hx, hxC⟩, (latTorsionEquiv_eq_torsionCoord hp hpn ⟨x, hx⟩).symm⟩
  rw [hset, Submodule.span_eq]

theorem torsionLines_proved : torsionLinesStatement := by
  intro n d p hn _hd hp hpn
  have : NeZero n := ⟨by omega⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- maps to lines
    intro C hC
    have hcard := (mem_orderPCyc_iff hp C).mp hC
    show Module.finrank (ZMod p) (lineOf n d p C) = 1
    rw [lineOf_eq_toMod hp hpn]
    exact finrank_eq_one_of_card_eq
      (by rw [card_toMod hpn (le_torsion_of_card_prime hcard)]; exact hcard)
  · -- injective
    intro C₁ h₁ C₂ h₂ heq
    have hT₁ := le_torsion_of_card_prime ((mem_orderPCyc_iff hp C₁).mp h₁)
    have hT₂ := le_torsion_of_card_prime ((mem_orderPCyc_iff hp C₂).mp h₂)
    rw [lineOf_eq_toMod hp hpn, lineOf_eq_toMod hp hpn] at heq
    rw [← ofMod_toMod hpn hT₁, ← ofMod_toMod hpn hT₂, heq]
  · -- surjective onto lines
    intro W hW
    refine ⟨ofMod hpn W, (mem_orderPCyc_iff hp _).mpr ?_, ?_⟩
    · rw [card_ofMod, card_submodule_pow, show Module.finrank (ZMod p) W = 1 from hW, pow_one]
    · rw [lineOf_eq_toMod hp hpn, toMod_ofMod]
  · intro C hC
    have hcard := (mem_orderPCyc_iff hp C).mp hC
    refine ⟨fun x hx => le_torsion_of_card_prime hcard hx, fun x hx => ?_⟩
    rw [lineOf_eq_toMod hp hpn, ← latTorsionEquiv_eq_torsionCoord hp hpn ⟨x, mem_latTorsion.mpr hx⟩]
    change x ∈ C ↔ _ ∈ ((C.addSubgroupOf (latTorsion n d p)).map
        (latTorsionEquiv hpn).toAddMonoidHom)
    constructor
    · intro hxC
      exact ⟨⟨x, hx⟩, hxC, rfl⟩
    · rintro ⟨y, hyC, hy⟩
      have : y = ⟨x, hx⟩ := (latTorsionEquiv hpn).injective hy
      rw [this] at hyC
      exact hyC

theorem torsionCount_proved : torsionCountStatement := by
  intro n d p hn _hd hp hpn
  have : NeZero n := ⟨by omega⟩
  have hset : orderPCyc n d p = {C : AddSubgroup (Lat n d) | Nat.card C = p} :=
    Set.ext fun C => mem_orderPCyc_iff hp C
  have hcount : (Nat.card (orderPCyc n d p) : ℚ) = gaussProd p d 1 := by
    rw [hset, ← gaussBinomDef_proved p d 1 hp.two_le]
    exact_mod_cast card_orderP_subgroups hp hpn
  refine ⟨hcount, ?_⟩
  rw [hcount]
  simp [gaussProd]

/-- `ofMod` commutes with arbitrary joins. -/
private theorem ofMod_iSup {n d p : ℕ} [NeZero n] [NeZero p] (hpn : p ∣ n) {ι : Sort*}
    (U : ι → Submodule (ZMod p) (Fin d → ZMod p)) :
    ofMod hpn (⨆ i, U i) = ⨆ i, ofMod hpn (U i) := by
  unfold ofMod
  have h : (⨆ i, U i).toAddSubgroup = ⨆ i, (U i).toAddSubgroup :=
    OrderIso.map_iSup ((AddSubgroup.toZModSubmodule p).symm
      : Submodule (ZMod p) (Fin d → ZMod p) ≃o AddSubgroup _) U
  rw [h, AddSubgroup.map_iSup, AddSubgroup.map_iSup]

theorem torsionJoin_proved : torsionJoinStatement := by
  intro n d p hn _hd hp hpn J hJ
  have : NeZero n := ⟨by omega⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  have : Fact p.Prime := ⟨hp⟩
  have hT : ∀ C ∈ J, C ≤ latTorsion n d p := fun C hC =>
    le_torsion_of_card_prime ((mem_orderPCyc_iff hp C).mp (hJ hC))
  have hcl : AddSubgroup.closure (⋃ C ∈ J, (C : Set (Lat n d))) = ⨆ C ∈ J, C := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨C, hC, hxC⟩ := hx
      exact (le_biSup (fun C => C) hC) hxC
    · refine iSup₂_le fun C hC => ?_
      intro x hxC
      exact AddSubgroup.subset_closure (Set.mem_biUnion hC hxC)
  have hW : ofMod hpn (⨆ C ∈ J, lineOf n d p C) = ⨆ C ∈ J, C := by
    rw [ofMod_iSup]
    refine iSup_congr fun C => ?_
    rw [ofMod_iSup]
    refine iSup_congr fun hC => ?_
    rw [lineOf_eq_toMod hp hpn, ofMod_toMod hpn (hT C hC)]
  rw [hcl, ← hW, card_ofMod, card_submodule_pow]
  rfl

theorem torsionLemma_proved : torsionLemmaStatement :=
  ⟨torsionEq_proved, torsionIso_proved, torsionOrder_proved, torsionLines_proved,
    torsionCount_proved, torsionJoin_proved⟩

/-! ## Lemma 3.4 -/

theorem completeness_proved : completenessStatement := by
  intro n d σ hn _hd _hσ
  have : NeZero n := ⟨by omega⟩
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hs
    obtain ⟨v, hvp, hvn, hvs⟩ := (isShiftSymmetric_iff_prime_order s).mp hs
    refine ⟨addOrderOf v, Nat.mem_primeFactors.mpr ⟨hvp, hvn, NeZero.ne n⟩,
      AddSubgroup.zmultiples v, ⟨⟨v, rfl⟩, Nat.card_zmultiples v⟩, ?_⟩
    intro h hh
    exact (AddSubgroup.zmultiples_le.mpr (show v ∈ stab s from hvs)) hh
  · rintro ⟨p, hp, C, ⟨⟨g, rfl⟩, hcard⟩, hfix⟩
    have hpp := (Nat.mem_primeFactors.mp hp).1
    refine ⟨g, ?_, hfix g (AddSubgroup.mem_zmultiples g)⟩
    intro hg0
    rw [hg0, Nat.card_zmultiples, addOrderOf_zero] at hcard
    exact hpp.one_lt.ne hcard

/-! ## Lemma 3.5 -/

theorem orderPCycDisjoint_proved : orderPCycDisjointStatement := by
  intro n d p q hpq
  rw [Set.disjoint_left]
  intro C h1 h2
  exact hpq (h1.2.symm.trans h2.2)

theorem multiPrimeJoin_proved : multiPrimeJoinStatement := by
  intro n d hn hd Jf hJf
  have : NeZero n := ⟨by omega⟩
  let K : n.primeFactors → AddSubgroup (Lat n d) := fun p =>
    AddSubgroup.closure (⋃ C ∈ Jf p, (C : Set (Lat n d)))
  have hK : ∀ p : n.primeFactors, K p ≤ latTorsion n d p := by
    intro p
    rw [AddSubgroup.closure_le]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    have hpp := (Nat.mem_primeFactors.mp p.2).1
    exact le_torsion_of_card_prime ((mem_orderPCyc_iff hpp C).mp (hJf p p.2 hC)) hxC
  have hcop : Pairwise (Function.onFun Nat.Coprime fun p : n.primeFactors => (p : ℕ)) := by
    intro a b hab
    exact (Nat.coprime_primes (Nat.mem_primeFactors.mp a.2).1
      (Nat.mem_primeFactors.mp b.2).1).mpr fun h => hab (Subtype.ext h)
  have hsup : AddSubgroup.closure (⋃ p ∈ n.primeFactors, ⋃ C ∈ Jf p, (C : Set (Lat n d)))
      = Finset.univ.sup K := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨p, hp, C, hC, hxC⟩ := hx
      refine (Finset.le_sup (f := K) (Finset.mem_univ ⟨p, hp⟩)) ?_
      exact AddSubgroup.subset_closure (Set.mem_biUnion hC hxC)
    · refine Finset.sup_le fun p _ => ?_
      refine AddSubgroup.closure_mono ?_
      intro x hx
      exact Set.mem_biUnion p.2 hx
  rw [hsup, card_univ_sup_of_torsion (fun p : n.primeFactors => (p : ℕ)) K hK hcop,
    ← Finset.prod_coe_sort n.primeFactors]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hpp := (Nat.mem_primeFactors.mp p.2).1
  have hpn := (Nat.mem_primeFactors.mp p.2).2.1
  exact torsionJoin_proved n d p hn hd hpp hpn (Jf p) (hJf p p.2)

/-! ## All of Section 3 -/

theorem section3_proved : section3Statement :=
  ⟨gaussianCount_proved, orderLemma_proved, fixLemma_proved, torsionLemma_proved,
    completeness_proved, multiPrimeJoin_proved⟩

end ShiftSym.P02
