/-
Extension E1, part 1: the RELATIVE enumeration theorem (frozen target
`relativeEnumerationStatement`).

For an arbitrary finite alphabet `A` and an arbitrary finset `X` of
configurations,

  |X ∩ S| = Σ_{∅≠J⊆L} (−1)^{|J|+1} |X ∩ Fix(⟨J⟩)|            (T1a, IE form)
          = Σ_{U} mobiusCoeff U · |X ∩ Fix(socSub U)| + |X|   (T1b, Möbius form)

The IE form is `card_shiftSymmetric_IE` (Assembly.lean) with the family
`C ↦ X ∩ Fix(C)`; the Möbius form is the weight-generic version of the
regrouping chain of Evaluate.lean (steps A–C), proved here once for an
ARBITRARY weight `w : AddSubgroup (Lat n d) → ℤ` (`relative_regroup`):
no factorisation over the primes is needed because the join
`socSub U` is constant on each fiber.  With `w = |X ∩ Fix(·)|` this gives
T1b; the full-shift theorem (Evaluate.lean) is the case `w = σ^{N/|·|}`.
-/
import Shiftsym.StatementE1

open scoped Classical

namespace ShiftSym

open Module

variable {n d : ℕ} {A : Type*} [Fintype A] [NeZero n]

/-! ### Fixed-sets over an arbitrary alphabet -/

theorem mem_fixedByA {H : AddSubgroup (Lat n d)} {s : Config n d A} :
    s ∈ fixedByA A H ↔ H ≤ stab s := by
  simp only [fixedByA, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

theorem fixedByA_bot : fixedByA A (⊥ : AddSubgroup (Lat n d)) = Finset.univ := by
  ext s
  simp only [mem_fixedByA, Finset.mem_univ, iff_true]
  exact bot_le

/-- Intersections of relativised fixed-sets are the relativised fixed-set
of the join. -/
theorem inf'_inter_fixedByA (X : Finset (Config n d A))
    {t : Finset (AddSubgroup (Lat n d))} (ht : t.Nonempty) :
    t.inf' ht (fun C => X ∩ fixedByA A C) = X ∩ fixedByA A (t.sup id) := by
  ext s
  rw [← Finset.singleton_subset_iff, Finset.le_inf'_iff]
  simp only [Finset.singleton_subset_iff, Finset.mem_inter]
  constructor
  · intro h
    obtain ⟨C₀, hC₀⟩ := ht
    refine ⟨(h C₀ hC₀).1, ?_⟩
    rw [mem_fixedByA]
    apply Finset.sup_le
    intro C hC
    exact mem_fixedByA.mp (h C hC).2
  · rintro ⟨hX, hfix⟩ C hC
    exact ⟨hX, mem_fixedByA.mpr
      (le_trans (Finset.le_sup (f := id) hC) (mem_fixedByA.mp hfix))⟩

omit [Fintype A] in
/-- Completeness, subgroup form, over an arbitrary alphabet: a
configuration is shift-symmetric iff some prime-order subgroup lies in its
stabilizer. -/
theorem isShiftSymmetric_iff_exists_primeOrderSub (s : Config n d A) :
    IsShiftSymmetric s ↔ ∃ C ∈ primeOrderSubs n d, C ≤ stab s := by
  constructor
  · intro hs
    obtain ⟨v, hvp, -, hvfix⟩ :=
      (isShiftSymmetric_iff_prime_order s).mp hs
    refine ⟨AddSubgroup.zmultiples v, ?_, ?_⟩
    · rw [mem_primeOrderSubs, Nat.card_zmultiples]
      exact hvp
    · exact AddSubgroup.zmultiples_le.mpr (mem_stab.mpr hvfix)
  · rintro ⟨C, hC, hsC⟩
    rw [mem_primeOrderSubs] at hC
    have hCbot : C ≠ ⊥ := by
      intro hbot
      rw [hbot, AddSubgroup.card_bot] at hC
      exact Nat.not_prime_one hC
    obtain ⟨v, hvC, hv0⟩ :=
      AddSubgroup.bot_or_exists_ne_zero C |>.resolve_left hCbot
    exact ⟨v, hv0, hsC hvC⟩

theorem filter_shiftSymmetric_eq_biUnion (X : Finset (Config n d A)) :
    X.filter IsShiftSymmetric
      = (primeOrderSubs n d).biUnion (fun C => X ∩ fixedByA A C) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_inter,
    mem_fixedByA]
  constructor
  · rintro ⟨hX, hs⟩
    obtain ⟨C, hC, hle⟩ :=
      (isShiftSymmetric_iff_exists_primeOrderSub s).mp hs
    exact ⟨C, hC, hX, hle⟩
  · rintro ⟨C, hC, hX, hle⟩
    exact ⟨hX, (isShiftSymmetric_iff_exists_primeOrderSub s).mpr ⟨C, hC, hle⟩⟩

/-- **T1a — the relative inclusion–exclusion formula**: for any finset
`X` of configurations over any finite alphabet,
`|X ∩ S| = Σ_{∅≠J⊆L} (−1)^{|J|+1} |X ∩ Fix(⟨J⟩)|`. -/
theorem card_filter_shiftSymmetric_IE (X : Finset (Config n d A)) :
    ((X.filter IsShiftSymmetric).card : ℤ)
      = ∑ t : ((primeOrderSubs n d).powerset.filter (·.Nonempty)),
          (-1 : ℤ) ^ (t.1.card + 1)
            * ((X ∩ fixedByA A (t.1.sup id)).card : ℤ) := by
  rw [filter_shiftSymmetric_eq_biUnion, Finset.inclusion_exclusion_card_biUnion]
  apply Finset.sum_congr rfl
  intro t _
  have hne : t.1.Nonempty := (Finset.mem_filter.mp t.2).2
  rw [Finset.inf'_congr hne rfl (fun C _ => rfl), inf'_inter_fixedByA X hne]

/-! ### The weight-generic regrouping chain (steps A–C of Evaluate.lean,
for an arbitrary weight `w`) -/

section Regroup

variable (w : AddSubgroup (Lat n d) → ℤ)

private theorem dvdn {m : ℕ} (p : m.primeFactors) : (p : ℕ) ∣ m :=
  Nat.dvd_of_mem_primeFactors p.2

private theorem sup_id_le_torsion {q : ℕ} (hq : q.Prime)
    {tp : Finset (AddSubgroup (Lat n d))} (h : tp ⊆ linesP n d q) :
    tp.sup id ≤ latTorsion n d q :=
  Finset.sup_le fun _C hC =>
    le_torsion_of_card_prime ((mem_linesP hq).mp (h hC))

private theorem biUnion_filter_card
    {t : Finset (AddSubgroup (Lat n d))} (ht : t ⊆ primeOrderSubs n d) :
    Finset.univ.biUnion
        (fun p : n.primeFactors =>
          t.filter (fun C : AddSubgroup (Lat n d) =>
            Nat.card C = (p : ℕ)))
      = t := by
  ext C
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_filter]
  constructor
  · rintro ⟨p, hCt, -⟩
    exact hCt
  · intro hCt
    have hprime : (Nat.card C).Prime := mem_primeOrderSubs.mp (ht hCt)
    exact ⟨⟨Nat.card C, card_mem_primeFactors hprime⟩, hCt, rfl⟩

/-- Step A: peel the empty set off the IE sum. -/
theorem sum_nonempty_eq_sum_powerset_add :
    (∑ t : ((primeOrderSubs n d).powerset.filter (·.Nonempty)),
        (-1 : ℤ) ^ (t.1.card + 1) * w (t.1.sup id))
      = (∑ t ∈ (primeOrderSubs n d).powerset,
          (-1 : ℤ) ^ (t.card + 1) * w (t.sup id)) + w ⊥ := by
  rw [Finset.sum_coe_sort
    ((primeOrderSubs n d).powerset.filter (·.Nonempty))
    (fun t => (-1 : ℤ) ^ (t.card + 1) * w (t.sup id))]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((primeOrderSubs n d).powerset) (·.Nonempty)
    (fun t => (-1 : ℤ) ^ (t.card + 1) * w (t.sup id))]
  have hnot : (primeOrderSubs n d).powerset.filter (fun t => ¬t.Nonempty)
      = {∅} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_singleton, Finset.not_nonempty_iff_eq_empty]
    exact ⟨fun h => h.2, fun h =>
      ⟨by rw [h]; exact Finset.empty_subset _, h⟩⟩
  rw [hnot, Finset.sum_singleton, Finset.card_empty, Finset.sup_empty]
  ring

/-- Step B: powersets of `L` ≃ tuples of powersets of the `L_p`. -/
theorem powerset_sum_eq_piFinset_w :
    (∑ t ∈ (primeOrderSubs n d).powerset,
      (-1 : ℤ) ^ (t.card + 1) * w (t.sup id))
    = ∑ g ∈ Fintype.piFinset
        (fun p : n.primeFactors => (linesP n d (p : ℕ)).powerset),
        (-1 : ℤ) ^ ((∑ p : n.primeFactors, (g p).card) + 1)
          * w (Finset.univ.sup
                (fun p : n.primeFactors => (g p).sup id)) := by
  refine Finset.sum_nbij'
    (fun t : Finset (AddSubgroup (Lat n d)) =>
      fun p : n.primeFactors =>
        t.filter (fun C : AddSubgroup (Lat n d) => Nat.card C = (p : ℕ)))
    (fun g => Finset.univ.biUnion (fun p : n.primeFactors => g p))
    ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro t _
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_powerset]
    intro C hC
    exact (mem_linesP (Nat.prime_of_mem_primeFactors p.2)).mpr
      (Finset.mem_filter.mp hC).2
  · -- backward membership
    intro g hg
    rw [Fintype.mem_piFinset] at hg
    rw [Finset.mem_powerset]
    intro C hC
    obtain ⟨p, -, hCp⟩ := Finset.mem_biUnion.mp hC
    exact Finset.filter_subset _ _ (Finset.mem_powerset.mp (hg p) hCp)
  · -- left inverse
    intro t ht
    exact biUnion_filter_card (Finset.mem_powerset.mp ht)
  · -- right inverse
    intro g hg
    rw [Fintype.mem_piFinset] at hg
    funext p
    ext C
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨q, hCq⟩, hcard⟩
      have hq := (mem_linesP (Nat.prime_of_mem_primeFactors q.2)).mp
        (Finset.mem_powerset.mp (hg q) hCq)
      have hqp : q = p := Subtype.ext (by rw [← hq, hcard])
      exact hqp ▸ hCq
    · intro hCp
      have hp := (mem_linesP (Nat.prime_of_mem_primeFactors p.2)).mp
        (Finset.mem_powerset.mp (hg p) hCp)
      exact ⟨⟨p, hCp⟩, hp⟩
  · -- values agree
    intro t ht
    have hbi := biUnion_filter_card (n := n) (d := d)
      (Finset.mem_powerset.mp ht)
    have hdisj : ∀ p ∈ (Finset.univ : Finset n.primeFactors),
        ∀ q ∈ (Finset.univ : Finset n.primeFactors), p ≠ q →
        Disjoint
          (t.filter (fun C : AddSubgroup (Lat n d) =>
            Nat.card C = (p : ℕ)))
          (t.filter (fun C : AddSubgroup (Lat n d) =>
            Nat.card C = (q : ℕ))) := by
      intro p _ q _ hpq
      rw [Finset.disjoint_left]
      intro C hCp hCq
      exact hpq (Subtype.ext (by
        rw [← (Finset.mem_filter.mp hCp).2,
          ← (Finset.mem_filter.mp hCq).2]))
    have hcard : t.card
        = ∑ p : n.primeFactors,
            (t.filter (fun C : AddSubgroup (Lat n d) =>
              Nat.card C = (p : ℕ))).card := by
      conv_lhs => rw [← hbi]
      exact Finset.card_biUnion hdisj
    have hsup : t.sup id
        = Finset.univ.sup (fun p : n.primeFactors =>
            (t.filter (fun C : AddSubgroup (Lat n d) =>
              Nat.card C = (p : ℕ))).sup id) := by
      conv_lhs => rw [← hbi]
      exact Finset.sup_biUnion _ _
    rw [hcard, hsup]

/-- Step C: fiber over the tuple of per-prime joins; the join is constant
on each fiber (= `socSub U`), so the weight factors out and the signed
count of the fiber is `−∏_p spanSum (U p) = mobiusCoeff U`. -/
theorem piFinset_sum_eq_tuple_sum_w :
    (∑ g ∈ Fintype.piFinset
        (fun p : n.primeFactors => (linesP n d (p : ℕ)).powerset),
        (-1 : ℤ) ^ ((∑ p : n.primeFactors, (g p).card) + 1)
          * w (Finset.univ.sup
                (fun p : n.primeFactors => (g p).sup id)))
    = ∑ U : ModTuple n d, mobiusCoeff U * w (socSub U) := by
  have hmaps : ∀ g ∈ Fintype.piFinset
      (fun p : n.primeFactors => (linesP n d (p : ℕ)).powerset),
      (fun p : n.primeFactors => toMod (dvdn p) ((g p).sup id))
        ∈ (Finset.univ : Finset (ModTuple n d)) :=
    fun g _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun g => (-1 : ℤ) ^ ((∑ p : n.primeFactors, (g p).card) + 1)
      * w (Finset.univ.sup (fun p : n.primeFactors => (g p).sup id)))]
  refine Finset.sum_congr rfl fun U _ => ?_
  -- the fiber over `U` is the tuple of per-prime sup-fibers
  have hfib : (Fintype.piFinset (fun p : n.primeFactors =>
        (linesP n d (p : ℕ)).powerset)).filter
      (fun g => (fun p : n.primeFactors =>
        toMod (dvdn p) ((g p).sup id)) = U)
      = Fintype.piFinset (fun p : n.primeFactors =>
          ((linesP n d (p : ℕ)).powerset).filter
            (fun tp => tp.sup id = ofMod (dvdn p) (U p))) := by
    ext g
    simp only [Finset.mem_filter, Fintype.mem_piFinset, funext_iff]
    constructor
    · rintro ⟨hmem, hcond⟩ p
      refine ⟨hmem p, ?_⟩
      rw [← hcond p, ofMod_toMod (dvdn p) (sup_id_le_torsion
        (Nat.prime_of_mem_primeFactors p.2)
        (Finset.mem_powerset.mp (hmem p)))]
    · intro hall
      refine ⟨fun p => (hall p).1, fun p => ?_⟩
      rw [(hall p).2, toMod_ofMod]
  rw [hfib]
  -- on the fiber, the join is constant, equal to `socSub U`
  have hjoin : ∀ g ∈ Fintype.piFinset (fun p : n.primeFactors =>
      ((linesP n d (p : ℕ)).powerset).filter
        (fun tp => tp.sup id = ofMod (dvdn p) (U p))),
      Finset.univ.sup (fun p : n.primeFactors => (g p).sup id) = socSub U := by
    intro g hg
    rw [Fintype.mem_piFinset] at hg
    have hsup : (fun p : n.primeFactors => (g p).sup id)
        = fun p : n.primeFactors => ofMod (dvdn p) (U p) :=
      funext fun p => (Finset.mem_filter.mp (hg p)).2
    rw [hsup]
    rfl
  calc ∑ g ∈ (Fintype.piFinset (fun p : n.primeFactors =>
        ((linesP n d (p : ℕ)).powerset).filter
          (fun tp => tp.sup id = ofMod (dvdn p) (U p)))),
        (-1 : ℤ) ^ ((∑ p : n.primeFactors, (g p).card) + 1)
          * w (Finset.univ.sup
                (fun p : n.primeFactors => (g p).sup id))
      = ∑ g ∈ (Fintype.piFinset (fun p : n.primeFactors =>
          ((linesP n d (p : ℕ)).powerset).filter
            (fun tp => tp.sup id = ofMod (dvdn p) (U p)))),
          -(∏ p : n.primeFactors, (-1 : ℤ) ^ (g p).card) * w (socSub U) := by
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [hjoin g hg, pow_succ, Finset.prod_pow_eq_pow_sum]
        ring
    _ = -(∑ g ∈ (Fintype.piFinset (fun p : n.primeFactors =>
          ((linesP n d (p : ℕ)).powerset).filter
            (fun tp => tp.sup id = ofMod (dvdn p) (U p)))),
          ∏ p : n.primeFactors, (-1 : ℤ) ^ (g p).card) * w (socSub U) := by
        rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    _ = -(∏ p : n.primeFactors,
          ∑ tp ∈ ((linesP n d (p : ℕ)).powerset).filter
            (fun tp => tp.sup id = ofMod (dvdn p) (U p)),
            (-1 : ℤ) ^ tp.card) * w (socSub U) := by
        rw [Finset.prod_univ_sum]
    _ = mobiusCoeff U * w (socSub U) := by
        unfold mobiusCoeff
        congr 2
        exact Finset.prod_congr rfl fun p _ =>
          spanSum_transport (dvdn p) (U p)

/-- **The weight-generic regrouping lemma** (FOLLOW_UPS.md A5): for ANY
weight `w` on subgroups, the alternating sum over nonempty sets of
prime-order subgroups regroups into the Möbius sum over socle subgroups.
Theorem 4.3 (`w = σ^{N/|·|}`), Theorem 5.1 (`w = |Fix_k(·)|`) and the
relative theorem (`w = |X ∩ Fix(·)|`) are instances. -/
theorem relative_regroup :
    (∑ t : ((primeOrderSubs n d).powerset.filter (·.Nonempty)),
        (-1 : ℤ) ^ (t.1.card + 1) * w (t.1.sup id))
      = ∑ U : ModTuple n d, mobiusCoeff U * w (socSub U) + w ⊥ := by
  rw [sum_nonempty_eq_sum_powerset_add, powerset_sum_eq_piFinset_w,
    piFinset_sum_eq_tuple_sum_w]

end Regroup

/-! ### T1b and the explicit Möbius coefficient -/

/-- **T1b — the relative enumeration theorem, machine-checked**
(frozen target `relativeEnumerationStatement`): for every finite alphabet
`A` and every finset `X` of configurations of `Z_n^d`,
`|X ∩ S| = Σ_U mobiusCoeff U · |X ∩ Fix(socSub U)| + |X|`. -/
theorem relativeEnumeration_proved (X : Finset (Config n d A)) :
    relativeEnumerationStatement n d A X := by
  unfold relativeEnumerationStatement
  rw [card_filter_shiftSymmetric_IE]
  have h := relative_regroup (n := n) (d := d)
    (fun H => ((X ∩ fixedByA A H).card : ℤ))
  rw [h, fixedByA_bot, Finset.inter_univ]

omit [NeZero n] in
/-- The Möbius coefficient in closed form:
`mobiusCoeff U = (−1)^{1 + Σ_p rk U_p} ∏_p p^{C(rk U_p, 2)}` — i.e.
`−μ(0, socSub U)` with Hall's evaluation of the Möbius function of the
subgroup lattice of an abelian group at an elementary abelian subgroup. -/
theorem mobiusCoeff_eq (U : ModTuple n d) :
    mobiusCoeff U
      = (-1 : ℤ) ^ (1 + ∑ p : n.primeFactors, finrank (ZMod (p : ℕ)) (U p))
        * ∏ p : n.primeFactors,
            ((p : ℕ) : ℤ) ^ ((finrank (ZMod (p : ℕ)) (U p)).choose 2) := by
  unfold mobiusCoeff
  have h : ∀ p : n.primeFactors, spanSum (U p)
      = (-1 : ℤ) ^ (finrank (ZMod (p : ℕ)) (U p))
        * ((p : ℕ) : ℤ) ^ ((finrank (ZMod (p : ℕ)) (U p)).choose 2) := by
    intro p
    rw [spanSum_eq_mobius, ZMod.card]
  rw [Finset.prod_congr rfl (fun p _ => h p), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, pow_add, pow_one]
  ring

/-- The value of the regrouping at the full shift reproduces the certified
divisor formula's input: `card_shiftSymmetric_IE` is `relative_regroup`
with `w H = σ^{N/|H|}` (consistency remark; `enumeration_proved` stands). -/
theorem card_shiftSymmetric_eq_tuple_sum (σ : ℕ) :
    ((Finset.univ.filter
        (fun s : Config n d (Fin σ) => IsShiftSymmetric s)).card : ℤ)
      = ∑ U : ModTuple n d,
          mobiusCoeff U * (σ : ℤ) ^ (n ^ d / Nat.card (socSub U))
        + (σ : ℤ) ^ (n ^ d) := by
  rw [card_shiftSymmetric_IE]
  have h := relative_regroup (n := n) (d := d)
    (fun H : AddSubgroup (Lat n d) => (σ : ℤ) ^ (n ^ d / Nat.card H))
  rw [h, AddSubgroup.card_bot, Nat.div_one]

end ShiftSym
