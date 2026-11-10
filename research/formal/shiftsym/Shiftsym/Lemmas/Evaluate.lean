/-
Phase D2, part 3: evaluating the certified inclusion–exclusion sum into
the divisor-indexed closed form — the machine-checked enumeration
theorem `enumeration_proved : enumerationStatement n d σ` (claim C001).

Chain (all sums over ℤ):
  |S|  =  Σ_{t ⊆ P} F(t) + σ^{n^d}                    (empty-set peel)
       =  Σ_{g ∈ Π_p 2^{P_p}} F(⊔ g)                  (powerset ≃ pi)
       =  Σ_{U : tuples of submodules} −(Π_p spanSum (U p)) σ^{n^d/hOf U}
                                                       (fiber over sups)
       =  Σ_{h ∣ rad(n)^d} coeffOf(h) σ^{n^d/h}        (fiber over hOf)
where `P_p` = order-p subgroups, `hOf U = Π_p p^{rank (U p)}`.
-/
import Shiftsym.Lemmas.Bridge

open scoped Classical

namespace ShiftSym

open Module Function

/-- Primality of the members of `n.primeFactors`, as an instance (this
is what lets `spanSum` and the `F_p`-machinery elaborate under binders
over `p : n.primeFactors`). -/
instance {m : ℕ} (p : m.primeFactors) : Fact ((p : ℕ)).Prime :=
  ⟨Nat.prime_of_mem_primeFactors p.2⟩

variable {n d : ℕ}

/-- A tuple of submodules of `F_p^d`, one for each prime `p ∣ n`. -/
abbrev ModTuple (n d : ℕ) :=
  ∀ p : n.primeFactors, Submodule (ZMod (p : ℕ)) (Fin d → ZMod (p : ℕ))

/-- The divisor `Π_p p^{rank (U p)}` of `rad(n)^d` attached to a tuple. -/
noncomputable def hOf (U : ModTuple n d) : ℕ :=
  ∏ p : n.primeFactors, (p : ℕ) ^ finrank (ZMod (p : ℕ)) (U p)

private theorem dvdn {m : ℕ} (p : m.primeFactors) : (p : ℕ) ∣ m :=
  Nat.dvd_of_mem_primeFactors p.2

private theorem coprime_coe {m : ℕ} :
    Pairwise (Nat.Coprime on fun p : m.primeFactors => (p : ℕ)) := by
  intro p q hpq
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
    (Nat.prime_of_mem_primeFactors q.2)).mpr fun h => hpq (Subtype.ext h)

theorem rad_ne_zero : rad n ≠ 0 := by
  unfold rad
  exact (Finset.prod_pos fun q hq =>
    (Nat.prime_of_mem_primeFactors hq).pos).ne'

private theorem sup_id_le_torsion [NeZero n] {q : ℕ} (hq : q.Prime)
    {tp : Finset (AddSubgroup (Lat n d))} (h : tp ⊆ linesP n d q) :
    tp.sup id ≤ latTorsion n d q :=
  Finset.sup_le fun C hC =>
    le_torsion_of_card_prime ((mem_linesP hq).mp (h hC))

private theorem biUnion_filter_card [NeZero n]
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

/-! ### Factorization bookkeeping -/

private theorem factorization_prod_pow (e : ℕ → ℕ) {q₀ : ℕ}
    (hq₀ : q₀ ∈ n.primeFactors) :
    (∏ q ∈ n.primeFactors, q ^ e q).factorization q₀ = e q₀ := by
  rw [Nat.factorization_prod (fun q hq =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).pos.ne')]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single q₀]
  · rw [Nat.factorization_pow, Finsupp.smul_apply,
      (Nat.prime_of_mem_primeFactors hq₀).factorization,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro q hq hne
    rw [Nat.factorization_pow, Finsupp.smul_apply,
      (Nat.prime_of_mem_primeFactors hq).factorization,
      Finsupp.single_apply, if_neg hne, smul_zero]
  · intro habs
    exact absurd hq₀ habs

private theorem factorization_radPow (hd : d ≠ 0) {q₀ : ℕ}
    (hq₀ : q₀ ∈ n.primeFactors) :
    (rad n ^ d).factorization q₀ = d := by
  have hrw : rad n ^ d = ∏ q ∈ n.primeFactors, q ^ d := by
    rw [rad, Finset.prod_pow]
  rw [hrw, factorization_prod_pow (fun _ => d) hq₀]

private noncomputable def eU (U : ModTuple n d) (q : ℕ) : ℕ :=
  if hq : q ∈ n.primeFactors then finrank (ZMod q) (U ⟨q, hq⟩) else 0

private theorem hOf_eq_prod (U : ModTuple n d) :
    hOf U = ∏ q ∈ n.primeFactors, q ^ eU U q := by
  rw [hOf, ← Finset.prod_coe_sort n.primeFactors (fun q => q ^ eU U q)]
  refine Finset.prod_congr rfl fun p _ => ?_
  congr 1
  rw [eU, dif_pos p.2]

private theorem factorization_hOf (U : ModTuple n d)
    (p : n.primeFactors) :
    (hOf U).factorization (p : ℕ) = finrank (ZMod (p : ℕ)) (U p) := by
  rw [hOf_eq_prod, factorization_prod_pow (eU U) p.2, eU, dif_pos p.2]

private theorem hOf_dvd (U : ModTuple n d) : hOf U ∣ rad n ^ d := by
  have hrw : rad n ^ d = ∏ p : n.primeFactors, (p : ℕ) ^ d := by
    rw [rad, ← Finset.prod_pow,
      ← Finset.prod_coe_sort n.primeFactors (fun q => q ^ d)]
  rw [hOf, hrw]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun p _ => ?_
  refine pow_dvd_pow _ ?_
  have hle := Submodule.finrank_le (U p)
  rwa [finrank_pi_d] at hle

private theorem hOf_eq_iff (hd : d ≠ 0) {h : ℕ}
    (hh : h ∈ (rad n ^ d).divisors) (U : ModTuple n d) :
    hOf U = h ↔ ∀ p : n.primeFactors,
      finrank (ZMod (p : ℕ)) (U p) = h.factorization (p : ℕ) := by
  obtain ⟨hdvd, hrad0⟩ := Nat.mem_divisors.mp hh
  have hh0 : h ≠ 0 := (Nat.pos_of_mem_divisors hh).ne'
  have hsub : h.primeFactors ⊆ n.primeFactors := by
    have hmono := Nat.primeFactors_mono hdvd hrad0
    rwa [Nat.primeFactors_pow _ hd, rad, Nat.primeFactors_prod
      (fun q hq => Nat.prime_of_mem_primeFactors hq)] at hmono
  constructor
  · rintro rfl
    exact fun p => (factorization_hOf U p).symm
  · intro hv
    calc hOf U = ∏ q ∈ n.primeFactors, q ^ h.factorization q := by
          rw [hOf, ← Finset.prod_coe_sort n.primeFactors
            (fun q => q ^ h.factorization q)]
          exact Finset.prod_congr rfl fun p _ => by rw [hv p]
      _ = ∏ q ∈ h.primeFactors, q ^ h.factorization q := by
          symm
          refine Finset.prod_subset hsub fun q _ hqn => ?_
          have h0 : h.factorization q = 0 := by
            rw [← Nat.support_factorization] at hqn
            exact Finsupp.notMem_support_iff.mp hqn
          rw [h0, pow_zero]
      _ = h := by
          conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hh0]
          rw [← Nat.support_factorization]
          rfl

/-! ### Step A: peel the empty set off the certified IE sum -/

private theorem card_eq_powerset_sum (σ : ℕ) [NeZero n] :
    ((Finset.univ.filter
        (fun s : Config n d (Fin σ) => IsShiftSymmetric s)).card : ℤ)
      = (∑ t ∈ (primeOrderSubs n d).powerset,
          (-1 : ℤ) ^ (t.card + 1)
            * (σ : ℤ) ^ (n ^ d /
                Nat.card ((t.sup id : AddSubgroup (Lat n d)))))
        + (σ : ℤ) ^ (n ^ d) := by
  rw [card_shiftSymmetric_IE]
  rw [Finset.sum_coe_sort
    ((primeOrderSubs n d).powerset.filter (·.Nonempty))
    (fun t => (-1 : ℤ) ^ (t.card + 1)
      * (σ : ℤ) ^ (n ^ d /
          Nat.card ((t.sup id : AddSubgroup (Lat n d)))))]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((primeOrderSubs n d).powerset) (·.Nonempty)
    (fun t => (-1 : ℤ) ^ (t.card + 1)
      * (σ : ℤ) ^ (n ^ d /
          Nat.card ((t.sup id : AddSubgroup (Lat n d)))))]
  have hnot : (primeOrderSubs n d).powerset.filter (fun t => ¬t.Nonempty)
      = {∅} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_singleton, Finset.not_nonempty_iff_eq_empty]
    exact ⟨fun h => h.2, fun h =>
      ⟨by rw [h]; exact Finset.empty_subset _, h⟩⟩
  rw [hnot, Finset.sum_singleton, Finset.card_empty, Finset.sup_empty,
    AddSubgroup.card_bot, Nat.div_one, zero_add, pow_one]
  ring

/-! ### Step B: powersets of `P` ≃ tuples of powersets of the `P_p` -/

private theorem powerset_sum_eq_piFinset (σ : ℕ) [NeZero n] :
    (∑ t ∈ (primeOrderSubs n d).powerset,
      (-1 : ℤ) ^ (t.card + 1)
        * (σ : ℤ) ^ (n ^ d /
            Nat.card ((t.sup id : AddSubgroup (Lat n d)))))
    = ∑ g ∈ Fintype.piFinset
        (fun p : n.primeFactors => (linesP n d (p : ℕ)).powerset),
        (-1 : ℤ) ^ ((∑ p : n.primeFactors, (g p).card) + 1)
          * (σ : ℤ) ^ (n ^ d / Nat.card
            ((Finset.univ.sup
                (fun p : n.primeFactors => (g p).sup id)
              : AddSubgroup (Lat n d)))) := by
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

/-! ### Step C: fiber over the tuple of per-prime joins -/

private theorem piFinset_sum_eq_tuple_sum (σ : ℕ) [NeZero n] :
    (∑ g ∈ Fintype.piFinset
        (fun p : n.primeFactors => (linesP n d (p : ℕ)).powerset),
        (-1 : ℤ) ^ ((∑ p : n.primeFactors, (g p).card) + 1)
          * (σ : ℤ) ^ (n ^ d / Nat.card
            ((Finset.univ.sup
                (fun p : n.primeFactors => (g p).sup id)
              : AddSubgroup (Lat n d)))))
    = ∑ U : ModTuple n d,
        -(∏ p : n.primeFactors, spanSum (U p))
          * (σ : ℤ) ^ (n ^ d / hOf U) := by
  have hmaps : ∀ g ∈ Fintype.piFinset
      (fun p : n.primeFactors => (linesP n d (p : ℕ)).powerset),
      (fun p : n.primeFactors => toMod (dvdn p) ((g p).sup id))
        ∈ (Finset.univ : Finset (ModTuple n d)) :=
    fun g _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun g => (-1 : ℤ) ^ ((∑ p : n.primeFactors, (g p).card) + 1)
      * (σ : ℤ) ^ (n ^ d / Nat.card
        ((Finset.univ.sup (fun p : n.primeFactors => (g p).sup id)
          : AddSubgroup (Lat n d)))))]
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
  -- on the fiber, the exponent is constant, equal to `n^d / hOf U`
  have hcard : ∀ g ∈ Fintype.piFinset (fun p : n.primeFactors =>
      ((linesP n d (p : ℕ)).powerset).filter
        (fun tp => tp.sup id = ofMod (dvdn p) (U p))),
      Nat.card ((Finset.univ.sup
          (fun p : n.primeFactors => (g p).sup id)
        : AddSubgroup (Lat n d))) = hOf U := by
    intro g hg
    rw [Fintype.mem_piFinset] at hg
    have hsup : (fun p : n.primeFactors => (g p).sup id)
        = fun p : n.primeFactors => ofMod (dvdn p) (U p) :=
      funext fun p => (Finset.mem_filter.mp (hg p)).2
    rw [hsup, card_univ_sup_of_torsion
      (fun p : n.primeFactors => (p : ℕ)) _
      (fun p => ofMod_le_torsion (dvdn p) (U p)) coprime_coe]
    rw [hOf]
    exact Finset.prod_congr rfl fun p _ => by
      rw [card_ofMod, card_submodule_pow]
  calc ∑ g ∈ (Fintype.piFinset (fun p : n.primeFactors =>
        ((linesP n d (p : ℕ)).powerset).filter
          (fun tp => tp.sup id = ofMod (dvdn p) (U p)))),
        (-1 : ℤ) ^ ((∑ p : n.primeFactors, (g p).card) + 1)
          * (σ : ℤ) ^ (n ^ d / Nat.card
            ((Finset.univ.sup
                (fun p : n.primeFactors => (g p).sup id)
              : AddSubgroup (Lat n d))))
      = ∑ g ∈ (Fintype.piFinset (fun p : n.primeFactors =>
          ((linesP n d (p : ℕ)).powerset).filter
            (fun tp => tp.sup id = ofMod (dvdn p) (U p)))),
          -(∏ p : n.primeFactors, (-1 : ℤ) ^ (g p).card)
            * (σ : ℤ) ^ (n ^ d / hOf U) := by
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [hcard g hg, pow_succ, Finset.prod_pow_eq_pow_sum]
        ring
    _ = -(∑ g ∈ (Fintype.piFinset (fun p : n.primeFactors =>
          ((linesP n d (p : ℕ)).powerset).filter
            (fun tp => tp.sup id = ofMod (dvdn p) (U p)))),
          ∏ p : n.primeFactors, (-1 : ℤ) ^ (g p).card)
            * (σ : ℤ) ^ (n ^ d / hOf U) := by
        rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    _ = -(∏ p : n.primeFactors,
          ∑ tp ∈ ((linesP n d (p : ℕ)).powerset).filter
            (fun tp => tp.sup id = ofMod (dvdn p) (U p)),
            (-1 : ℤ) ^ tp.card)
            * (σ : ℤ) ^ (n ^ d / hOf U) := by
        rw [Finset.prod_univ_sum]
    _ = -(∏ p : n.primeFactors, spanSum (U p))
          * (σ : ℤ) ^ (n ^ d / hOf U) := by
        congr 2
        exact Finset.prod_congr rfl fun p _ =>
          spanSum_transport (dvdn p) (U p)

/-! ### Step D: fiber the tuples over their divisor `hOf` -/

private theorem tuple_sum_eq_divisor_sum (σ : ℕ) [NeZero n]
    (hd : d ≠ 0) :
    (∑ U : ModTuple n d,
      -(∏ p : n.primeFactors, spanSum (U p))
        * (σ : ℤ) ^ (n ^ d / hOf U))
    = ∑ h ∈ (rad n ^ d).divisors,
        coeffOf d h * (σ : ℤ) ^ (n ^ d / h) := by
  have hrad0 : rad n ^ d ≠ 0 := pow_ne_zero _ rad_ne_zero
  have hmaps : ∀ U ∈ (Finset.univ : Finset (ModTuple n d)),
      hOf U ∈ (rad n ^ d).divisors :=
    fun U _ => Nat.mem_divisors.mpr ⟨hOf_dvd U, hrad0⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun U : ModTuple n d => -(∏ p : n.primeFactors, spanSum (U p))
      * (σ : ℤ) ^ (n ^ d / hOf U))]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hh0 : h ≠ 0 := (Nat.pos_of_mem_divisors hh).ne'
  obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hh
  have hsub : h.primeFactors ⊆ n.primeFactors := by
    have hmono := Nat.primeFactors_mono hdvd hrad0
    rwa [Nat.primeFactors_pow _ hd, rad, Nat.primeFactors_prod
      (fun q hq => Nat.prime_of_mem_primeFactors hq)] at hmono
  have hvle : ∀ p : n.primeFactors, h.factorization (p : ℕ) ≤ d := by
    intro p
    have hle := (Nat.factorization_le_iff_dvd hh0 hrad0).mpr hdvd
    have hp := Finsupp.le_def.mp hle (p : ℕ)
    rwa [factorization_radPow hd p.2] at hp
  calc ∑ U ∈ Finset.univ.filter (fun U : ModTuple n d => hOf U = h),
        -(∏ p : n.primeFactors, spanSum (U p))
          * (σ : ℤ) ^ (n ^ d / hOf U)
      = ∑ U ∈ Finset.univ.filter (fun U : ModTuple n d => hOf U = h),
        -(∏ p : n.primeFactors, spanSum (U p))
          * (σ : ℤ) ^ (n ^ d / h) := by
        refine Finset.sum_congr rfl fun U hU => ?_
        rw [(Finset.mem_filter.mp hU).2]
    _ = (∑ U ∈ Finset.univ.filter (fun U : ModTuple n d => hOf U = h),
          -(∏ p : n.primeFactors, spanSum (U p)))
          * (σ : ℤ) ^ (n ^ d / h) := (Finset.sum_mul _ _ _).symm
    _ = coeffOf d h * (σ : ℤ) ^ (n ^ d / h) := by
        congr 1
        have hfilter : Finset.univ.filter
            (fun U : ModTuple n d => hOf U = h)
            = Fintype.piFinset (fun p : n.primeFactors =>
                Finset.univ.filter
                  (fun W : Submodule (ZMod (p : ℕ))
                      (Fin d → ZMod (p : ℕ)) =>
                    finrank (ZMod (p : ℕ)) W
                      = h.factorization (p : ℕ))) := by
          ext U
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Fintype.mem_piFinset]
          exact hOf_eq_iff hd hh U
        rw [Finset.sum_neg_distrib, hfilter, ← Finset.prod_univ_sum]
        have hclass : (∏ p : n.primeFactors,
            ∑ W ∈ Finset.univ.filter
              (fun W : Submodule (ZMod (p : ℕ)) (Fin d → ZMod (p : ℕ)) =>
                finrank (ZMod (p : ℕ)) W = h.factorization (p : ℕ)),
              spanSum W)
            = ∏ p : n.primeFactors,
                ((-1 : ℤ) ^ (h.factorization (p : ℕ))
                  * (p : ℤ) ^ ((h.factorization (p : ℕ)).choose 2)
                  * (gaussBinom (p : ℕ) d (h.factorization (p : ℕ)) : ℤ)) :=
          Finset.prod_congr rfl fun q _ =>
            spanSum_rank_classified_pd (hvle q)
        rw [hclass]
        have hsign : (∑ p : n.primeFactors, h.factorization (p : ℕ))
            = bigOmega h := by
          rw [Finset.sum_coe_sort n.primeFactors
            (fun q => h.factorization q)]
          have hfs : bigOmega h
              = ∑ q ∈ h.primeFactors, h.factorization q := by
            rw [bigOmega, ← Nat.support_factorization]
            rfl
          rw [hfs]
          refine (Finset.sum_subset hsub fun q _ hq => ?_).symm
          rw [← Nat.support_factorization] at hq
          exact Finsupp.notMem_support_iff.mp hq
        have hX : (∏ p : n.primeFactors,
            ((p : ℤ) ^ ((h.factorization (p : ℕ)).choose 2)
              * (gaussBinom (p : ℕ) d (h.factorization (p : ℕ)) : ℤ)))
            = ∏ q ∈ h.primeFactors,
                (rdCoeff q (h.factorization q) d : ℤ) := by
          rw [Finset.prod_coe_sort n.primeFactors (fun q =>
            ((q : ℤ) ^ ((h.factorization q).choose 2)
              * (gaussBinom q d (h.factorization q) : ℤ)))]
          rw [← Finset.prod_subset hsub (fun q _ hqn => ?_)]
          · exact (Finset.prod_congr rfl fun q _ => by
              rw [rdCoeff]
              push_cast
              ring).symm
          · have h0 : h.factorization q = 0 := by
              rw [← Nat.support_factorization] at hqn
              exact Finsupp.notMem_support_iff.mp hqn
            rw [h0]
            simp [gaussBinom]
        have hsplit : ∀ p ∈ (Finset.univ : Finset n.primeFactors),
            (-1 : ℤ) ^ (h.factorization (p : ℕ))
                * (p : ℤ) ^ ((h.factorization (p : ℕ)).choose 2)
                * (gaussBinom (p : ℕ) d (h.factorization (p : ℕ)) : ℤ)
              = (-1 : ℤ) ^ (h.factorization (p : ℕ))
                * ((p : ℤ) ^ ((h.factorization (p : ℕ)).choose 2)
                  * (gaussBinom (p : ℕ) d (h.factorization (p : ℕ)) : ℤ)) :=
          fun p _ => by ring
        rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib,
          Finset.prod_pow_eq_pow_sum, hsign, hX, coeffOf]
        rw [pow_add, pow_one]
        ring

/-! ### The main theorem -/

/-- **The enumeration theorem, machine-checked** (paper Theorem 4.3,
contract statement, claim C001): for `n ≥ 2`, `d ≥ 1`, `σ ≥ 1`, the
number of shift-symmetric configurations of `Z_n^d` over an alphabet of
size `σ` equals the divisor-indexed closed formula. -/
theorem enumeration_proved (n dd σ : ℕ) : enumerationStatement n dd σ := by
  intro hn2 hd1 _
  haveI : NeZero n := ⟨by omega⟩
  rw [natCard_shiftSymmetric_eq_filterCard]
  rw [card_eq_powerset_sum, powerset_sum_eq_piFinset,
    piFinset_sum_eq_tuple_sum, tuple_sum_eq_divisor_sum σ (by omega)]
  rw [enumerationRHS]
  have h1mem : (1 : ℕ) ∈ (rad n ^ dd).divisors :=
    Nat.one_mem_divisors.mpr (pow_ne_zero _ rad_ne_zero)
  rw [← Finset.add_sum_erase _ _ h1mem]
  have hc1 : coeffOf dd 1 = -1 := by
    simp [coeffOf, bigOmega]
  rw [hc1, Nat.div_one]
  ring

end ShiftSym
