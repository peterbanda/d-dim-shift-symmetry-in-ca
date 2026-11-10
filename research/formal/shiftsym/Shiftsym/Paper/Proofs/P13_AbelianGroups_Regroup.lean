/-
Paper group 13 (Section 4.5; moved from extension group A1) (AbelianEnum) — proof helper module 2: the regrouping on an
arbitrary finite abelian group `G` (THEOREMS.md, Theorem A1, Steps 3–4).

For an ARBITRARY weight `w : AddSubgroup G → ℤ`, the alternating sum over the
nonempty sets of prime-order subgroups regroups into the sum over the tuples
`U = (U_p)_{p ∣ N}` of `F_p`-subspaces of the `G[p]` of the Möbius coefficient
`−∏_p spanSum (U_p)` times the weight of `socSubG U = ⊕_p U_p`
(`relative_regroupG`; the core's `Relative.lean` with `Lat n d` replaced by `G`).
The order of `socSubG U` is `∏_p p ^ dim U_p` (`card_socSubG`).
-/
import Shiftsym.Paper.Proofs.P13_AbelianGroups_Core

open scoped Classical

namespace ShiftSym.P13.Gen

open ShiftSym ShiftSym.P13 Module Function

/-- Primality of the members of `m.primeFactors`, as a (scoped) instance. -/
scoped instance factPrimeFactors {m : ℕ} (p : m.primeFactors) : Fact ((p : ℕ)).Prime :=
  ⟨Nat.prime_of_mem_primeFactors p.2⟩

variable {G : Type*} [AddCommGroup G] [Finite G]

/-! ### Transport of the signed spanning-set count -/

section Transport

variable {p : ℕ} [hpF : Fact p.Prime]

/-- Summing `(−1)^{|t|}` over the sets `t` of order-`p` subgroups of `G` whose
join is `ofModG p U` gives `spanSum U`. -/
theorem spanSum_transportG (U : Submodule (ZMod p) (torsG G p)) :
    ∑ t ∈ (linesPG G p).powerset.filter (fun t => t.sup id = ofModG p U),
      (-1 : ℤ) ^ t.card
      = spanSum U := by
  have hp : p.Prime := hpF.out
  rw [spanSum, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun t => t.image (toModG p))
    (fun J => J.image (ofModG p)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨htsub, htsup⟩ := Finset.mem_filter.mp ht
    rw [Finset.mem_powerset] at htsub
    have hmemT : ∀ C ∈ t, C ≤ torsG G p := fun C hC =>
      le_torsG_of_card ((mem_linesPG hp).mp (htsub hC))
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro L hL
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hL
      rw [mem_linesF]
      constructor
      · exact finrank_eq_one_of_card_eq
          (by rw [card_toModG p (hmemT C hC)]
              exact (mem_linesPG hp).mp (htsub hC))
      · have h1 : C ≤ ofModG p U := htsup ▸ Finset.le_sup (f := id) hC
        have h2 := toModG_mono p h1
        rwa [toModG_ofModG] at h2
    · rw [Finset.sup_image]
      have hcomp : t.sup (id ∘ toModG p) = t.sup (fun C => toModG p C) := rfl
      rw [hcomp, ← toModG_finset_sup p hmemT, htsup, toModG_ofModG]
  · intro J hJ
    obtain ⟨hJsub, hJsup⟩ := Finset.mem_filter.mp hJ
    rw [Finset.mem_powerset] at hJsub
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro C hC
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hC
      have hline := mem_linesF.mp (hJsub hL)
      rw [mem_linesPG hp, card_ofModG, card_submodule_pow, hline.1, pow_one]
    · rw [Finset.sup_image]
      have hcomp : J.sup (id ∘ ofModG p) = J.sup (fun L => ofModG p (id L)) := rfl
      rw [hcomp, ← ofModG_finset_sup p J id, hJsup]
  · intro t ht
    obtain ⟨htsub, _⟩ := Finset.mem_filter.mp ht
    rw [Finset.mem_powerset] at htsub
    rw [Finset.image_image]
    refine (Finset.image_congr ?_).trans Finset.image_id
    intro C hC
    exact ofModG_toModG p (le_torsG_of_card ((mem_linesPG hp).mp (htsub hC)))
  · intro J _
    rw [Finset.image_image]
    refine (Finset.image_congr ?_).trans Finset.image_id
    intro L _
    exact toModG_ofModG p L
  · intro t ht
    obtain ⟨htsub, _⟩ := Finset.mem_filter.mp ht
    rw [Finset.mem_powerset] at htsub
    congr 1
    refine (Finset.card_image_of_injOn ?_).symm
    intro C₁ h₁ C₂ h₂ heq
    have hT₁ := le_torsG_of_card ((mem_linesPG hp).mp (htsub h₁))
    have hT₂ := le_torsG_of_card ((mem_linesPG hp).mp (htsub h₂))
    rw [← ofModG_toModG p hT₁, ← ofModG_toModG p hT₂, heq]

end Transport

/-! ### Tuples of subspaces and the socle subgroup -/

variable (G) in
/-- A tuple of `F_p`-subspaces of the `G[p]`, one for each prime `p ∣ N`. -/
abbrev ModTupleG :=
  ∀ p : (Nat.card G).primeFactors, Submodule (ZMod (p : ℕ)) (torsG G p)

/-- The subgroup `⊕_p U_p` of the socle attached to a tuple. -/
noncomputable def socSubG (U : ModTupleG G) : AddSubgroup G :=
  Finset.univ.sup fun p : (Nat.card G).primeFactors => ofModG (p : ℕ) (U p)

/-- The Möbius coefficient `−∏_p spanSum (U_p)`. -/
noncomputable def mobiusCoeffG (U : ModTupleG G) : ℤ :=
  -(∏ p : (Nat.card G).primeFactors, spanSum (U p))

/-- The order `∏_p p ^ dim U_p` of `socSubG U`. -/
noncomputable def hOfG (U : ModTupleG G) : ℕ :=
  ∏ p : (Nat.card G).primeFactors, (p : ℕ) ^ finrank (ZMod (p : ℕ)) (U p)

private theorem coprime_coe {m : ℕ} :
    Pairwise (Nat.Coprime on fun p : m.primeFactors => (p : ℕ)) := by
  intro p q hpq
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
    (Nat.prime_of_mem_primeFactors q.2)).mpr fun h => hpq (Subtype.ext h)

theorem card_socSubG (U : ModTupleG G) : Nat.card (socSubG U) = hOfG U := by
  unfold socSubG
  rw [card_univ_sup_of_torsG (fun p : (Nat.card G).primeFactors => (p : ℕ)) _
    (fun p => ofModG_le_torsG (p : ℕ) (U p)) coprime_coe]
  exact Finset.prod_congr rfl fun p _ => by rw [card_ofModG, card_submodule_pow]

/-! ### The weight-generic regrouping -/

section Regroup

variable (w : AddSubgroup G → ℤ)

private theorem sup_id_le_torsG {q : ℕ} (hq : q.Prime)
    {tp : Finset (AddSubgroup G)} (h : tp ⊆ linesPG G q) :
    tp.sup id ≤ torsG G q :=
  Finset.sup_le fun _C hC => le_torsG_of_card ((mem_linesPG hq).mp (h hC))

private theorem biUnion_filter_cardG {t : Finset (AddSubgroup G)}
    (ht : t ⊆ primeOrderSubsG G) :
    Finset.univ.biUnion
        (fun p : (Nat.card G).primeFactors =>
          t.filter (fun C : AddSubgroup G => Nat.card C = (p : ℕ)))
      = t := by
  ext C
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨p, hCt, -⟩
    exact hCt
  · intro hCt
    have hprime : (Nat.card C).Prime := mem_primeOrderSubsG.mp (ht hCt)
    exact ⟨⟨Nat.card C, card_mem_primeFactorsG hprime⟩, hCt, rfl⟩

/-- Step A: peel the empty set off the IE sum. -/
theorem sum_nonempty_eq_sum_powerset_addG :
    (∑ t : ((primeOrderSubsG G).powerset.filter (·.Nonempty)),
        (-1 : ℤ) ^ (t.1.card + 1) * w (t.1.sup id))
      = (∑ t ∈ (primeOrderSubsG G).powerset,
          (-1 : ℤ) ^ (t.card + 1) * w (t.sup id)) + w ⊥ := by
  rw [Finset.sum_coe_sort ((primeOrderSubsG G).powerset.filter (·.Nonempty))
    (fun t => (-1 : ℤ) ^ (t.card + 1) * w (t.sup id))]
  rw [← Finset.sum_filter_add_sum_filter_not ((primeOrderSubsG G).powerset) (·.Nonempty)
    (fun t => (-1 : ℤ) ^ (t.card + 1) * w (t.sup id))]
  have hnot : (primeOrderSubsG G).powerset.filter (fun t => ¬t.Nonempty) = {∅} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton,
      Finset.not_nonempty_iff_eq_empty]
    exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact Finset.empty_subset _, h⟩⟩
  rw [hnot, Finset.sum_singleton, Finset.card_empty, Finset.sup_empty]
  ring

/-- Step B: powersets of the prime-order subgroups ≃ tuples of powersets of the
order-`p` subgroups. -/
theorem powerset_sum_eq_piFinset_wG :
    (∑ t ∈ (primeOrderSubsG G).powerset, (-1 : ℤ) ^ (t.card + 1) * w (t.sup id))
    = ∑ g ∈ Fintype.piFinset
        (fun p : (Nat.card G).primeFactors => (linesPG G (p : ℕ)).powerset),
        (-1 : ℤ) ^ ((∑ p : (Nat.card G).primeFactors, (g p).card) + 1)
          * w (Finset.univ.sup (fun p : (Nat.card G).primeFactors => (g p).sup id)) := by
  refine Finset.sum_nbij'
    (fun t : Finset (AddSubgroup G) =>
      fun p : (Nat.card G).primeFactors =>
        t.filter (fun C : AddSubgroup G => Nat.card C = (p : ℕ)))
    (fun g => Finset.univ.biUnion (fun p : (Nat.card G).primeFactors => g p))
    ?_ ?_ ?_ ?_ ?_
  · intro t _
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_powerset]
    intro C hC
    exact (mem_linesPG (Nat.prime_of_mem_primeFactors p.2)).mpr (Finset.mem_filter.mp hC).2
  · intro g hg
    rw [Fintype.mem_piFinset] at hg
    rw [Finset.mem_powerset]
    intro C hC
    obtain ⟨p, -, hCp⟩ := Finset.mem_biUnion.mp hC
    exact Finset.filter_subset _ _ (Finset.mem_powerset.mp (hg p) hCp)
  · intro t ht
    exact biUnion_filter_cardG (Finset.mem_powerset.mp ht)
  · intro g hg
    rw [Fintype.mem_piFinset] at hg
    funext p
    ext C
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨q, hCq⟩, hcard⟩
      have hq := (mem_linesPG (Nat.prime_of_mem_primeFactors q.2)).mp
        (Finset.mem_powerset.mp (hg q) hCq)
      have hqp : q = p := Subtype.ext (by rw [← hq, hcard])
      exact hqp ▸ hCq
    · intro hCp
      have hp := (mem_linesPG (Nat.prime_of_mem_primeFactors p.2)).mp
        (Finset.mem_powerset.mp (hg p) hCp)
      exact ⟨⟨p, hCp⟩, hp⟩
  · intro t ht
    have hbi := biUnion_filter_cardG (G := G) (Finset.mem_powerset.mp ht)
    have hdisj : ∀ p ∈ (Finset.univ : Finset (Nat.card G).primeFactors),
        ∀ q ∈ (Finset.univ : Finset (Nat.card G).primeFactors), p ≠ q →
        Disjoint (t.filter (fun C : AddSubgroup G => Nat.card C = (p : ℕ)))
          (t.filter (fun C : AddSubgroup G => Nat.card C = (q : ℕ))) := by
      intro p _ q _ hpq
      rw [Finset.disjoint_left]
      intro C hCp hCq
      exact hpq (Subtype.ext (by
        rw [← (Finset.mem_filter.mp hCp).2, ← (Finset.mem_filter.mp hCq).2]))
    have hcard : t.card = ∑ p : (Nat.card G).primeFactors,
        (t.filter (fun C : AddSubgroup G => Nat.card C = (p : ℕ))).card := by
      conv_lhs => rw [← hbi]
      exact Finset.card_biUnion hdisj
    have hsup : t.sup id = Finset.univ.sup (fun p : (Nat.card G).primeFactors =>
        (t.filter (fun C : AddSubgroup G => Nat.card C = (p : ℕ))).sup id) := by
      conv_lhs => rw [← hbi]
      exact Finset.sup_biUnion _ _
    rw [hcard, hsup]

/-- Step C: fiber over the tuple of per-prime joins. -/
theorem piFinset_sum_eq_tuple_sum_wG :
    (∑ g ∈ Fintype.piFinset
        (fun p : (Nat.card G).primeFactors => (linesPG G (p : ℕ)).powerset),
        (-1 : ℤ) ^ ((∑ p : (Nat.card G).primeFactors, (g p).card) + 1)
          * w (Finset.univ.sup (fun p : (Nat.card G).primeFactors => (g p).sup id)))
    = ∑ U : ModTupleG G, mobiusCoeffG U * w (socSubG U) := by
  have hmaps : ∀ g ∈ Fintype.piFinset
      (fun p : (Nat.card G).primeFactors => (linesPG G (p : ℕ)).powerset),
      (fun p : (Nat.card G).primeFactors => toModG (p : ℕ) ((g p).sup id))
        ∈ (Finset.univ : Finset (ModTupleG G)) :=
    fun g _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun g => (-1 : ℤ) ^ ((∑ p : (Nat.card G).primeFactors, (g p).card) + 1)
      * w (Finset.univ.sup (fun p : (Nat.card G).primeFactors => (g p).sup id)))]
  refine Finset.sum_congr rfl fun U _ => ?_
  have hfib : (Fintype.piFinset (fun p : (Nat.card G).primeFactors =>
        (linesPG G (p : ℕ)).powerset)).filter
      (fun g => (fun p : (Nat.card G).primeFactors => toModG (p : ℕ) ((g p).sup id)) = U)
      = Fintype.piFinset (fun p : (Nat.card G).primeFactors =>
          ((linesPG G (p : ℕ)).powerset).filter
            (fun tp => tp.sup id = ofModG (p : ℕ) (U p))) := by
    ext g
    simp only [Finset.mem_filter, Fintype.mem_piFinset, funext_iff]
    constructor
    · rintro ⟨hmem, hcond⟩ p
      refine ⟨hmem p, ?_⟩
      rw [← hcond p, ofModG_toModG (p : ℕ) (sup_id_le_torsG
        (Nat.prime_of_mem_primeFactors p.2) (Finset.mem_powerset.mp (hmem p)))]
    · intro hall
      refine ⟨fun p => (hall p).1, fun p => ?_⟩
      rw [(hall p).2, toModG_ofModG]
  rw [hfib]
  have hjoin : ∀ g ∈ Fintype.piFinset (fun p : (Nat.card G).primeFactors =>
      ((linesPG G (p : ℕ)).powerset).filter
        (fun tp => tp.sup id = ofModG (p : ℕ) (U p))),
      Finset.univ.sup (fun p : (Nat.card G).primeFactors => (g p).sup id) = socSubG U := by
    intro g hg
    rw [Fintype.mem_piFinset] at hg
    have hsup : (fun p : (Nat.card G).primeFactors => (g p).sup id)
        = fun p : (Nat.card G).primeFactors => ofModG (p : ℕ) (U p) :=
      funext fun p => (Finset.mem_filter.mp (hg p)).2
    rw [hsup]
    rfl
  calc ∑ g ∈ (Fintype.piFinset (fun p : (Nat.card G).primeFactors =>
        ((linesPG G (p : ℕ)).powerset).filter
          (fun tp => tp.sup id = ofModG (p : ℕ) (U p)))),
        (-1 : ℤ) ^ ((∑ p : (Nat.card G).primeFactors, (g p).card) + 1)
          * w (Finset.univ.sup (fun p : (Nat.card G).primeFactors => (g p).sup id))
      = ∑ g ∈ (Fintype.piFinset (fun p : (Nat.card G).primeFactors =>
          ((linesPG G (p : ℕ)).powerset).filter
            (fun tp => tp.sup id = ofModG (p : ℕ) (U p)))),
          -(∏ p : (Nat.card G).primeFactors, (-1 : ℤ) ^ (g p).card) * w (socSubG U) := by
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [hjoin g hg, pow_succ, Finset.prod_pow_eq_pow_sum]
        ring
    _ = -(∑ g ∈ (Fintype.piFinset (fun p : (Nat.card G).primeFactors =>
          ((linesPG G (p : ℕ)).powerset).filter
            (fun tp => tp.sup id = ofModG (p : ℕ) (U p)))),
          ∏ p : (Nat.card G).primeFactors, (-1 : ℤ) ^ (g p).card) * w (socSubG U) := by
        rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    _ = -(∏ p : (Nat.card G).primeFactors,
          ∑ tp ∈ ((linesPG G (p : ℕ)).powerset).filter
            (fun tp => tp.sup id = ofModG (p : ℕ) (U p)),
            (-1 : ℤ) ^ tp.card) * w (socSubG U) := by
        rw [Finset.prod_univ_sum]
    _ = mobiusCoeffG U * w (socSubG U) := by
        unfold mobiusCoeffG
        congr 2
        exact Finset.prod_congr rfl fun p _ => spanSum_transportG (U p)

/-- **The weight-generic regrouping on `G`.** -/
theorem relative_regroupG :
    (∑ t : ((primeOrderSubsG G).powerset.filter (·.Nonempty)),
        (-1 : ℤ) ^ (t.1.card + 1) * w (t.1.sup id))
      = ∑ U : ModTupleG G, mobiusCoeffG U * w (socSubG U) + w ⊥ := by
  rw [sum_nonempty_eq_sum_powerset_addG, powerset_sum_eq_piFinset_wG,
    piFinset_sum_eq_tuple_sum_wG]

end Regroup

end ShiftSym.P13.Gen
