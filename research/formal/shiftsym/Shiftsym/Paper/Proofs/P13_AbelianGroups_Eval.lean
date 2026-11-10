/-
Paper group 13 (Section 4.5; moved from extension group A1) (AbelianEnum) — proof helper module 3: evaluation of the
regrouped sum on a finite abelian group `G` (THEOREMS.md, Theorem A1, Step 5).

For ANY weight `W : ℕ → ℤ` evaluated at the order of the socle subgroup,
`Σ_U mobiusCoeffG U · W(|socSubG U|) = Σ_{h ∣ R} coeffA (pRank G) h · W h`,
`R = rankRad N (pRank G)`: the tuples are grouped by their dimension vector
`v_p = dim U_p` (`∏_p [d_p, v_p]_p` tuples, `spanSum_rank_classified`) and the
vector is coded by the divisor `h = ∏_p p ^ v_p` of `R` (the core's
`Evaluate.lean`, step D, with `d` replaced by `d_p`). Combined with the IE form
and the regrouping: `relative_divisorG` — for every finset `X` of configurations
over any finite alphabet whose relativised fixed-set counts depend only on the
order of the subgroup, `|X ∩ S_G| = Σ_{h ∣ R, h ≠ 1} coeffA h · W h`.
-/
import Shiftsym.Paper.Proofs.P13_AbelianGroups_Regroup

open scoped Classical

namespace ShiftSym.P13.Gen

open ShiftSym ShiftSym.P13 Module Function

variable {G : Type*} [AddCommGroup G] [Finite G]

/-! ### Factorization bookkeeping -/

private theorem factorization_prod_pow {m : ℕ} (e : ℕ → ℕ) {q₀ : ℕ}
    (hq₀ : q₀ ∈ m.primeFactors) :
    (∏ q ∈ m.primeFactors, q ^ e q).factorization q₀ = e q₀ := by
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

theorem rankRad_ne_zero (m : ℕ) (dp : ℕ → ℕ) : rankRad m dp ≠ 0 := by
  unfold rankRad
  exact (Finset.prod_pos fun q hq =>
    pow_pos (Nat.prime_of_mem_primeFactors hq).pos _).ne'

theorem factorization_rankRad {m : ℕ} (dp : ℕ → ℕ) {q₀ : ℕ} (hq₀ : q₀ ∈ m.primeFactors) :
    (rankRad m dp).factorization q₀ = dp q₀ :=
  factorization_prod_pow dp hq₀

theorem primeFactors_rankRad_subset (m : ℕ) (dp : ℕ → ℕ) :
    (rankRad m dp).primeFactors ⊆ m.primeFactors := by
  intro q hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqd : q ∣ rankRad m dp := Nat.dvd_of_mem_primeFactors hq
  unfold rankRad at hqd
  obtain ⟨p, hp, hqpd⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).mp hqd
  have hqp' : q ∣ p := hqp.dvd_of_dvd_pow hqpd
  have heq : q = p :=
    (Nat.prime_dvd_prime_iff_eq hqp (Nat.prime_of_mem_primeFactors hp)).mp hqp'
  exact heq ▸ hp

private noncomputable def eU (U : ModTupleG G) (q : ℕ) : ℕ :=
  if hq : q ∈ (Nat.card G).primeFactors then
    finrank (ZMod q) (U ⟨q, hq⟩) else 0

omit [Finite G] in
private theorem hOfG_eq_prod (U : ModTupleG G) :
    hOfG U = ∏ q ∈ (Nat.card G).primeFactors, q ^ eU U q := by
  rw [hOfG, ← Finset.prod_coe_sort (Nat.card G).primeFactors (fun q => q ^ eU U q)]
  refine Finset.prod_congr rfl fun p _ => ?_
  congr 1
  rw [eU, dif_pos p.2]

omit [Finite G] in
private theorem factorization_hOfG (U : ModTupleG G) (p : (Nat.card G).primeFactors) :
    (hOfG U).factorization (p : ℕ) = finrank (ZMod (p : ℕ)) (U p) := by
  rw [hOfG_eq_prod, factorization_prod_pow (eU U) p.2, eU, dif_pos p.2]

theorem finrank_tuple_le (U : ModTupleG G) (p : (Nat.card G).primeFactors) :
    finrank (ZMod (p : ℕ)) (U p) ≤ pRank G (p : ℕ) := by
  rw [pRank_eq_finrank]
  exact Submodule.finrank_le (U p)

theorem hOfG_dvd (U : ModTupleG G) : hOfG U ∣ rankRad (Nat.card G) (pRank G) := by
  rw [hOfG, rankRad, ← Finset.prod_coe_sort (Nat.card G).primeFactors
    (fun q => q ^ pRank G q)]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun p _ => pow_dvd_pow _ (finrank_tuple_le U p)

omit [Finite G] in
private theorem hOfG_eq_iff {h : ℕ}
    (hh : h ∈ (rankRad (Nat.card G) (pRank G)).divisors) (U : ModTupleG G) :
    hOfG U = h ↔ ∀ p : (Nat.card G).primeFactors,
      finrank (ZMod (p : ℕ)) (U p) = h.factorization (p : ℕ) := by
  obtain ⟨hdvd, hR0⟩ := Nat.mem_divisors.mp hh
  have hh0 : h ≠ 0 := (Nat.pos_of_mem_divisors hh).ne'
  have hsub : h.primeFactors ⊆ (Nat.card G).primeFactors :=
    (Nat.primeFactors_mono hdvd hR0).trans (primeFactors_rankRad_subset _ _)
  constructor
  · rintro rfl
    exact fun p => (factorization_hOfG U p).symm
  · intro hv
    calc hOfG U = ∏ q ∈ (Nat.card G).primeFactors, q ^ h.factorization q := by
          rw [hOfG, ← Finset.prod_coe_sort (Nat.card G).primeFactors
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

/-- The classified spanning-set sum on `G[p]`. -/
theorem spanSum_rank_classifiedG (p : ℕ) [Fact p.Prime] {r : ℕ}
    (hr : r ≤ finrank (ZMod p) (torsG G p)) :
    ∑ U ∈ Finset.univ.filter
        (fun U : Submodule (ZMod p) (torsG G p) => finrank (ZMod p) U = r),
      spanSum U
      = (-1 : ℤ) ^ r * (p : ℤ) ^ (r.choose 2)
          * gaussBinom p (finrank (ZMod p) (torsG G p)) r := by
  have h := spanSum_rank_classified (K := ZMod p) (V := torsG G p) (r := r) hr
  rw [ZMod.card] at h
  exact h

/-! ### Step D: fiber the tuples over their divisor -/

/-- **Evaluation for an arbitrary order-dependent weight.** -/
theorem tuple_sum_eq_divisor_sumG (W : ℕ → ℤ) :
    (∑ U : ModTupleG G, mobiusCoeffG U * W (hOfG U))
      = ∑ h ∈ (rankRad (Nat.card G) (pRank G)).divisors, coeffA (pRank G) h * W h := by
  set R := rankRad (Nat.card G) (pRank G) with hRdef
  have hR0 : R ≠ 0 := rankRad_ne_zero _ _
  have hmaps : ∀ U ∈ (Finset.univ : Finset (ModTupleG G)), hOfG U ∈ R.divisors :=
    fun U _ => Nat.mem_divisors.mpr ⟨hOfG_dvd U, hR0⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun U : ModTupleG G => mobiusCoeffG U * W (hOfG U))]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hh0 : h ≠ 0 := (Nat.pos_of_mem_divisors hh).ne'
  obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hh
  have hsub : h.primeFactors ⊆ (Nat.card G).primeFactors :=
    (Nat.primeFactors_mono hdvd hR0).trans (primeFactors_rankRad_subset _ _)
  have hvle : ∀ p : (Nat.card G).primeFactors,
      h.factorization (p : ℕ) ≤ finrank (ZMod (p : ℕ)) (torsG G (p : ℕ)) := by
    intro p
    have hle := (Nat.factorization_le_iff_dvd hh0 hR0).mpr hdvd
    have hp := Finsupp.le_def.mp hle (p : ℕ)
    rwa [hRdef, factorization_rankRad _ p.2, pRank_eq_finrank] at hp
  calc ∑ U ∈ Finset.univ.filter (fun U : ModTupleG G => hOfG U = h),
        mobiusCoeffG U * W (hOfG U)
      = ∑ U ∈ Finset.univ.filter (fun U : ModTupleG G => hOfG U = h),
          mobiusCoeffG U * W h := by
        refine Finset.sum_congr rfl fun U hU => ?_
        rw [(Finset.mem_filter.mp hU).2]
    _ = (∑ U ∈ Finset.univ.filter (fun U : ModTupleG G => hOfG U = h),
          mobiusCoeffG U) * W h := (Finset.sum_mul _ _ _).symm
    _ = coeffA (pRank G) h * W h := by
        congr 1
        have hfilter : Finset.univ.filter (fun U : ModTupleG G => hOfG U = h)
            = Fintype.piFinset (fun p : (Nat.card G).primeFactors =>
                Finset.univ.filter
                  (fun U : Submodule (ZMod (p : ℕ)) (torsG G (p : ℕ)) =>
                    finrank (ZMod (p : ℕ)) U = h.factorization (p : ℕ))) := by
          ext U
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
          exact hOfG_eq_iff hh U
        unfold mobiusCoeffG
        rw [Finset.sum_neg_distrib, hfilter, ← Finset.prod_univ_sum]
        have hclass : (∏ p : (Nat.card G).primeFactors,
            ∑ U ∈ Finset.univ.filter
              (fun U : Submodule (ZMod (p : ℕ)) (torsG G (p : ℕ)) =>
                finrank (ZMod (p : ℕ)) U = h.factorization (p : ℕ)),
              spanSum U)
            = ∏ p : (Nat.card G).primeFactors,
                ((-1 : ℤ) ^ (h.factorization (p : ℕ))
                  * ((p : ℕ) : ℤ) ^ ((h.factorization (p : ℕ)).choose 2)
                  * (gaussBinom (p : ℕ) (pRank G (p : ℕ)) (h.factorization (p : ℕ)) : ℤ)) :=
          Finset.prod_congr rfl fun q _ => by
            rw [spanSum_rank_classifiedG (q : ℕ) (hvle q), pRank_eq_finrank]
        rw [hclass]
        have hsign : (∑ p : (Nat.card G).primeFactors, h.factorization (p : ℕ))
            = bigOmega h := by
          rw [Finset.sum_coe_sort (Nat.card G).primeFactors (fun q => h.factorization q)]
          have hfs : bigOmega h = ∑ q ∈ h.primeFactors, h.factorization q := by
            rw [bigOmega, ← Nat.support_factorization]
            rfl
          rw [hfs]
          refine (Finset.sum_subset hsub fun q _ hq => ?_).symm
          rw [← Nat.support_factorization] at hq
          exact Finsupp.notMem_support_iff.mp hq
        have hX : (∏ p : (Nat.card G).primeFactors,
            (((p : ℕ) : ℤ) ^ ((h.factorization (p : ℕ)).choose 2)
              * (gaussBinom (p : ℕ) (pRank G (p : ℕ)) (h.factorization (p : ℕ)) : ℤ)))
            = ∏ q ∈ h.primeFactors, (rdCoeff q (h.factorization q) (pRank G q) : ℤ) := by
          rw [Finset.prod_coe_sort (Nat.card G).primeFactors (fun q =>
            ((q : ℤ) ^ ((h.factorization q).choose 2)
              * (gaussBinom q (pRank G q) (h.factorization q) : ℤ)))]
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
        have hsplit : ∀ p ∈ (Finset.univ : Finset (Nat.card G).primeFactors),
            (-1 : ℤ) ^ (h.factorization (p : ℕ))
                * ((p : ℕ) : ℤ) ^ ((h.factorization (p : ℕ)).choose 2)
                * (gaussBinom (p : ℕ) (pRank G (p : ℕ)) (h.factorization (p : ℕ)) : ℤ)
              = (-1 : ℤ) ^ (h.factorization (p : ℕ))
                * (((p : ℕ) : ℤ) ^ ((h.factorization (p : ℕ)).choose 2)
                  * (gaussBinom (p : ℕ) (pRank G (p : ℕ)) (h.factorization (p : ℕ)) : ℤ)) :=
          fun p _ => by ring
        rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib,
          Finset.prod_pow_eq_pow_sum, hsign, hX, coeffA]
        rw [pow_add, pow_one]
        ring

theorem coeffA_one (dp : ℕ → ℕ) : coeffA dp 1 = -1 := by
  simp [coeffA, bigOmega]

/-! ### The relative theorem in divisor form -/

/-- **Relative enumeration on `G`, divisor form**: if the relativised fixed-set
counts depend only on the order of the subgroup, `|X ∩ Fix(H)| = W(|H|)`, then
`|X ∩ S_G| = Σ_{h ∣ R, h ≠ 1} coeffA (pRank G) h · W h`. -/
theorem relative_divisorG [Fintype G] {A : Type*} [Fintype A] [DecidableEq A] (X : Finset (G → A))
    (W : ℕ → ℤ) (hW : ∀ H : AddSubgroup G, ((X ∩ fixA A H).card : ℤ) = W (Nat.card H)) :
    ((X.filter IsShiftSymmetricG).card : ℤ)
      = ∑ h ∈ (rankRad (Nat.card G) (pRank G)).divisors.erase 1,
          coeffA (pRank G) h * W h := by
  rw [card_filter_shiftSymmetricG_IE, relative_regroupG (fun H => ((X ∩ fixA A H).card : ℤ))]
  have hsum : (∑ U : ModTupleG G, mobiusCoeffG U * ((X ∩ fixA A (socSubG U)).card : ℤ))
      = ∑ U : ModTupleG G, mobiusCoeffG U * W (hOfG U) :=
    Finset.sum_congr rfl fun U _ => by rw [hW, card_socSubG]
  rw [hsum, tuple_sum_eq_divisor_sumG, hW, AddSubgroup.card_bot]
  have h1mem : (1 : ℕ) ∈ (rankRad (Nat.card G) (pRank G)).divisors :=
    Nat.one_mem_divisors.mpr (rankRad_ne_zero _ _)
  rw [← Finset.add_sum_erase _ _ h1mem, coeffA_one]
  ring

end ShiftSym.P13.Gen
