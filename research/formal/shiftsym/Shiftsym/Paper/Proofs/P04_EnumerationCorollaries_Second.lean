/-
Phase H, group 04 — proofs, part 5: the **second derivation** of eq. (2)
(§4.3 of the paper), carried out along the paper's route and WITHOUT the
certified first derivation (`enumeration_proved` is not used here):

  σ^N − ∑_{K ≤ A} μ(0,K) σ^{N/|K|} = right side of eq. (2),

via multiplicativity of `μ` (`cmu_mult`), Hall's evaluation on each `A_p`
(`cmu_bot_eq_hallW`), the reindexing of the surviving (socle) subgroups by
tuples of subspaces `U_p ≤ F_p^d`, and the Grassmannian count `[d r]_p`.
-/
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Mobius

open Finset

namespace ShiftSym.P04

open ShiftSym Module

section Second

open scoped Classical

variable {n d : ℕ} [NeZero n]

theorem primComp_inf_primComp (hn : 2 ≤ n) {p q : ℕ} (hp : p ∈ n.primeFactors)
    (hq : q ∈ n.primeFactors) (hpq : p ≠ q) :
    primComp n d p ⊓ primComp n d q = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.mp hy
  rw [AddSubgroup.mem_bot, ← crt_smul_self hn hp h1, crt_smul_eq_zero hn hq hp hpq h2]

theorem proj_bot (p : ℕ) : proj (⊥ : AddSubgroup (Lat n d)) p = ⊥ := by
  rw [proj, bot_inf_eq]
  simp

/-- `μ(0, K ∩ A_p)` computed in `L(A)` is the `p`-factor of the multiplicativity. -/
theorem cmu_bot_inf (hn : 2 ≤ n) (K : AddSubgroup (Lat n d)) (p : n.primeFactors) :
    cmu ⊥ (K ⊓ primComp n d (p : ℕ))
      = cmu (⊥ : AddSubgroup ↥(primComp n d (p : ℕ))) (proj K (p : ℕ)) := by
  rw [cmu_mult hn, Finset.prod_eq_single p]
  · rw [proj_bot]
    congr 1
    rw [proj, proj, inf_assoc, inf_idem]
  · intro q _ hqp
    rw [proj_bot]
    have : proj (K ⊓ primComp n d (p : ℕ)) (q : ℕ) = ⊥ := by
      rw [proj, inf_assoc,
        primComp_inf_primComp hn p.2 q.2 (fun h => hqp (Subtype.ext h).symm), inf_bot_eq]
      simp
    rw [this, cmu_self]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- `μ(0,K) = ∏_p μ(0, K ∩ A_p)` (all values in `L(A)`). -/
theorem cmu_bot_prod (hn : 2 ≤ n) (K : AddSubgroup (Lat n d)) :
    cmu ⊥ K = ∏ p : n.primeFactors, cmu ⊥ (K ⊓ primComp n d (p : ℕ)) := by
  rw [cmu_mult hn]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [proj_bot, cmu_bot_inf hn]

/-- `μ(0,K) = ∏_p hallW_p(K ∩ A_p)` (multiplicativity + Hall). -/
theorem cmu_bot_eq_prod_hallW (hn : 2 ≤ n) (K : AddSubgroup (Lat n d)) :
    cmu ⊥ K = ∏ p : n.primeFactors,
      hallW (Nat.dvd_of_mem_primeFactors p.2) (K ⊓ primComp n d (p : ℕ)) := by
  rw [cmu_bot_prod hn]
  refine Finset.prod_congr rfl fun p _ => ?_
  exact cmu_bot_eq_hallW _ _ inf_le_right

/-- The socle subgroup attached to a tuple of subspaces `U_p ≤ F_p^d`. -/
noncomputable def socP (U : ModTuple n d) : AddSubgroup (Lat n d) :=
  Finset.univ.sup fun p : n.primeFactors => ofMod (Nat.dvd_of_mem_primeFactors p.2) (U p)

theorem sup_inf_eq (hn : 2 ≤ n) (L : n.primeFactors → AddSubgroup (Lat n d))
    (hL : ∀ q, L q ≤ primComp n d (q : ℕ)) (p : n.primeFactors) :
    Finset.univ.sup L ⊓ primComp n d (p : ℕ) = L p := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxK, hxp⟩ := AddSubgroup.mem_inf.mp hx
    have hle : Finset.univ.sup L ≤ (L p).comap (smulHom (n := n) (d := d) (crtCoeff n p)) := by
      refine Finset.sup_le fun q _ => ?_
      intro y hy
      rw [AddSubgroup.mem_comap, smulHom_apply]
      by_cases hqp : q = p
      · subst hqp
        rw [crt_smul_self hn q.2 (hL q hy)]
        exact hy
      · rw [crt_smul_eq_zero hn q.2 p.2 (fun h => hqp (Subtype.ext h).symm) (hL q hy)]
        exact AddSubgroup.zero_mem _
    have := hle hxK
    rw [AddSubgroup.mem_comap, smulHom_apply, crt_smul_self hn p.2 hxp] at this
    exact this
  · exact le_inf (Finset.le_sup (f := L) (Finset.mem_univ p)) (hL p)

theorem socP_inf (hn : 2 ≤ n) (U : ModTuple n d) (p : n.primeFactors) :
    socP U ⊓ primComp n d (p : ℕ) = ofMod (Nat.dvd_of_mem_primeFactors p.2) (U p) :=
  sup_inf_eq hn _ (fun q => (ofMod_le_torsion _ _).trans latTorsion_le_primComp) p

theorem split_sup (hn : 2 ≤ n) (K : AddSubgroup (Lat n d)) :
    Finset.univ.sup (fun p : n.primeFactors => K ⊓ primComp n d (p : ℕ)) = K := by
  rw [Finset.sup_univ_eq_iSup]
  exact (split_eq' hn K).symm

theorem coprime_primeFactors_coe :
    Pairwise (Function.onFun Nat.Coprime fun p : n.primeFactors => (p : ℕ)) := by
  intro p q hpq
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
    (Nat.prime_of_mem_primeFactors q.2)).mpr fun h => hpq (Subtype.ext h)

theorem card_socP (U : ModTuple n d) :
    Nat.card (socP U) = ∏ p : n.primeFactors, (p : ℕ) ^ finrank (ZMod (p : ℕ)) (U p) := by
  unfold socP
  rw [card_univ_sup_of_torsion (fun p : n.primeFactors => (p : ℕ)) _
    (fun p => ofMod_le_torsion (Nat.dvd_of_mem_primeFactors p.2) (U p)) coprime_primeFactors_coe]
  exact Finset.prod_congr rfl fun p _ => by rw [card_ofMod, card_submodule_pow]

/-- The Möbius weight of a tuple: `∏_p (-1)^{r_p} p^{C(r_p,2)}`. -/
noncomputable def tupleWeight (U : ModTuple n d) : ℤ :=
  ∏ p : n.primeFactors, ((-1 : ℤ) ^ finrank (ZMod (p : ℕ)) (U p)
    * ((p : ℕ) : ℤ) ^ ((finrank (ZMod (p : ℕ)) (U p)).choose 2))

/-- Only socle subgroups survive; they are indexed by tuples of subspaces. -/
theorem sum_mu_eq_tuple_sum (hn : 2 ≤ n) (w : AddSubgroup (Lat n d) → ℤ) :
    ∑ K, cmu ⊥ K * w K = ∑ U : ModTuple n d, tupleWeight U * w (socP U) := by
  have hpd : ∀ p : n.primeFactors, (p : ℕ) ∣ n := fun p => Nat.dvd_of_mem_primeFactors p.2
  -- restrict to the subgroups with every primary part inside the p-torsion
  have hrestrict : ∑ K, cmu ⊥ K * w K
      = ∑ K ∈ univ.filter (fun K : AddSubgroup (Lat n d) =>
          ∀ p : n.primeFactors, K ⊓ primComp n d (p : ℕ) ≤ latTorsion n d (p : ℕ)),
        cmu ⊥ K * w K := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun K _ hK => ?_
    rw [Finset.mem_filter] at hK
    push Not at hK
    obtain ⟨p, hp⟩ := hK (Finset.mem_univ _)
    rw [cmu_bot_eq_prod_hallW hn, Finset.prod_eq_zero (Finset.mem_univ p), zero_mul]
    unfold hallW
    rw [if_neg hp]
  rw [hrestrict]
  refine Finset.sum_nbij' (fun K => fun p : n.primeFactors => toMod (hpd p) (K ⊓ primComp n d (p : ℕ)))
    socP ?_ ?_ ?_ ?_ ?_
  · intro K _
    exact Finset.mem_univ _
  · intro U _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun p => ?_⟩
    rw [socP_inf hn U p]
    exact ofMod_le_torsion _ _
  · intro K hK
    rw [Finset.mem_filter] at hK
    unfold socP
    have : (fun p : n.primeFactors =>
        ofMod (Nat.dvd_of_mem_primeFactors p.2) (toMod (hpd p) (K ⊓ primComp n d (p : ℕ))))
        = fun p : n.primeFactors => K ⊓ primComp n d (p : ℕ) := by
      funext p
      exact ofMod_toMod _ (hK.2 p)
    rw [this, split_sup hn K]
  · intro U _
    funext p
    rw [socP_inf hn U p, toMod_ofMod]
  · intro K hK
    rw [Finset.mem_filter] at hK
    have hleft : socP (fun p : n.primeFactors => toMod (hpd p) (K ⊓ primComp n d (p : ℕ))) = K := by
      unfold socP
      have : (fun p : n.primeFactors =>
          ofMod (Nat.dvd_of_mem_primeFactors p.2) (toMod (hpd p) (K ⊓ primComp n d (p : ℕ))))
          = fun p : n.primeFactors => K ⊓ primComp n d (p : ℕ) := by
        funext p
        exact ofMod_toMod _ (hK.2 p)
      rw [this, split_sup hn K]
    rw [hleft, cmu_bot_eq_prod_hallW hn, tupleWeight]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    unfold hallW
    rw [if_pos (hK.2 p)]

/-! ### Grouping the tuples by their rank vector -/

theorem card_tuples_of_rank (r : n.primeFactors → ℕ) (hr : ∀ p, r p ≤ d) :
    (univ.filter fun U : ModTuple n d =>
        (fun p : n.primeFactors => finrank (ZMod (p : ℕ)) (U p)) = r).card
      = ∏ p : n.primeFactors, gaussBinom (p : ℕ) d (r p) := by
  have hset : (univ.filter fun U : ModTuple n d =>
        (fun p : n.primeFactors => finrank (ZMod (p : ℕ)) (U p)) = r)
      = Fintype.piFinset fun p : n.primeFactors =>
          univ.filter fun W : Submodule (ZMod (p : ℕ)) (Fin d → ZMod (p : ℕ)) =>
            finrank (ZMod (p : ℕ)) W = r p := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, funext_iff]
  rw [hset, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← card_submodule_finrank (Nat.prime_of_mem_primeFactors p.2) (hr p),
    Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem tuple_sum_eq_rank_sum (G : (n.primeFactors → ℕ) → ℤ) :
    ∑ U : ModTuple n d, G (fun p : n.primeFactors => finrank (ZMod (p : ℕ)) (U p))
      = ∑ r ∈ Fintype.piFinset (fun _ : n.primeFactors => Finset.range (d + 1)),
          (∏ p : n.primeFactors, (gaussBinom (p : ℕ) d (r p) : ℤ)) * G r := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ)
    (t := Fintype.piFinset (fun _ : n.primeFactors => Finset.range (d + 1)))
    (g := fun U : ModTuple n d => fun p : n.primeFactors => finrank (ZMod (p : ℕ)) (U p))]
  · refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : ∀ p, r p ≤ d := fun p => by
      have := Fintype.mem_piFinset.mp hr p
      rw [Finset.mem_range] at this
      omega
    rw [Finset.sum_congr rfl (g := fun _ => G r) (fun U hU => by
      rw [(Finset.mem_filter.mp hU).2]), Finset.sum_const, card_tuples_of_rank r hr',
      nsmul_eq_mul]
    push_cast
    rfl
  · intro U _
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have h := Submodule.finrank_le (U p)
    rwa [finrank_pi_d] at h

/-- `Fin k ≃ n.primeFactors` (increasing enumeration). -/
noncomputable def primeEquiv (n : ℕ) : Fin n.primeFactors.card ≃ n.primeFactors :=
  (n.primeFactors.orderIsoOfFin rfl).toEquiv

theorem primeEquiv_coe (n : ℕ) (i : Fin n.primeFactors.card) :
    ((primeEquiv n i : n.primeFactors) : ℕ) = primeSeq n i := by
  simp [primeEquiv, primeSeq, Finset.coe_orderIsoOfFin_apply]

theorem rank_sum_eq_rankVector_sum (H : (n.primeFactors → ℕ) → ℤ) :
    ∑ r ∈ Fintype.piFinset (fun _ : n.primeFactors => Finset.range (d + 1)), H r
      = ∑ v ∈ allRankVectors n d, H (fun p => v ((primeEquiv n).symm p)) := by
  symm
  refine Finset.sum_nbij' (fun v => fun p => v ((primeEquiv n).symm p))
    (fun r => fun i => r (primeEquiv n i)) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    rw [Fintype.mem_piFinset]
    intro p
    exact Fintype.mem_piFinset.mp hv _
  · intro r hr
    rw [allRankVectors, Fintype.mem_piFinset]
    intro i
    exact Fintype.mem_piFinset.mp hr _
  · intro v _
    funext i
    simp
  · intro r _
    funext p
    simp
  · intro v _
    rfl

theorem prod_primeEquiv {M : Type*} [CommMonoid M] (v : Fin n.primeFactors.card → ℕ)
    (f : ℕ → ℕ → M) :
    ∏ p : n.primeFactors, f (p : ℕ) (v ((primeEquiv n).symm p))
      = ∏ i, f (primeSeq n i) (v i) := by
  rw [← Equiv.prod_comp (primeEquiv n)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Equiv.symm_apply_apply, primeEquiv_coe]

/-- **The second derivation of eq. (2)** (§4.3), independent of `enumeration_proved`. -/
theorem secondDerivation_independent (hn : 2 ≤ n) (σ : ℕ) :
    (σ : ℤ) ^ (n ^ d) - ∑ K ∈ allSubgroups n d,
        subgroupMu n d ⊥ K * (σ : ℤ) ^ (n ^ d / Nat.card K)
      = mainFormulaRHS n d σ := by
  have hsum : ∑ K ∈ allSubgroups n d, subgroupMu n d ⊥ K * (σ : ℤ) ^ (n ^ d / Nat.card K)
      = ∑ v ∈ allRankVectors n d,
          (-1 : ℤ) ^ (∑ i, v i) * (∏ i, (rdCoeff (primeSeq n i) (v i) d : ℤ))
            * (σ : ℤ) ^ (n ^ d / ∏ i, primeSeq n i ^ v i) := by
    have h1 : ∑ K ∈ allSubgroups n d, subgroupMu n d ⊥ K * (σ : ℤ) ^ (n ^ d / Nat.card K)
        = ∑ K : AddSubgroup (Lat n d), cmu ⊥ K * (σ : ℤ) ^ (n ^ d / Nat.card K) := rfl
    rw [h1, sum_mu_eq_tuple_sum hn]
    simp_rw [card_socP]
    have h2 : ∑ U : ModTuple n d, tupleWeight U
          * (σ : ℤ) ^ (n ^ d / ∏ p : n.primeFactors, (p : ℕ) ^ finrank (ZMod (p : ℕ)) (U p))
        = ∑ r ∈ Fintype.piFinset (fun _ : n.primeFactors => Finset.range (d + 1)),
            (∏ p : n.primeFactors, (gaussBinom (p : ℕ) d (r p) : ℤ))
              * ((∏ p : n.primeFactors, ((-1 : ℤ) ^ r p * ((p : ℕ) : ℤ) ^ ((r p).choose 2)))
                * (σ : ℤ) ^ (n ^ d / ∏ p : n.primeFactors, (p : ℕ) ^ r p)) :=
      tuple_sum_eq_rank_sum (fun r => (∏ p : n.primeFactors, ((-1 : ℤ) ^ r p
        * ((p : ℕ) : ℤ) ^ ((r p).choose 2)))
        * (σ : ℤ) ^ (n ^ d / ∏ p : n.primeFactors, (p : ℕ) ^ r p))
    rw [h2, rank_sum_eq_rankVector_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [prod_primeEquiv v (fun p r => (gaussBinom p d r : ℤ)),
      prod_primeEquiv v (fun p r => (-1 : ℤ) ^ r * (p : ℤ) ^ (r.choose 2)),
      prod_primeEquiv v (fun p r => p ^ r)]
    rw [← mul_assoc]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold rdCoeff
    push_cast
    ring
  rw [hsum]
  have h0 : (0 : Fin n.primeFactors.card → ℕ) ∈ allRankVectors n d := by
    rw [mem_allRankVectors]; intro i; exact Nat.zero_le _
  rw [← Finset.add_sum_erase _ _ h0]
  have herase : (allRankVectors n d).erase 0 = rankVectors n d := by
    rw [rankVectors, Finset.filter_ne']
  rw [herase]
  simp only [Pi.zero_apply, Finset.sum_const_zero, pow_zero, rdCoeff_zero, Nat.cast_one,
    Finset.prod_const_one, one_mul, Nat.div_one]
  rw [mainFormulaRHS, sub_add_eq_sub_sub, sub_self, zero_sub, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [pow_add, pow_one]
  ring

end Second

end ShiftSym.P04
