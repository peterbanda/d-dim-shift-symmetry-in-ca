/-
Phase H, group 10 (Appendix A) — proof helpers, part 3 ("Core").

The union interpretation of the truncations `q^m(1/e)` on `Z_n^d`:
for a subgroup `K` of order coprime to `p_1 ⋯ p_m`,

  |Fix(K) ∩ ⋃_{C prime order p_i, i < m} Fix(C)| = q^m(1/|K|)       (`core_card`)

(integer shadow `qTruncZ`). Proof: restricted inclusion–exclusion over the family of
order-`p_i` subgroups (`i < m`), converted into the full family with the weight
`H ↦ [H ≤ (p_1⋯p_m)-torsion]·|Fix(K) ∩ Fix(H)|`, the certified weight-generic
`relative_regroup` (E1), and the regrouping of the supported subspace tuples by their rank
vector (`supp_sum_regroup`, via the certified `spanSum_rank_classified_pd`).

No `sorry`; only the standard axioms.
-/
import Shiftsym.Paper.Proofs.P10_AppendixLemmas_Basic

open scoped Classical

namespace ShiftSym.P10

open Finset Module Function

/-- Product of the first `m` primes `p_1 ⋯ p_m`. -/
def primeProd (n m : ℕ) : ℕ := ∏ i ∈ range m, primeAt n i

/-- The first `m` primes as a finset. -/
def lowP (n m : ℕ) : Finset ℕ := (range m).image (primeAt n)

theorem primeAt_dvd_primeProd {n m i : ℕ} (hi : i < m) : primeAt n i ∣ primeProd n m :=
  Finset.dvd_prod_of_mem _ (mem_range.mpr hi)

/-- A prime outside the first `m` primes is coprime to `p_1 ⋯ p_m`. -/
theorem coprime_primeProd {n m q : ℕ} (hm : m ≤ kOf n) (hq : q.Prime)
    (hnot : ∀ i < m, q ≠ primeAt n i) : Nat.Coprime q (primeProd n m) := by
  unfold primeProd
  apply Nat.Coprime.prod_right
  intro i hi
  rw [mem_range] at hi
  exact (Nat.coprime_primes hq (primeAt_prime (by omega))).mpr (hnot i hi)

variable {n d : ℕ}

/-- The restricted family: prime-order subgroups of order `p_i`, `i < m`. -/
noncomputable def lowSubs (n d m : ℕ) [NeZero n] : Finset (AddSubgroup (Lat n d)) :=
  (primeOrderSubs n d).filter (fun C => ∃ i < m, Nat.card C = primeAt n i)

theorem le_latTorsion_card [NeZero n] (K : AddSubgroup (Lat n d)) :
    K ≤ latTorsion n d (Nat.card K) := by
  intro x hx
  rw [mem_latTorsion, ← addOrderOf_dvd_iff_nsmul_eq_zero]
  exact AddSubgroup.addOrderOf_dvd_natCard K hx

/-- **L1**: a set of prime-order subgroups lies in the restricted family iff its join lies
in the `p_1 ⋯ p_m`-torsion. -/
theorem subset_lowSubs_iff [NeZero n] {m : ℕ} (hm : m ≤ kOf n)
    {t : Finset (AddSubgroup (Lat n d))} (ht : t ⊆ primeOrderSubs n d) :
    t ⊆ lowSubs n d m ↔ t.sup id ≤ latTorsion n d (primeProd n m) := by
  constructor
  · intro h
    apply Finset.sup_le
    intro C hC
    obtain ⟨-, i, hi, hCi⟩ := Finset.mem_filter.mp (h hC)
    exact le_trans (le_torsion_of_card_prime hCi)
      (latTorsion_mono (primeAt_dvd_primeProd hi))
  · intro h C hC
    have hCle : C ≤ latTorsion n d (primeProd n m) :=
      le_trans (Finset.le_sup (f := id) hC) h
    have hprime : (Nat.card C).Prime := mem_primeOrderSubs.mp (ht hC)
    refine Finset.mem_filter.mpr ⟨ht hC, ?_⟩
    by_contra hcon
    push Not at hcon
    have hcop := coprime_primeProd hm hprime hcon
    have hbot : C ≤ latTorsion n d (Nat.card C) ⊓ latTorsion n d (primeProd n m) :=
      le_inf (le_torsion_of_card_prime rfl) hCle
    rw [latTorsion_inf_coprime hcop, le_bot_iff] at hbot
    rw [hbot, AddSubgroup.card_bot] at hprime
    exact Nat.not_prime_one hprime

/-- The prime factor `p_{i+1}` as an element of `n.primeFactors`. -/
def pfAt (n : ℕ) (i : ℕ) (hi : i < kOf n) : n.primeFactors := ⟨primeAt n i, primeAt_mem hi⟩

/-- A tuple of subspaces is supported on the first `m` primes. -/
def Supp (m : ℕ) (U : ModTuple n d) : Prop :=
  ∀ p : n.primeFactors, (p : ℕ) ∉ lowP n m → U p = ⊥

private theorem dvdn' {m : ℕ} (p : m.primeFactors) : (p : ℕ) ∣ m :=
  Nat.dvd_of_mem_primeFactors p.2

theorem ofMod_le_socSub [NeZero n] (U : ModTuple n d) (p : n.primeFactors) :
    ofMod (dvdn' p) (U p) ≤ socSub U :=
  Finset.le_sup (f := fun p : n.primeFactors => ofMod (dvdn' p) (U p)) (Finset.mem_univ p)

theorem mem_lowP {m q : ℕ} : q ∈ lowP n m ↔ ∃ i < m, primeAt n i = q := by
  simp [lowP]

/-- **L2**: the socle subgroup of `U` lies in the `p_1 ⋯ p_m`-torsion iff `U` is supported
on the first `m` primes. -/
theorem socSub_le_iff [NeZero n] {m : ℕ} (hm : m ≤ kOf n) (U : ModTuple n d) :
    socSub U ≤ latTorsion n d (primeProd n m) ↔ Supp m U := by
  constructor
  · intro h p hp
    have hcop : Nat.Coprime (p : ℕ) (primeProd n m) := by
      apply coprime_primeProd hm (Nat.prime_of_mem_primeFactors p.2)
      intro i hi hpi
      exact hp (mem_lowP.mpr ⟨i, hi, hpi.symm⟩)
    have h1 : ofMod (dvdn' p) (U p) ≤ latTorsion n d p ⊓ latTorsion n d (primeProd n m) :=
      le_inf (ofMod_le_torsion _ _) (le_trans (ofMod_le_socSub U p) h)
    rw [latTorsion_inf_coprime hcop, le_bot_iff, ← ofMod_bot (dvdn' p)] at h1
    exact ofMod_injective _ h1
  · intro hS
    apply Finset.sup_le
    intro p _
    by_cases hp : (p : ℕ) ∈ lowP n m
    · obtain ⟨i, hi, hpi⟩ := mem_lowP.mp hp
      refine le_trans (ofMod_le_torsion _ _) (latTorsion_mono ?_)
      rw [← hpi]; exact primeAt_dvd_primeProd hi
    · rw [hS p hp, ofMod_bot]; exact bot_le

/-- **L3**: `|socSub U| = hOf U`. -/
theorem card_socSub [NeZero n] (U : ModTuple n d) : Nat.card (socSub U) = hOf U := by
  have hcop : Pairwise (Nat.Coprime on fun p : n.primeFactors => (p : ℕ)) := by
    intro p q hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
      (Nat.prime_of_mem_primeFactors q.2)).mpr fun h => hpq (Subtype.ext h)
  rw [socSub, card_univ_sup_of_torsion (fun p : n.primeFactors => (p : ℕ)) _
    (fun p => ofMod_le_torsion (dvdn' p) (U p)) hcop, hOf]
  exact Finset.prod_congr rfl fun p _ => by rw [card_ofMod, card_submodule_pow]

/-- **L4**: joins of subgroups in coprime torsions have multiplicative order. -/
theorem card_sup_coprime [NeZero n] (K H : AddSubgroup (Lat n d)) {M : ℕ}
    (hH : H ≤ latTorsion n d M) (hcop : Nat.Coprime (Nat.card K) M) :
    Nat.card (K ⊔ H : AddSubgroup (Lat n d)) = Nat.card K * Nat.card H := by
  let L : Fin 2 → AddSubgroup (Lat n d) := ![K, H]
  let mm : Fin 2 → ℕ := ![Nat.card K, M]
  have hL : ∀ i, L i ≤ latTorsion n d (mm i) := by
    intro i; fin_cases i
    · exact le_latTorsion_card K
    · exact hH
  have hc : Pairwise (Nat.Coprime on mm) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hcop
    · exact hcop.symm
    · exact absurd rfl hij
  have h := card_univ_sup_of_torsion mm L hL hc
  have hsup : (Finset.univ.sup L : AddSubgroup (Lat n d)) = K ⊔ H := by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl, Finset.sup_insert,
      Finset.sup_singleton]
    rfl
  rw [hsup, Fin.prod_univ_two] at h
  exact h

variable {σ : ℕ}


theorem fixedByA_eq_fixedByF [NeZero n] (σ : ℕ) (H : AddSubgroup (Lat n d)) :
    fixedByA (Fin σ) H = fixedByF σ H := by
  ext s; rw [mem_fixedByA, mem_fixedByF]

theorem card_fixedByA_fin [NeZero n] (σ : ℕ) (H : AddSubgroup (Lat n d)) :
    (fixedByA (Fin σ) H).card = σ ^ (n ^ d / Nat.card H) := by
  rw [fixedByA_eq_fixedByF, card_fixedByF]

theorem inf'_inter_fix [NeZero n] (σ : ℕ) (X : Finset (Config n d (Fin σ)))
    {t : Finset (AddSubgroup (Lat n d))} (ht : t.Nonempty) :
    t.inf' ht (fun C => X ∩ fixedByA (Fin σ) C) = X ∩ fixedByA (Fin σ) (t.sup id) := by
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

theorem card_fix_inter [NeZero n] (σ : ℕ) (K H : AddSubgroup (Lat n d)) :
    (fixedByA (Fin σ) K ∩ fixedByA (Fin σ) H).card = σ ^ (n ^ d / Nat.card (K ⊔ H : AddSubgroup (Lat n d))) := by
  rw [← card_fixedByA_fin]
  congr 1
  ext s
  simp only [Finset.mem_inter, mem_fixedByA, sup_le_iff]


/-- **Restricted inclusion–exclusion, Möbius form**: for `K` of order coprime to
`p_1 ⋯ p_m`, the configurations fixed by `K` and by some order-`p_i` subgroup (`i < m`)
are counted by the Möbius sum over the tuples supported on the first `m` primes. -/
theorem card_inter_lowUnion [NeZero n] {m : ℕ} (hm : m ≤ kOf n) (σ : ℕ)
    (K : AddSubgroup (Lat n d)) (hK : Nat.Coprime (Nat.card K) (primeProd n m)) :
    ((fixedByA (Fin σ) K ∩ (lowSubs n d m).biUnion (fixedByA (Fin σ))).card : ℤ)
      = ∑ U : ModTuple n d, (if Supp m U then
          mobiusCoeff U * (σ : ℤ) ^ (n ^ d / (Nat.card K * hOf U)) else 0)
        + (σ : ℤ) ^ (n ^ d / Nat.card K) := by
  set X := fixedByA (Fin σ) K with hX
  set T := latTorsion n d (primeProd n m) with hT
  set W : AddSubgroup (Lat n d) → ℤ := fun H => ((X ∩ fixedByA (Fin σ) H).card : ℤ) with hW
  set w' : AddSubgroup (Lat n d) → ℤ := fun H => if H ≤ T then W H else 0 with hw'
  have step1 : ((X ∩ (lowSubs n d m).biUnion (fixedByA (Fin σ))).card : ℤ)
      = ∑ t ∈ (lowSubs n d m).powerset.filter (·.Nonempty),
          (-1 : ℤ) ^ (t.card + 1) * W (t.sup id) := by
    rw [Finset.inter_biUnion, Finset.inclusion_exclusion_card_biUnion]
    rw [← Finset.sum_coe_sort ((lowSubs n d m).powerset.filter (·.Nonempty))]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have hne : t.1.Nonempty := (Finset.mem_filter.mp t.2).2
    rw [inf'_inter_fix σ X hne]
  have step2 : (∑ t ∈ (lowSubs n d m).powerset.filter (·.Nonempty),
          (-1 : ℤ) ^ (t.card + 1) * W (t.sup id))
      = ∑ t : ((primeOrderSubs n d).powerset.filter (·.Nonempty)),
          (-1 : ℤ) ^ (t.1.card + 1) * w' (t.1.sup id) := by
    rw [Finset.sum_coe_sort ((primeOrderSubs n d).powerset.filter (·.Nonempty))
      (fun t => (-1 : ℤ) ^ (t.card + 1) * w' (t.sup id))]
    simp only [hw', mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hts, hne⟩
      have htP : t ⊆ primeOrderSubs n d := fun C hC => (Finset.mem_filter.mp (hts hC)).1
      exact ⟨⟨htP, hne⟩, (subset_lowSubs_iff hm htP).mp hts⟩
    · rintro ⟨⟨htP, hne⟩, hsup⟩
      exact ⟨(subset_lowSubs_iff hm htP).mpr hsup, hne⟩
  have step3 := relative_regroup (n := n) (d := d) w'
  have step4 : w' ⊥ = (σ : ℤ) ^ (n ^ d / Nat.card K) := by
    simp only [hw', bot_le, if_true, hW, fixedByA_bot, Finset.inter_univ, hX,
      card_fixedByA_fin, Nat.cast_pow]
  have step5 : ∀ U : ModTuple n d, mobiusCoeff U * w' (socSub U)
      = if Supp m U then mobiusCoeff U * (σ : ℤ) ^ (n ^ d / (Nat.card K * hOf U)) else 0 := by
    intro U
    by_cases hS : Supp m U
    · have hle : socSub U ≤ T := (socSub_le_iff hm U).mpr hS
      rw [if_pos hS]
      simp only [hw', if_pos hle, hW, hX]
      rw [card_fix_inter, card_sup_coprime K (socSub U) hle hK, card_socSub, Nat.cast_pow]
    · have hle : ¬ socSub U ≤ T := fun h => hS ((socSub_le_iff hm U).mp h)
      rw [if_neg hS]
      simp only [hw', if_neg hle, mul_zero]
  rw [step1, step2, step3, step4]
  congr 1
  exact Finset.sum_congr rfl (fun U _ => step5 U)


/-! ### Regrouping the supported tuples by their rank vector -/

/-- The increasing bijection `Fin k ≃ n.primeFactors`. -/
noncomputable def eqv (n : ℕ) : Fin (kOf n) ≃ n.primeFactors :=
  (n.primeFactors.orderIsoOfFin (card_pf n)).toEquiv

theorem eqv_coe (n : ℕ) (i : Fin (kOf n)) : ((eqv n i : n.primeFactors) : ℕ) = primeAt n i := by
  rw [primeAt_eq_emb i.2]; rfl

/-- The rank target attached to a vector `v : Fin m → Fin (d+1)`. -/
noncomputable def tgt (m : ℕ) (v : Fin m → Fin (d + 1)) (p : n.primeFactors) : ℕ :=
  if h : (((eqv n).symm p : Fin (kOf n)) : ℕ) < m then ((v ⟨_, h⟩ : Fin (d + 1)) : ℕ) else 0

theorem tgt_le (m : ℕ) (v : Fin m → Fin (d + 1)) (p : n.primeFactors) : tgt m v p ≤ d := by
  unfold tgt
  split_ifs
  · exact Nat.lt_succ_iff.mp (v _).2
  · exact Nat.zero_le _

theorem tgt_eqv (m : ℕ) (v : Fin m → Fin (d + 1)) (i : Fin (kOf n)) :
    tgt m v (eqv n i) = if h : (i : ℕ) < m then ((v ⟨i, h⟩ : Fin (d + 1)) : ℕ) else 0 := by
  unfold tgt
  simp only [Equiv.symm_apply_apply]

/-- **GL**: a product over the prime factors evaluated at the rank target is the product
over the first `m` primes. -/
theorem prod_tgt {M : Type*} [CommMonoid M] {m : ℕ} (hm : m ≤ kOf n) (F : ℕ → ℕ → M)
    (hF : ∀ p, F p 0 = 1) (v : Fin m → Fin (d + 1)) :
    ∏ p : n.primeFactors, F p (tgt m v p) = ∏ i : Fin m, F (primeAt n i) (v i) := by
  rw [← (eqv n).prod_comp]
  simp only [tgt_eqv, eqv_coe]
  set G : ℕ → M := fun i => F (primeAt n i) (if h : i < m then ((v ⟨i, h⟩ : Fin (d + 1)) : ℕ) else 0)
    with hG
  have h1 : ∏ i : Fin (kOf n), F (primeAt n i)
      (if h : (i : ℕ) < m then ((v ⟨i, h⟩ : Fin (d + 1)) : ℕ) else 0)
      = ∏ i : Fin (kOf n), G i := rfl
  have h2 : ∏ i : Fin m, F (primeAt n i) (v i) = ∏ i : Fin m, G i := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hG, dif_pos i.2]
  rw [h1, h2, Fin.prod_univ_eq_prod_range G, Fin.prod_univ_eq_prod_range G]
  symm
  apply Finset.prod_subset (Finset.range_subset_range.mpr hm)
  intro i _ hi
  rw [Finset.mem_range, not_lt] at hi
  simp only [hG, dif_neg (show ¬ i < m by omega), hF]

/-- The rank vector of a tuple, read off at the first `m` primes. -/
noncomputable def rkv {m : ℕ} (hm : m ≤ kOf n) (U : ModTuple n d) : Fin m → Fin (d + 1) :=
  fun i => ⟨finrank (ZMod ((eqv n (Fin.castLE hm i) : n.primeFactors) : ℕ))
      (U (eqv n (Fin.castLE hm i))),
    Nat.lt_succ_iff.mpr (by
      have := Submodule.finrank_le (U (eqv n (Fin.castLE hm i)))
      rwa [finrank_pi_d] at this)⟩

theorem fiber_eq [NeZero n] {m : ℕ} (hm : m ≤ kOf n) (v : Fin m → Fin (d + 1)) :
    (Finset.univ.filter (fun U : ModTuple n d => Supp m U)).filter (fun U => rkv hm U = v)
      = Fintype.piFinset (fun p : n.primeFactors =>
          Finset.univ.filter (fun W : Submodule (ZMod (p : ℕ)) (Fin d → ZMod (p : ℕ)) =>
            finrank (ZMod (p : ℕ)) W = tgt m v p)) := by
  ext U
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hS, hv⟩ p
    obtain ⟨i, rfl⟩ := (eqv n).surjective p
    rw [tgt_eqv]
    split_ifs with h
    · have := congrArg (fun w => ((w ⟨i, h⟩ : Fin (d + 1)) : ℕ)) hv
      simp only [rkv] at this
      rw [← this]
      rfl
    · have hp : ((eqv n i : n.primeFactors) : ℕ) ∉ lowP n m := by
        rw [eqv_coe, mem_lowP]
        rintro ⟨i', hi', heq⟩
        have := primeAt_inj (by omega) i.2 heq
        omega
      rw [hS _ hp, finrank_bot]
  · intro hU
    refine ⟨fun p hp => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := (eqv n).surjective p
      have h0 := hU (eqv n i)
      rw [tgt_eqv, dif_neg] at h0
      · exact Submodule.finrank_eq_zero.mp h0
      · intro h
        exact hp (by rw [eqv_coe, mem_lowP]; exact ⟨i, h, rfl⟩)
    · funext i
      apply Fin.ext
      simp only [rkv]
      rw [hU, tgt_eqv, dif_pos (by simp)]
      rfl

theorem hOf_of_fiber [NeZero n] {m : ℕ} (hm : m ≤ kOf n) (v : Fin m → Fin (d + 1))
    (U : ModTuple n d) (hU : ∀ p : n.primeFactors, finrank (ZMod (p : ℕ)) (U p) = tgt m v p) :
    hOf U = ∏ i : Fin m, primeAt n i ^ ((v i : Fin (d + 1)) : ℕ) := by
  rw [hOf]
  simp only [hU]
  exact prod_tgt hm (fun p r => p ^ r) (fun p => pow_zero p) v

/-- **RG**: the supported Möbius sum, regrouped by rank vectors. -/
theorem supp_sum_regroup [NeZero n] {m : ℕ} (hm : m ≤ kOf n) (f : ℕ → ℤ) :
    ∑ U : ModTuple n d, (if Supp m U then mobiusCoeff U * f (hOf U) else 0)
      = ∑ v : Fin m → Fin (d + 1),
          (-1 : ℤ) ^ (1 + ∑ i : Fin m, ((v i : Fin (d + 1)) : ℕ)) *
            (∏ i : Fin m, (rdCoeff (primeAt n i) ((v i : Fin (d + 1)) : ℕ) d : ℤ)) *
            f (∏ i : Fin m, primeAt n i ^ ((v i : Fin (d + 1)) : ℕ)) := by
  rw [← Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun U : ModTuple n d => Supp m U))
    (t := (Finset.univ : Finset (Fin m → Fin (d + 1)))) (g := rkv hm)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [fiber_eq hm v]
  have hconst : ∀ U ∈ Fintype.piFinset (fun p : n.primeFactors =>
        Finset.univ.filter (fun W : Submodule (ZMod (p : ℕ)) (Fin d → ZMod (p : ℕ)) =>
          finrank (ZMod (p : ℕ)) W = tgt m v p)),
      mobiusCoeff U * f (hOf U)
        = mobiusCoeff U * f (∏ i : Fin m, primeAt n i ^ ((v i : Fin (d + 1)) : ℕ)) := by
    intro U hU
    rw [Fintype.mem_piFinset] at hU
    rw [hOf_of_fiber hm v U (fun p => (Finset.mem_filter.mp (hU p)).2)]
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul]
  congr 1
  simp only [mobiusCoeff, Finset.sum_neg_distrib]
  rw [← Finset.prod_univ_sum]
  have hclass : ∀ p : n.primeFactors,
      ∑ W ∈ Finset.univ.filter (fun W : Submodule (ZMod (p : ℕ)) (Fin d → ZMod (p : ℕ)) =>
          finrank (ZMod (p : ℕ)) W = tgt m v p), spanSum W
        = (-1 : ℤ) ^ (tgt m v p) * ((p : ℕ) : ℤ) ^ ((tgt m v p).choose 2)
            * (gaussBinom (p : ℕ) d (tgt m v p) : ℤ) :=
    fun p => spanSum_rank_classified_pd (tgt_le m v p)
  rw [Finset.prod_congr rfl (fun p _ => hclass p)]
  rw [prod_tgt hm (fun p r => (-1 : ℤ) ^ r * (p : ℤ) ^ (r.choose 2) * (gaussBinom p d r : ℤ))
    (fun p => by simp [gaussBinom]) v]
  have hsplit : ∀ i : Fin m,
      (-1 : ℤ) ^ ((v i : Fin (d + 1)) : ℕ) * (primeAt n i : ℤ) ^ (((v i : Fin (d + 1)) : ℕ).choose 2)
          * (gaussBinom (primeAt n i) d ((v i : Fin (d + 1)) : ℕ) : ℤ)
        = (-1 : ℤ) ^ ((v i : Fin (d + 1)) : ℕ)
          * (rdCoeff (primeAt n i) ((v i : Fin (d + 1)) : ℕ) d : ℤ) := by
    intro i; rw [rdCoeff]; push_cast; ring
  rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, pow_add, pow_one]
  ring

/-- **The core lemma**: for `K` of order coprime to `p_1 ⋯ p_m`,
`|Fix(K) ∩ ⋃_{C : |C| = p_i, i<m} Fix(C)| = q^m(1/|K|)` (integer shadow). -/
theorem core_card [NeZero n] {m : ℕ} (hm : m ≤ kOf n) (σ : ℕ)
    (K : AddSubgroup (Lat n d)) (hK : Nat.Coprime (Nat.card K) (primeProd n m)) :
    ((fixedByA (Fin σ) K ∩ (lowSubs n d m).biUnion (fixedByA (Fin σ))).card : ℤ)
      = qTruncZ n d σ m (Nat.card K) := by
  rw [card_inter_lowUnion hm σ K hK,
    supp_sum_regroup hm (fun h => (σ : ℤ) ^ (n ^ d / (Nat.card K * h))), qTruncZ,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin m → Fin (d + 1)))]
  simp [rdCoeff, gaussBinom]

end ShiftSym.P10
