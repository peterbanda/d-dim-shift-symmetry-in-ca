/-
Phase H, group 04 — proofs, part 1: formula-level results.

* the rank-vector ↔ divisor bridge (`h = ∏ pᵢ^{vᵢ}`), exponent integrality
  and exactness of the `ℕ`-quotient;
* Corollary 4.4 and its special cases, [banda2019, Cor. E.20];
* the formula-level parts of Remark 4.5 (n = 1, σ = 1, d = 2 / Thm E.19,
  the per-prime identities, CG Lemma 7(iv) complement identity);
* the §4.4 reference values.
-/
import Shiftsym.Paper.S04_EnumerationCorollaries
import Shiftsym.Lemmas.Evaluate
import Shiftsym.Lemmas.PrimeCase

open Finset

namespace ShiftSym.P04

open ShiftSym

/-! ### `primeSeq` bookkeeping -/

theorem primeSeq_mem (n : ℕ) (i : Fin n.primeFactors.card) :
    primeSeq n i ∈ n.primeFactors :=
  Finset.orderEmbOfFin_mem _ _ i

theorem primeSeq_prime (n : ℕ) (i : Fin n.primeFactors.card) : (primeSeq n i).Prime :=
  Nat.prime_of_mem_primeFactors (primeSeq_mem n i)

theorem primeSeq_injective (n : ℕ) : Function.Injective (primeSeq n) :=
  (n.primeFactors.orderEmbOfFin rfl).injective

theorem prod_primeSeq {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∏ i, f (primeSeq n i) = ∏ p ∈ n.primeFactors, f p := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ n.primeFactors rfl]
  rw [Finset.prod_map]
  rfl

theorem sum_primeSeq {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ i, f (primeSeq n i) = ∑ p ∈ n.primeFactors, f p := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ n.primeFactors rfl]
  rw [Finset.sum_map]
  rfl

theorem exists_primeSeq_eq {n p : ℕ} (hp : p ∈ n.primeFactors) :
    ∃ i, primeSeq n i = p := by
  have h := Finset.range_orderEmbOfFin n.primeFactors rfl
  have : p ∈ Set.range (n.primeFactors.orderEmbOfFin rfl) := by
    rw [h]; exact hp
  obtain ⟨i, hi⟩ := this
  exact ⟨i, hi⟩

/-- `φ(v) = ∏ᵢ pᵢ^{vᵢ}`. -/
def phi (n : ℕ) (v : Fin n.primeFactors.card → ℕ) : ℕ := ∏ i, primeSeq n i ^ v i

theorem phi_ne_zero (n : ℕ) (v : Fin n.primeFactors.card → ℕ) : phi n v ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (primeSeq_prime n i).ne_zero

theorem factorization_phi (n : ℕ) (v : Fin n.primeFactors.card → ℕ) :
    (phi n v).factorization = ∑ i, Finsupp.single (primeSeq n i) (v i) := by
  unfold phi
  rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (primeSeq_prime n i).ne_zero)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (primeSeq_prime n i).factorization_pow

theorem factorization_phi_apply (n : ℕ) (v : Fin n.primeFactors.card → ℕ)
    (j : Fin n.primeFactors.card) : (phi n v).factorization (primeSeq n j) = v j := by
  rw [factorization_phi, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Finsupp.single_apply, if_neg]
    exact fun h => hij (primeSeq_injective n h)
  · intro h; exact absurd (Finset.mem_univ j) h

theorem factorization_phi_apply_of_notMem (n : ℕ) (v : Fin n.primeFactors.card → ℕ)
    {q : ℕ} (hq : q ∉ n.primeFactors) : (phi n v).factorization q = 0 := by
  rw [factorization_phi, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finsupp.single_apply, if_neg]
  intro h; exact hq (h ▸ primeSeq_mem n i)

theorem support_factorization_phi_subset (n : ℕ) (v : Fin n.primeFactors.card → ℕ) :
    (phi n v).factorization.support ⊆ n.primeFactors := by
  intro q hq
  by_contra h
  exact (Finsupp.mem_support_iff.mp hq) (factorization_phi_apply_of_notMem n v h)

theorem primeFactors_phi_subset (n : ℕ) (v : Fin n.primeFactors.card → ℕ) :
    (phi n v).primeFactors ⊆ n.primeFactors := by
  rw [← Nat.support_factorization]; exact support_factorization_phi_subset n v

theorem rad_pow_eq_phi (n d : ℕ) : rad n ^ d = phi n (fun _ => d) := by
  unfold phi rad
  rw [← Finset.prod_pow, prod_primeSeq n (fun p => p ^ d)]

theorem mem_allRankVectors {n d : ℕ} {v : Fin n.primeFactors.card → ℕ} :
    v ∈ allRankVectors n d ↔ ∀ i, v i ≤ d := by
  simp [allRankVectors, Fintype.mem_piFinset]

theorem mem_rankVectors {n d : ℕ} {v : Fin n.primeFactors.card → ℕ} :
    v ∈ rankVectors n d ↔ (∀ i, v i ≤ d) ∧ v ≠ 0 := by
  simp only [rankVectors, Finset.mem_filter, mem_allRankVectors]

theorem phi_dvd_rad_pow {n d : ℕ} {v : Fin n.primeFactors.card → ℕ} (hv : ∀ i, v i ≤ d) :
    phi n v ∣ rad n ^ d := by
  rw [rad_pow_eq_phi]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => pow_dvd_pow _ (hv i)

theorem phi_factorization_eq (n : ℕ) {h : ℕ} (hh0 : h ≠ 0)
    (hsub : h.primeFactors ⊆ n.primeFactors) :
    phi n (fun i => h.factorization (primeSeq n i)) = h := by
  unfold phi
  rw [prod_primeSeq n (fun p => p ^ h.factorization p)]
  calc ∏ p ∈ n.primeFactors, p ^ h.factorization p
      = ∏ p ∈ h.primeFactors, p ^ h.factorization p := by
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

theorem primeFactors_subset_of_dvd_rad_pow {n d h : ℕ} (hh : h ∣ rad n ^ d) :
    h.primeFactors ⊆ n.primeFactors := by
  have hrad0 : rad n ^ d ≠ 0 := pow_ne_zero _ rad_ne_zero
  refine (Nat.primeFactors_mono hh hrad0).trans ?_
  rw [rad_pow_eq_phi]; exact primeFactors_phi_subset n _

theorem factorization_le_of_dvd_rad_pow {n d h : ℕ} (hh : h ∣ rad n ^ d)
    (i : Fin n.primeFactors.card) : h.factorization (primeSeq n i) ≤ d := by
  have hrad0 : rad n ^ d ≠ 0 := pow_ne_zero _ rad_ne_zero
  have hh0 : h ≠ 0 := fun h0 => hrad0 (zero_dvd_iff.mp (h0 ▸ hh))
  have hle := (Nat.factorization_le_iff_dvd hh0 hrad0).mpr hh
  have := Finsupp.le_def.mp hle (primeSeq n i)
  rwa [rad_pow_eq_phi, factorization_phi_apply] at this

theorem phi_eq_one_iff {n : ℕ} (v : Fin n.primeFactors.card → ℕ) : phi n v = 1 ↔ v = 0 := by
  constructor
  · intro h
    funext j
    have := factorization_phi_apply n v j
    rw [h, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply] at this
    exact this.symm
  · rintro rfl
    simp [phi]

/-- **The rank-vector ↔ divisor transport.** -/
theorem sum_rankVectors_eq {M : Type*} [AddCommMonoid M] (n d : ℕ) (F : ℕ → M) :
    ∑ v ∈ rankVectors n d, F (phi n v) = ∑ h ∈ (rad n ^ d).divisors.erase 1, F h := by
  have hrad0 : rad n ^ d ≠ 0 := pow_ne_zero _ rad_ne_zero
  refine Finset.sum_nbij' (fun v => phi n v) (fun h i => h.factorization (primeSeq n i))
    ?_ ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_rankVectors] at hv
    rw [Finset.mem_erase, Nat.mem_divisors]
    exact ⟨fun h1 => hv.2 ((phi_eq_one_iff v).mp h1), phi_dvd_rad_pow hv.1, hrad0⟩
  · intro h hh
    rw [Finset.mem_erase, Nat.mem_divisors] at hh
    rw [mem_rankVectors]
    refine ⟨fun i => factorization_le_of_dvd_rad_pow hh.2.1 i, fun h0 => hh.1 ?_⟩
    have hh0 : h ≠ 0 := fun h0' => hrad0 (zero_dvd_iff.mp (h0' ▸ hh.2.1))
    rw [← phi_factorization_eq n hh0 (primeFactors_subset_of_dvd_rad_pow hh.2.1), h0,
      (phi_eq_one_iff 0).mpr rfl]
  · intro v _
    funext i
    exact factorization_phi_apply n v i
  · intro h hh
    rw [Finset.mem_erase, Nat.mem_divisors] at hh
    have hh0 : h ≠ 0 := fun h0' => hrad0 (zero_dvd_iff.mp (h0' ▸ hh.2.1))
    exact phi_factorization_eq n hh0 (primeFactors_subset_of_dvd_rad_pow hh.2.1)
  · intro v _
    rfl

theorem rdCoeff_zero (p d : ℕ) : rdCoeff p 0 d = 1 := by
  simp [rdCoeff, gaussBinom]

theorem bigOmega_phi (n : ℕ) (v : Fin n.primeFactors.card → ℕ) :
    bigOmega (phi n v) = ∑ i, v i := by
  unfold bigOmega
  rw [factorization_phi, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finsupp.sum_single_index rfl

theorem coeffOf_phi (n d : ℕ) (v : Fin n.primeFactors.card → ℕ) :
    coeffOf d (phi n v)
      = (-1 : ℤ) ^ (1 + ∑ i, v i) * ∏ i, (rdCoeff (primeSeq n i) (v i) d : ℤ) := by
  unfold coeffOf
  rw [bigOmega_phi]
  congr 1
  rw [Finset.prod_subset (primeFactors_phi_subset n v) (fun q _ hq => ?_)]
  · rw [← prod_primeSeq n (fun p => (rdCoeff p ((phi n v).factorization p) d : ℤ))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [factorization_phi_apply]
  · have h0 : (phi n v).factorization q = 0 := by
      rw [← Nat.support_factorization] at hq
      exact Finsupp.notMem_support_iff.mp hq
    rw [h0, rdCoeff_zero, Nat.cast_one]

/-- `rankVectorReindexStatement`: the paper's rank-vector right side of
eq. (2) is the divisor-indexed `enumerationRHS`. -/
theorem mainFormulaRHS_eq_enumerationRHS (n d σ : ℕ) :
    mainFormulaRHS n d σ = enumerationRHS n d σ := by
  unfold mainFormulaRHS enumerationRHS
  rw [← sum_rankVectors_eq n d (fun h => coeffOf d h * (σ : ℤ) ^ (n ^ d / h))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [coeffOf_phi]
  rfl

/-! ### Exponents -/

theorem phi_dvd_pow {n d : ℕ} {v : Fin n.primeFactors.card → ℕ} (hv : ∀ i, v i ≤ d) :
    phi n v ∣ n ^ d :=
  (phi_dvd_rad_pow hv).trans (pow_dvd_pow_of_dvd (Nat.prod_primeFactors_dvd n) d)

theorem exponent_cast (n d : ℕ) {v : Fin n.primeFactors.card → ℕ} (hv : v ∈ allRankVectors n d) :
    (((n ^ d / ∏ i, primeSeq n i ^ v i : ℕ)) : ℚ)
      = (n : ℚ) ^ d * ∏ i, ((primeSeq n i : ℚ) ^ (-(v i : ℤ))) := by
  have hdvd : phi n v ∣ n ^ d := phi_dvd_pow (mem_allRankVectors.mp hv)
  have hne : ((phi n v : ℕ) : ℚ) ≠ 0 := by exact_mod_cast phi_ne_zero n v
  change ((n ^ d / phi n v : ℕ) : ℚ) = _
  rw [Nat.cast_div hdvd hne]
  push_cast
  rw [div_eq_mul_inv]
  congr 1
  unfold phi
  push_cast
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_neg, zpow_natCast]

/-! ### Corollary 4.4 -/

theorem numSS_eq_enumerationRHS {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    (numSS n d σ : ℤ) = enumerationRHS n d σ :=
  enumeration_proved n d σ hn hd hσ

theorem numSS_eq_mainFormulaRHS {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    (numSS n d σ : ℤ) = mainFormulaRHS n d σ := by
  rw [mainFormulaRHS_eq_enumerationRHS]; exact numSS_eq_enumerationRHS hn hd hσ

theorem lowerEnvelope_eq_cor44RHS (p d σ : ℕ) : lowerEnvelope p d σ = cor44RHS p d σ := by
  unfold lowerEnvelope cor44RHS
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold rdCoeff
  push_cast
  ring

theorem numSS_prime {p d σ : ℕ} (hp : p.Prime) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    (numSS p d σ : ℤ) = cor44RHS p d σ := by
  rw [numSS_eq_enumerationRHS hp.two_le hd hσ, enumerationRHS_prime hp,
    lowerEnvelope_eq_cor44RHS]

theorem cor44RHS_one (p σ : ℕ) : cor44RHS p 1 σ = σ := by
  simp [cor44RHS, gaussBinom]

theorem cor44RHS_two (p σ : ℕ) :
    cor44RHS p 2 σ = ((p : ℤ) + 1) * (σ : ℤ) ^ p - (p : ℤ) * σ := by
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [cor44RHS, hI, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [gaussBinom]
  ring

theorem cor44RHS_three (p σ : ℕ) :
    cor44RHS p 3 σ = ((p : ℤ) ^ 2 + p + 1) * (σ : ℤ) ^ (p ^ 2)
        - (p : ℤ) * ((p : ℤ) ^ 2 + p + 1) * (σ : ℤ) ^ p + (p : ℤ) ^ 3 * σ := by
  have hI : Finset.Icc 1 3 = {1, 2, 3} := by decide
  rw [cor44RHS, hI, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [gaussBinom, Nat.choose]
  ring

/-! ### Remark 4.5(i): the CG Lemma 7(iv) complement identity -/

theorem cor44_complement (p d σ : ℕ) :
    (σ : ℤ) ^ (p ^ d) - cor44RHS p d σ = cgLemma7ivRHS p d σ := by
  unfold cor44RHS cgLemma7ivRHS
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Nat.choose_two_right]
  ring

/-! ### Remark 4.5(ii): `n = 1` -/

theorem isEmpty_fin_primeFactors_one : IsEmpty (Fin (Nat.primeFactors 1).card) := by
  rw [Nat.primeFactors_one, Finset.card_empty]; infer_instance

theorem rankVectors_one (d : ℕ) : rankVectors 1 d = ∅ := by
  haveI := isEmpty_fin_primeFactors_one
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  exact (mem_rankVectors.mp hv).2 (funext fun i => isEmptyElim i)

theorem mainFormulaRHS_one (d σ : ℕ) : mainFormulaRHS 1 d σ = 0 := by
  rw [mainFormulaRHS, rankVectors_one, Finset.sum_empty]

theorem numSS_one (d σ : ℕ) : numSS 1 d σ = 0 := by
  unfold numSS
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨s, v, hv, -⟩
  exact hv (Subsingleton.elim v 0)

/-! ### Remark 4.5(ii): `σ = 1` -/

theorem numSS_sigma_one {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) : numSS n d 1 = 1 := by
  unfold numSS
  haveI : NeZero n := ⟨by omega⟩
  have hsym : ∀ s : Config n d (Fin 1), IsShiftSymmetric s := by
    intro s
    refine ⟨fun _ => 1, ?_, Subsingleton.elim _ _⟩
    intro h
    have h1 := congrFun h ⟨0, by omega⟩
    simp only [Pi.zero_apply] at h1
    haveI : Fact (1 < n) := ⟨by omega⟩
    exact one_ne_zero h1
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨fun _ => 0, hsym _⟩⟩⟩

theorem mainFormulaRHS_sigma_one {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    mainFormulaRHS n d 1 = 1 := by
  rw [← numSS_eq_mainFormulaRHS hn hd le_rfl, numSS_sigma_one hn hd, Nat.cast_one]

/-! ### Remark 4.5(ii): `d = 2` and Theorem E.19 -/

theorem rdCoeff_two_eq_e19r {p v : ℕ} (hv : v ≤ 2) : rdCoeff p v 2 = e19r p v := by
  interval_cases v <;> simp [rdCoeff, gaussBinom, e19r] <;> ring

theorem mainFormulaRHS_two_eq_e19RHS (n σ : ℕ) : mainFormulaRHS n 2 σ = e19RHS n σ := by
  unfold mainFormulaRHS e19RHS rankVectors allRankVectors
  refine Finset.sum_congr rfl fun v hv => ?_
  have hv' : ∀ i, v i ≤ 2 := by
    intro i
    have := (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hv).1) i
    rw [Finset.mem_range] at this
    omega
  rw [mul_right_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rdCoeff_two_eq_e19r (hv' i)]

theorem e19RHS_one (σ : ℕ) : e19RHS 1 σ = 0 := by
  have := mainFormulaRHS_two_eq_e19RHS 1 σ
  rw [mainFormulaRHS_one] at this
  exact this.symm

/-! ### Remark 4.5(ii): the per-prime identity -/

theorem perPrime_closed {p d : ℕ} (hd : 1 ≤ d) :
    ∑ r ∈ range (d + 1), (-1 : ℤ) ^ r * (p : ℤ) ^ (r.choose 2) * (gaussBinom p d r : ℤ) = 0 := by
  rw [gaussBinom_alt_sum, if_neg (by omega)]

theorem linesFp_nonempty {p d : ℕ} [NeZero p] (hp : p.Prime) (hd : 1 ≤ d) :
    (linesFp p d).Nonempty := by
  haveI := Fact.mk hp
  set e : Fin d → ZMod p := Pi.single ⟨0, by omega⟩ 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp [he] at this
  refine ⟨Submodule.span (ZMod p) {e}, ?_⟩
  unfold linesFp
  rw [Finset.filter_congr_decidable, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, finrank_span_singleton he0⟩

theorem crSigned_eq (p d r : ℕ) [NeZero p] :
    crSigned p d r = ∑ J ∈ (linesFp p d).powerset.filter
        (fun J : Finset (Submodule (ZMod p) (Fin d → ZMod p)) =>
          Module.finrank (ZMod p) ↥(J.sup id) = r), (-1 : ℤ) ^ J.card := by
  unfold crSigned
  rw [Finset.filter_congr_decidable]

theorem perPrime_signed {p d : ℕ} [NeZero p] (hp : p.Prime) (hd : 1 ≤ d) :
    ∑ r ∈ range (d + 1), crSigned p d r = 0 := by
  haveI := Fact.mk hp
  simp_rw [crSigned_eq]
  rw [Finset.sum_fiberwise_of_maps_to (g := fun J : Finset (Submodule (ZMod p) (Fin d → ZMod p)) =>
      Module.finrank (ZMod p) ↥(J.sup id))]
  · exact Finset.sum_powerset_neg_one_pow_card_of_nonempty (linesFp_nonempty hp hd)
  · intro J _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have h := Submodule.finrank_le (J.sup id)
    rwa [finrank_pi_d] at h

/-! ### Complement counts -/

theorem natCard_add_compl {α : Type*} [Finite α] (P : α → Prop) :
    Nat.card {x // P x} + Nat.card {x // ¬ P x} = Nat.card α := by
  classical
  rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl P)]

theorem stab_eq_bot_iff {n d : ℕ} {A : Type*} (s : Config n d A) :
    stab s = ⊥ ↔ ¬ IsShiftSymmetric s := by
  rw [AddSubgroup.eq_bot_iff_forall]
  constructor
  · rintro h ⟨v, hv, hfix⟩
    exact hv (h v hfix)
  · intro h v hv
    by_contra hne
    exact h ⟨v, hne, hv⟩

theorem natCard_config {n d σ : ℕ} [NeZero n] :
    Nat.card (Config n d (Fin σ)) = σ ^ (n ^ d) := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card]
  simp

theorem numSS_add_compl {n d σ : ℕ} [NeZero n] :
    numSS n d σ + Nat.card {s : Config n d (Fin σ) // ¬ IsShiftSymmetric s} = σ ^ (n ^ d) := by
  rw [← natCard_config]; exact natCard_add_compl _

theorem acount_eq {n d σ : ℕ} [NeZero n] :
    (acount n d σ : ℤ) = (σ : ℤ) ^ (n ^ d) - numSS n d σ := by
  have h1 : acount n d σ = Nat.card {s : Config n d (Fin σ) // ¬ IsShiftSymmetric s} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s => stab_eq_bot_iff s)
  have h2 := numSS_add_compl (n := n) (d := d) (σ := σ)
  rw [h1]
  have h3 : ((numSS n d σ + Nat.card {s : Config n d (Fin σ) // ¬ IsShiftSymmetric s} : ℕ) : ℤ)
      = ((σ ^ (n ^ d) : ℕ) : ℤ) := by rw [h2]
  push_cast at h3
  linarith

theorem injective_shift_iff {n d : ℕ} {A : Type*} (s : Config n d A) :
    Function.Injective (fun v : Lat n d => shift v s) ↔ ¬ IsShiftSymmetric s := by
  constructor
  · rintro h ⟨v, hv, hfix⟩
    exact hv (h (show shift v s = shift 0 s by rw [hfix, shift_zero]))
  · intro h v w hvw
    simp only at hvw
    by_contra hne
    apply h
    refine ⟨v - w, sub_ne_zero.mpr hne, ?_⟩
    have : shift (-w + v) s = s := by
      rw [shift_add, hvw, ← shift_add, neg_add_cancel, shift_zero]
    rwa [neg_add_eq_sub] at this

theorem a323863_eq {n : ℕ} (hn : 1 ≤ n) : (a323863 n : ℤ) = 2 ^ (n ^ 2) - numSS n 2 2 := by
  haveI : NeZero n := ⟨by omega⟩
  have h1 : a323863 n = Nat.card {s : Config n 2 (Fin 2) // ¬ IsShiftSymmetric s} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s => injective_shift_iff s)
  have h2 := numSS_add_compl (n := n) (d := 2) (σ := 2)
  rw [h1]
  have h3 : ((numSS n 2 2 + Nat.card {s : Config n 2 (Fin 2) // ¬ IsShiftSymmetric s} : ℕ) : ℤ)
      = ((2 ^ (n ^ 2) : ℕ) : ℤ) := by rw [h2]
  push_cast at h3
  linarith

/-! ### §4.4 reference values -/

theorem coeffOf_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (a b d : ℕ) :
    coeffOf d (p ^ a * q ^ b)
      = (-1 : ℤ) ^ (1 + (a + b)) * ((rdCoeff p a d : ℤ) * (rdCoeff q b d : ℤ)) := by
  have hfac : (p ^ a * q ^ b).factorization = Finsupp.single p a + Finsupp.single q b := by
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
      hp.factorization_pow, hq.factorization_pow]
  have hsub : (p ^ a * q ^ b).primeFactors ⊆ {p, q} := by
    intro r hr
    rw [← Nat.support_factorization, hfac] at hr
    have := Finsupp.support_add hr
    rw [Finset.mem_union] at this
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases this with h | h
    · left; exact Finset.mem_singleton.mp (Finsupp.support_single_subset h)
    · right; exact Finset.mem_singleton.mp (Finsupp.support_single_subset h)
  unfold coeffOf bigOmega
  rw [hfac, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
  congr 1
  rw [Finset.prod_subset hsub (fun r _ hr => ?_)]
  · rw [Finset.prod_insert (by simpa using hpq), Finset.prod_singleton]
    simp [Finsupp.single_apply, hpq, Ne.symm hpq]
  · have h0 : (Finsupp.single p a + Finsupp.single q b) r = 0 := by
      rw [← hfac]
      rw [← Nat.support_factorization] at hr
      exact Finsupp.notMem_support_iff.mp hr
    rw [h0, rdCoeff_zero, Nat.cast_one]

theorem enumerationRHS_six : enumerationRHS 6 2 2 = 801064 := by
  have hpf : Nat.primeFactors 6 = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
    rfl
  have hrad : rad 6 = 6 := by rw [rad, hpf]; rfl
  have hdiv : ((rad 6) ^ 2).divisors.erase 1 = {2, 3, 4, 6, 9, 12, 18, 36} := by
    rw [hrad]; decide
  have c : ∀ a b : ℕ, coeffOf 2 (2 ^ a * 3 ^ b)
      = (-1 : ℤ) ^ (1 + (a + b)) * ((rdCoeff 2 a 2 : ℤ) * (rdCoeff 3 b 2 : ℤ)) :=
    fun a b => coeffOf_two_primes Nat.prime_two Nat.prime_three (by norm_num) a b 2
  have e2 : coeffOf 2 2 = 3 := by
    rw [show coeffOf 2 2 = coeffOf 2 (2 ^ 1 * 3 ^ 0) by norm_num, c]; decide
  have e3 : coeffOf 2 3 = 4 := by
    rw [show coeffOf 2 3 = coeffOf 2 (2 ^ 0 * 3 ^ 1) by norm_num, c]; decide
  have e4 : coeffOf 2 4 = -2 := by
    rw [show coeffOf 2 4 = coeffOf 2 (2 ^ 2 * 3 ^ 0) by norm_num, c]; decide
  have e6 : coeffOf 2 6 = -12 := by
    rw [show coeffOf 2 6 = coeffOf 2 (2 ^ 1 * 3 ^ 1) by norm_num, c]; decide
  have e9 : coeffOf 2 9 = -3 := by
    rw [show coeffOf 2 9 = coeffOf 2 (2 ^ 0 * 3 ^ 2) by norm_num, c]; decide
  have e12 : coeffOf 2 12 = 8 := by
    rw [show coeffOf 2 12 = coeffOf 2 (2 ^ 2 * 3 ^ 1) by norm_num, c]; decide
  have e18 : coeffOf 2 18 = 9 := by
    rw [show coeffOf 2 18 = coeffOf 2 (2 ^ 1 * 3 ^ 2) by norm_num, c]; decide
  have e36 : coeffOf 2 36 = -6 := by
    rw [show coeffOf 2 36 = coeffOf 2 (2 ^ 2 * 3 ^ 2) by norm_num, c]; decide
  rw [enumerationRHS, hdiv]
  norm_num [Finset.sum_insert, Finset.sum_singleton, e2, e3, e4, e6, e9, e12, e18, e36]

end ShiftSym.P04
