/-
Phase H, group 05 (KActive) — proof helper module 2 of 3.

Theorem 5.1 (`thm:kactive`).  Route (the paper's own, lines 550–553: "the
inclusion–exclusion and rank-vector grouping of Theorem 4.3 apply verbatim,
since the summand again depends on J only through |⟨∪J⟩|"):
* the certified relative enumeration theorem (`relativeEnumeration_proved`,
  E1) applied to `X = C^a_k` (configurations with exactly `k` cells in
  state `a`) gives `|X ∩ S| = Σ_U mobiusCoeff U · |X ∩ Fix(socSub U)| + |X|`;
* `|X ∩ Fix(H)| = convTerm N k |H| σ` (helper module 1, `natCard_fixK`);
* `|socSub U| = h(rk U)` and the fiber of the tuples `U` over the rank
  vector `v` has signed weight `(−1)^{1+|v|} ∏_p r_d(p, v_p)`
  (`spanSum_rank_classified_pd`); the `v = 0` fiber cancels `|X|`.
-/
import Shiftsym.Paper.Proofs.P05_KActive_Fix
import Shiftsym.Lemmas.Relative

open scoped Classical

namespace ShiftSym.P05

open ShiftSym Module Function

variable {n d : ℕ}

theorem coprime_primeFactors_coe {m : ℕ} :
    Pairwise (Nat.Coprime on fun p : m.primeFactors => (p : ℕ)) := by
  intro p q hpq
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
    (Nat.prime_of_mem_primeFactors q.2)).mpr fun h => hpq (Subtype.ext h)

/-- The rank vector of a tuple of subspaces. -/
noncomputable def rkVec (U : ModTuple n d) : n.primeFactors → ℕ :=
  fun p => finrank (ZMod (p : ℕ)) (U p)

/-- `|socSub U| = h(rk U) = ∏_p p^{rk U_p}`. -/
theorem card_socSub [NeZero n] (U : ModTuple n d) :
    Nat.card (socSub U) = hVec (rkVec U) := by
  unfold socSub hVec rkVec
  rw [card_univ_sup_of_torsion (fun p : n.primeFactors => (p : ℕ)) _
      (fun p => ofMod_le_torsion (Nat.dvd_of_mem_primeFactors p.2) (U p))
      coprime_primeFactors_coe]
  exact Finset.prod_congr rfl fun p _ => by rw [card_ofMod, card_submodule_pow]

theorem rkVec_mem (U : ModTuple n d) : rkVec U ∈ rankVectors n d := by
  rw [rankVectors, Fintype.mem_piFinset]
  intro p
  have hle := Submodule.finrank_le (U p)
  rw [finrank_pi_d] at hle
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)

/-- Signed weight of the fiber of tuples over a rank vector `v`. -/
theorem sum_mobiusCoeff_fiber {v : n.primeFactors → ℕ} (hv : v ∈ rankVectors n d) :
    ∑ U ∈ Finset.univ.filter (fun U : ModTuple n d => rkVec U = v), mobiusCoeff U
      = (-1 : ℤ) ^ (1 + absVec v) * ∏ p : n.primeFactors, (rdCoeff p (v p) d : ℤ) := by
  have hvle : ∀ p, v p ≤ d := fun p => by
    have := Fintype.mem_piFinset.mp hv p
    simpa [Finset.mem_range, Nat.lt_succ_iff] using this
  have hfilter : Finset.univ.filter (fun U : ModTuple n d => rkVec U = v)
      = Fintype.piFinset (fun p : n.primeFactors =>
          Finset.univ.filter
            (fun W : Submodule (ZMod (p : ℕ)) (Fin d → ZMod (p : ℕ)) =>
              finrank (ZMod (p : ℕ)) W = v p)) := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, rkVec,
      funext_iff]
  rw [hfilter]
  unfold mobiusCoeff
  rw [Finset.sum_neg_distrib, ← Finset.prod_univ_sum]
  rw [Finset.prod_congr rfl (fun (p : n.primeFactors) _ =>
    spanSum_rank_classified_pd (p := (p : ℕ)) (hvle p))]
  have hsplit : ∀ p ∈ (Finset.univ : Finset n.primeFactors),
      (-1 : ℤ) ^ (v p) * ((p : ℕ) : ℤ) ^ ((v p).choose 2) * (gaussBinom (p : ℕ) d (v p) : ℤ)
        = (-1 : ℤ) ^ (v p) * (rdCoeff p (v p) d : ℤ) := by
    intro p _
    rw [rdCoeff]
    push_cast
    ring
  rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    absVec, pow_add, pow_one]
  ring

/-- **Rank-vector regrouping** of the relative Möbius sum, for any weight
depending only on the order of the subgroup. -/
theorem rank_regroup [NeZero n] (f : ℕ → ℤ) :
    ∑ U : ModTuple n d, mobiusCoeff U * f (Nat.card (socSub U)) + f 1
      = ∑ v ∈ (rankVectors n d).erase 0,
          (-1 : ℤ) ^ (1 + absVec v) * (∏ p : n.primeFactors, (rdCoeff p (v p) d : ℤ))
            * f (hVec v) := by
  simp_rw [card_socSub]
  have hmaps : ∀ U ∈ (Finset.univ : Finset (ModTuple n d)), rkVec U ∈ rankVectors n d :=
    fun U _ => rkVec_mem U
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ v ∈ rankVectors n d,
      ∑ U ∈ Finset.univ.filter (fun U : ModTuple n d => rkVec U = v),
          mobiusCoeff U * f (hVec (rkVec U))
        = (-1 : ℤ) ^ (1 + absVec v) * (∏ p : n.primeFactors, (rdCoeff p (v p) d : ℤ))
            * f (hVec v) := by
    intro v hv
    rw [Finset.sum_congr rfl (fun U hU => by rw [(Finset.mem_filter.mp hU).2]),
      ← Finset.sum_mul, sum_mobiusCoeff_fiber hv]
  rw [Finset.sum_congr rfl hfib]
  have h0 : (0 : n.primeFactors → ℕ) ∈ rankVectors n d := by
    rw [rankVectors, Fintype.mem_piFinset]
    intro p
    simp
  rw [← Finset.add_sum_erase _ _ h0]
  have hv0 : (-1 : ℤ) ^ (1 + absVec (0 : n.primeFactors → ℕ))
      * (∏ p : n.primeFactors, (rdCoeff p ((0 : n.primeFactors → ℕ) p) d : ℤ))
      * f (hVec (0 : n.primeFactors → ℕ)) = -f 1 := by
    simp [absVec, hVec, rdCoeff, gaussBinom]
  rw [hv0]
  ring

/-- **Theorem 5.1, core form** (no `d ≥ 1`, no `k ≤ N` needed): for
`n ≥ 2`, `σ ≥ 1`, every `k` and every state `a`,
`|S^a_{n^d,k}| = kActiveRHS n d σ k`. -/
theorem numKActive_eq_rhs (n d σ k : ℕ) (hn : 2 ≤ n) (hσ : 1 ≤ σ) (a : Fin σ) :
    (numKActive n d σ a k : ℤ) = kActiveRHS n d σ k := by
  have : NeZero n := ⟨by omega⟩
  set X : Finset (Config n d (Fin σ)) := Finset.univ.filter fun s => cellsInState s a = k
    with hXdef
  have hnum : numKActive n d σ a k = (X.filter IsShiftSymmetric).card := by
    rw [numKActive, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext s
    simp [hXdef, and_comm]
  have hw : ∀ H : AddSubgroup (Lat n d),
      ((X ∩ fixedByA (Fin σ) H).card : ℤ) = convTerm (n ^ d) k (Nat.card H) σ := by
    intro H
    rw [← natCard_fixK n d σ hσ a k H]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext s
    simp [hXdef, fixedByA, fixedBy, and_comm]
  have hX : (X.card : ℤ) = convTerm (n ^ d) k 1 σ := by
    have := hw ⊥
    rwa [fixedByA_bot, Finset.inter_univ, AddSubgroup.card_bot] at this
  rw [hnum]
  have h := relativeEnumeration_proved (n := n) (d := d) (A := Fin σ) X
  unfold relativeEnumerationStatement at h
  rw [h, hX]
  have hR : kActiveRHS n d σ k
      = ∑ U : ModTuple n d, mobiusCoeff U * convTerm (n ^ d) k (Nat.card (socSub U)) σ
        + convTerm (n ^ d) k 1 σ := by
    rw [rank_regroup (fun h => convTerm (n ^ d) k h σ)]
    unfold kActiveRHS
    exact Finset.sum_congr rfl fun v _ => kActiveSummand_eq_convTerm n d σ k v
  rw [hR]
  congr 1
  refine Finset.sum_congr rfl fun U _ => ?_
  congr 1
  convert hw (socSub U) using 3
  ext s
  simp only [Finset.mem_inter]

end ShiftSym.P05
