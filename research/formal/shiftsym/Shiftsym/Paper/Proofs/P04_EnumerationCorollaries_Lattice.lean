/-
Phase H, group 04 — proofs, part 3: the primary decomposition of the
subgroup lattice of `A = (ZMod n)^d` (§4.3 of the paper).

* `A_p = primComp n d p` is the `p^{v_p(n)}`-torsion, hence `≅ (Z/p^α)^d`;
* CRT coefficients `c_p ∈ ℤ` with `∑ c_p = 1`, `n ∣ p^{α_p} c_p` and
  `p^{α_p} ∣ c_q` (`q ≠ p`); the projections `x ↦ c_p • x`;
* every subgroup splits, the `A_p` are independent, and
  `K ↦ (K ∩ A_p)_p` is a lattice isomorphism `L(A) ≅ ∏_p L(A_p)`.
-/
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Formula

open Finset

namespace ShiftSym.P04

open ShiftSym

variable {n d : ℕ}

/-- `p^{v_p(n)}`. -/
abbrev ppow (n p : ℕ) : ℕ := p ^ n.factorization p

theorem mem_primComp_iff [NeZero n] {p : ℕ} (hp : p.Prime) {x : Lat n d} :
    x ∈ primComp n d p ↔ ppow n p • x = 0 := by
  unfold primComp
  rw [AddCommGroup.mem_primaryComponent]
  constructor
  · rintro ⟨k, hk⟩
    have h1 : addOrderOf x ∣ p ^ k := addOrderOf_dvd_of_nsmul_eq_zero hk
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hp).mp h1
    have h2 : addOrderOf x ∣ n := addOrderOf_lat_dvd x
    rw [hjeq] at h2
    have hj' : j ≤ n.factorization p :=
      (hp.pow_dvd_iff_le_factorization (NeZero.ne n)).mp h2
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [hjeq]
    exact pow_dvd_pow p hj'
  · intro h
    exact ⟨_, h⟩

theorem primComp_eq_latTorsion [NeZero n] {p : ℕ} (hp : p.Prime) :
    primComp n d p = latTorsion n d (ppow n p) := by
  ext x
  rw [mem_primComp_iff hp, mem_latTorsion]

theorem ppow_dvd (n p : ℕ) : ppow n p ∣ n := Nat.ordProj_dvd n p

/-- `A_p ≅ (Z/p^α Z)^d` (`primaryIsoStatement`). -/
noncomputable def primCompEquiv [NeZero n] {p : ℕ} (hp : p.Prime) :
    primComp n d p ≃+ (Fin d → ZMod (ppow n p)) :=
  haveI : NeZero (ppow n p) := ⟨pow_ne_zero _ hp.ne_zero⟩
  (AddEquiv.addSubgroupCongr (primComp_eq_latTorsion hp)).trans
    (latTorsionEquiv (ppow_dvd n p))

/-! ### CRT coefficients -/

theorem prod_ppow (hn : n ≠ 0) : ∏ p ∈ n.primeFactors, ppow n p = n := by
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [← Nat.support_factorization]
  rfl

theorem exists_crt_coeffs (hn : 2 ≤ n) : ∃ c : ℕ → ℤ,
    (∑ p ∈ n.primeFactors, c p = 1) ∧
    (∀ p ∈ n.primeFactors, (n : ℤ) ∣ (ppow n p : ℤ) * c p) ∧
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, q ≠ p → (ppow n p : ℤ) ∣ c q) := by
  classical
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  have hcop : Pairwise (Function.onFun IsCoprime
      fun i : n.primeFactors => ((ppow n i : ℕ) : ℤ)) := by
    intro i j hij
    simp only [Function.onFun]
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors i.2)
      (Nat.prime_of_mem_primeFactors j.2)).mpr fun h => hij (Subtype.ext h))
  obtain ⟨μ, hμ⟩ := (exists_sum_eq_one_iff_pairwise_coprime hne
    (s := fun p => ((ppow n p : ℕ) : ℤ))).mpr hcop
  refine ⟨fun p => μ p * ∏ j ∈ n.primeFactors \ {p}, ((ppow n j : ℕ) : ℤ), hμ, ?_, ?_⟩
  · intro p hp
    have hprod : ∏ j ∈ n.primeFactors, ((ppow n j : ℕ) : ℤ) = n := by
      rw [← Nat.cast_prod, prod_ppow (by omega)]
    refine ⟨μ p, ?_⟩
    rw [← hprod, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hp]
    ring
  · intro p hp q _ hqp
    refine Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ ?_) _
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hp, Ne.symm hqp⟩

/-- The CRT coefficients (chosen once and for all; junk for `n < 2`). -/
noncomputable def crtCoeff (n : ℕ) : ℕ → ℤ :=
  if h : 2 ≤ n then Classical.choose (exists_crt_coeffs h) else 0

theorem crtCoeff_spec (hn : 2 ≤ n) :
    (∑ p ∈ n.primeFactors, crtCoeff n p = 1) ∧
    (∀ p ∈ n.primeFactors, (n : ℤ) ∣ (ppow n p : ℤ) * crtCoeff n p) ∧
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, q ≠ p → (ppow n p : ℤ) ∣ crtCoeff n q) := by
  unfold crtCoeff
  rw [dif_pos hn]
  exact Classical.choose_spec (exists_crt_coeffs hn)

theorem sum_crt_smul (hn : 2 ≤ n) (x : Lat n d) :
    ∑ p ∈ n.primeFactors, crtCoeff n p • x = x := by
  rw [← Finset.sum_smul, (crtCoeff_spec hn).1, one_smul]

theorem crt_smul_mem (hn : 2 ≤ n) {p : ℕ} (hp : p ∈ n.primeFactors) (x : Lat n d) :
    crtCoeff n p • x ∈ primComp n d p := by
  haveI : NeZero n := ⟨by omega⟩
  rw [mem_primComp_iff (Nat.prime_of_mem_primeFactors hp)]
  obtain ⟨k, hk⟩ := (crtCoeff_spec hn).2.1 p hp
  rw [← natCast_zsmul, smul_smul, hk, mul_comm, mul_smul, natCast_zsmul, nsmul_self_lat,
    smul_zero]

theorem crt_smul_eq_zero (hn : 2 ≤ n) {p q : ℕ} (hp : p ∈ n.primeFactors)
    (hq : q ∈ n.primeFactors) (hqp : q ≠ p) {y : Lat n d} (hy : y ∈ primComp n d p) :
    crtCoeff n q • y = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  rw [mem_primComp_iff (Nat.prime_of_mem_primeFactors hp)] at hy
  obtain ⟨k, hk⟩ := (crtCoeff_spec hn).2.2 p hp q hq hqp
  rw [hk, mul_comm, mul_smul, natCast_zsmul, hy, smul_zero]

theorem crt_smul_self (hn : 2 ≤ n) {p : ℕ} (hp : p ∈ n.primeFactors) {y : Lat n d}
    (hy : y ∈ primComp n d p) : crtCoeff n p • y = y := by
  conv_rhs => rw [← sum_crt_smul hn y]
  rw [Finset.sum_eq_single_of_mem p hp]
  intro q hq hqp
  exact crt_smul_eq_zero hn hp hq hqp hy

/-- The projection `x ↦ c_p • x` as an additive endomorphism. -/
def smulHom (c : ℤ) : Lat n d →+ Lat n d := DistribSMul.toAddMonoidHom (Lat n d) c

@[simp] theorem smulHom_apply (c : ℤ) (x : Lat n d) : smulHom c x = c • x := rfl

/-! ### §4.3 statements -/

/-- Primary components are integer multiples (`primaryComponentsMultiplesStatement`). -/
theorem primary_multiples (hn : 2 ≤ n) (x : Lat n d) : ∃ c : ℕ → ℤ,
    (∀ p ∈ n.primeFactors, c p • x ∈ primComp n d p) ∧
      x = ∑ p ∈ n.primeFactors, c p • x :=
  ⟨crtCoeff n, fun _ hp => crt_smul_mem hn hp x, (sum_crt_smul hn x).symm⟩

theorem le_iSup_inf (hn : 2 ≤ n) (K : AddSubgroup (Lat n d)) :
    K ≤ ⨆ p ∈ n.primeFactors, K ⊓ primComp n d p := by
  intro x hx
  rw [← sum_crt_smul hn x]
  refine AddSubgroup.sum_mem _ fun p hp => ?_
  refine (le_iSup₂ (f := fun p (_ : p ∈ n.primeFactors) => K ⊓ primComp n d p) p hp) ?_
  exact AddSubgroup.mem_inf.mpr ⟨AddSubgroup.zsmul_mem _ hx _, crt_smul_mem hn hp x⟩

theorem split_eq (hn : 2 ≤ n) (K : AddSubgroup (Lat n d)) :
    K = ⨆ p ∈ n.primeFactors, K ⊓ primComp n d p :=
  le_antisymm (le_iSup_inf hn K) (iSup₂_le fun _ _ => inf_le_left)

theorem split_eq' (hn : 2 ≤ n) (K : AddSubgroup (Lat n d)) :
    K = ⨆ p : n.primeFactors, K ⊓ primComp n d (p : ℕ) := by
  exact (split_eq hn K).trans iSup_subtype'

theorem iSup_ne_le_ker (hn : 2 ≤ n) (i : n.primeFactors) :
    (⨆ (j : n.primeFactors) (_ : j ≠ i), primComp n d (j : ℕ))
      ≤ (smulHom (n := n) (d := d) (crtCoeff n i)).ker := by
  refine iSup₂_le fun j hji => ?_
  intro y hy
  rw [AddMonoidHom.mem_ker, smulHom_apply]
  exact crt_smul_eq_zero hn j.2 i.2 (fun h => hji (Subtype.ext h).symm) hy

theorem iSupIndep_primComp (hn : 2 ≤ n) :
    iSupIndep fun p : n.primeFactors => primComp n d (p : ℕ) := by
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff, eq_bot_iff]
  intro y hy
  obtain ⟨hyi, hyj⟩ := AddSubgroup.mem_inf.mp hy
  have h1 : crtCoeff n i • y = 0 := by
    have := iSup_ne_le_ker hn i hyj
    rwa [AddMonoidHom.mem_ker, smulHom_apply] at this
  rw [crt_smul_self hn i.2 hyi] at h1
  rw [h1]
  exact AddSubgroup.zero_mem _

/-- `subgroupSplitStatement`. -/
theorem subgroup_split (hn : 2 ≤ n) (K : AddSubgroup (Lat n d)) :
    K = (⨆ p ∈ n.primeFactors, K ⊓ primComp n d p) ∧
      iSupIndep fun p : n.primeFactors => K ⊓ primComp n d (p : ℕ) :=
  ⟨split_eq hn K, (iSupIndep_primComp hn).mono fun _ => inf_le_right⟩

theorem le_iff_inf_le (hn : 2 ≤ n) (K K' : AddSubgroup (Lat n d)) :
    K ≤ K' ↔ ∀ p ∈ n.primeFactors, K ⊓ primComp n d p ≤ K' ⊓ primComp n d p := by
  constructor
  · intro h p _
    exact inf_le_inf_right _ h
  · intro h
    rw [split_eq hn K]
    exact iSup₂_le fun p hp => (h p hp).trans inf_le_left

/-- For `L_q ≤ A_q`, `(⨆_q L_q) ∩ A_p = L_p`. -/
theorem iSup_inf_eq (hn : 2 ≤ n) {s : Finset ℕ} (hs : s ⊆ n.primeFactors)
    (L : ℕ → AddSubgroup (Lat n d)) (hL : ∀ q ∈ s, L q ≤ primComp n d q)
    {p : ℕ} (hp : p ∈ s) :
    (⨆ q ∈ s, L q) ⊓ primComp n d p = L p := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxK, hxp⟩ := AddSubgroup.mem_inf.mp hx
    have hle : (⨆ q ∈ s, L q) ≤ (L p).comap (smulHom (n := n) (d := d) (crtCoeff n p)) := by
      refine iSup₂_le fun q hq => ?_
      intro y hy
      rw [AddSubgroup.mem_comap, smulHom_apply]
      by_cases hqp : q = p
      · subst hqp
        rw [crt_smul_self hn (hs hq) (hL q hq hy)]
        exact hy
      · rw [crt_smul_eq_zero hn (hs hq) (hs hp) (Ne.symm hqp) (hL q hq hy)]
        exact AddSubgroup.zero_mem _
    have := hle hxK
    rw [AddSubgroup.mem_comap, smulHom_apply, crt_smul_self hn (hs hp) hxp] at this
    exact this
  · exact le_inf (le_iSup₂ (f := fun q (_ : q ∈ s) => L q) p hp) (hL p hp)

/-- `subgroupLatticeProductStatement`. -/
theorem lattice_product (hn : 2 ≤ n) :
    (∀ K K' : AddSubgroup (Lat n d),
        K ≤ K' ↔ ∀ p ∈ n.primeFactors, K ⊓ primComp n d p ≤ K' ⊓ primComp n d p) ∧
      (∀ L : ℕ → AddSubgroup (Lat n d), (∀ p ∈ n.primeFactors, L p ≤ primComp n d p) →
        ∃ K : AddSubgroup (Lat n d), ∀ p ∈ n.primeFactors, K ⊓ primComp n d p = L p) :=
  ⟨le_iff_inf_le hn, fun L hL =>
    ⟨⨆ q ∈ n.primeFactors, L q, fun _ hp => iSup_inf_eq hn subset_rfl L hL hp⟩⟩

end ShiftSym.P04
