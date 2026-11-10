/-
Phase D2, part 1: torsion arithmetic and the order of a join of
subgroups sitting inside pairwise-coprime torsion subgroups.

Main result: `card_univ_sup_of_torsion` — if `L i ≤ latTorsion n d (m i)`
with the moduli `m i` pairwise coprime, then `|⊔ᵢ L i| = ∏ᵢ |L i|`.
Proof: the summation homomorphism `(∀ i, L i) →+ Lat n d` has range
`⊔ᵢ L i` and is injective (an integer Bézout identity separates the
components; no primary-decomposition machinery needed).
-/
import Shiftsym.Lemmas.Torsion

open scoped Classical

namespace ShiftSym

variable {n d : ℕ}

/-- Torsion is monotone in the modulus. -/
theorem latTorsion_mono {a b : ℕ} (hab : a ∣ b) :
    latTorsion n d a ≤ latTorsion n d b := by
  intro v hv
  rw [mem_latTorsion] at hv ⊢
  obtain ⟨c, rfl⟩ := hab
  rw [mul_nsmul, hv, smul_zero]

/-- Coprime torsion subgroups intersect trivially (integer Bézout). -/
theorem latTorsion_inf_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    latTorsion n d a ⊓ latTorsion n d b = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hva, hvb⟩ := AddSubgroup.mem_inf.mp hv
  rw [mem_latTorsion] at hva hvb
  rw [AddSubgroup.mem_bot]
  have hcop : IsCoprime (a : ℤ) (b : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact hab
  obtain ⟨u, w, huw⟩ := hcop
  have hva' : (a : ℤ) • v = 0 := by rw [natCast_zsmul]; exact hva
  have hvb' : (b : ℤ) • v = 0 := by rw [natCast_zsmul]; exact hvb
  calc v = (1 : ℤ) • v := (one_zsmul v).symm
    _ = (u * a + w * b : ℤ) • v := by rw [huw]
    _ = u • ((a : ℤ) • v) + w • ((b : ℤ) • v) := by
        rw [add_zsmul, mul_zsmul, mul_zsmul]
    _ = 0 := by rw [hva', hvb', smul_zero, smul_zero, add_zero]

/-- A subgroup of prime cardinality `p` lies inside the `p`-torsion. -/
theorem le_torsion_of_card_prime {p : ℕ}
    {C : AddSubgroup (Lat n d)} (hC : Nat.card C = p) :
    C ≤ latTorsion n d p := by
  intro x hx
  rw [mem_latTorsion, ← addOrderOf_dvd_iff_nsmul_eq_zero]
  have h := AddSubgroup.addOrderOf_dvd_natCard C hx
  rwa [hC] at h

/-- The order of the translation group is `n ^ d`. -/
theorem card_lat [NeZero n] : Nat.card (Lat n d) = n ^ d := by
  rw [show (Lat n d) = (Fin d → ZMod n) from rfl, Nat.card_fun]
  simp [Nat.card_eq_fintype_card]

/-- The prime order of a prime-order subgroup divides `n`. -/
theorem prime_card_dvd [NeZero n] {C : AddSubgroup (Lat n d)}
    (hC : (Nat.card C).Prime) : Nat.card C ∣ n := by
  have h := AddSubgroup.card_addSubgroup_dvd_card C
  rw [card_lat] at h
  exact hC.dvd_of_dvd_pow h

/-- The prime order of a prime-order subgroup is a prime factor of `n`
(for `d ≥ 1` the subgroup is nontrivial only when `n ≥ 2`; membership in
`primeFactors` needs only `n ≠ 0`). -/
theorem card_mem_primeFactors [NeZero n] {C : AddSubgroup (Lat n d)}
    (hC : (Nat.card C).Prime) : Nat.card C ∈ n.primeFactors :=
  Nat.mem_primeFactors.mpr ⟨hC, prime_card_dvd hC, NeZero.ne n⟩

section SupCard

open Function

variable {ι : Type*} [Fintype ι]

/-- The summation homomorphism out of the product of a family of
subgroups of the (abelian) translation group. -/
def sumHom (L : ι → AddSubgroup (Lat n d)) : (∀ i, L i) →+ Lat n d :=
  AddMonoidHom.mk' (fun y => ∑ i, (y i : Lat n d)) (by
    intro y z
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => rfl)

theorem sumHom_apply (L : ι → AddSubgroup (Lat n d)) (y : ∀ i, L i) :
    sumHom L y = ∑ i, (y i : Lat n d) := rfl

/-- The range of the summation homomorphism is the join. -/
theorem sumHom_range (L : ι → AddSubgroup (Lat n d)) :
    (sumHom L).range = Finset.univ.sup L := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact AddSubgroup.sum_mem _ fun i _ =>
      Finset.le_sup (f := L) (Finset.mem_univ i) (y i).2
  · apply Finset.sup_le
    intro i _
    intro x hx
    refine ⟨Pi.single i ⟨x, hx⟩, ?_⟩
    rw [sumHom_apply, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji]
      rfl
    · intro hi
      exact absurd (Finset.mem_univ i) hi

/-- Injectivity of the summation homomorphism: Bézout separates the
components across pairwise-coprime torsions. -/
theorem sumHom_injective (m : ι → ℕ) (L : ι → AddSubgroup (Lat n d))
    (hm : ∀ i, L i ≤ latTorsion n d (m i))
    (hcop : Pairwise (Nat.Coprime on m)) :
    Function.Injective (sumHom L) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [sumHom_apply] at hy
  funext i
  refine Subtype.ext ?_
  show (y i : Lat n d) = 0
  -- separate the i-th summand
  have hsplit : (y i : Lat n d)
      = -∑ j ∈ Finset.univ.erase i, (y j : Lat n d) := by
    have h := Finset.add_sum_erase Finset.univ
      (fun j => (y j : Lat n d)) (Finset.mem_univ i)
    rw [hy] at h
    exact eq_neg_of_add_eq_zero_left h
  -- the i-th summand is (m i)-torsion; the rest is (∏ other m)-torsion
  have hmem_i : (y i : Lat n d) ∈ latTorsion n d (m i) := hm i (y i).2
  have hmem_rest : (y i : Lat n d)
      ∈ latTorsion n d (∏ j ∈ Finset.univ.erase i, m j) := by
    rw [hsplit]
    exact AddSubgroup.neg_mem _ (AddSubgroup.sum_mem _ fun j hj =>
      latTorsion_mono (Finset.dvd_prod_of_mem m hj) (hm j (y j).2))
  have hcop' : Nat.Coprime (m i) (∏ j ∈ Finset.univ.erase i, m j) :=
    Nat.Coprime.prod_right fun j hj =>
      hcop (Ne.symm (Finset.ne_of_mem_erase hj))
  have := latTorsion_inf_coprime (n := n) (d := d) hcop'
  have hbot : (y i : Lat n d) ∈
      (⊥ : AddSubgroup (Lat n d)) := by
    rw [← this]
    exact AddSubgroup.mem_inf.mpr ⟨hmem_i, hmem_rest⟩
  exact AddSubgroup.mem_bot.mp hbot

/-- **Order of a join across coprime torsions**: the cardinality of the
join is the product of the cardinalities. -/
theorem card_univ_sup_of_torsion (m : ι → ℕ)
    (L : ι → AddSubgroup (Lat n d))
    (hm : ∀ i, L i ≤ latTorsion n d (m i))
    (hcop : Pairwise (Nat.Coprime on m)) :
    Nat.card ((Finset.univ.sup L : AddSubgroup (Lat n d)))
      = ∏ i, Nat.card (L i) := by
  rw [← sumHom_range]
  rw [← Nat.card_congr
    (AddMonoidHom.ofInjective (sumHom_injective m L hm hcop)).toEquiv]
  rw [Nat.card_pi]

end SupCard

end ShiftSym
