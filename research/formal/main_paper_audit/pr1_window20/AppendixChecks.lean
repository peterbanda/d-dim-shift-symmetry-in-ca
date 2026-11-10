import Shiftsym.AuditPaper

namespace PR1Review.Appendix
open ShiftSym ShiftSym.P10

-- The product formula written with signed integer exponents, including
-- ranks j>d. This checks the apparent extra j≤d hypothesis in Lemma A.2.
noncomputable def printedGaussian (q : ℝ) (d j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j,
    (q ^ ((d : ℤ) - (i : ℤ)) - 1) / (q ^ (i + 1) - 1)

theorem coefficient_bound_without_rank_restriction
    (q : ℝ) (d j : ℕ) (hq : 2 ≤ q) (hd : 1 ≤ d) :
    printedGaussian q d j ≤ 4 * q ^ ((j : ℤ) * ((d : ℤ) - (j : ℤ))) := by
  by_cases hj : j ≤ d
  · have hp : printedGaussian q d j = gaussProd q d j := by
      unfold printedGaussian gaussProd
      apply Finset.prod_congr rfl
      intro i hi
      have hid : i ≤ d := by have := Finset.mem_range.mp hi; omega
      rw [← Int.natCast_sub hid, zpow_natCast]
    rw [hp, ← Int.natCast_sub hj, ← Int.natCast_mul, zpow_natCast]
    exact lemA2Part1_proved q d j hq hd hj
  · have hz : printedGaussian q d j = 0 := by
      unfold printedGaussian
      rw [Finset.prod_eq_zero_iff]
      refine ⟨d, Finset.mem_range.mpr (by omega), ?_⟩
      simp
    rw [hz]
    have hq0 : 0 < q := by linarith
    positivity

#print axioms coefficient_bound_without_rank_restriction
end PR1Review.Appendix
