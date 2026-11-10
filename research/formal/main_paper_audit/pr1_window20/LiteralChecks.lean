import Shiftsym.AuditPaper

/- Independent review of merged PR #1. The probability below is written
   directly as a cardinality of functions fixed by a nonzero translation. -/
namespace PR1Review
open ShiftSym ShiftSym.P09

noncomputable def paperProbability (n d σ : ℕ) : ℝ :=
  (Nat.card {s : (Fin d → ZMod n) → Fin σ //
    ∃ v : Fin d → ZMod n, v ≠ 0 ∧ (fun u => s (u + v)) = s} : ℝ) /
      (σ : ℝ) ^ (n ^ d)

noncomputable def paperCenter (p : ℕ) : ℝ :=
  Real.log (2 - 2 / (p : ℝ)) / Real.log (1 + 1 / (p : ℝ))

noncomputable def paperPhi (p d : ℕ) : ℝ :=
  (1 - 1 / (p : ℝ)) * (p : ℝ) ^ d - (1 / 2 : ℝ) * ((p : ℝ) + 1) ^ d

theorem criteria_as_printed (p σ d : ℕ)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hσ : 2 ≤ σ) (hd : 1 ≤ d) :
    ((d : ℝ) ≤ paperCenter p - 20 →
      Real.log (2 * (Real.log (p : ℝ) / Real.log 2) * (p : ℝ) ^ (d - 1)) /
        Real.log (σ : ℝ) < paperPhi p d) ∧
    (paperCenter p + 20 ≤ (d : ℝ) →
      paperPhi p d <
        -(Real.log (2 * (Real.log ((p : ℝ) + 1) / Real.log 2) *
          ((p : ℝ) + 1) ^ (d - 1)) / Real.log (σ : ℝ))) := by
  simpa only [paperCenter, paperPhi, dc, phi_natCast, Real.logb] using
    inversionExplicitWindow20_proved p σ d hp hp3 hσ hd

theorem actual_cardinality_window (p σ d : ℕ)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hσ : 2 ≤ σ) (hd : 1 ≤ d) :
    ((d : ℝ) ≤ paperCenter p - 20 →
      paperProbability p d σ < paperProbability (p + 1) d σ) ∧
    (paperCenter p + 20 ≤ (d : ℝ) →
      paperProbability (p + 1) d σ < paperProbability p d σ) := by
  exact inversionWindow20_proved p σ d hp hp3 hσ hd

-- The paper does not repeat d ≥ 1 in the upper branch. It follows from
-- the window condition; the shared Lean antecedent loses no instances.
theorem upper_without_extra_dimension_hypothesis (p σ d : ℕ)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hσ : 2 ≤ σ)
    (hwin : paperCenter p + 20 ≤ (d : ℝ)) :
    paperProbability (p + 1) d σ < paperProbability p d σ := by
  have hc : (0 : ℝ) ≤ paperCenter p := (dc_bounds (by omega : 2 ≤ p)).1
  have hdreal : (1 : ℝ) ≤ d := by linarith
  have hd : 1 ≤ d := by exact_mod_cast hdreal
  exact (actual_cardinality_window p σ d hp hp3 hσ hd).2 hwin

-- These are conclusions about actual configuration counts, not merely
-- proofs that a window hypothesis is inhabited.
theorem first_lower_window_instance (σ : ℕ) (hσ : 2 ≤ σ) :
    paperProbability 37 4 σ < paperProbability 38 4 σ := by
  apply (actual_cardinality_window 37 σ 4 (by norm_num) (by omega) hσ (by omega)).1
  have hc : (24 : ℝ) ≤ paperCenter 37 := dc37_bounds.1
  norm_num
  linarith

theorem exact_upper_boundary_instance (σ : ℕ) (hσ : 2 ≤ σ) :
    paperProbability 4 21 σ < paperProbability 3 21 σ := by
  apply upper_without_extra_dimension_hypothesis 3 σ 21 (by norm_num) (by omega) hσ
  change dc 3 + 20 ≤ (21 : ℝ)
  rw [← p11_dc_eq, ShiftSym.P11.dc_three]
  norm_num

-- Existing existential statements are preserved by the supplement.
example (h : inversionExplicitWindow20Statement) : inversionExplicitWindowStatement := ⟨20, h⟩
example (h : inversionWindow20Statement) : inversionWindowStatement := ⟨20, h⟩

#print axioms criteria_as_printed
#print axioms actual_cardinality_window
#print axioms upper_without_extra_dimension_hypothesis
#print axioms first_lower_window_instance
#print axioms exact_upper_boundary_instance
end PR1Review
