/-
Independent judgment of the two open correspondence-audit items (2026-10-27):
Lemma A.2 (`lem:coef`) and Corollary 8.2 (`cor:insolv`). Probes only; nothing here
is part of the Lean development. Run from research/formal/shiftsym:
  lake env lean ../correspondence_audit/independent_judgment/Probes.lean
-/
import Shiftsym.Paper.Proofs.P07_Dynamics
import Shiftsym.Paper.Proofs.P10_AppendixLemmas

namespace IndependentJudgment
open ShiftSym ShiftSym.P07 ShiftSym.P10

/-! ## Lemma A.2 -/

-- The certificates have exactly the frozen types.
#check (lemA2_proved : lemA2Statement)

-- `gaussProd` is the §3 product formula: spot values against subspace counts of 𝔽_2^d
-- ([3 1]_2 = 7 lines in 𝔽_2^3, [4 2]_2 = 35 planes in 𝔽_2^4).
example : gaussProd 2 3 1 = 7 := by norm_num [gaussProd]
example : gaussProd 2 4 2 = 35 := by norm_num [gaussProd, Finset.prod_range_succ]
-- r_d(q, j) = q^C(j,2)·[d j]_q:  r_3(2, 2) = 2·[3 2]_2 = 14.
example : rdReal 2 3 2 = 14 := by norm_num [rdReal, gaussProd, Finset.prod_range_succ]
-- D = d(d−1)/2.
example : DD 4 = 6 := by decide

-- The standing hypothesis d ≥ 1 is needed by part (3): at d = 0 its right side is −4.
example : ¬ ∀ q : ℝ, 2 ≤ q →
    ∑ j ∈ Finset.Icc 2 0, rdReal q 0 j ≤ 4 * ((0 : ℝ) - 1) * q ^ DD 0 := by
  intro h
  have := h 2 le_rfl
  norm_num [DD] at this

-- Part (1) without the restriction j ≤ d, with the printed exponents read as integers
-- (q^{d−i} and q^{j(d−j)} with d − i, d − j possibly negative): for j > d the product
-- contains the factor q^0 − 1 = 0, so the frozen j ≤ d loses nothing.
noncomputable def printedGauss (q : ℝ) (d j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j, (q ^ ((d : ℤ) - i) - 1) / (q ^ (i + 1) - 1)

theorem lemA2Part1_all_j (q : ℝ) (d j : ℕ) (hq : 2 ≤ q) (hd : 1 ≤ d) :
    printedGauss q d j ≤ 4 * q ^ ((j : ℤ) * ((d : ℤ) - j)) := by
  have hq0 : 0 < q := by linarith
  rcases le_or_gt j d with hj | hj
  · have hp : printedGauss q d j = gaussProd q d j := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have : i ≤ d := by have := Finset.mem_range.mp hi; omega
      rw [← Int.natCast_sub this, zpow_natCast]
    rw [hp, ← Int.natCast_sub hj, ← Int.natCast_mul, zpow_natCast]
    exact lemA2Part1_proved q d j hq hd hj
  · have h0 : printedGauss q d j = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hj) (by simp)
    rw [h0]; positivity

#print axioms lemA2Part1_all_j

/-! ## Corollary 8.2 -/

#check (insolv_proved : insolvStatement)

-- Non-vacuity of the general statement with NONEMPTY acceptable-output sets: leader
-- election on Z_2 (σ = 2, leader state 0) requires leaving S.
def oneLeader : Config 2 1 (Fin 2) := fun u => if u = 0 then 0 else 1

example : RequiresLeavingS (leaderTask 2 1 2 0) ∧ oneLeader ∈ (leaderTask 2 1 2 0).accept 0 := by
  refine ⟨⟨fun _ => 0, Set.mem_univ _, ⟨fun _ => 1, by decide, rfl⟩, fun t ht => ?_⟩, ?_⟩
  · exact leaderAsym_proved 2 1 2 le_rfl le_rfl le_rfl (by norm_num) t ⟨0, ht⟩
  · refine ⟨0, by simp [oneLeader], fun u hu => ?_⟩
    by_contra h
    simp [oneLeader, h] at hu

/- The sentence added in paper v5 ("every pattern-recognition or image-processing task
whose required output breaks a symmetry of some admissible input") read literally: on some
admissible input x, no acceptable output keeps all the symmetries of x. -/
def BreaksSymmetry {n d σ : ℕ} (T : Task n d σ) : Prop :=
  ∃ x ∈ T.admissible, ∀ y ∈ T.accept x, ¬ stab x ≤ stab y

-- (a) The claim is true: it follows from Theorem 8.1 in stabilizer form (frozen
-- `irrevStabStatement`), iterated along the trajectory.
theorem insolv_breaksSymmetry : ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ → 1 < n ^ d →
    ∀ T : Task n d σ, BreaksSymmetry T →
      ∀ Φ : Config n d (Fin σ) → Config n d (Fin σ), Equivariant Φ → ¬ Solves Φ T := by
  intro n d σ hn hd hσ _ T ⟨x, hx, hbr⟩ Φ hΦ hsol
  have hmono : ∀ k : ℕ, stab x ≤ stab (Φ^[k] x) := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (irrevStab_proved n d σ hn hd hσ Φ hΦ _)
  obtain ⟨k, hk⟩ := hsol x hx
  exact hbr _ hk (hmono k)

#print axioms insolv_breaksSymmetry

-- (b) It is strictly more than `RequiresLeavingS`, the hypothesis of the frozen
-- `insolvGeneralStatement`: on Z_4, asking the constant input to become the period-2
-- pattern 0101 breaks the symmetry of the input, yet the output is still shift-symmetric.
def zero4 : Config 4 1 (Fin 2) := fun _ => 0
def alt4 : Config 4 1 (Fin 2) := fun u => if (u 0).val % 2 = 0 then 0 else 1

def stripeTask : Task 4 1 2 where
  admissible := {zero4}
  accept := fun _ => {alt4}

example : BreaksSymmetry stripeTask ∧ ¬ RequiresLeavingS stripeTask := by
  have hfix : shift (fun _ => 2) alt4 = alt4 := by
    funext u; revert u; decide
  refine ⟨⟨zero4, rfl, fun y hy hle => ?_⟩, fun ⟨x, hx, _, hacc⟩ => ?_⟩
  · have hy' : y = alt4 := hy
    subst hy'
    have h1 : (fun _ => (1 : ZMod 4)) ∈ stab zero4 := rfl
    have := congrFun (hle h1) 0
    revert this; decide
  · have hx' : x = zero4 := hx
    subst hx'
    exact hacc (rfl : alt4 ∈ stripeTask.accept zero4) ⟨fun _ => 2, by decide, hfix⟩

end IndependentJudgment
