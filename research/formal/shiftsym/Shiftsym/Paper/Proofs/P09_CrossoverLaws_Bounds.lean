/-
Phase H, group 09 (CrossoverLaws) — PROOF helper module: the combinatorial
two-sided bound of Proposition 10.1 (`prop:rate`) and the prefactor chain.

* `numSS_ge_pow`      — `σ^{N/p_1} ≤ |S|` (one order-`p_1` fixed set);
* `numSS_le_sopfD`    — `|S| ≤ sopf_d(n) · σ^{N/p_1}` (union bound over the
                        prime-order cyclic subgroups, grouped by their order);
* prefactor chain     — `sopf_d(n) ≤ Σ 2p^{d−1} ≤ 2ω(n)n^{d−1} ≤ 2 log₂(n) n^{d−1}`.
-/
import Shiftsym.Paper.S09_CrossoverLaws
import Shiftsym.Lemmas.LowerBound

open scoped Classical

namespace ShiftSym.P09

open ShiftSym

/-- `|S|` as a filter-cardinality (bridge to the certified library). -/
theorem numSS_eq_filterCard (n d σ : ℕ) [NeZero n] :
    numSS n d σ = (Finset.univ.filter
      (fun s : Config n d (Fin σ) => IsShiftSymmetric s)).card :=
  natCard_shiftSymmetric_eq_filterCard σ

/-- Lower bound of Proposition 10.1 in `ℕ`. -/
theorem numSS_ge_pow {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    σ ^ (n ^ d / p1 n) ≤ numSS n d σ := by
  have : NeZero n := ⟨by omega⟩
  rw [numSS_eq_filterCard]
  exact card_SS_ge_fix σ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n) hd

/-- Every prime-order subgroup has order a prime factor of `n`. -/
theorem card_mem_primeFactors {n d : ℕ} [NeZero n] {C : AddSubgroup (Lat n d)}
    (hC : (Nat.card C).Prime) : Nat.card C ∈ n.primeFactors := by
  rw [Nat.mem_primeFactors]
  refine ⟨hC, ?_, NeZero.ne n⟩
  have h1 : Nat.card C ∣ Nat.card (Lat n d) := AddSubgroup.card_addSubgroup_dvd_card C
  rw [card_lat] at h1
  exact hC.dvd_of_dvd_pow h1

/-- The number of prime-order cyclic subgroups is at most `sopf_d(n)`. -/
theorem card_primeOrderSubs_le {n d : ℕ} [NeZero n] :
    (primeOrderSubs n d).card ≤ sopfD n d := by
  have hsub : primeOrderSubs n d ⊆ n.primeFactors.biUnion
      (fun p => Finset.univ.filter (fun C : AddSubgroup (Lat n d) => Nat.card C = p)) := by
    intro C hC
    rw [mem_primeOrderSubs] at hC
    rw [Finset.mem_biUnion]
    exact ⟨Nat.card C, card_mem_primeFactors hC, by simp⟩
  calc (primeOrderSubs n d).card
      ≤ (n.primeFactors.biUnion
          (fun p => Finset.univ.filter
            (fun C : AddSubgroup (Lat n d) => Nat.card C = p))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ n.primeFactors, (Finset.univ.filter
          (fun C : AddSubgroup (Lat n d) => Nat.card C = p)).card :=
        Finset.card_biUnion_le
    _ = sopfD n d := by
        unfold sopfD
        apply Finset.sum_congr rfl
        intro p hp
        rw [← card_orderP_subgroups (n := n) (d := d) (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp)]
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- For every prime `p ∣ n`: `N/p ≤ N/p_1`. -/
theorem div_le_div_p1 {n d p : ℕ} (hp : p ∈ n.primeFactors) :
    n ^ d / p ≤ n ^ d / p1 n :=
  Nat.div_le_div_left (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le
    (Nat.dvd_of_mem_primeFactors hp)) (Nat.minFac_pos n)

/-- Union bound (Theorem 6.3(i) form, exponents raised to `N/p_1`):
`|S| ≤ sopf_d(n) · σ^{N/p_1}`. -/
theorem numSS_le_sopfD {n d σ : ℕ} (hn : 2 ≤ n) (hσ : 1 ≤ σ) :
    numSS n d σ ≤ sopfD n d * σ ^ (n ^ d / p1 n) := by
  have : NeZero n := ⟨by omega⟩
  rw [numSS_eq_filterCard]
  have hunion : Finset.univ.filter
      (fun s : Config n d (Fin σ) => IsShiftSymmetric s)
      = (primeOrderSubs n d).biUnion (fun C => fixedByF σ C) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isShiftSymmetric_iff_mem_biUnion σ s
  rw [hunion]
  calc ((primeOrderSubs n d).biUnion (fun C => fixedByF σ C)).card
      ≤ ∑ C ∈ primeOrderSubs n d, (fixedByF σ C).card := Finset.card_biUnion_le
    _ ≤ ∑ _C ∈ primeOrderSubs n d, σ ^ (n ^ d / p1 n) := by
        apply Finset.sum_le_sum
        intro C hC
        rw [card_fixedByF]
        apply Nat.pow_le_pow_right hσ
        exact div_le_div_p1 (card_mem_primeFactors (mem_primeOrderSubs.mp hC))
    _ = (primeOrderSubs n d).card * σ ^ (n ^ d / p1 n) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ sopfD n d * σ ^ (n ^ d / p1 n) :=
        Nat.mul_le_mul_right _ card_primeOrderSubs_le

/-! ### The prefactor chain (proof of Proposition 10.1, lines 912–915) -/

/-- `Σ_{p∣n} [d 1]_p ≤ Σ_{p∣n} 2 p^{d−1}`. -/
theorem sopfD_le_sum (n d : ℕ) :
    (sopfD n d : ℝ) ≤ ∑ p ∈ n.primeFactors, 2 * (p : ℝ) ^ (d - 1) := by
  unfold sopfD
  push_cast
  apply Finset.sum_le_sum
  intro p hp
  have h := gaussBinom_d_one_le (Nat.prime_of_mem_primeFactors hp).two_le d
  exact_mod_cast h

/-- `Σ_{p∣n} 2 p^{d−1} ≤ 2 ω(n) n^{d−1}`. -/
theorem sum_le_omega {n : ℕ} (d : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ n.primeFactors, 2 * (p : ℝ) ^ (d - 1) ≤
      2 * (n.primeFactors.card : ℝ) * (n : ℝ) ^ (d - 1) := by
  calc ∑ p ∈ n.primeFactors, 2 * (p : ℝ) ^ (d - 1)
      ≤ ∑ _p ∈ n.primeFactors, 2 * (n : ℝ) ^ (d - 1) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpn : p ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
        have hpn' : (p : ℝ) ≤ n := by exact_mod_cast hpn
        gcongr
    _ = 2 * (n.primeFactors.card : ℝ) * (n : ℝ) ^ (d - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- `ω(n) ≤ log₂ n` (from `2^{ω(n)} ≤ ∏_{p∣n} p ≤ n`). -/
theorem omega_le_log2 {n : ℕ} (hn : 2 ≤ n) :
    (n.primeFactors.card : ℝ) ≤ Real.logb 2 (n : ℝ) := by
  have h1 : 2 ^ n.primeFactors.card ≤ n := by
    calc 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
          Finset.pow_card_le_prod _ _ _
            (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
  exact_mod_cast h1

/-- `2 ω(n) n^{d−1} ≤ 2 log₂(n) n^{d−1}`. -/
theorem omega_term_le {n : ℕ} (d : ℕ) (hn : 2 ≤ n) :
    2 * (n.primeFactors.card : ℝ) * (n : ℝ) ^ (d - 1) ≤
      2 * Real.logb 2 (n : ℝ) * (n : ℝ) ^ (d - 1) := by
  have h := omega_le_log2 hn
  gcongr

/-- Real-valued upper bound `|S| ≤ 2 log₂(n) n^{d−1} σ^{N/p_1}`. -/
theorem numSS_le_real {n d σ : ℕ} (hn : 2 ≤ n) (hσ : 1 ≤ σ) :
    (numSS n d σ : ℝ) ≤
      2 * Real.logb 2 (n : ℝ) * (n : ℝ) ^ (d - 1) * (σ : ℝ) ^ (n ^ d / p1 n) := by
  have h1 : (numSS n d σ : ℝ) ≤ (sopfD n d : ℝ) * (σ : ℝ) ^ (n ^ d / p1 n) := by
    exact_mod_cast numSS_le_sopfD (d := d) hn hσ
  have h2 : (sopfD n d : ℝ) ≤ 2 * Real.logb 2 (n : ℝ) * (n : ℝ) ^ (d - 1) :=
    (sopfD_le_sum n d).trans ((sum_le_omega d hn).trans (omega_term_le d hn))
  calc (numSS n d σ : ℝ) ≤ (sopfD n d : ℝ) * (σ : ℝ) ^ (n ^ d / p1 n) := h1
    _ ≤ 2 * Real.logb 2 (n : ℝ) * (n : ℝ) ^ (d - 1) * (σ : ℝ) ^ (n ^ d / p1 n) := by
        gcongr

end ShiftSym.P09
