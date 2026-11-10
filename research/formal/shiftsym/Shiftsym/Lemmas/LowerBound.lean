/-
Phase E, part 3: the machine-checked lower-bound theorem
`lowerBound_proved : lowerBoundStatement n d σ` (paper Theorem 6.1,
claim C009): for n ≥ 2, d ≥ 1, σ ≥ 2,

    F_d(n, σ) ≤ |S|,  with equality iff n is prime.

Proof strategy (post-D2, purely arithmetic — no rectangular tori):
* prime n: the certified enumeration formula collapses to F_d
  (PrimeCase.lean) — equality;
* composite n: a single order-p₁ subgroup (p₁ = minFac n) already fixes
  σ^{n^d/p₁} ≥ σ^{2·n^{d−1}} configurations, while the whole envelope is
  at most K·σ^{n^{d−1}} with K < 2^{n^{d−1}} ≤ σ^{n^{d−1}} (Ineq.lean) —
  strict inequality.
-/
import Shiftsym.Lemmas.Ineq
import Shiftsym.Lemmas.PrimeCase
import Shiftsym.Lemmas.Evaluate

open scoped Classical

namespace ShiftSym

variable {n d : ℕ}

theorem gaussBinom_one_pos {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) :
    0 < gaussBinom q d 1 := by
  by_contra h
  have h0 : gaussBinom q d 1 = 0 := by omega
  have hgeom := sub_one_mul_gaussBinom (by omega : 1 ≤ q) d
  rw [h0, Nat.mul_zero] at hgeom
  have h2 : 2 ≤ q ^ d := by
    calc 2 ≤ q := hq
    _ = q ^ 1 := (pow_one q).symm
    _ ≤ q ^ d := Nat.pow_le_pow_right (by omega) hd
  omega

theorem exists_orderP_subgroup [NeZero n] {p : ℕ} (pp : p.Prime)
    (hpn : p ∣ n) (hd : 1 ≤ d) :
    ∃ C : AddSubgroup (Lat n d), Nat.card C = p := by
  have hcount := card_orderP_subgroups (n := n) (d := d) pp hpn
  have hpos : 0 < Nat.card {C : AddSubgroup (Lat n d) // Nat.card C = p} := by
    rw [hcount]
    exact gaussBinom_one_pos pp.two_le hd
  obtain ⟨⟨C, hC⟩, -⟩ := Nat.card_pos_iff.mp hpos
  exact ⟨C, hC⟩

/-- The fixed configurations of a single order-`p` subgroup already give
`σ^{n^d/p}` shift-symmetric configurations. -/
theorem card_SS_ge_fix (σ : ℕ) [NeZero n] {p : ℕ} (pp : p.Prime)
    (hpn : p ∣ n) (hd : 1 ≤ d) :
    σ ^ (n ^ d / p)
      ≤ (Finset.univ.filter
          (fun s : Config n d (Fin σ) => IsShiftSymmetric s)).card := by
  obtain ⟨C, hC⟩ := exists_orderP_subgroup pp hpn hd
  have hcard : (fixedByF σ C).card = σ ^ (n ^ d / p) := by
    rw [card_fixedByF, hC]
  rw [← hcard]
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [isShiftSymmetric_iff_mem_biUnion]
  exact Finset.mem_biUnion.mpr ⟨C, mem_primeOrderSubs.mpr (hC ▸ pp), hs⟩

/-- The envelope is at most `K · σ^{n^{d−1}}` with
`K = [d 1]_n + (d−2)·2^d·n^{C(d,2)}`. -/
theorem lowerEnvelope_le_K {σ : ℕ} (hn : 2 ≤ n) (hσ : 1 ≤ σ)
    (hd : 1 ≤ d) :
    lowerEnvelope n d σ
      ≤ ((gaussBinom n d 1 + (d - 2) * 2 ^ d * n ^ d.choose 2 : ℕ) : ℤ)
          * (σ : ℤ) ^ n ^ (d - 1) := by
  rw [lowerEnvelope]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 d)
    (fun r => Odd r)]
  have heven : (∑ r ∈ (Finset.Icc 1 d).filter (fun r => ¬Odd r),
      (-1 : ℤ) ^ (r + 1) * (rdCoeff n r d : ℤ)
        * (σ : ℤ) ^ n ^ (d - r)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro r hr
    obtain ⟨-, hre⟩ := Finset.mem_filter.mp hr
    rw [Nat.not_odd_iff_even] at hre
    rw [hre.add_one.neg_one_pow, neg_one_mul, neg_mul]
    exact neg_nonpos_of_nonneg (mul_nonneg (Int.natCast_nonneg _)
      (pow_nonneg (Int.natCast_nonneg _) _))
  have hodd : (∑ r ∈ (Finset.Icc 1 d).filter (fun r => Odd r),
      (-1 : ℤ) ^ (r + 1) * (rdCoeff n r d : ℤ) * (σ : ℤ) ^ n ^ (d - r))
      ≤ ((gaussBinom n d 1 : ℕ) : ℤ) * (σ : ℤ) ^ n ^ (d - 1)
        + (((d - 2) * 2 ^ d * n ^ d.choose 2 : ℕ) : ℤ)
            * (σ : ℤ) ^ n ^ (d - 1) := by
    have hterm : ∀ r ∈ (Finset.Icc 1 d).filter (fun r => Odd r),
        (-1 : ℤ) ^ (r + 1) * (rdCoeff n r d : ℤ) * (σ : ℤ) ^ n ^ (d - r)
          = (rdCoeff n r d : ℤ) * (σ : ℤ) ^ n ^ (d - r) := by
      intro r hr
      obtain ⟨-, hro⟩ := Finset.mem_filter.mp hr
      rw [hro.add_one.neg_one_pow, one_mul]
    rw [Finset.sum_congr rfl hterm]
    have h1mem : 1 ∈ (Finset.Icc 1 d).filter (fun r => Odd r) := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_refl 1, hd⟩, odd_one⟩
    rw [← Finset.add_sum_erase _ _ h1mem]
    apply add_le_add
    · rw [rdCoeff, show (1 : ℕ).choose 2 = 0 from rfl, pow_zero, one_mul]
    · set B : ℤ := ((2 ^ d * n ^ d.choose 2 : ℕ) : ℤ)
        * (σ : ℤ) ^ n ^ (d - 1) with hBdef
      have hBnonneg : 0 ≤ B := mul_nonneg (Int.natCast_nonneg _)
        (pow_nonneg (Int.natCast_nonneg _) _)
      have htail : ∀ r ∈ ((Finset.Icc 1 d).filter (fun r => Odd r)).erase 1,
          (rdCoeff n r d : ℤ) * (σ : ℤ) ^ n ^ (d - r) ≤ B := by
        intro r hr
        obtain ⟨hIcc, -⟩ :=
          Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)
        obtain ⟨hr1, hrd⟩ := Finset.mem_Icc.mp hIcc
        have hcoeff : rdCoeff n r d ≤ 2 ^ d * n ^ d.choose 2 :=
          rdCoeff_le (by omega) hrd
        have hexp : (σ : ℤ) ^ n ^ (d - r) ≤ (σ : ℤ) ^ n ^ (d - 1) := by
          apply pow_le_pow_right₀ (by exact_mod_cast hσ)
          exact Nat.pow_le_pow_right (by omega) (by omega)
        rw [hBdef]
        exact mul_le_mul (by exact_mod_cast hcoeff) hexp
          (pow_nonneg (Int.natCast_nonneg _) _) (Int.natCast_nonneg _)
      have hsubset : ((Finset.Icc 1 d).filter (fun r => Odd r)).erase 1
          ⊆ Finset.Icc 3 d := by
        intro r hr
        have hr1 : r ≠ 1 := Finset.ne_of_mem_erase hr
        obtain ⟨hIcc, hro⟩ :=
          Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hIcc
        rw [Finset.mem_Icc]
        have hmod := Nat.odd_iff.mp hro
        omega
      have hcardle :
          (((Finset.Icc 1 d).filter (fun r => Odd r)).erase 1).card
            ≤ d - 2 := by
        calc _ ≤ (Finset.Icc 3 d).card := Finset.card_le_card hsubset
        _ = d - 2 := by rw [Nat.card_Icc]; omega
      calc (∑ r ∈ ((Finset.Icc 1 d).filter (fun r => Odd r)).erase 1,
            (rdCoeff n r d : ℤ) * (σ : ℤ) ^ n ^ (d - r))
          ≤ (((Finset.Icc 1 d).filter (fun r => Odd r)).erase 1).card • B :=
            Finset.sum_le_card_nsmul _ _ _ htail
        _ = ((((Finset.Icc 1 d).filter
              (fun r => Odd r)).erase 1).card : ℤ) * B := nsmul_eq_mul _ _
        _ ≤ ((d - 2 : ℕ) : ℤ) * B := by
            apply mul_le_mul_of_nonneg_right ?_ hBnonneg
            exact_mod_cast hcardle
        _ = (((d - 2) * 2 ^ d * n ^ d.choose 2 : ℕ) : ℤ)
              * (σ : ℤ) ^ n ^ (d - 1) := by
            rw [hBdef]
            push_cast
            ring
  calc (∑ r ∈ (Finset.Icc 1 d).filter (fun r => Odd r), _)
        + (∑ r ∈ (Finset.Icc 1 d).filter (fun r => ¬Odd r), _)
      ≤ (((gaussBinom n d 1 : ℕ) : ℤ) * (σ : ℤ) ^ n ^ (d - 1)
          + (((d - 2) * 2 ^ d * n ^ d.choose 2 : ℕ) : ℤ)
              * (σ : ℤ) ^ n ^ (d - 1)) + 0 := add_le_add hodd heven
    _ = ((gaussBinom n d 1 + (d - 2) * 2 ^ d * n ^ d.choose 2 : ℕ) : ℤ)
          * (σ : ℤ) ^ n ^ (d - 1) := by
        push_cast
        ring

/-- **Strict inequality at composite `n`**: one fixed-set beats the
whole envelope. -/
theorem lowerEnvelope_lt_card (σ : ℕ) [NeZero n] (hn2 : 2 ≤ n)
    (hnp : ¬n.Prime) (hd : 1 ≤ d) (hσ : 2 ≤ σ) :
    lowerEnvelope n d σ
      < ((Finset.univ.filter
          (fun s : Config n d (Fin σ) => IsShiftSymmetric s)).card : ℤ) := by
  set p := n.minFac with hpdef
  have pp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := n.minFac_dvd
  have hp2 : 2 ≤ p := pp.two_le
  have hsq : p * p ≤ n := by
    have h := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
    calc p * p = p ^ 2 := (sq p).symm
    _ ≤ n := h
  have hn4 : 4 ≤ n := le_trans (Nat.mul_le_mul hp2 hp2) hsq
  have hdiv2 : 2 ≤ n / p := by
    rw [Nat.le_div_iff_mul_le pp.pos]
    calc 2 * p ≤ p * p := Nat.mul_le_mul_right p hp2
    _ ≤ n := hsq
  have hexp : 2 * n ^ (d - 1) ≤ n ^ d / p := by
    have h1 : n ^ d = n ^ (d - 1) * n := by
      conv_lhs => rw [show d = (d - 1) + 1 by omega]
      ring
    rw [h1, Nat.mul_div_assoc _ hpn]
    calc 2 * n ^ (d - 1) = n ^ (d - 1) * 2 := by ring
    _ ≤ n ^ (d - 1) * (n / p) := Nat.mul_le_mul_left _ hdiv2
  have hKσ : (gaussBinom n d 1 + (d - 2) * 2 ^ d * n ^ d.choose 2 : ℕ)
      < σ ^ n ^ (d - 1) := by
    calc _ < 2 ^ n ^ (d - 1) := envelope_coeff_lt_two_pow hn4 hd
    _ ≤ σ ^ n ^ (d - 1) := Nat.pow_le_pow_left hσ _
  have hσpos : (0 : ℤ) < (σ : ℤ) ^ n ^ (d - 1) :=
    pow_pos (by exact_mod_cast (by omega : 0 < σ)) _
  calc lowerEnvelope n d σ
      ≤ ((gaussBinom n d 1 + (d - 2) * 2 ^ d * n ^ d.choose 2 : ℕ) : ℤ)
          * (σ : ℤ) ^ n ^ (d - 1) :=
        lowerEnvelope_le_K (by omega) (by omega) hd
    _ < (σ : ℤ) ^ n ^ (d - 1) * (σ : ℤ) ^ n ^ (d - 1) := by
        apply mul_lt_mul_of_pos_right ?_ hσpos
        exact_mod_cast hKσ
    _ = (σ : ℤ) ^ (2 * n ^ (d - 1)) := by
        rw [← pow_add]
        congr 1
        ring
    _ ≤ (σ : ℤ) ^ (n ^ d / p) :=
        pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ σ)) hexp
    _ ≤ ((Finset.univ.filter
          (fun s : Config n d (Fin σ) => IsShiftSymmetric s)).card : ℤ) := by
        exact_mod_cast card_SS_ge_fix σ pp hpn hd

/-! ### The lower-bound theorem -/

/-- **The lower-bound theorem, machine-checked** (paper Theorem 6.1,
claim C009): for `n ≥ 2`, `d ≥ 1`, `σ ≥ 2`, the envelope `F_d(n, σ)` is
a lower bound for the number of shift-symmetric configurations, with
equality precisely when `n` is prime. -/
theorem lowerBound_proved (n dd σ : ℕ) : lowerBoundStatement n dd σ := by
  intro hn2 hd1 hσ2
  haveI : NeZero n := ⟨by omega⟩
  have hcard := enumeration_proved n dd σ hn2 hd1 (by omega)
  by_cases hp : n.Prime
  · have heq : lowerEnvelope n dd σ
        = (Nat.card {s : Config n dd (Fin σ) // IsShiftSymmetric s} : ℤ) := by
      rw [hcard, enumerationRHS_prime hp dd σ]
    exact ⟨le_of_eq heq, fun _ => hp, fun _ => heq⟩
  · have hlt' := lowerEnvelope_lt_card (n := n) (d := dd) σ hn2 hp hd1 hσ2
    have hlt : lowerEnvelope n dd σ
        < (Nat.card {s : Config n dd (Fin σ) // IsShiftSymmetric s} : ℤ) := by
      rw [natCard_shiftSymmetric_eq_filterCard]
      exact hlt'
    exact ⟨le_of_lt hlt, fun heq => absurd heq (ne_of_lt hlt),
      fun hp' => absurd hp' hp⟩

end ShiftSym
