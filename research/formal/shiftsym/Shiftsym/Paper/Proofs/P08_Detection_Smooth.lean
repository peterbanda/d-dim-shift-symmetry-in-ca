/-
Group 08 (paper §9, Remark 9.3 (ii)(b)): integers all of whose prime factors are
polylogarithmically small have natural density zero (Rankin's trick).
Helper module of `P08_Detection.lean`.

Route: for `0 < α`, `#{n ≤ X : P⁺(n) ≤ Y} ≤ X^α ∏_{p ≤ Y} (1 - p^{-α})⁻¹` (each such `n`
is `∏_{p ≤ Y} p^{e_p}` with `e_p ≤ X`); for `1/2 ≤ α ≤ 1` the product is at most
`exp(4 Y^{1-α} (1 + log Y))` (harmonic-sum bound); with `Y = B (log X)^K` and
`α = 1 - 1/(2K)` the exponent is `-(log X)/(2K) + O(√(log X) log log X) → -∞`.
-/
import Shiftsym.Paper.S08_Detection

namespace ShiftSym.P08

open Finset

/-- **Rankin's bound**. -/
theorem rankin_bound (Y X : ℕ) (hX : 1 ≤ X) {α : ℝ} (hα : 0 < α) :
    (((Finset.Icc 1 X).filter fun n => ∀ p ∈ n.primeFactors, p ≤ Y).card : ℝ)
      ≤ (X : ℝ) ^ α * ∏ p ∈ (Finset.range (Y + 1)).filter Nat.Prime,
          (1 - ((p : ℝ) ^ α)⁻¹)⁻¹ := by
  classical
  set P := (Finset.range (Y + 1)).filter Nat.Prime with hP
  set S := (Finset.Icc 1 X).filter fun n => ∀ p ∈ n.primeFactors, p ≤ Y with hS
  set g : ℕ → ℝ := fun n => ((n : ℝ) ^ α)⁻¹ with hg
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  -- Step 1: `#S ≤ X^α Σ_{n ∈ S} g n`
  have h1 : (S.card : ℝ) ≤ (X : ℝ) ^ α * ∑ n ∈ S, g n := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn'.1
    have hle : (n : ℝ) ^ α ≤ (X : ℝ) ^ α :=
      Real.rpow_le_rpow hnpos.le (by exact_mod_cast hn'.2) hα.le
    have hpos : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos hnpos α
    simp only [hg, Nat.cast_one]
    rw [← div_eq_mul_inv, one_le_div hpos]
    exact hle
  -- Step 2: `Σ_{n ∈ S} g n ≤ ∏_{p ∈ P} Σ_{e ≤ X} (g p)^e`
  set T := Fintype.piFinset (fun _ : P => Finset.range (X + 1)) with hT
  set ψ : (P → ℕ) → ℕ := fun t => ∏ i : P, (i : ℕ) ^ (t i) with hψ
  have hsub : S ⊆ T.image ψ := by
    intro n hn
    have hn1 := Finset.mem_filter.mp hn
    have hnI := Finset.mem_Icc.mp hn1.1
    have hn0 : n ≠ 0 := by omega
    rw [Finset.mem_image]
    refine ⟨fun i => n.factorization i, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      have := Nat.factorization_lt (i : ℕ) hn0
      rw [Finset.mem_range]; omega
    · simp only [hψ]
      rw [Finset.prod_coe_sort P (fun p => p ^ n.factorization p)]
      have hsubP : n.primeFactors ⊆ P := by
        intro p hp
        rw [hP, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le (hn1.2 p hp), Nat.prime_of_mem_primeFactors hp⟩
      rw [← Finset.prod_subset hsubP (fun p _ hp => by
        rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization]), pow_zero])]
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      rw [Finsupp.prod, Nat.support_factorization]
  have hgnn : ∀ n, 0 ≤ g n := fun n => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) α)
  have hgψ : ∀ t : P → ℕ, g (ψ t) = ∏ i : P, (g i) ^ (t i) := by
    intro t
    simp only [hg, hψ]
    push_cast
    rw [← Real.finsetProd_rpow _ _ (fun i _ => pow_nonneg (Nat.cast_nonneg _) _),
      ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← Real.rpow_pow_comm (Nat.cast_nonneg _), inv_pow]
  have h2 : ∑ n ∈ S, g n ≤ ∏ p ∈ P, ∑ e ∈ Finset.range (X + 1), (g p) ^ e := by
    calc ∑ n ∈ S, g n ≤ ∑ n ∈ T.image ψ, g n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hgnn n)
      _ ≤ ∑ t ∈ T, g (ψ t) := Finset.sum_image_le_of_nonneg (fun n _ => hgnn n)
      _ = ∑ t ∈ T, ∏ i : P, (g i) ^ (t i) := Finset.sum_congr rfl (fun t _ => hgψ t)
      _ = ∏ i : P, ∑ e ∈ Finset.range (X + 1), (g i) ^ e := by
          rw [hT, Finset.prod_univ_sum]
      _ = ∏ p ∈ P, ∑ e ∈ Finset.range (X + 1), (g p) ^ e :=
          Finset.prod_coe_sort P (fun p => ∑ e ∈ Finset.range (X + 1), (g p) ^ e)
  -- Step 3: geometric sums
  have h3 : ∏ p ∈ P, ∑ e ∈ Finset.range (X + 1), (g p) ^ e ≤ ∏ p ∈ P, (1 - g p)⁻¹ := by
    refine Finset.prod_le_prod (fun p _ => Finset.sum_nonneg (fun e _ => pow_nonneg (hgnn p) e))
      (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
    have hgp1 : g p < 1 := by
      simp only [hg]
      have : 1 < (p : ℝ) ^ α := Real.one_lt_rpow (by exact_mod_cast hp2) hα
      exact inv_lt_one_of_one_lt₀ this
    rw [geom_sum_eq hgp1.ne, ← neg_div_neg_eq, neg_sub, neg_sub, div_eq_mul_inv]
    have hpow : 0 ≤ (g p) ^ (X + 1) := pow_nonneg (hgnn p) _
    have hinv : 0 ≤ (1 - g p)⁻¹ := inv_nonneg.mpr (by linarith)
    nlinarith
  calc (S.card : ℝ) ≤ (X : ℝ) ^ α * ∑ n ∈ S, g n := h1
    _ ≤ (X : ℝ) ^ α * ∏ p ∈ P, (1 - g p)⁻¹ := by
        apply mul_le_mul_of_nonneg_left (h2.trans h3) (Real.rpow_nonneg hXpos.le α)

/-- `(1 - r)⁻¹ ≤ exp(4r)` for `0 ≤ r ≤ 3/4`. -/
theorem inv_one_sub_le_exp {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 3 / 4) :
    (1 - r)⁻¹ ≤ Real.exp (4 * r) := by
  have h1 : (1 - r)⁻¹ ≤ 1 + 4 * r := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith
  have h2 := Real.add_one_le_exp (4 * r)
  linarith

/-- `2^α ≥ 4/3` for `α ≥ 1/2`. -/
theorem four_thirds_le_two_rpow {α : ℝ} (hα : 1 / 2 ≤ α) : (4 / 3 : ℝ) ≤ (2 : ℝ) ^ α := by
  have h1 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ α :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hα
  have h2 : (4 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  linarith

/-- The Rankin product is at most `exp(4 Y^{1-α} (1 + log Y))` for `1/2 ≤ α ≤ 1`. -/
theorem rankin_prod_le (Y : ℕ) {α : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α ≤ 1) :
    ∏ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, (1 - ((p : ℝ) ^ α)⁻¹)⁻¹
      ≤ Real.exp (4 * ((Y : ℝ) ^ (1 - α) * (1 + Real.log Y))) := by
  set P := (Finset.range (Y + 1)).filter Nat.Prime with hP
  have hα0 : 0 < α := by linarith
  have hr : ∀ p ∈ P, 0 ≤ ((p : ℝ) ^ α)⁻¹ ∧ ((p : ℝ) ^ α)⁻¹ ≤ 3 / 4 := by
    intro p hp
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
    have hpa : (2 : ℝ) ^ α ≤ (p : ℝ) ^ α :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp2) hα0.le
    have h43 := four_thirds_le_two_rpow hα
    refine ⟨inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg p) α), ?_⟩
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    norm_num; linarith
  -- product ≤ exp(4 Σ r_p)
  have h1 : ∏ p ∈ P, (1 - ((p : ℝ) ^ α)⁻¹)⁻¹ ≤ Real.exp (4 * ∑ p ∈ P, ((p : ℝ) ^ α)⁻¹) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · exact inv_nonneg.mpr (by linarith [(hr p hp).2])
    · exact inv_one_sub_le_exp (hr p hp).1 (hr p hp).2
  -- Σ_{p ∈ P} p^{-α} ≤ Σ_{m ∈ [1, Y]} p^{-α} ≤ Y^{1-α} H_Y
  have hPsub : P ⊆ Finset.Icc 1 Y := by
    intro p hp
    have := Finset.mem_filter.mp hp
    rw [Finset.mem_Icc]
    exact ⟨this.2.one_lt.le, Nat.lt_succ_iff.mp (Finset.mem_range.mp this.1)⟩
  have h2 : ∑ p ∈ P, ((p : ℝ) ^ α)⁻¹ ≤ ∑ m ∈ Finset.Icc 1 Y, ((m : ℝ) ^ α)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hPsub
      (fun m _ _ => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg m) α))
  have h3 : ∑ m ∈ Finset.Icc 1 Y, ((m : ℝ) ^ α)⁻¹
      ≤ ∑ m ∈ Finset.Icc 1 Y, (Y : ℝ) ^ (1 - α) * (m : ℝ)⁻¹ := by
    refine Finset.sum_le_sum (fun m hm => ?_)
    have hm' := Finset.mem_Icc.mp hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm'.1
    have hle : (m : ℝ) ^ (1 - α) ≤ (Y : ℝ) ^ (1 - α) :=
      Real.rpow_le_rpow hmpos.le (by exact_mod_cast hm'.2) (by linarith)
    have hpos : 0 < (m : ℝ) ^ α := Real.rpow_pos_of_pos hmpos α
    calc ((m : ℝ) ^ α)⁻¹ = (m : ℝ) ^ (1 - α) * (m : ℝ)⁻¹ := by
          rw [Real.rpow_sub hmpos, Real.rpow_one]
          field_simp
      _ ≤ (Y : ℝ) ^ (1 - α) * (m : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hmpos.le)
  have h4 : ∑ m ∈ Finset.Icc 1 Y, (Y : ℝ) ^ (1 - α) * (m : ℝ)⁻¹
      ≤ (Y : ℝ) ^ (1 - α) * (1 + Real.log Y) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg Y) _)
    have hh := harmonic_le_one_add_log Y
    rw [harmonic_eq_sum_Icc] at hh
    push_cast at hh
    exact hh
  calc ∏ p ∈ P, (1 - ((p : ℝ) ^ α)⁻¹)⁻¹ ≤ Real.exp (4 * ∑ p ∈ P, ((p : ℝ) ^ α)⁻¹) := h1
    _ ≤ Real.exp (4 * ((Y : ℝ) ^ (1 - α) * (1 + Real.log Y))) := by
        apply Real.exp_le_exp.mpr
        linarith [h2.trans (h3.trans h4)]

/-- `b √L (c + K log L) - a L → -∞` as `L → ∞` (explicit form). -/
theorem eventually_sqrt_log_le {a b c K : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hK : 0 ≤ K) (t : ℝ) :
    ∃ L0 : ℝ, ∀ L ≥ L0, b * Real.sqrt L * (c + K * Real.log L) - a * L ≤ t := by
  set D := b * (c + K) with hDdef
  have hD0 : 0 ≤ D := by positivity
  set δ := a / (2 * (D + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨L1, hL1⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound hδpos)
  refine ⟨max (max 1 L1) (max (1 / δ ^ 2) (-2 * t / a)), ?_⟩
  intro L hL
  have hL1' : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLL1 : L1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLδ : 1 / δ ^ 2 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLt : -2 * t / a ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hLpos : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1'
  have hsq0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hsqsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have hlog : Real.log L ≤ δ * Real.sqrt L := by
    have h := hL1 L hLL1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hLpos.le _), ← Real.sqrt_eq_rpow] at h
    exact h
  have hsq : Real.sqrt L ≤ δ * L := by
    have h1 : 1 / δ ≤ Real.sqrt L := by
      rw [Real.le_sqrt (by positivity) hLpos.le, div_pow, one_pow]; exact hLδ
    have h2 : 1 ≤ δ * Real.sqrt L := by
      rw [div_le_iff₀ hδpos] at h1; linarith
    calc Real.sqrt L = 1 * Real.sqrt L := (one_mul _).symm
      _ ≤ (δ * Real.sqrt L) * Real.sqrt L := mul_le_mul_of_nonneg_right h2 hsq0
      _ = δ * L := by rw [mul_assoc, hsqsq]
  have hsqlog : Real.sqrt L * Real.log L ≤ δ * L := by
    calc Real.sqrt L * Real.log L ≤ Real.sqrt L * (δ * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left hlog hsq0
      _ = δ * (Real.sqrt L * Real.sqrt L) := by ring
      _ = δ * L := by rw [hsqsq]
  have e4 : D * δ ≤ a / 2 := by
    have : D * δ = a / 2 * (D / (D + 1)) := by rw [hδ]; field_simp
    rw [this]
    apply mul_le_of_le_one_right (by positivity)
    rw [div_le_one (by positivity)]; linarith
  have hmain : b * Real.sqrt L * (c + K * Real.log L) ≤ a / 2 * L := by
    have e1 : b * Real.sqrt L * (c + K * Real.log L)
        = b * c * Real.sqrt L + b * K * (Real.sqrt L * Real.log L) := by ring
    have e2 : b * c * Real.sqrt L ≤ b * c * (δ * L) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e3 : b * K * (Real.sqrt L * Real.log L) ≤ b * K * (δ * L) :=
      mul_le_mul_of_nonneg_left hsqlog (by positivity)
    have e5 : b * c * (δ * L) + b * K * (δ * L) = D * δ * L := by rw [hDdef]; ring
    have e6 : D * δ * L ≤ a / 2 * L := mul_le_mul_of_nonneg_right e4 hLpos.le
    linarith
  have ht : -2 * t ≤ a * L := by
    rw [div_le_iff₀ ha] at hLt; linarith
  linarith

/-- **Density zero** of the integers `n ≤ X` with `Σ_{p ∣ n} p^d ≤ C (log n^d)^k`. -/
theorem polylog_density_zero (d : ℕ) (hd : 1 ≤ d) (C : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ((((Finset.Icc 2 X).filter fun n : ℕ =>
        (∑ p ∈ n.primeFactors, (p : ℝ) ^ d) ≤ C * (Real.log ((n : ℝ) ^ d)) ^ k).card : ℝ)
        ≤ ε * (X : ℝ)) := by
  set K : ℕ := k + 1 with hK
  have hKpos : (0 : ℝ) < K := by positivity
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  set B : ℝ := |C| * (d : ℝ) ^ k + 1 with hB
  have hB0 : 0 ≤ |C| * (d : ℝ) ^ k := by positivity
  have hB1 : 1 ≤ B := by linarith
  set α : ℝ := 1 - 1 / (2 * K) with hα
  have hinv : 1 / (2 * (K : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hinv0 : 0 < 1 / (2 * (K : ℝ)) := by positivity
  have hα12 : 1 / 2 ≤ α := by rw [hα]; linarith
  have hα1 : α ≤ 1 := by rw [hα]; linarith
  have h1α : 1 - α = 1 / (2 * K) := by rw [hα]; ring
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  obtain ⟨L0, hL0⟩ := eventually_sqrt_log_le (a := 1 / (2 * K)) (b := 4 * B ^ (1 / (2 * (K : ℝ))))
    (c := 1 + Real.log B) (K := K) hinv0 (by positivity) (by linarith) hKpos.le (Real.log ε)
  refine ⟨max 3 ⌈Real.exp L0⌉₊, ?_⟩
  intro X hX
  have hX3 : 3 ≤ X := le_trans (le_max_left _ _) hX
  have hXr : (3 : ℝ) ≤ X := by exact_mod_cast hX3
  have hXpos : (0 : ℝ) < X := by linarith
  set L := Real.log X with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hXpos]
    have := Real.exp_one_lt_d9
    linarith
  have hLL0 : L0 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hXpos]
    have : (⌈Real.exp L0⌉₊ : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_right _ _) hX
    exact le_trans (Nat.le_ceil _) this
  have hL0' : (0 : ℝ) ≤ L := by linarith
  set y : ℝ := B * L ^ K with hy
  have hLK1 : 1 ≤ L ^ K := one_le_pow₀ hL1
  have hy1 : 1 ≤ y := one_le_mul_of_one_le_of_one_le hB1 hLK1
  set Y : ℕ := ⌊y⌋₊ with hYdef
  have hY1 : 1 ≤ Y := Nat.le_floor (by simpa using hy1)
  have hYy : (Y : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY1
  -- the set is contained in the `Y`-smooth integers `≤ X`
  have hsub : ((Finset.Icc 2 X).filter fun n : ℕ =>
      (∑ p ∈ n.primeFactors, (p : ℝ) ^ d) ≤ C * (Real.log ((n : ℝ) ^ d)) ^ k)
      ⊆ (Finset.Icc 1 X).filter fun n => ∀ p ∈ n.primeFactors, p ≤ Y := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    obtain ⟨hnI, hsum⟩ := hn
    have hnI' := Finset.mem_Icc.mp hnI
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, hnI'.2⟩, ?_⟩
    intro p hp
    apply Nat.le_floor
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hlognL : Real.log n ≤ L := Real.log_le_log hnpos (by exact_mod_cast hnI'.2)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    calc (p : ℝ) ≤ (p : ℝ) ^ d := le_self_pow₀ hp1 (by omega)
      _ ≤ ∑ q ∈ n.primeFactors, (q : ℝ) ^ d :=
          Finset.single_le_sum (f := fun q : ℕ => (q : ℝ) ^ d) (fun q _ => by positivity) hp
      _ ≤ C * (Real.log ((n : ℝ) ^ d)) ^ k := hsum
      _ = C * ((d : ℝ) ^ k * (Real.log n) ^ k) := by rw [Real.log_pow, mul_pow]
      _ ≤ |C| * ((d : ℝ) ^ k * (Real.log n) ^ k) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((d : ℝ) ^ k * L ^ K) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc (Real.log n) ^ k ≤ L ^ k := pow_le_pow_left₀ hlogn0 hlognL k
            _ ≤ L ^ K := pow_le_pow_right₀ hL1 (by omega)
      _ ≤ y := by
          rw [hy, hB, ← mul_assoc]
          nlinarith
  have hcard := Finset.card_le_card hsub
  have hR := rankin_bound Y X (by omega) (α := α) (by linarith)
  have hP := rankin_prod_le Y hα12 hα1
  -- the exponent
  have hY1α : (Y : ℝ) ^ (1 - α) ≤ B ^ (1 / (2 * (K : ℝ))) * Real.sqrt L := by
    calc (Y : ℝ) ^ (1 - α) ≤ y ^ (1 - α) := Real.rpow_le_rpow hYpos.le hYy (by linarith)
      _ = B ^ (1 / (2 * (K : ℝ))) * (L ^ K) ^ (1 / (2 * (K : ℝ))) := by
          rw [h1α, hy, Real.mul_rpow (by linarith) (by positivity)]
      _ = B ^ (1 / (2 * (K : ℝ))) * Real.sqrt L := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0', Real.sqrt_eq_rpow]
          congr 1; field_simp
  have hlogY : Real.log Y ≤ Real.log B + K * Real.log L := by
    calc Real.log Y ≤ Real.log y := Real.log_le_log hYpos hYy
      _ = Real.log B + K * Real.log L := by
          rw [hy, Real.log_mul (by linarith) (by positivity), Real.log_pow]
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast hY1)
  have hA : 0 ≤ (Y : ℝ) ^ (1 - α) := Real.rpow_nonneg hYpos.le _
  have hexp : 4 * ((Y : ℝ) ^ (1 - α) * (1 + Real.log Y))
      ≤ 4 * B ^ (1 / (2 * (K : ℝ))) * Real.sqrt L * (1 + Real.log B + K * Real.log L) := by
    have hm := mul_le_mul hY1α (by linarith : 1 + Real.log Y ≤ 1 + Real.log B + K * Real.log L)
      (by linarith) (by positivity)
    linarith
  have hfinal : (X : ℝ) ^ α * Real.exp (4 * ((Y : ℝ) ^ (1 - α) * (1 + Real.log Y)))
      ≤ ε * X := by
    have hL := hL0 L hLL0
    have hεX : ε * X = Real.exp (Real.log ε + L) := by
      rw [Real.exp_add, Real.exp_log hε, hLdef, Real.exp_log hXpos]
    rw [Real.rpow_def_of_pos hXpos, ← Real.exp_add, hεX, ← hLdef]
    apply Real.exp_le_exp.mpr
    have hαL : L * α = L - 1 / (2 * (K : ℝ)) * L := by rw [hα]; ring
    rw [hαL]
    linarith
  calc _ ≤ (((Finset.Icc 1 X).filter fun n => ∀ p ∈ n.primeFactors, p ≤ Y).card : ℝ) := by
        exact_mod_cast hcard
    _ ≤ (X : ℝ) ^ α * ∏ p ∈ (Finset.range (Y + 1)).filter Nat.Prime,
          (1 - ((p : ℝ) ^ α)⁻¹)⁻¹ := hR
    _ ≤ (X : ℝ) ^ α * Real.exp (4 * ((Y : ℝ) ^ (1 - α) * (1 + Real.log Y))) :=
        mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg hXpos.le _)
    _ ≤ ε * X := hfinal

end ShiftSym.P08
