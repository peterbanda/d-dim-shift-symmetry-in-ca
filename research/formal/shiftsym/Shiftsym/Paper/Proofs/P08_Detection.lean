/-
Group 08 (paper §9, Detection): proofs of every frozen statement of
`Shiftsym/Paper/S08_Detection.lean` (namespace `ShiftSym.P08`).

Helper modules: `P08_Detection_Algo` (the algorithm model: pass characterization,
disjoint walks, exact orbit sum via independence, single-defect sum, schedules,
correctness, union bound) and `P08_Detection_Smooth` (Rankin's bound: polylog-smooth
integers have density zero).
-/
import Shiftsym.Paper.Proofs.P08_Detection_Algo
import Shiftsym.Paper.Proofs.P08_Detection_Smooth

namespace ShiftSym.P08

open ShiftSym

/-! ## Arithmetic helpers -/

section Helpers

variable {n d : ℕ}

theorem card_lat_eq [NeZero n] : Fintype.card (Lat n d) = n ^ d := by
  simp [Lat, ZMod.card]

theorem card_config_real [NeZero n] (σ : ℕ) :
    (Fintype.card (Config n d (Fin σ)) : ℝ) = (σ : ℝ) ^ Fintype.card (Lat n d) := by
  have : Fintype.card (Config n d (Fin σ)) = σ ^ Fintype.card (Lat n d) := by
    simp only [Config, Fintype.card_fun, Fintype.card_fin]
  rw [this]; push_cast; rfl

/-- `Q = σ^(1-p)` lies in `(0, 1/2]` for `σ, p ≥ 2`. -/
theorem Q_pos {σ : ℕ} (hσ : 2 ≤ σ) (p : ℕ) : 0 < (σ : ℝ) ^ ((1 : ℤ) - p) :=
  zpow_pos (by exact_mod_cast (by omega : 0 < σ)) _

theorem Q_le_half {σ p : ℕ} (hσ : 2 ≤ σ) (hp : 2 ≤ p) : (σ : ℝ) ^ ((1 : ℤ) - p) ≤ 1 / 2 := by
  have h1 : (1 : ℝ) ≤ σ := by exact_mod_cast (by omega : 1 ≤ σ)
  have h2 : (1 : ℤ) - p ≤ -1 := by omega
  calc (σ : ℝ) ^ ((1 : ℤ) - p) ≤ (σ : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ h1 h2
    _ = (σ : ℝ)⁻¹ := zpow_neg_one _
    _ ≤ 1 / 2 := by
      rw [one_div]
      exact inv_anti₀ (by norm_num) (by exact_mod_cast hσ)

theorem geom_eq {Q : ℝ} (hQ : Q < 1) (m : ℕ) :
    ∑ i ∈ Finset.range m, Q ^ i = (1 - Q ^ m) / (1 - Q) := by
  rw [geom_sum_eq hQ.ne m, ← neg_div_neg_eq, neg_sub, neg_sub]

theorem geom_le {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ : Q < 1) (m : ℕ) :
    ∑ i ∈ Finset.range m, Q ^ i ≤ 1 / (1 - Q) := by
  rw [geom_eq hQ]
  apply div_le_div_of_nonneg_right _ (by linarith)
  have := pow_nonneg hQ0 m
  linarith

theorem one_div_one_sub_Q_le_two {σ p : ℕ} (hσ : 2 ≤ σ) (hp : 2 ≤ p) :
    1 / (1 - (σ : ℝ) ^ ((1 : ℤ) - p)) ≤ 2 := by
  have h := Q_le_half hσ hp
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem gaussBinom_ge_pow {q : ℕ} (hq : 1 ≤ q) {d : ℕ} (hd : 1 ≤ d) :
    q ^ (d - 1) ≤ gaussBinom q d 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hgeom := sub_one_mul_gaussBinom hq (e + 1)
  simp only [Nat.add_sub_cancel]
  rcases Nat.eq_or_lt_of_le hq with h1 | h1
  · subst h1
    -- q = 1: [e+1 1]_1 = e + 1
    have : ∀ m, gaussBinom 1 m 1 = m := by
      intro m
      induction m with
      | zero => simp [gaussBinom]
      | succ m ih => simp [gaussBinom, ih]; omega
    rw [this]; simp
  · have hpos : 0 < q - 1 := by omega
    have hpow : q ^ (e + 1) = q * q ^ e := by ring
    have h1' : 1 ≤ q ^ e := Nat.one_le_pow _ _ (by omega)
    have key : (q - 1) * q ^ e ≤ (q - 1) * gaussBinom q (e + 1) 1 := by
      rw [hgeom, hpow, Nat.sub_mul, one_mul]
      omega
    exact Nat.le_of_mul_le_mul_left key hpos

theorem p_mul_gaussBinom_le {p : ℕ} (hp : 2 ≤ p) {d : ℕ} (hd : 1 ≤ d) :
    p * gaussBinom p d 1 ≤ 2 * p ^ d := by
  have h := gaussBinom_d_one_le hp d
  have : p * p ^ (d - 1) = p ^ d := by
    rw [← pow_succ']; congr 1; omega
  calc p * gaussBinom p d 1 ≤ p * (2 * p ^ (d - 1)) := Nat.mul_le_mul_left _ h
    _ = 2 * p ^ d := by rw [← this]; ring

theorem sopfD_prime {n : ℕ} (hn : n.Prime) (d : ℕ) : sopfD n d = gaussBinom n d 1 := by
  rw [sopfD, hn.primeFactors, Finset.sum_singleton]

end Helpers

/-! ## Claims inside the algorithm's description -/

theorem algorithmInputsExist_proved : ∀ n d : ℕ, algorithmInputsExistStatement n d := by
  intro n d hn _
  have : NeZero n := ⟨by omega⟩
  exact ⟨schedule_exists, traversal_exists⟩

theorem scheduleCount_proved : ∀ n d : ℕ, scheduleCountStatement n d := by
  intro n d hn _ sched hs
  have : NeZero n := ⟨by omega⟩
  exact ⟨fun p hp hpn => schedule_filter_length hs hp hpn, schedule_length hs⟩

theorem algorithmSpec_proved : ∀ n d : ℕ, algorithmSpecStatement n d :=
  fun n d => ⟨algorithmInputsExist_proved n d, scheduleCount_proved n d⟩

/-! ## Correctness -/

theorem completenessIff_proved : ∀ n d σ : ℕ, completenessIffStatement n d σ := by
  intro n d σ hn _ _ s
  have : NeZero n := ⟨by omega⟩
  exact completeness_iff s

theorem detectCorrect_proved : ∀ n d σ : ℕ, detectCorrectStatement n d σ := by
  intro n d σ hn _ _ sched hs ord hord st s
  have : NeZero n := ⟨by omega⟩
  exact detect_correct hs hord st s

/-! ## Theorem 9.1 -/

theorem detect_reads_le_worst {n d : ℕ} [NeZero n] {A : Type*} [DecidableEq A]
    {sched : List (ℕ × Lat n d)} (hs : IsSchedule sched) (ord : ℕ × Lat n d → List (Lat n d))
    (st : Bool) (s : Config n d A) :
    (detect st s ord sched).2 ≤ n ^ d * sopfD n d := by
  calc (detect st s ord sched).2
      ≤ (sched.map fun e => (subgroupTest st s (ord e) e.1 e.2).2.2).sum :=
        detect_reads_le_sum st s ord sched
    _ ≤ (sched.map fun _ => n ^ d).sum := by
        apply List.sum_le_sum
        intro e he
        rw [← card_lat_eq]
        exact subgroupTest_reads_le st s (ord e) (hs.1 e he).1.pos (hs.1 e he).2.2
    _ = n ^ d * sopfD n d := by
        rw [List.map_const', List.sum_replicate, schedule_length hs, smul_eq_mul, Nat.mul_comm]

theorem detectWorst_proved : ∀ n d σ : ℕ, detectWorstStatement n d σ := by
  intro n d σ hn _ _ sched hs ord _ st s
  have : NeZero n := ⟨by omega⟩
  exact detect_reads_le_worst hs ord st s

theorem thmDetectWorst_proved : ∀ n d σ : ℕ, thmDetectWorstStatement n d σ :=
  fun n d σ => ⟨completenessIff_proved n d σ, detectCorrect_proved n d σ,
    detectWorst_proved n d σ⟩

/-! ## Proposition 9.2 -/

/-- Exact expectation of the number of orbits visited by one subgroup test. -/
theorem expect_orbits {n d : ℕ} [NeZero n] {σ : ℕ} (hσ : 2 ≤ σ) {p : ℕ} (hp : 2 ≤ p)
    {w : Lat n d} (hw : addOrderOf w = p) {ord : List (Lat n d)} (hord : IsTraversalOrder ord)
    (st : Bool) :
    expectUnif (fun s : Config n d (Fin σ) => (subgroupTest st s ord p w).2.1)
      = ∑ i ∈ Finset.range (Fintype.card (Lat n d) / p), ((σ : ℝ) ^ ((1 : ℤ) - p)) ^ i := by
  unfold expectUnif
  rw [subgroupTest_sum_orbits st (by omega) hord (by omega) hw, card_config_real]
  have : (σ : ℝ) ^ Fintype.card (Lat n d) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (by omega : σ ≠ 0))
  field_simp

theorem detectAvgOrbits_proved : ∀ (n d σ : ℕ) [NeZero n], detectAvgOrbitsStatement n d σ := by
  intro n d σ _ _ _ hσ p hp _ w hw ord hord st
  rw [expect_orbits hσ hp.two_le hw hord st, card_lat_eq]
  have hQ : (σ : ℝ) ^ ((1 : ℤ) - p) < 1 := by
    have := Q_le_half hσ hp.two_le; linarith
  exact geom_eq hQ _

/-- The expected total reads are at most `Σ_{p ∣ n} [d 1]_p p/(1 - σ^(1-p))`. -/
theorem expect_reads_le {n d : ℕ} [NeZero n] {σ : ℕ} (hσ : 2 ≤ σ)
    {sched : List (ℕ × Lat n d)} (hs : IsSchedule sched)
    {ord : ℕ × Lat n d → List (Lat n d)} (hord : ∀ e ∈ sched, IsTraversalOrder (ord e))
    (st : Bool) :
    expectUnif (fun s : Config n d (Fin σ) => (detect st s ord sched).2)
      ≤ ∑ p ∈ n.primeFactors,
          (gaussBinom p d 1 : ℝ) * ((p : ℝ) / (1 - (σ : ℝ) ^ ((1 : ℤ) - (p : ℤ)))) := by
  set T := sched.toFinset with hT
  set N := Fintype.card (Lat n d) with hN
  have hσpos : (0 : ℝ) < (σ : ℝ) ^ N := pow_pos (by exact_mod_cast (by omega : 0 < σ)) _
  -- pointwise bound
  have hpt : ∀ s : Config n d (Fin σ), ((detect st s ord sched).2 : ℝ)
      ≤ ∑ e ∈ T, (e.1 : ℝ) * ((subgroupTest st s (ord e) e.1 e.2).2.1 : ℝ) := by
    intro s
    have h1 := detect_reads_le_sum st s ord sched
    rw [← List.sum_toFinset _ (schedule_nodup hs)] at h1
    have h2 : ((detect st s ord sched).2 : ℝ)
        ≤ ∑ e ∈ T, ((subgroupTest st s (ord e) e.1 e.2).2.2 : ℝ) := by
      exact_mod_cast h1
    refine h2.trans (Finset.sum_le_sum (fun e _ => ?_))
    exact_mod_cast subgroupTest_reads_le_mul st s (ord e) e.1 e.2
  unfold expectUnif
  rw [card_config_real, div_le_iff₀ hσpos]
  calc ∑ s : Config n d (Fin σ), ((detect st s ord sched).2 : ℝ)
      ≤ ∑ s : Config n d (Fin σ),
          ∑ e ∈ T, (e.1 : ℝ) * ((subgroupTest st s (ord e) e.1 e.2).2.1 : ℝ) :=
        Finset.sum_le_sum (fun s _ => hpt s)
    _ = ∑ e ∈ T, (e.1 : ℝ) *
          ∑ s : Config n d (Fin σ), ((subgroupTest st s (ord e) e.1 e.2).2.1 : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ e ∈ T, (e.1 : ℝ) * ((σ : ℝ) ^ N *
          ∑ i ∈ Finset.range (N / e.1), ((σ : ℝ) ^ ((1 : ℤ) - e.1)) ^ i) := by
        refine Finset.sum_congr rfl (fun e he => ?_)
        have he' := List.mem_toFinset.mp he
        rw [subgroupTest_sum_orbits st (by omega) (hord e he') (hs.1 e he').1.pos
          (hs.1 e he').2.2]
    _ ≤ ∑ e ∈ T, (e.1 : ℝ) * ((σ : ℝ) ^ N * (1 / (1 - (σ : ℝ) ^ ((1 : ℤ) - e.1)))) := by
        refine Finset.sum_le_sum (fun e he => ?_)
        have he' := List.mem_toFinset.mp he
        have hp2 := (hs.1 e he').1.two_le
        have hQ0 := (Q_pos hσ e.1).le
        have hQ1 : (σ : ℝ) ^ ((1 : ℤ) - e.1) < 1 := by
          have := Q_le_half hσ hp2; linarith
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (geom_le hQ0 hQ1 _) hσpos.le
    _ = (∑ e ∈ T, (fun p : ℕ => (p : ℝ) / (1 - (σ : ℝ) ^ ((1 : ℤ) - p))) e.1) *
          (σ : ℝ) ^ N := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        simp only; ring
    _ = (∑ p ∈ n.primeFactors,
          (gaussBinom p d 1 : ℝ) * ((p : ℝ) / (1 - (σ : ℝ) ^ ((1 : ℤ) - (p : ℤ))))) *
          (σ : ℝ) ^ N := by
        rw [hT, schedule_sum hs (fun p : ℕ => (p : ℝ) / (1 - (σ : ℝ) ^ ((1 : ℤ) - p)))]
        simp only [nsmul_eq_mul]

theorem detectAvgReads_proved : ∀ (n d σ : ℕ) [NeZero n], detectAvgReadsStatement n d σ := by
  intro n d σ _ _ _ hσ sched hs ord hord st
  exact expect_reads_le hσ hs hord st

theorem bound_le {n d σ : ℕ} (hσ : 2 ≤ σ) :
    ∑ p ∈ n.primeFactors,
        (gaussBinom p d 1 : ℝ) * ((p : ℝ) / (1 - (σ : ℝ) ^ ((1 : ℤ) - (p : ℤ))))
      ≤ 2 * ∑ p ∈ n.primeFactors, (p : ℝ) * (gaussBinom p d 1 : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  have h := one_div_one_sub_Q_le_two hσ hp2
  have hQ := Q_le_half hσ hp2
  have : (p : ℝ) / (1 - (σ : ℝ) ^ ((1 : ℤ) - (p : ℤ))) ≤ 2 * p := by
    rw [div_le_iff₀ (by linarith)]
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith
  calc (gaussBinom p d 1 : ℝ) * ((p : ℝ) / (1 - (σ : ℝ) ^ ((1 : ℤ) - (p : ℤ))))
      ≤ (gaussBinom p d 1 : ℝ) * (2 * p) := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
    _ = 2 * ((p : ℝ) * (gaussBinom p d 1 : ℝ)) := by ring

theorem detectAvgBoundLe_proved : ∀ n d σ : ℕ, detectAvgBoundLeStatement n d σ := by
  intro n d σ _ _ hσ
  exact bound_le hσ

theorem bigO_le {n d : ℕ} (hd : 1 ≤ d) :
    2 * ∑ p ∈ n.primeFactors, (p : ℝ) * (gaussBinom p d 1 : ℝ)
      ≤ 4 * ∑ p ∈ n.primeFactors, (p : ℝ) ^ d := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  have h := p_mul_gaussBinom_le hp2 hd
  have h' : (p : ℝ) * (gaussBinom p d 1 : ℝ) ≤ 2 * (p : ℝ) ^ d := by exact_mod_cast h
  linarith

theorem detectAvgBigO_proved : detectAvgBigOStatement :=
  ⟨4, fun _ _ _ hd => bigO_le hd⟩

theorem detectAvgReadsBigO_proved : detectAvgReadsBigOStatement := by
  refine ⟨4, ?_⟩
  intro n d σ _ _ hd hσ sched hs ord hord st
  exact (expect_reads_le hσ hs hord st).trans ((bound_le hσ).trans (bigO_le hd))

theorem propDetectAvg_proved : ∀ (n d σ : ℕ) [NeZero n], propDetectAvgStatement n d σ :=
  fun n d σ _ => ⟨detectAvgOrbits_proved n d σ, detectAvgReads_proved n d σ,
    detectAvgBoundLe_proved n d σ, detectAvgBigO_proved, detectAvgReadsBigO_proved⟩

theorem avgOrbitsChecked_proved : avgOrbitsCheckedStatement :=
  ⟨detectAvgOrbits_proved 2 3 2, detectAvgOrbits_proved 2 3 3, detectAvgOrbits_proved 2 4 2,
    detectAvgOrbits_proved 2 2 2, detectAvgOrbits_proved 3 2 2, detectAvgOrbits_proved 3 2 3,
    detectAvgOrbits_proved 4 2 2⟩

/-! ## Remark 9.3 -/

theorem remPolylogPrimeSum_proved : ∀ n d : ℕ, remPolylogPrimeSumStatement n d := by
  intro n d hn _
  rw [hn.primeFactors, Finset.sum_singleton]

/-- For prime `n`, the expected reads are at most `4 n^d`. -/
theorem expect_reads_le_prime {n d σ : ℕ} [NeZero n] (hn : n.Prime) (hd : 1 ≤ d) (hσ : 2 ≤ σ)
    {sched : List (ℕ × Lat n d)} (hs : IsSchedule sched)
    {ord : ℕ × Lat n d → List (Lat n d)} (hord : ∀ e ∈ sched, IsTraversalOrder (ord e))
    (st : Bool) :
    expectUnif (fun s : Config n d (Fin σ) => (detect st s ord sched).2) ≤ 4 * (n : ℝ) ^ d := by
  have h := (expect_reads_le hσ hs hord st).trans ((bound_le hσ).trans (bigO_le hd))
  rwa [hn.primeFactors, Finset.sum_singleton] at h

theorem remPolylogAvgPrime_proved : remPolylogAvgPrimeStatement := by
  refine ⟨4, ?_⟩
  intro n d σ _ hn hd hσ sched hs ord hord st
  exact expect_reads_le_prime hn hd hσ hs hord st

theorem remPolylogWorstPrime_proved : remPolylogWorstPrimeStatement := by
  refine ⟨2, ?_⟩
  intro n d σ hn hd _ sched hs ord _ st s
  have : NeZero n := ⟨hn.ne_zero⟩
  have h := detect_reads_le_worst hs ord st s
  rw [sopfD_prime hn] at h
  have h2 := gaussBinom_d_one_le hn.two_le d
  have h3 : (detect st s ord sched).2 ≤ 2 * (n ^ d * n ^ (d - 1)) := by
    calc (detect st s ord sched).2 ≤ n ^ d * gaussBinom n d 1 := h
      _ ≤ n ^ d * (2 * n ^ (d - 1)) := Nat.mul_le_mul_left _ h2
      _ = 2 * (n ^ d * n ^ (d - 1)) := by ring
  exact_mod_cast h3

theorem defect_not_sym {n d σ : ℕ} (hσ : 2 ≤ σ) (x0 : Lat n d) :
    ¬ IsShiftSymmetric (defect hσ x0) := by
  rintro ⟨v, hv, hfix⟩
  have h := congrFun hfix (x0 - v)
  simp only [shift_apply, sub_add_cancel] at h
  have hne : x0 - v ≠ x0 := by
    intro h'; apply hv; simpa using h'
  simp only [defect, if_neg hne] at h
  exact absurd (congrArg Fin.val h) (by simp)

theorem aux_ineq_worst (n m T S : ℕ) (hm : 2 ≤ m) (hT : m ≤ T)
    (hS : T * (n * n * (m * (m - 1))) ≤ 2 * S) : n * m * (n * m * m) ≤ 4 * S := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : k + 2 - 1 = k + 1 := by omega
  rw [hk] at hS
  calc n * (k + 2) * (n * (k + 2) * (k + 2))
      = (k + 2) * (n * n * ((k + 2) * (k + 2))) := by ring
    _ ≤ (k + 2) * (n * n * ((k + 2) * (2 * (k + 1)))) := by
        apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; omega
    _ = 2 * ((k + 2) * (n * n * ((k + 2) * (k + 1)))) := by ring
    _ ≤ 2 * (T * (n * n * ((k + 2) * (k + 1)))) := by
        apply Nat.mul_le_mul_left; exact Nat.mul_le_mul_right _ hT
    _ ≤ 4 * S := by omega

/-- For prime `n`, some configuration costs at least `N n^(d-1) / 4` reads. -/
theorem worst_lower_exists {n d σ : ℕ} [NeZero n] (hn : n.Prime) (hd : 1 ≤ d) (hσ : 2 ≤ σ)
    {sched : List (ℕ × Lat n d)} (hs : IsSchedule sched)
    {ord : ℕ × Lat n d → List (Lat n d)} (hord : ∀ e ∈ sched, IsTraversalOrder (ord e))
    (st : Bool) :
    ∃ s : Config n d (Fin σ), n ^ d * n ^ (d - 1) ≤ 4 * (detect st s ord sched).2 := by
  rcases Nat.eq_or_lt_of_le hd with h1 | h2
  · -- d = 1: the constant configuration passes the first subgroup, reading all `N` cells
    subst h1
    let s0 : Config n 1 (Fin σ) := fun _ => ⟨0, by omega⟩
    refine ⟨s0, ?_⟩
    have hlen := schedule_length hs
    rw [sopfD_prime hn] at hlen
    have hg : gaussBinom n 1 1 = 1 := by simp [gaussBinom]
    rw [hg] at hlen
    obtain ⟨e, rest, rfl⟩ : ∃ e rest, sched = e :: rest := by
      rcases sched with _ | ⟨e, rest⟩
      · simp at hlen
      · exact ⟨e, rest, rfl⟩
    have he : e ∈ e :: rest := List.mem_cons_self
    have hpass : (subgroupTest st s0 (ord e) e.1 e.2).1 = true :=
      (entry_test_iff hs hord st s0 he).mpr rfl
    rw [detect_reads_cons_of_pass st s0 ord e rest hpass,
      subgroupTest_reads_of_pass st s0 (hord e he) (hs.1 e he).1.pos (hs.1 e he).2.2 hpass,
      card_lat_eq]
    simp only [pow_one, Nat.sub_self, pow_zero, mul_one]
    omega
  · -- d ≥ 2: average over the single-defect configurations
    have hall : ∀ x0 : Lat n d, ∀ e ∈ sched,
        (subgroupTest st (defect hσ x0) (ord e) e.1 e.2).1 = false := by
      intro x0 e he
      by_contra hc
      have hc' : (subgroupTest st (defect hσ x0) (ord e) e.1 e.2).1 = true := by
        simpa using hc
      exact defect_not_sym hσ x0
        ⟨e.2, entry_ne_zero hs he, (entry_test_iff hs hord st _ he).mp hc'⟩
    have hreads : ∀ x0 : Lat n d, (detect st (defect hσ x0) ord sched).2
        = ∑ e ∈ sched.toFinset, (subgroupTest st (defect hσ x0) (ord e) e.1 e.2).2.2 := by
      intro x0
      rw [detect_reads_eq_sum_of_fail st _ ord sched (hall x0),
        List.sum_toFinset _ (schedule_nodup hs)]
    have he1 : ∀ e ∈ sched, e.1 = n := fun e he =>
      (Nat.prime_dvd_prime_iff_eq (hs.1 e he).1 hn).mp (hs.1 e he).2.1
    set m := n ^ (d - 1) with hmdef
    have hnd : n ^ d = n * m := by
      rw [hmdef, ← pow_succ']; congr 1; omega
    have hN : Fintype.card (Lat n d) = n * m := by rw [card_lat_eq, hnd]
    have hNm : Fintype.card (Lat n d) / n = m := by
      rw [hN]; exact Nat.mul_div_cancel_left m hn.pos
    have hsum_e : ∀ e ∈ sched.toFinset, n * n * (m * (m - 1)) ≤
        2 * ∑ x0 : Lat n d, (subgroupTest st (defect hσ x0) (ord e) e.1 e.2).2.2 := by
      intro e he
      have he' := List.mem_toFinset.mp he
      have := subgroupTest_sum_defect st hσ (hord e he') (hs.1 e he').1.pos (hs.1 e he').2.2
      rw [he1 e he'] at this ⊢
      rwa [hNm] at this
    have htot : sched.toFinset.card * (n * n * (m * (m - 1))) ≤
        2 * ∑ x0 : Lat n d, (detect st (defect hσ x0) ord sched).2 := by
      simp_rw [hreads]
      rw [Finset.sum_comm, Finset.mul_sum, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum hsum_e
    have hcardT : m ≤ sched.toFinset.card := by
      rw [schedule_card hs, sopfD_prime hn]; exact gaussBinom_ge_pow hn.one_le hd
    have hm2 : 2 ≤ m := by
      rw [hmdef]
      calc 2 ≤ n := hn.two_le
        _ = n ^ 1 := (pow_one n).symm
        _ ≤ n ^ (d - 1) := Nat.pow_le_pow_right hn.pos (by omega)
    obtain ⟨x0, -, hx0⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
      (f := fun _ : Lat n d => n ^ d * n ^ (d - 1))
      (g := fun x0 => 4 * (detect st (defect hσ x0) ord sched).2) (by
        rw [Finset.sum_const, Finset.card_univ, hN, smul_eq_mul, ← Finset.mul_sum, hnd]
        exact aux_ineq_worst n m _ _ hm2 hcardT htot)
    exact ⟨defect hσ x0, hx0⟩

theorem remPolylogWorstLower_proved : remPolylogWorstLowerStatement := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro n d σ hn hd hσ sched hs ord hord st
  have : NeZero n := ⟨hn.ne_zero⟩
  obtain ⟨s, hs'⟩ := worst_lower_exists hn hd hσ hs hord st
  refine ⟨s, ?_⟩
  have : ((n ^ d * n ^ (d - 1) : ℕ) : ℝ) ≤ 4 * ((detect st s ord sched).2 : ℝ) := by
    exact_mod_cast hs'
  push_cast at this
  linarith

theorem remPolylogFactor_proved : remPolylogFactorStatement := by
  refine ⟨1 / 16, by norm_num, ?_⟩
  intro n d σ _ hn hd hσ sched hs ord hord st
  obtain ⟨s, hs'⟩ := worst_lower_exists hn hd hσ hs hord st
  refine ⟨s, ?_⟩
  have h1 : ((n ^ d * n ^ (d - 1) : ℕ) : ℝ) ≤ 4 * ((detect st s ord sched).2 : ℝ) := by
    exact_mod_cast hs'
  push_cast at h1
  have hE := expect_reads_le_prime hn hd hσ hs hord st
  have hu : (0 : ℝ) ≤ (n : ℝ) ^ (d - 1) := by positivity
  have h2 : 1 / 16 * (n : ℝ) ^ (d - 1) *
      expectUnif (fun s' : Config n d (Fin σ) => (detect st s' ord sched).2)
      ≤ 1 / 16 * (n : ℝ) ^ (d - 1) * (4 * (n : ℝ) ^ d) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  nlinarith

/-- `8a ≤ 3·2^a + 4`. -/
theorem aux_two_pow (a : ℕ) : 8 * a ≤ 3 * 2 ^ a + 4 := by
  rcases Nat.lt_or_ge a 2 with h | h
  · interval_cases a <;> norm_num
  · induction a, h using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have : 8 ≤ 3 * 2 ^ k := by
        calc 8 ≤ 3 * 2 ^ 2 := by norm_num
          _ ≤ 3 * 2 ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk)
      rw [pow_succ]; omega

/-- The union bound leaves at least a quarter of the configurations asymmetric:
`4 [d 1]_n ≤ 3 · 2^(n^(d-1) (n-1))`. -/
theorem key_ineq {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    4 * gaussBinom n d 1 ≤ 3 * 2 ^ (n ^ (d - 1) * (n - 1)) := by
  set a := n ^ (d - 1) with ha
  have ha1 : 1 ≤ a := Nat.one_le_pow _ _ (by omega)
  have hnd : n ^ d = n * a := by rw [ha, ← pow_succ']; congr 1; omega
  have hgeom := sub_one_mul_gaussBinom (by omega : 1 ≤ n) d
  rw [hnd] at hgeom
  rcases Nat.eq_or_lt_of_le hn with h2 | h3
  · subst h2
    simp only [Nat.add_one_sub_one, one_mul, mul_one] at hgeom ⊢
    have := aux_two_pow a
    omega
  · -- n ≥ 3, b = n - 1 ≥ 2
    have hb : 2 ≤ n - 1 := by omega
    have h4a : 4 * a ≤ 2 ^ (a * (n - 1)) := by
      have hlt := Nat.lt_two_pow_self (n := a)
      have hsq : 2 ^ (2 * a) = 2 ^ a * 2 ^ a := by rw [two_mul, pow_add]
      calc 4 * a ≤ (a + 1) * (a + 1) := by nlinarith
        _ ≤ 2 ^ a * 2 ^ a := Nat.mul_le_mul hlt hlt
        _ = 2 ^ (2 * a) := hsq.symm
        _ ≤ 2 ^ (a * (n - 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have hpos : 0 < n - 1 := by omega
    apply Nat.le_of_mul_le_mul_left _ hpos
    calc (n - 1) * (4 * gaussBinom n d 1) = 4 * ((n - 1) * gaussBinom n d 1) := by ring
      _ = 4 * (n * a - 1) := by rw [hgeom]
      _ ≤ 4 * (n * a) := by omega
      _ ≤ (n - 1) * (3 * (4 * a)) := by
          have : n ≤ 3 * (n - 1) := by omega
          calc 4 * (n * a) = 4 * a * n := by ring
            _ ≤ 4 * a * (3 * (n - 1)) := Nat.mul_le_mul_left _ this
            _ = (n - 1) * (3 * (4 * a)) := by ring
      _ ≤ (n - 1) * (3 * 2 ^ (a * (n - 1))) := by
          apply Nat.mul_le_mul_left; exact Nat.mul_le_mul_left _ h4a

/-- Conservative reading, prime `n`: the expected reads are at least `N/4`. -/
theorem expect_reads_ge_conservative {n d σ : ℕ} [NeZero n] (hn : n.Prime) (hd : 1 ≤ d)
    (hσ : 2 ≤ σ) {sched : List (ℕ × Lat n d)} (hs : IsSchedule sched)
    {ord : ℕ × Lat n d → List (Lat n d)} (hord : ∀ e ∈ sched, IsTraversalOrder (ord e)) :
    (n : ℝ) ^ d / 4 ≤
      expectUnif (fun s : Config n d (Fin σ) => (detect false s ord sched).2) := by
  classical
  set N := Fintype.card (Lat n d) with hN
  set m := n ^ (d - 1) with hmdef
  have hnd : n ^ d = n * m := by rw [hmdef, ← pow_succ']; congr 1; omega
  have hNm : N = n * m := by rw [hN, card_lat_eq, hnd]
  have he1 : ∀ e ∈ sched, e.1 = n := fun e he =>
    (Nat.prime_dvd_prime_iff_eq (hs.1 e he).1 hn).mp (hs.1 e he).2.1
  -- asymmetric configurations cost at least `n^d` reads
  have hasym : ∀ s : Config n d (Fin σ), ¬ IsShiftSymmetric s →
      n ^ d ≤ (detect false s ord sched).2 := by
    intro s hns
    have hall : ∀ e ∈ sched, (subgroupTest false s (ord e) e.1 e.2).1 = false := by
      intro e he
      by_contra hc
      have hc' : (subgroupTest false s (ord e) e.1 e.2).1 = true := by simpa using hc
      exact hns ⟨e.2, entry_ne_zero hs he, (entry_test_iff hs hord false s he).mp hc'⟩
    rw [detect_reads_eq_sum_of_fail false s ord sched hall,
      ← List.sum_toFinset _ (schedule_nodup hs)]
    have hge : ∀ e ∈ sched.toFinset, n ≤ (subgroupTest false s (ord e) e.1 e.2).2.2 := by
      intro e he
      have he' := List.mem_toFinset.mp he
      have := subgroupTest_reads_ge_of_fail s (ord e) e.1 e.2 (hall e he')
      rw [he1 e he'] at this ⊢
      exact this
    calc n ^ d = n * m := hnd
      _ ≤ sched.toFinset.card * n := by
          rw [Nat.mul_comm n m]
          apply Nat.mul_le_mul_right
          rw [schedule_card hs, sopfD_prime hn]; exact gaussBinom_ge_pow hn.one_le hd
      _ = ∑ _e ∈ sched.toFinset, n := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hge
  -- counting
  have hσpos : (0 : ℝ) < (σ : ℝ) ^ N := pow_pos (by exact_mod_cast (by omega : 0 < σ)) _
  have hsymc := card_sym_le (d := d) (σ := σ) hn
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hsymc
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset
    (Config n d (Fin σ)))) (fun s => IsShiftSymmetric s)
  rw [Finset.card_univ] at hsplit
  have hcardC : Fintype.card (Config n d (Fin σ)) = σ ^ N := by
    rw [hN]; simp only [Config, Fintype.card_fun, Fintype.card_fin]
  rw [hcardC] at hsplit
  have hNdiv : n ^ d / n = m := by rw [hnd]; exact Nat.mul_div_cancel_left m hn.pos
  rw [hNdiv] at hsymc
  -- 4 #sym ≤ 3 σ^N
  have hkey : 4 * (gaussBinom n d 1 * σ ^ m) ≤ 3 * σ ^ N := by
    have hk := key_ineq hn.two_le hd
    have hpow : σ ^ N = σ ^ m * σ ^ (m * (n - 1)) := by
      rw [← pow_add, hNm]; congr 1
      obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by have := hn.pos; omega⟩
      simp only [Nat.add_sub_cancel]; ring
    have h2 : 2 ^ (m * (n - 1)) ≤ σ ^ (m * (n - 1)) := Nat.pow_le_pow_left hσ _
    calc 4 * (gaussBinom n d 1 * σ ^ m) = (4 * gaussBinom n d 1) * σ ^ m := by ring
      _ ≤ (3 * 2 ^ (m * (n - 1))) * σ ^ m := Nat.mul_le_mul_right _ hk
      _ ≤ (3 * σ ^ (m * (n - 1))) * σ ^ m := by
          apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_left _ h2
      _ = 3 * σ ^ N := by rw [hpow]; ring
  set A := (Finset.univ.filter fun s : Config n d (Fin σ) => ¬ IsShiftSymmetric s).card with hA
  have hA4 : σ ^ N ≤ 4 * A := by omega
  -- sum bound
  have hsum : ((A * n ^ d : ℕ) : ℝ) ≤ ∑ s : Config n d (Fin σ), ((detect false s ord sched).2 : ℝ) := by
    have : A * n ^ d = ∑ s : Config n d (Fin σ), (if IsShiftSymmetric s then 0 else n ^ d) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul]
    rw [this]
    push_cast
    refine Finset.sum_le_sum (fun s _ => ?_)
    split_ifs with hsym
    · exact Nat.cast_nonneg _
    · exact_mod_cast hasym s hsym
  unfold expectUnif
  rw [card_config_real, le_div_iff₀ hσpos]
  have hA4' : ((σ : ℝ) ^ N) ≤ 4 * (A : ℝ) := by exact_mod_cast hA4
  push_cast at hsum
  have hnd0 : (0 : ℝ) ≤ (n : ℝ) ^ d := by positivity
  nlinarith

theorem remPolylogFactorConservative_proved : remPolylogFactorConservativeStatement := by
  refine ⟨8, ?_⟩
  intro n d σ _ hn hd hσ sched hs ord hord s
  have hE := expect_reads_ge_conservative hn hd hσ hs hord
  have h := detect_reads_le_worst hs ord false s
  rw [sopfD_prime hn] at h
  have h2 := gaussBinom_d_one_le hn.two_le d
  have h3 : (detect false s ord sched).2 ≤ 2 * (n ^ d * n ^ (d - 1)) := by
    calc (detect false s ord sched).2 ≤ n ^ d * gaussBinom n d 1 := h
      _ ≤ n ^ d * (2 * n ^ (d - 1)) := Nat.mul_le_mul_left _ h2
      _ = 2 * (n ^ d * n ^ (d - 1)) := by ring
  have h3' : ((detect false s ord sched).2 : ℝ) ≤ 2 * ((n : ℝ) ^ d * (n : ℝ) ^ (d - 1)) := by
    exact_mod_cast h3
  have hu : (0 : ℝ) ≤ (n : ℝ) ^ (d - 1) := by positivity
  nlinarith

theorem remPolylogBoundRatio_proved : ∀ n d σ : ℕ, remPolylogBoundRatioStatement n d σ := by
  intro n d σ hn hd hσ
  rw [hn.primeFactors, Finset.sum_singleton, sopfD_prime hn]
  have hQ := Q_le_half hσ hn.two_le
  have hQ0 := Q_pos hσ n
  set D := 1 - (σ : ℝ) ^ ((1 : ℤ) - (n : ℤ)) with hD
  have hD1 : D ≤ 1 := by linarith
  have hD2 : 1 / 2 ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  set g := (gaussBinom n d 1 : ℝ)
  set u := (n : ℝ) ^ (d - 1)
  have hg : 0 ≤ g := Nat.cast_nonneg _
  have hu : 0 ≤ u := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnd : (n : ℝ) ^ d = u * n := by
    simp only [u]; rw [← pow_succ]; congr 1; omega
  have hcast : ((n ^ d * gaussBinom n d 1 : ℕ) : ℝ) = u * n * g := by
    push_cast; rw [hnd]
  rw [hcast]
  constructor
  · -- (u/2) (g n / D) ≤ u n g
    have h1 : u / 2 * (g * (n / D)) = (u * n * g) * (1 / (2 * D)) := by
      field_simp
    rw [h1]
    apply mul_le_of_le_one_right (by positivity)
    rw [div_le_one (by linarith)]; linarith
  · have h1 : u * (g * (n / D)) = (u * n * g) * (1 / D) := by
      field_simp
    rw [h1]
    apply le_mul_of_one_le_right (by positivity)
    rw [le_div_iff₀ hDpos]; linarith

/-! ### Remark 9.3 (ii): the bound expression `Σ_{p ∣ n} p^d` -/

theorem remPolylogNotPolylog_proved : remPolylogNotPolylogStatement := by
  rintro d hd ⟨C, k, M, hCM⟩
  set ε : ℝ := 1 / (2 * (|C| + 1) * (d : ℝ) ^ k) with hε
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hεpos : 0 < ε := by positivity
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp
    ((Real.isLittleO_pow_log_id_atTop (n := k)).bound hεpos)
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max M (max ⌈X0⌉₊ 2))
  have h := hCM p (le_trans (le_max_left _ _) hpge)
  rw [hp.primeFactors, Finset.sum_singleton] at h
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hpX : X0 ≤ (p : ℝ) := by
    have h1 : ⌈X0⌉₊ ≤ p := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hpge
    exact le_trans (Nat.le_ceil X0) (by exact_mod_cast h1)
  have hb := hX0 p hpX
  simp only [Real.norm_eq_abs, id] at hb
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
  rw [abs_of_nonneg (pow_nonneg hlog0 k), abs_of_nonneg (by linarith)] at hb
  rw [Real.log_pow, mul_pow] at h
  have hdk : (0 : ℝ) < (d : ℝ) ^ k := by positivity
  have h1 : C * ((d : ℝ) ^ k * Real.log p ^ k) ≤ |C| * ((d : ℝ) ^ k * (ε * p)) := by
    calc C * ((d : ℝ) ^ k * Real.log p ^ k) ≤ |C| * ((d : ℝ) ^ k * Real.log p ^ k) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((d : ℝ) ^ k * (ε * p)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          exact mul_le_mul_of_nonneg_left hb hdk.le
  have h2 : |C| * ((d : ℝ) ^ k * (ε * p)) = |C| / (2 * (|C| + 1)) * p := by
    rw [hε]; field_simp
  have h3 : |C| / (2 * (|C| + 1)) * (p : ℝ) < p := by
    have hC : |C| / (2 * (|C| + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [abs_nonneg C]
    have : (0 : ℝ) < p := by linarith
    nlinarith
  have h4 : (p : ℝ) ≤ (p : ℝ) ^ d := le_self_pow₀ hp1 (by omega)
  linarith

theorem card_primeFactors_mul_log_two_le {n : ℕ} (hn : n ≠ 0) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
  have h1 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 : ∏ p ∈ n.primeFactors, p ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
  have h3 : ((2 ^ n.primeFactors.card : ℕ) : ℝ) ≤ n := by exact_mod_cast h1.trans h2
  push_cast at h3
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) h3

theorem remPolylogSmooth_proved : remPolylogSmoothStatement := by
  intro d hd c
  refine ⟨1 / Real.log 2, c * d + 1, ?_⟩
  intro n hn hsm
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set L := Real.log (n : ℝ) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hcard := card_primeFactors_mul_log_two_le (n := n) (by omega)
  have hcard' : (n.primeFactors.card : ℝ) ≤ L / Real.log 2 := by
    rw [le_div_iff₀ hl2]; exact hcard
  have hsum : ∑ p ∈ n.primeFactors, (p : ℝ) ^ d ≤ (n.primeFactors.card : ℝ) * L ^ (c * d) := by
    calc ∑ p ∈ n.primeFactors, (p : ℝ) ^ d ≤ ∑ _p ∈ n.primeFactors, (L ^ c) ^ d :=
          Finset.sum_le_sum (fun p hp => pow_le_pow_left₀ (Nat.cast_nonneg p) (hsm p hp) d)
      _ = (n.primeFactors.card : ℝ) * L ^ (c * d) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← pow_mul]
  have hLd : L ≤ Real.log ((n : ℝ) ^ d) := by
    rw [Real.log_pow]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  calc ∑ p ∈ n.primeFactors, (p : ℝ) ^ d ≤ (n.primeFactors.card : ℝ) * L ^ (c * d) := hsum
    _ ≤ L / Real.log 2 * L ^ (c * d) :=
        mul_le_mul_of_nonneg_right hcard' (pow_nonneg hL0 _)
    _ = 1 / Real.log 2 * L ^ (c * d + 1) := by rw [pow_succ]; ring
    _ ≤ 1 / Real.log 2 * (Real.log ((n : ℝ) ^ d)) ^ (c * d + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ hL0 hLd _

theorem remPolylogRandomN_proved : remPolylogRandomNStatement := by
  intro d hd C k ε hε
  exact polylog_density_zero d hd C k ε hε

/-! ### Remark 9.3, whole statement -/

theorem remPolylog_proved : remPolylogStatement :=
  ⟨remPolylogPrimeSum_proved, remPolylogNotPolylog_proved, remPolylogRandomN_proved,
    remPolylogSmooth_proved, remPolylogAvgPrime_proved, remPolylogWorstPrime_proved,
    remPolylogWorstLower_proved, remPolylogFactor_proved, remPolylogFactorConservative_proved,
    remPolylogBoundRatio_proved⟩

end ShiftSym.P08
