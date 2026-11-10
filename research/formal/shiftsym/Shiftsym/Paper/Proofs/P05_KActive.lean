/-
Phase H, group 05 (KActive) — PROOFS of every frozen statement of
`Shiftsym/Paper/S05_KActive.lean` (namespace `ShiftSym.P05`).

Helper modules (all in `Shiftsym/Paper/Proofs/`):
* `P05_KActive_Fix`   — `|Fix_k(H)|` for every `k` (`natCard_fixK`), `|C^a_k|`,
                        the partition `Σ_k |S^a_k| = |S|` (`sum_numKActive`);
* `P05_KActive_Rank`  — Theorem 5.1 (`numKActive_eq_rhs`) from the certified
                        relative enumeration theorem (E1) by rank-vector regrouping;
* `P05_KActive_B2019` — the 2019 Eqs. (30)–(33) as rewritings of the `d = 2`
                        right-hand side of Theorem 5.1.
Certified results reused: `relativeEnumeration_proved` (E1), `enumeration_proved`
(Theorem 4.3), `lowerBound_proved` (Theorem 6.1), `fixedByEquiv`.
No `maxHeartbeats`/`maxRecDepth` options are used.
-/
import Shiftsym.Paper.Proofs.P05_KActive_Rank
import Shiftsym.Paper.Proofs.P05_KActive_B2019
import Shiftsym.Lemmas.LowerBound

namespace ShiftSym.P05

open ShiftSym

/-! ## The §5 convention claims -/

theorem noFracAt_of_dvd {N k h : ℕ} (hpos : 0 < h) (hdvd : h ∣ N) : NoFracAt N k h := by
  rintro ⟨j, hj, -⟩
  obtain ⟨M, rfl⟩ := hdvd
  refine ⟨(M : ℤ) - j, ?_⟩
  have hq : (h : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast
  rw [hj]
  field_simp

theorem noFractionalExponent_proved : noFractionalExponentStatement := by
  intro n d k hn _ _
  have : NeZero n := ⟨by omega⟩
  exact ⟨fun v hv => noFracAt_of_dvd (hVec_pos v) (hVec_dvd_pow (Finset.mem_of_mem_erase hv)),
    fun H => noFracAt_of_dvd (card_addSubgroup_pos n d H) (card_addSubgroup_dvd_pow n d H),
    noFracAt_of_dvd one_pos (one_dvd _)⟩

theorem not_binomNonvanishing_4_2_4 : ¬ BinomNonvanishing (2 ^ 2) 2 4 := by
  rintro ⟨j, hj, -⟩
  have h2 : (2 * j : ℚ) = 1 := by rw [hj]; norm_num
  have h2' : 2 * j = 1 := by exact_mod_cast h2
  omega

theorem not_isIntQ_half : ¬ IsIntQ ((((2 ^ 2 : ℕ) : ℚ) - ((2 : ℕ) : ℚ)) / ((4 : ℕ) : ℚ)) := by
  rintro ⟨m, hm⟩
  have h2 : (2 * m : ℚ) = 1 := by rw [hm]; norm_num
  have h2' : 2 * m = 1 := by exact_mod_cast h2
  omega

theorem fractionalExponentArises_proved : fractionalExponentArisesStatement := by
  have h2pf : (2 : ℕ).primeFactors = {2} := Nat.prime_two.primeFactors
  have hmem : (2 : ℕ) ∈ (2 : ℕ).primeFactors := by rw [h2pf]; exact Finset.mem_singleton_self 2
  have hV : hVec (fun _ => 2 : (2 : ℕ).primeFactors → ℕ) = 4 := by
    unfold hVec
    rw [Finset.prod_coe_sort (2 : ℕ).primeFactors (fun p => p ^ 2), h2pf, Finset.prod_singleton]
    norm_num
  have hT : Nat.card (⊤ : AddSubgroup (Lat 2 2)) = 4 := by
    rw [AddSubgroup.card_top, Nat.card_eq_fintype_card, card_lat]
    norm_num
  refine ⟨2, 2, 2, le_rfl, by norm_num, by norm_num, ⟨fun _ => 2, ?_, ?_⟩, ⟨⊤, ?_⟩⟩
  · rw [Finset.mem_erase]
    refine ⟨fun h => ?_, Fintype.mem_piFinset.mpr fun _ => by simp⟩
    have := congrFun h ⟨2, hmem⟩
    simp at this
  · rw [hV]
    exact ⟨not_binomNonvanishing_4_2_4, not_isIntQ_half⟩
  · rw [hT]
    exact ⟨not_binomNonvanishing_4_2_4, not_isIntQ_half⟩

theorem zeroPowOnlyAt_of_pos {N σ k h : ℕ} (hpos : 0 < h) : ZeroPowOnlyAt N σ k h := by
  rintro _ ⟨hσ, hk⟩
  have hq : (h : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [div_eq_zero_iff] at hk
  rcases hk with hk | hk
  · constructor
    · have : (σ : ℚ) = 1 := by linarith
      exact_mod_cast this
    · have : (N : ℚ) = k := by linarith
      exact_mod_cast this.symm
  · exact absurd hk hq

theorem zeroPowOnly_proved : zeroPowOnlyStatement := by
  intro n d σ k hn _ _ _
  have : NeZero n := ⟨by omega⟩
  exact ⟨fun v _ => zeroPowOnlyAt_of_pos (hVec_pos v),
    fun H => zeroPowOnlyAt_of_pos (card_addSubgroup_pos n d H),
    fun _ => zeroPowOnlyAt_of_pos one_pos⟩

theorem zeroPowOccursAt_of_dvd {N h : ℕ} (hpos : 0 < h) (hdvd : h ∣ N) :
    ZeroPowOccursAt N 1 N h :=
  ⟨(guard_iff_of_dvd hpos hdvd).mp ⟨hdvd, le_rfl⟩, by norm_num, by simp⟩

theorem zeroPowOccurs_proved : zeroPowOccursStatement := by
  intro n d hn _
  have : NeZero n := ⟨by omega⟩
  exact ⟨fun v hv => zeroPowOccursAt_of_dvd (hVec_pos v) (hVec_dvd_pow (Finset.mem_of_mem_erase hv)),
    fun H => zeroPowOccursAt_of_dvd (card_addSubgroup_pos n d H) (card_addSubgroup_dvd_pow n d H)⟩

theorem convTermZ_top {N h : ℕ} (hdvd : h ∣ N) (z : ℤ) : convTermZ z N N h 1 = z := by
  unfold convTermZ powZ
  rw [if_pos ⟨hdvd, le_rfl⟩, Nat.choose_self, Nat.sub_self, Nat.zero_div]
  simp

theorem kActiveRHSZ_top (n d : ℕ) (z : ℤ) :
    kActiveRHSZ z n d 1 (n ^ d) = z * kActiveRHSZ 1 n d 1 (n ^ d) := by
  unfold kActiveRHSZ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [convTermZ_top (hVec_dvd_pow (Finset.mem_of_mem_erase hv)),
    convTermZ_top (hVec_dvd_pow (Finset.mem_of_mem_erase hv))]
  ring

theorem zeroPowMatters_proved : zeroPowMattersStatement := by
  intro n d hn hd a z
  have : NeZero n := ⟨by omega⟩
  have h1 : (numKActive n d 1 a (n ^ d) : ℤ) = 1 := by
    rw [numKActive_top hn hd a]; rfl
  have hS : kActiveRHSZ 1 n d 1 (n ^ d) = 1 := by
    rw [kActiveRHSZ_one, ← numKActive_eq_rhs n d 1 (n ^ d) hn le_rfl a, h1]
  refine ⟨?_, fun H => ?_⟩
  · rw [h1, kActiveRHSZ_top, hS, mul_one]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · rw [natCard_fixK n d 1 le_rfl a (n ^ d) H, ← convTermZ_one,
      convTermZ_top (card_addSubgroup_dvd_pow n d H), convTermZ_top (card_addSubgroup_dvd_pow n d H)]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem zeroPowRelevance_proved : zeroPowRelevanceStatement :=
  ⟨zeroPowOnly_proved, zeroPowOccurs_proved, zeroPowMatters_proved⟩

theorem conventionClaims_proved : conventionClaimsStatement :=
  ⟨noFractionalExponent_proved, fractionalExponentArises_proved, zeroPowRelevance_proved⟩

/-! ## Scope of the convention (AUXILIARY) -/

theorem gaussBinom_one_pos (q d : ℕ) (hd : 1 ≤ d) : 1 ≤ gaussBinom q d 1 := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  show 1 ≤ gaussBinom q d' 0 + q ^ 1 * gaussBinom q d' 1
  simp [gaussBinom]

theorem conventionScopeLiteral_proved : conventionScopeLiteralStatement := by
  have ha : ∀ n d σ : ℕ, n.Prime → 1 ≤ d → 2 ≤ σ →
      lowerEnvelopeLit n d σ < (numSS n d σ : ℤ) := by
    intro n d σ hp hd hσ
    have hLB := lowerBound_proved n d σ hp.two_le hd hσ
    have heq : lowerEnvelope n d σ = (numSS n d σ : ℤ) := hLB.2.mpr hp
    rw [lowerEnvelopeLit_eq hd, heq]
    have h1 : (1 : ℤ) ≤ gaussBinom n d 1 := by exact_mod_cast gaussBinom_one_pos n d hd
    have h2 : (1 : ℤ) ≤ (σ : ℤ) ^ (n ^ (d - 1)) :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ σ))
    nlinarith
  refine ⟨ha, fun h => ?_⟩
  have h2 := h 2 1 2 le_rfl le_rfl le_rfl
  have hlt := ha 2 1 2 Nat.prime_two le_rfl le_rfl
  have heq := h2.2.mpr Nat.prime_two
  omega

/-! ## The counting step, Theorem 5.1, the consistency check -/

theorem fixKCount_proved : fixKCountStatement := by
  intro n d σ k hn _ hσ _ a H
  have : NeZero n := ⟨by omega⟩
  exact natCard_fixK n d σ hσ a k H

theorem kActive_proved : kActiveStatement := by
  intro n d σ k hn _ hσ _ a
  exact numKActive_eq_rhs n d σ k hn hσ a

theorem kActiveConsistency_proved : kActiveConsistencyStatement := by
  intro n d σ hn _ _ a
  have : NeZero n := ⟨by omega⟩
  exact sum_numKActive n d σ a

theorem kActiveRHSConsistency_proved : kActiveRHSConsistencyStatement := by
  intro n d σ hn hd hσ
  have : NeZero n := ⟨by omega⟩
  let a : Fin σ := ⟨0, by omega⟩
  calc ∑ k ∈ Finset.range (n ^ d + 1), kActiveRHS n d σ k
      = ∑ k ∈ Finset.range (n ^ d + 1), (numKActive n d σ a k : ℤ) :=
        Finset.sum_congr rfl fun k _ => (numKActive_eq_rhs n d σ k hn hσ a).symm
    _ = ((∑ k ∈ Finset.range (n ^ d + 1), numKActive n d σ a k : ℕ) : ℤ) := by push_cast; rfl
    _ = (numSS n d σ : ℤ) := by rw [sum_numKActive]
    _ = enumerationRHS n d σ := enumeration_proved n d σ hn hd hσ

/-! ## The remark on Eqs. (29)–(33) of [banda2019] -/

theorem banda2019Eq29Needs_proved : banda2019Eq29NeedsStatement := by
  have hc : Nat.card (AddSubgroup.zmultiples (0 : Lat 2 2)) = 1 := by
    rw [AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.card_bot]
  refine ⟨2, 1, 4, 0, le_rfl, le_rfl, ?_, ?_, ?_, ?_⟩
  · rw [hc]; exact one_dvd 4
  · rw [hc]; exact ⟨4, by norm_num, by norm_num⟩
  · norm_num
  · rw [hc]; norm_num

theorem gcd22_primeFactors : (Nat.gcd 2 2).primeFactors = {2} := by
  rw [Nat.gcd_self]; exact Nat.prime_two.primeFactors

theorem gcd22_mem : (2 : ℕ) ∈ (Nat.gcd 2 2).primeFactors := by
  rw [gcd22_primeFactors]; exact Finset.mem_singleton_self 2

theorem const2_ne_zero : (fun _ => 2 : (Nat.gcd 2 2).primeFactors → ℕ) ≠ 0 := by
  intro h
  have := congrFun h ⟨2, gcd22_mem⟩
  simp at this

theorem h2019_const2 : h2019 (fun _ => 2 : (Nat.gcd 2 2).primeFactors → ℕ) = 4 := by
  rw [h2019_const_singleton gcd22_primeFactors]; norm_num

theorem not_isIntQ_two_four : ¬ IsIntQ (((2 : ℕ) : ℚ) / ((4 : ℕ) : ℚ)) := by
  rintro ⟨m, hm⟩
  have h2 : (2 * m : ℚ) = 1 := by rw [hm]; norm_num
  have h2' : 2 * m = 1 := by exact_mod_cast h2
  omega

theorem const2_mem_idxTwo : (fun _ => 2 : (Nat.gcd 2 2).primeFactors → ℕ) ∈ idxTwo2019 2 2 := by
  rw [idxTwo2019, Finset.mem_erase]
  exact ⟨const2_ne_zero, Fintype.mem_piFinset.mpr fun _ => by simp⟩

theorem banda2019Eq30Needs_proved : banda2019Eq30NeedsStatement := by
  refine ⟨2, 2, le_rfl, le_rfl, fun _ => 2, ?_, ?_⟩
  · rw [idxThirty2019, Finset.mem_erase]
    refine ⟨const2_ne_zero, Fintype.mem_piFinset.mpr fun r => ?_⟩
    rw [Finset.mem_range]
    have := (Nat.prime_of_mem_primeFactors r.2).two_le
    omega
  · rw [h2019_const2]
    exact ⟨not_isIntQ_two_four, not_isIntQ_half⟩

theorem banda2019Eq31Needs_proved : banda2019Eq31NeedsStatement := by
  refine ⟨2, 2, le_rfl, le_rfl, fun _ => 2, const2_mem_idxTwo, fun _ => 2, ?_, ?_⟩
  · rw [idxInner2019, Fintype.mem_piFinset]
    intro r
    rw [Finset.mem_Icc, top2019]
    have := (Nat.prime_of_mem_primeFactors r.2).two_le
    simp only [lt_irrefl, if_false]
    omega
  · rw [h2019_const2]
    exact ⟨not_isIntQ_two_four, not_isIntQ_half⟩

theorem banda2019Eq32Needs_proved : banda2019Eq32NeedsStatement := by
  refine ⟨2, 2, le_rfl, le_rfl, fun _ => 2, const2_mem_idxTwo, ?_⟩
  rw [h2019_const2]
  exact ⟨not_isIntQ_two_four, not_isIntQ_half⟩

theorem banda2019Eq33Needs_proved : banda2019Eq33NeedsStatement := by
  refine ⟨2, 2, le_rfl, le_rfl, fun _ => 2, const2_mem_idxTwo, ?_⟩
  rw [h2019_const2]
  exact not_isIntQ_two_four

theorem banda2019Needs_proved : banda2019NeedsStatement :=
  ⟨banda2019Eq29Needs_proved, banda2019Eq30Needs_proved, banda2019Eq31Needs_proved,
    banda2019Eq32Needs_proved, banda2019Eq33Needs_proved⟩

theorem banda2019Eq29Valid_proved : banda2019Eq29ValidStatement := by
  intro n σ k hn hσ a v _
  have : NeZero n := ⟨by omega⟩
  exact natCard_fixK n 2 σ hσ a k (AddSubgroup.zmultiples v)

theorem banda2019Eq32Valid_proved : banda2019Eq32ValidStatement := by
  intro n σ k hn hσ _ a
  rw [numKActive_eq_rhs n 2 σ k hn hσ a, eq32RHS_eq_kActiveRHS n k σ (by omega)]

theorem banda2019Eq31Valid_proved : banda2019Eq31ValidStatement := by
  intro n σ k hn hσ hk a
  rw [eq31RHS_eq_eq32RHS]
  exact banda2019Eq32Valid_proved n σ k hn hσ hk a

theorem banda2019Eq30Valid_proved : banda2019Eq30ValidStatement := by
  intro n σ k hn hσ hk a
  rw [eq30RHS_eq_eq31RHS, eq31RHS_eq_eq32RHS]
  exact banda2019Eq32Valid_proved n σ k hn hσ hk a

theorem banda2019Eq33Valid_proved : banda2019Eq33ValidStatement := by
  intro n k hn hk a
  rw [eq33RHS_eq_eq32RHS]
  exact banda2019Eq32Valid_proved n 2 k hn (by norm_num) hk a

theorem banda2019Valid_proved : banda2019ValidStatement :=
  ⟨banda2019Eq29Valid_proved, banda2019Eq30Valid_proved, banda2019Eq31Valid_proved,
    banda2019Eq32Valid_proved, banda2019Eq33Valid_proved⟩

theorem banda2019Eq29Standard_proved : banda2019Eq29StandardStatement := by
  intro n σ k hn hσ v hdvd
  have : NeZero n := ⟨by omega⟩
  have hc : 0 < Nat.card (AddSubgroup.zmultiples v) := card_addSubgroup_pos n 2 _
  have hq : (Nat.card (AddSubgroup.zmultiples v) : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  obtain ⟨M, hM⟩ := card_addSubgroup_dvd_pow n 2 (AddSubgroup.zmultiples v)
  obtain ⟨J, hJ⟩ := hdvd
  refine ⟨⟨M, J, ?_, ?_⟩, ⟨(M : ℤ) - J, ?_⟩, ?_⟩
  · rw [hM]; push_cast; field_simp
  · rw [hJ]; push_cast; field_simp
  · rw [hM, hJ]; push_cast; field_simp
  · have : (2 : ℚ) ≤ σ := by exact_mod_cast hσ
    linarith

/-! ### Eqs. (32)–(33) as printed are false -/

theorem gcd36_primeFactors : (Nat.gcd 3 6).primeFactors = {3} := by
  rw [show Nat.gcd 3 6 = 3 by norm_num]; exact Nat.prime_three.primeFactors

theorem gcd26_primeFactors : (Nat.gcd 2 6).primeFactors = {2} := by
  rw [show Nat.gcd 2 6 = 2 by norm_num]; exact Nat.prime_two.primeFactors

theorem six_primeFactors : (6 : ℕ).primeFactors = {2, 3} := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
  rfl

theorem eq32PrintedRHS_6_3 (P R : List ℕ) :
    eq32PrintedRHS 6 3 2 P R = 12 * (coef2019 (P.getD (R.idxOf 3) 0) 1 : ℤ) := by
  unfold eq32PrintedRHS idxTwo2019
  rw [sum_idxTwo_singleton gcd36_primeFactors]
  simp only [absVec_const_singleton gcd36_primeFactors, h2019_const_singleton gcd36_primeFactors]
  rw [prod_singleton_coe gcd36_primeFactors (fun r => (coef2019 (P.getD (R.idxOf r) 0) 1 : ℤ)),
    prod_singleton_coe gcd36_primeFactors (fun r => (coef2019 (P.getD (R.idxOf r) 0) 2 : ℤ))]
  norm_num [convTerm]

theorem eq32PrintedRHS_6_2 (P R : List ℕ) :
    eq32PrintedRHS 6 2 2 P R = 18 * (coef2019 (P.getD (R.idxOf 2) 0) 1 : ℤ) := by
  unfold eq32PrintedRHS idxTwo2019
  rw [sum_idxTwo_singleton gcd26_primeFactors]
  simp only [absVec_const_singleton gcd26_primeFactors, h2019_const_singleton gcd26_primeFactors]
  rw [prod_singleton_coe gcd26_primeFactors (fun r => (coef2019 (P.getD (R.idxOf r) 0) 1 : ℤ)),
    prod_singleton_coe gcd26_primeFactors (fun r => (coef2019 (P.getD (R.idxOf r) 0) 2 : ℤ))]
  norm_num [convTerm]

theorem eq33PrintedRHS_6_3 (P R : List ℕ) :
    eq33PrintedRHS 6 3 P R = 12 * (coef2019 (P.getD (R.idxOf 3) 0) 1 : ℤ) := by
  unfold eq33PrintedRHS idxTwo2019
  rw [sum_idxTwo_singleton gcd36_primeFactors]
  simp only [absVec_const_singleton gcd36_primeFactors, h2019_const_singleton gcd36_primeFactors]
  rw [prod_singleton_coe gcd36_primeFactors (fun r => (coef2019 (P.getD (R.idxOf r) 0) 1 : ℤ)),
    prod_singleton_coe gcd36_primeFactors (fun r => (coef2019 (P.getD (R.idxOf r) 0) 2 : ℤ))]
  norm_num [convBinom]

theorem eq33PrintedRHS_6_2 (P R : List ℕ) :
    eq33PrintedRHS 6 2 P R = 18 * (coef2019 (P.getD (R.idxOf 2) 0) 1 : ℤ) := by
  unfold eq33PrintedRHS idxTwo2019
  rw [sum_idxTwo_singleton gcd26_primeFactors]
  simp only [absVec_const_singleton gcd26_primeFactors, h2019_const_singleton gcd26_primeFactors]
  rw [prod_singleton_coe gcd26_primeFactors (fun r => (coef2019 (P.getD (R.idxOf r) 0) 1 : ℤ)),
    prod_singleton_coe gcd26_primeFactors (fun r => (coef2019 (P.getD (R.idxOf r) 0) 2 : ℤ))]
  norm_num [convBinom]

theorem eq32RHS_6_3 : eq32RHS 6 3 2 = 48 := by
  unfold eq32RHS idxTwo2019
  rw [sum_idxTwo_singleton gcd36_primeFactors]
  simp only [absVec_const_singleton gcd36_primeFactors, h2019_const_singleton gcd36_primeFactors]
  rw [prod_singleton_coe gcd36_primeFactors (fun r => (coef2019 r 1 : ℤ)),
    prod_singleton_coe gcd36_primeFactors (fun r => (coef2019 r 2 : ℤ))]
  norm_num [convTerm, coef2019]

theorem eq32RHS_6_2 : eq32RHS 6 2 2 = 54 := by
  unfold eq32RHS idxTwo2019
  rw [sum_idxTwo_singleton gcd26_primeFactors]
  simp only [absVec_const_singleton gcd26_primeFactors, h2019_const_singleton gcd26_primeFactors]
  rw [prod_singleton_coe gcd26_primeFactors (fun r => (coef2019 r 1 : ℤ)),
    prod_singleton_coe gcd26_primeFactors (fun r => (coef2019 r 2 : ℤ))]
  norm_num [convTerm, coef2019]

theorem numKActive_6_3 (a : Fin 2) : (numKActive 6 2 2 a 3 : ℤ) = 48 := by
  rw [banda2019Eq32Valid_proved 6 2 3 (by norm_num) (by norm_num) (by norm_num) a, eq32RHS_6_3]

theorem numKActive_6_2 (a : Fin 2) : (numKActive 6 2 2 a 2 : ℤ) = 54 := by
  rw [banda2019Eq32Valid_proved 6 2 2 (by norm_num) (by norm_num) (by norm_num) a, eq32RHS_6_2]

/-- For a labelling `P` of the primes of `6`, its first entry is `2` or `3`. -/
theorem listing6_head {P : List ℕ} (hP : IsPrimeListing 6 P) :
    P.getD 0 0 = 2 ∨ P.getD 0 0 = 3 := by
  cases P with
  | nil =>
    exfalso
    have := (hP.2 2).mpr (by rw [six_primeFactors]; simp)
    simp at this
  | cons p P' =>
    have hp := (hP.2 p).mp (by simp)
    rw [six_primeFactors] at hp
    simpa using hp

/-- For a labelling `R` of the primes of a number whose only prime is `q`,
`q` sits at position `0`. -/
theorem listing_single_idxOf {m q : ℕ} (hq : m.primeFactors = {q}) {R : List ℕ}
    (hR : IsPrimeListing m R) : R.idxOf q = 0 := by
  cases R with
  | nil =>
    exfalso
    have := (hR.2 q).mpr (by rw [hq]; exact Finset.mem_singleton_self q)
    simp at this
  | cons x R' =>
    have hx := (hR.2 x).mp (by simp)
    rw [hq, Finset.mem_singleton] at hx
    subst hx
    simp

theorem banda2019Eq32PrintedFalse_proved : banda2019Eq32PrintedFalseStatement := by
  refine ⟨6, 2, by norm_num, by norm_num, 0, fun P hP => ?_⟩
  rcases listing6_head hP with h2 | h3
  · refine ⟨3, by norm_num, fun R hR => ?_⟩
    rw [numKActive_6_3, eq32PrintedRHS_6_3, listing_single_idxOf gcd36_primeFactors hR, h2]
    norm_num [coef2019]
  · refine ⟨2, by norm_num, fun R hR => ?_⟩
    rw [numKActive_6_2, eq32PrintedRHS_6_2, listing_single_idxOf gcd26_primeFactors hR, h3]
    norm_num [coef2019]

theorem banda2019Eq33PrintedFalse_proved : banda2019Eq33PrintedFalseStatement := by
  refine ⟨6, by norm_num, 0, fun P hP => ?_⟩
  rcases listing6_head hP with h2 | h3
  · refine ⟨3, by norm_num, fun R hR => ?_⟩
    rw [numKActive_6_3, eq33PrintedRHS_6_3, listing_single_idxOf gcd36_primeFactors hR, h2]
    norm_num [coef2019]
  · refine ⟨2, by norm_num, fun R hR => ?_⟩
    rw [numKActive_6_2, eq33PrintedRHS_6_2, listing_single_idxOf gcd26_primeFactors hR, h3]
    norm_num [coef2019]

theorem banda2019Convention_proved : banda2019ConventionStatement :=
  ⟨banda2019Needs_proved, banda2019Valid_proved⟩

/-! ## Corollary 7.2 -/

theorem card_filter_configsWithK (n d σ : ℕ) [NeZero n] (a : Fin σ) (k : ℕ)
    (inst : DecidablePred (· ∈ {s : Config n d (Fin σ) | IsShiftSymmetric s})) :
    (@Finset.filter _ (· ∈ {s : Config n d (Fin σ) | IsShiftSymmetric s}) inst
      (configsWithK n d σ a k)).card = numKActive n d σ a k := by
  classical
  rw [numKActive, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext s
  simp [configsWithK, and_comm]

theorem card_configsWithK (n d σ : ℕ) [NeZero n] (hσ : 1 ≤ σ) (a : Fin σ) {k : ℕ}
    (hk : k ≤ n ^ d) :
    ((configsWithK n d σ a k).card : ℤ) = ((n ^ d).choose k : ℤ) * ((σ : ℤ) - 1) ^ (n ^ d - k) := by
  classical
  rw [← convTerm_one_of_le hk, ← natCard_cells_eq n d σ hσ a k]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem probDens_eq (n d σ : ℕ) [NeZero n] (hσ : 2 ≤ σ) (a : Fin σ) :
    probDens n d σ hσ a
      = (1 / ((n ^ d : ℕ) + 1 : ℝ))
          * ∑ k ∈ Finset.range (n ^ d + 1),
              (numKActive n d σ a k : ℝ)
                / (((n ^ d).choose k : ℝ) * ((σ : ℝ) - 1) ^ (n ^ d - k)) := by
  have hσ1 : 1 ≤ σ := by omega
  unfold probDens densPMF
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, PMF.toOuterMeasure_uniformOfFinset_apply,
    Fintype.card_fin]
  rw [ENNReal.toReal_sum]
  · rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (k : ℕ) ≤ n ^ d := Nat.lt_succ_iff.mp k.isLt
    have hC := card_configsWithK n d σ hσ1 a hk
    have hCR : ((configsWithK n d σ a k).card : ℝ)
        = ((n ^ d).choose k : ℝ) * ((σ : ℝ) - 1) ^ (n ^ d - k) := by
      exact_mod_cast hC
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast, card_filter_configsWithK, hCR]
    push_cast
    ring
  · intro k _
    apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr (by simp)
    · apply ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      simp only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
      exact (configsWithK_nonempty hσ a (Nat.lt_succ_iff.mp k.isLt)).ne_empty

theorem density_proved : densityStatement := by
  intro n d σ hn _ hσ a
  have : NeZero n := ⟨by omega⟩
  exact probDens_eq n d σ hσ a

theorem densityClosed_proved : densityClosedStatement := by
  intro n d σ hn _ hσ a
  have : NeZero n := ⟨by omega⟩
  rw [probDens_eq n d σ hσ a]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := numKActive_eq_rhs n d σ k hn (by omega) a
  have h' : (numKActive n d σ a k : ℝ) = (kActiveRHS n d σ k : ℝ) := by
    rw [← h]; norm_cast
  rw [h']

theorem corDens_proved : corDensStatement :=
  ⟨density_proved, densityClosed_proved⟩

end ShiftSym.P05
