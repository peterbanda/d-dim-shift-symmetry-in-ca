/-
Phase H, group 07 — proofs of the frozen statements of
`Shiftsym/Paper/S07_Dynamics.lean` (paper Section 8, L725–800).

* Figure 2 caption: helper module `P07_Dynamics_Caption` (exact prime
  counts from the certified Theorem 6.1, union bound over prime-order
  subgroups, explicit fixed sets, kernel `decide` on the resulting
  integer inequalities).
* Theorem 8.1, Corollary 8.2: from the certified dynamics core
  (`Shiftsym/Lemmas/Dynamics.lean`).
* Proposition 8.3 and the prose after it: every `p`-rank statement is
  reduced to the cardinality identity `|Stab(s) ∩ A[p]| = p ^ rk_p(s)`
  (`card_eq_pow_rkP`).
-/
import Shiftsym.Paper.S07_Dynamics
import Shiftsym.Paper.Proofs.P07_Dynamics_Caption
import Shiftsym.Lemmas.Dynamics
import Shiftsym.Lemmas.LowerBound

namespace ShiftSym.P07

open ShiftSym

/-! ## The `p`-rank through cardinalities -/

/-- `|Stab(s) ∩ A[p]| = p ^ rk_p(s)`. -/
theorem card_eq_pow_rkP {n d σ p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n)
    (s : Config n d (Fin σ)) :
    Nat.card (stab s ⊓ latTorsion n d p : AddSubgroup (Lat n d))
      = p ^ rkP hn hp hpn s := by
  have : NeZero n := ⟨hn⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  unfold rkP
  set K : AddSubgroup (Lat n d) := stab s ⊓ latTorsion n d p with hK
  set H : AddSubgroup (Fin d → ZMod p) :=
    (K.addSubgroupOf (latTorsion n d p)).map (latTorsionEquiv hpn).toAddMonoidHom with hH
  have h1 : Nat.card H = Nat.card K := by
    rw [hH, AddSubgroup.card_map_of_injective (latTorsionEquiv hpn).injective]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe inf_le_right).toEquiv
  have h2 : Nat.card (AddSubgroup.toZModSubmodule p H) = Nat.card H := rfl
  rw [← h1, ← h2, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]


/-- `rk_p` is determined by the cardinality: `rk_p(s) = k ↔ |Stab(s) ∩ A[p]| = p^k`. -/
theorem rkP_eq_iff {n d σ p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n)
    (s : Config n d (Fin σ)) (k : ℕ) :
    rkP hn hp hpn s = k ↔
      Nat.card (stab s ⊓ latTorsion n d p : AddSubgroup (Lat n d)) = p ^ k := by
  rw [card_eq_pow_rkP hn hp hpn s]
  exact (Nat.pow_right_injective hp.two_le).eq_iff.symm

/-- Monotonicity of `rk_p` in the stabilizer. -/
theorem rkP_le_of_stab_le {n d σ p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n)
    {s t : Config n d (Fin σ)} (hst : stab s ≤ stab t) :
    rkP hn hp hpn s ≤ rkP hn hp hpn t := by
  have : NeZero n := ⟨hn⟩
  have hc : Nat.card (stab s ⊓ latTorsion n d p : AddSubgroup (Lat n d))
      ≤ Nat.card (stab t ⊓ latTorsion n d p : AddSubgroup (Lat n d)) :=
    AddSubgroup.card_le_of_le (inf_le_inf_right _ hst)
  rw [card_eq_pow_rkP hn hp hpn s, card_eq_pow_rkP hn hp hpn t] at hc
  exact (Nat.pow_le_pow_iff_right hp.two_le).mp hc

/-! ## Theorem 8.1 -/

theorem irrevStab_proved : irrevStabStatement := by
  intro n d σ _ _ _ Φ hΦ s
  exact stab_le_stab_apply hΦ s

theorem irrevVec_proved : irrevVecStatement := by
  intro n d σ _ _ _ Φ hΦ v _ s hs
  exact shift_apply_eq_of_shift_eq hΦ hs

theorem irrevSet_proved : irrevSetStatement := by
  intro n d σ _ _ _ Φ hΦ
  rintro _ ⟨s, hs, rfl⟩
  exact isShiftSymmetric_apply hΦ hs

theorem irrev_proved : irrevStatement :=
  ⟨irrevStab_proved, irrevVec_proved, irrevSet_proved⟩

/-! ## The sentence after Theorem 8.1 -/

theorem equivarianceNeeded_proved : equivarianceNeededStatement := by
  intro h
  have key := h 4 1 2 (by norm_num) le_rfl le_rfl 1
    (fun (u : Lat 4 1) (_ : Fin 1) => if u 0 = 2 then (fun _ => 1) else u)
    (fun x : Fin 1 → Fin 2 => x 0)
  have hs : (fun u : Lat 4 1 => if (u 0).val % 2 = 1 then (1 : Fin 2) else 0)
      ∈ SS 4 1 2 := by
    show IsShiftSymmetric _
    unfold IsShiftSymmetric
    decide
  have himg := key ⟨_, hs, rfl⟩
  have hn : ¬ IsShiftSymmetric
      (locMap (fun (u : Lat 4 1) (_ : Fin 1) => if u 0 = 2 then (fun _ => 1) else u)
        (fun x : Fin 1 → Fin 2 => x 0)
        (fun u : Lat 4 1 => if (u 0).val % 2 = 1 then (1 : Fin 2) else 0)) := by
    unfold IsShiftSymmetric locMap
    decide
  exact hn himg

/-! ## Corollary 8.2 -/

theorem insolvTraj_proved : insolvTrajStatement := by
  intro n d σ _ _ _ _ Φ hΦ s hs k
  exact isShiftSymmetric_iterate hΦ hs k

theorem insolvGeneral_proved : insolvGeneralStatement := by
  intro n d σ _ _ _ _ T hT Φ hΦ hsol
  obtain ⟨x, hxT, hxS, hacc⟩ := hT
  obtain ⟨k, hk⟩ := hsol x hxT
  exact hacc hk (isShiftSymmetric_iterate hΦ hxS k)

theorem insolvGeneralCA_proved : insolvGeneralCAStatement := by
  intro n d σ hn hd hσ hN T hT b offs φ
  exact insolvGeneral_proved n d σ hn hd hσ hN T hT _ (caMap_equivariant offs φ)

/-- A nonzero translation exists for `n ≥ 2`, `d ≥ 1`. -/
theorem exists_ne_zero_lat {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    (fun _ : Fin d => (1 : ZMod n)) ≠ 0 := by
  have : Fact (1 < n) := ⟨by omega⟩
  intro h
  have := congrFun h ⟨0, by omega⟩
  exact one_ne_zero this

theorem insolvConst_proved : insolvConstStatement := by
  intro n d σ hn hd hσ _
  have hc : ∀ a : Fin σ, (fun _ : Lat n d => a) ∈ SS n d σ := fun a =>
    isShiftSymmetric_const a _ (exists_ne_zero_lat hn hd)
  exact ⟨⟨_, hc ⟨0, by omega⟩⟩, hc⟩

theorem leaderAsym_proved : leaderAsymStatement := by
  intro n d σ _ _ _ _ t ht hS
  obtain ⟨a, u, hu, huniq⟩ := ht
  obtain ⟨v, hv0, hv⟩ := hS
  have h1 : t (u + v) = a := by
    have := congrFun hv u
    simp only [shift_apply] at this
    rw [this, hu]
  have h2 := huniq _ h1
  exact hv0 (by simpa using h2)

theorem leaderNeverReached_proved : leaderNeverReachedStatement := by
  intro n d σ hn hd hσ hN Φ hΦ x hx k h
  exact leaderAsym_proved n d σ hn hd hσ hN _ h (isShiftSymmetric_iterate hΦ hx k)

theorem leaderRestrict_proved : leaderRestrictStatement := by
  intro n d σ hn hd hσ hN ℓ X Φ hΦ hsol
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro x ⟨hxX, hxS⟩
  obtain ⟨k, hk⟩ := hsol x hxX
  exact leaderNeverReached_proved n d σ hn hd hσ hN Φ hΦ x hxS k ⟨ℓ, hk⟩

theorem leaderElection_proved : leaderElectionStatement := by
  intro n d σ hn hd hσ hN ℓ Φ hΦ hsol
  have h := leaderRestrict_proved n d σ hn hd hσ hN ℓ Set.univ Φ hΦ hsol
  obtain ⟨⟨x, hx⟩, -⟩ := insolvConst_proved n d σ hn hd hσ hN
  have : x ∈ (Set.univ ∩ SS n d σ) := ⟨Set.mem_univ _, hx⟩
  rw [h] at this
  exact this

theorem insolv_proved : insolvStatement :=
  ⟨insolvGeneral_proved, insolvGeneralCA_proved, insolvConst_proved,
    insolvTraj_proved, leaderAsym_proved, leaderNeverReached_proved,
    leaderElection_proved, leaderRestrict_proved⟩

/-! ## Proposition 8.3 -/

theorem rankCard_proved : rankCardStatement := by
  intro n d σ hn _ _ p hp hpn s
  exact card_eq_pow_rkP _ hp hpn s

theorem rankIntrinsic_proved : rankIntrinsicStatement := by
  intro n d σ hn _ _ p hp hpn s
  have : NeZero n := ⟨by omega⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  rw [rkP_eq_iff]
  let _ : Module (ZMod p) (stab s ⊓ latTorsion n d p : AddSubgroup (Lat n d)) :=
    AddCommMonoid.zmodModule (fun x => Subtype.ext x.2.2)
  exact (FiniteField.pow_finrank_eq_natCard p
    (stab s ⊓ latTorsion n d p : AddSubgroup (Lat n d))).symm

theorem rankRange_proved : rankRangeStatement := by
  intro n d σ hn _ _ p hp hpn s
  have : NeZero n := ⟨by omega⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hc : Nat.card (stab s ⊓ latTorsion n d p : AddSubgroup (Lat n d))
      ≤ Nat.card (latTorsion n d p) := AddSubgroup.card_le_of_le inf_le_right
  rw [card_eq_pow_rkP (by omega) hp hpn s, card_latTorsion hpn] at hc
  rw [Finset.mem_Icc]
  exact ⟨Nat.zero_le _, (Nat.pow_le_pow_iff_right hp.two_le).mp hc⟩

theorem rankMono_proved : rankMonoStatement := by
  intro n d σ hn _ _ Φ hΦ s p hp hpn
  exact rkP_le_of_stab_le _ hp hpn (stab_le_stab_apply hΦ s)

theorem rankTraj_proved : rankTrajStatement := by
  intro n d σ hn hd hσ Φ hΦ s p hp hpn
  refine monotone_nat_of_le_succ fun k => ?_
  simp only [Function.iterate_succ_apply']
  exact rankMono_proved n d σ hn hd hσ Φ hΦ _ p hp hpn

theorem rank_proved : rankStatement :=
  ⟨rankCard_proved, rankIntrinsic_proved, rankRange_proved, rankMono_proved,
    rankTraj_proved⟩

/-! ## Prose after Proposition 8.3 -/

theorem rankFull_proved : rankFullStatement := by
  intro n d σ hn _ _ p hp hpn s
  have : NeZero n := ⟨by omega⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [rkP_eq_iff, ← card_latTorsion (n := n) (d := d) hpn]
  constructor
  · intro hc
    have heq : stab s ⊓ latTorsion n d p = latTorsion n d p :=
      AddSubgroup.eq_of_le_of_card_ge inf_le_right hc.ge
    exact inf_eq_right.mp heq
  · intro hle
    rw [inf_eq_right.mpr hle]

theorem rankOne_proved : rankOneStatement := by
  intro n d σ hn _ _ p hp hpn s
  have : NeZero n := ⟨by omega⟩
  rw [rkP_eq_iff, pow_one]
  constructor
  · intro hc
    set K : AddSubgroup (Lat n d) := stab s ⊓ latTorsion n d p
    have hKbot : K ≠ ⊥ := by
      intro hbot
      rw [hbot, AddSubgroup.card_bot] at hc
      exact hp.one_lt.ne hc
    obtain ⟨w, hwK, hw0⟩ := (AddSubgroup.bot_or_exists_ne_zero K).resolve_left hKbot
    exact ⟨w, addOrderOf_eq_of_mem_card_prime hp hc hwK hw0,
      (zmultiples_eq_of_mem_card_prime hp hc hwK hw0).symm⟩
  · rintro ⟨w, hw, heq⟩
    rw [heq, Nat.card_zmultiples, hw]

theorem levelSetInvariantFalse_proved : levelSetInvariantFalseStatement := by
  intro h
  have key := h 2 1 2 le_rfl le_rfl le_rfl
    (caMap (fun _ : Fin 1 => (0 : Lat 2 1)) (fun _ : Fin 1 → Fin 2 => (0 : Fin 2)))
    (caMap_equivariant _ _) 2 Nat.prime_two (dvd_refl 2)
    (fun u : Lat 2 1 => if u = 0 then (0 : Fin 2) else 1)
  -- the image is the constant `0`, fixed by every translation
  have hconst : caMap (fun _ : Fin 1 => (0 : Lat 2 1)) (fun _ : Fin 1 → Fin 2 => (0 : Fin 2))
      (fun u : Lat 2 1 => if u = 0 then (0 : Fin 2) else 1) = fun _ => 0 := rfl
  have hstab_top : stab (fun _ : Lat 2 1 => (0 : Fin 2)) = ⊤ := by
    ext v; simp only [mem_stab, AddSubgroup.mem_top, iff_true]; rfl
  have hstab_bot : stab (fun u : Lat 2 1 => if u = 0 then (0 : Fin 2) else 1) = ⊥ := by
    ext v
    simp only [mem_stab, AddSubgroup.mem_bot]
    revert v
    decide
  have h1 : rkP (n := 2) (d := 1) (σ := 2) (by omega) Nat.prime_two (dvd_refl 2)
      (fun _ : Lat 2 1 => (0 : Fin 2)) = 1 := by
    rw [rkP_eq_iff, hstab_top, top_inf_eq, card_latTorsion (dvd_refl 2)]
  have h0 : rkP (n := 2) (d := 1) (σ := 2) (by omega) Nat.prime_two (dvd_refl 2)
      (fun u : Lat 2 1 => if u = 0 then (0 : Fin 2) else 1) = 0 := by
    rw [rkP_eq_iff, hstab_bot, bot_inf_eq, AddSubgroup.card_bot, pow_zero]
  rw [hconst, h1, h0] at key
  exact one_ne_zero key

theorem superlevelInvariant_proved : superlevelInvariantStatement := by
  intro n d σ hn hd hσ Φ hΦ p hp hpn k s hk t
  have h := rankTraj_proved n d σ hn hd hσ Φ hΦ s p hp hpn (Nat.zero_le t)
  simp only [Function.iterate_zero, id_eq] at h
  exact hk.trans h

theorem rankProse_proved : rankProseStatement :=
  ⟨rankFull_proved, rankOne_proved, superlevelInvariant_proved⟩

/-! ## Everything -/

theorem S07_proved : S07Statement :=
  ⟨caption_proved, irrev_proved, equivarianceNeeded_proved, insolv_proved,
    rank_proved, rankProse_proved⟩

end ShiftSym.P07
