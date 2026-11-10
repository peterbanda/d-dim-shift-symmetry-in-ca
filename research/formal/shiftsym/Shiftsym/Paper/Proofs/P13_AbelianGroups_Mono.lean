/-
Paper group 13 (Section 4.5) — Corollary 4.8(ii) (`cor:abelian-ranks`), Remark 4.9(ii)'s free
action, and the order of a rectangular torus. Proofs of the frozen statements

* `rectCard_proved`    — `|Z_{n_1} × ⋯ × Z_{n_d}| = ∏ n_i`;
* `freeAction_proved`  — translates of an aperiodic configuration are aperiodic, only `0` fixes one;
* `monotone_proved`    — `|S_{G'}| - |S_G| = p^{d_p(G)} ac(G'') > 0` for a supplied `G''`;
* `stepStrict_proved`  — the strict increase along a rank step, `G''` not supplied;
* `cyclicMin_proved`   — the cyclic group has the fewest shift-symmetric configurations.

Route. By Theorem 4.7 (`abelianEnum_proved`) every count is `abelianRHS N (pRank ·) σ`; the step
identity `acR_step` (`P13_AbelianGroups_MonoAlg`, the `q`-Pascal argument of the paper) gives
`|S_{G'}| - |S_G| = p^{d_p} (σ^(N/p) - abelianRHS (N/p) (pRank G) σ)`. Positivity of the last
factor: it is `ac(H) ≥ 1` for a group `H` of order `N/p` with the ranks of `G` — either the supplied
`G''`, or a rectangular torus `∏_{q ∣ N/p} (Z_{q^(a_q - r_q + 1)} × Z_q^(r_q - 1))` built here
(`exists_torus`, the paper's construction; it needs `1 ≤ d_q(G) ≤ v_q(N/p)`, from Cauchy and
`|G[q]| ∣ |G|`). The indicator of one cell is aperiodic (`aper_nonempty`). The cyclic minimum is an
induction on `Σ_q d_q` lowering one rank at a time.
Frozen statements: `Shiftsym/Paper/S13_AbelianGroups.lean`.
-/
import Shiftsym.Paper.Proofs.P13_AbelianGroups_MonoAlg

namespace ShiftSym.P13.Mono

open ShiftSym ShiftSym.P13

/-! ### Aperiodic configurations exist (`σ ≥ 2`) -/

section Aper

variable {G : Type*} [AddCommGroup G]

theorem aper_nonempty {σ : ℕ} (hσ : 2 ≤ σ) : Nonempty (Aper G σ) := by
  classical
  refine ⟨⟨fun u => if u = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩, ?_⟩⟩
  rintro ⟨v, hv, h⟩
  have h1 := h (-v)
  simp only [neg_add_cancel, if_neg (neg_ne_zero.mpr hv)] at h1
  exact absurd (congrArg Fin.val h1) (by simp)

variable [Finite G]

/-- `ac(G) = σ^N - |S_G|` is the number of aperiodic configurations. -/
theorem ac_eq_card_aper (σ : ℕ) :
    (σ : ℤ) ^ Nat.card G - Nat.card {s : G → Fin σ // IsShiftSymmetricG s}
      = Nat.card (Aper G σ) := by
  have h := card_sym_add_card_aper (G := G) (σ := σ)
  have h' : ((Nat.card {s : G → Fin σ // IsShiftSymmetricG s} : ℕ) : ℤ)
      + (Nat.card (Aper G σ) : ℤ) = (σ : ℤ) ^ Nat.card G := by
    exact_mod_cast h
  linarith

theorem ac_pos {σ : ℕ} (hσ : 2 ≤ σ) :
    0 < (σ : ℤ) ^ Nat.card G - Nat.card {s : G → Fin σ // IsShiftSymmetricG s} := by
  rw [ac_eq_card_aper]
  have := aper_nonempty (G := G) hσ
  exact_mod_cast Nat.card_pos

end Aper

/-! ### Cauchy and Lagrange for the `p`-ranks -/

section Ranks

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem pRank_pow_dvd {q : ℕ} (hq : q.Prime) : q ^ pRank G q ∣ Nat.card G := by
  rw [← pRankPow_proved G q hq, ← Gen.card_torsG]
  exact AddSubgroup.card_addSubgroup_dvd_card _

theorem one_le_pRank {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card G) : 1 ≤ pRank G q := by
  have := Fact.mk hq
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := G) q hdvd
  by_contra h0
  have h0' : pRank G q = 0 := by omega
  have hcard := pRankPow_proved G q hq
  rw [h0', pow_zero, Nat.card_eq_one_iff_unique] at hcard
  have hxq : q • x = 0 := hx ▸ addOrderOf_nsmul_eq_zero x
  have hx0 : x ≠ 0 := by
    intro hx0
    rw [hx0, addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have := hcard.1.elim (⟨x, hxq⟩ : {g : G // q • g = 0}) ⟨0, smul_zero q⟩
  exact hx0 (congrArg Subtype.val this)

end Ranks

/-! ### Divisibility bookkeeping -/

theorem pow_dvd_div_of_ne {q p r N : ℕ} (hq : q.Prime) (hp : p.Prime) (hne : q ≠ p)
    (hpN : p ∣ N) (hqN : q ^ r ∣ N) : q ^ r ∣ N / p := by
  have hcop : Nat.Coprime (q ^ r) p := Nat.Coprime.pow_left r ((Nat.coprime_primes hq hp).mpr hne)
  rw [← Nat.mul_div_cancel' hpN] at hqN
  exact hcop.dvd_of_dvd_mul_left hqN

theorem pow_dvd_div_self {p k N : ℕ} (h : p ^ (k + 1) ∣ N) : p ^ k ∣ N / p :=
  Nat.dvd_div_of_mul_dvd (by rwa [← pow_succ'])

/-! ### A group with prescribed order and ranks -/

/-- `|G[p]| = p ^ #{i | p ∣ n_i}` for `G = ∀ i, ZMod (n i)` over any finite index type. -/
theorem card_pi_torsion' {ι : Type*} [Fintype ι] (n : ι → ℕ) {p : ℕ} (hn : ∀ i, 1 ≤ n i)
    (hp : p.Prime) :
    Nat.card {g : (∀ i, ZMod (n i)) // p • g = 0}
      = p ^ (Finset.univ.filter fun i => p ∣ n i).card := by
  classical
  have e : {g : (∀ i, ZMod (n i)) // p • g = 0} ≃ ∀ i, {x : ZMod (n i) // p • x = 0} :=
    (Equiv.subtypeEquivRight fun g => by
      simp only [funext_iff, Pi.smul_apply, Pi.zero_apply]).trans
      (Equiv.subtypePiEquivPi (p := fun i (x : ZMod (n i)) => p • x = 0))
  rw [Nat.card_congr e, Nat.card_pi]
  simp only [card_zmod_torsion (hn _) hp]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem prime_dvd_prime_pow_iff {q q' k : ℕ} (hq : q.Prime) (hq' : q'.Prime) (hk : k ≠ 0) :
    q ∣ q' ^ k ↔ q = q' := by
  constructor
  · intro h
    exact (Nat.prime_dvd_prime_iff_eq hq hq').mp (hq.dvd_of_dvd_pow h)
  · rintro rfl
    exact dvd_pow_self q hk

/-- **The paper's construction**: for `N ≠ 0` and ranks `1 ≤ r q` with `q ^ r q ∣ N` at every
prime `q ∣ N`, the torus `∏_{q ∣ N} (Z_{q^(v_q(N) - r q + 1)} × Z_q^(r q - 1))`, as a family of
cyclic orders indexed by `Σ q : N.primeFactors, Fin (r q)`. -/
theorem exists_torus {N : ℕ} (hN : N ≠ 0) (r : ℕ → ℕ)
    (hr : ∀ q ∈ N.primeFactors, 1 ≤ r q ∧ q ^ r q ∣ N) :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ), (∀ x, 1 ≤ n x) ∧ ∏ x, n x = N ∧
      ∀ q ∈ N.primeFactors, (Finset.univ.filter fun x => q ∣ n x).card = r q := by
  classical
  let ex : ℕ → ℕ → ℕ := fun q i => if i = 0 then N.factorization q - r q + 1 else 1
  have hex : ∀ q i, ex q i ≠ 0 := fun q i => by
    simp only [ex]; split_ifs <;> omega
  refine ⟨Σ q : N.primeFactors, Fin (r q), inferInstance,
    fun x => (x.1 : ℕ) ^ ex x.1 x.2, ?_, ?_, ?_⟩
  · rintro ⟨q, i⟩
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.prime_of_mem_primeFactors q.2).ne_zero)
  · rw [Fintype.prod_sigma]
    have hq : ∀ q : N.primeFactors,
        ∏ i : Fin (r q), (q : ℕ) ^ ex q i = (q : ℕ) ^ N.factorization q := by
      intro q
      obtain ⟨h1, hdvd⟩ := hr q q.2
      have hle : r q ≤ N.factorization q :=
        ((Nat.prime_of_mem_primeFactors q.2).pow_dvd_iff_le_factorization hN).mp hdvd
      rw [Fin.prod_univ_eq_prod_range (fun i => (q : ℕ) ^ ex q i) (r q)]
      obtain ⟨s, hs⟩ : ∃ s, r q = s + 1 := ⟨r q - 1, by omega⟩
      rw [hs, Finset.prod_range_succ']
      simp only [ex, if_neg (Nat.succ_ne_zero _), if_pos rfl, pow_one, Finset.prod_const,
        Finset.card_range, ← pow_add]
      congr 1
      omega
    rw [Fintype.prod_congr _ _ hq,
      Finset.prod_coe_sort N.primeFactors (fun q => q ^ N.factorization q)]
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hN]
    rw [Finsupp.prod, Nat.support_factorization]
  · intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    rw [Finset.card_filter, Fintype.sum_sigma]
    have hin : ∀ q' : N.primeFactors, (∑ i : Fin (r q'),
        if q ∣ (q' : ℕ) ^ ex q' i then 1 else 0) = if q = q' then r q' else 0 := by
      intro q'
      have hq'p : (q' : ℕ).Prime := Nat.prime_of_mem_primeFactors q'.2
      simp only [prime_dvd_prime_pow_iff hqp hq'p (hex _ _)]
      split_ifs with h
      · simp
      · simp
    rw [Fintype.sum_congr _ _ hin, Finset.sum_eq_single ⟨q, hq⟩]
    · simp
    · intro q' _ hne
      rw [if_neg]
      intro h
      exact hne (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- **Positivity of the complement**: if `1 ≤ r q` and `q ^ r q ∣ N` at every prime `q ∣ N`, then
`σ^N - abelianRHS N r σ > 0` (`σ ≥ 2`): it is `ac(H)` for the torus `H` of `exists_torus`. -/
theorem acR_pos {σ : ℕ} (hσ : 2 ≤ σ) {N : ℕ} (hN : N ≠ 0) (r : ℕ → ℕ)
    (hr : ∀ q ∈ N.primeFactors, 1 ≤ r q ∧ q ^ r q ∣ N) :
    0 < (σ : ℤ) ^ N - abelianRHS N r σ := by
  obtain ⟨ι, _, n, hn1, hprod, hcount⟩ := exists_torus hN r hr
  have : ∀ x, NeZero (n x) := fun x => ⟨by have := hn1 x; omega⟩
  have hcard : Nat.card (∀ x, ZMod (n x)) = N := by
    rw [Nat.card_pi]
    simp only [Nat.card_zmod]
    exact hprod
  have hrank : ∀ q ∈ N.primeFactors, pRank (∀ x, ZMod (n x)) q = r q := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    unfold pRank
    rw [card_pi_torsion' n hn1 hqp, hqp.factorization_pow, Finsupp.single_eq_same, hcount q hq]
  have hE := abelianEnum_proved (∀ x, ZMod (n x)) σ (by omega)
  rw [hcard, abelianRHS_congr_pf hrank] at hE
  have hpos := ac_pos (G := ∀ x, ZMod (n x)) hσ
  rw [hcard, hE] at hpos
  exact hpos

/-! ### The cyclic minimum on the right-hand sides -/

/-- Lowering ranks towards `1` lowers the right-hand side: for ranks `1 ≤ dp q` with
`q ^ dp q ∣ N` at every prime `q ∣ N`, `abelianRHS N 1 σ ≤ abelianRHS N dp σ`. -/
theorem abelianRHS_one_le {σ : ℕ} (hσ : 2 ≤ σ) {N : ℕ} (hN : N ≠ 0) :
    ∀ k : ℕ, ∀ dp : ℕ → ℕ, ∑ q ∈ N.primeFactors, dp q = k →
      (∀ q ∈ N.primeFactors, 1 ≤ dp q ∧ q ^ dp q ∣ N) →
        abelianRHS N (fun _ => 1) σ ≤ abelianRHS N dp σ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro dp hk hdp
  by_cases hall : ∀ q ∈ N.primeFactors, dp q = 1
  · exact le_of_eq (abelianRHS_congr_pf (fun q hq => (hall q hq).symm) σ)
  push Not at hall
  obtain ⟨p, hpN, hp1⟩ := hall
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpN
  have hp2 : 2 ≤ dp p := by have := (hdp p hpN).1; omega
  set dp₀ : ℕ → ℕ := Function.update dp p (dp p - 1) with hdp₀
  have hdp₀p : dp₀ p = dp p - 1 := Function.update_self _ _ _
  have hdp₀q : ∀ q, q ≠ p → dp₀ q = dp q := fun q hq => Function.update_of_ne hq _ _
  -- the rank sum drops by one
  have hsum : ∑ q ∈ N.primeFactors, dp₀ q + 1 = k := by
    have e1 : dp₀ p + ∑ q ∈ N.primeFactors.erase p, dp₀ q = ∑ q ∈ N.primeFactors, dp₀ q :=
      Finset.add_sum_erase _ _ hpN
    have e2 : dp p + ∑ q ∈ N.primeFactors.erase p, dp q = ∑ q ∈ N.primeFactors, dp q :=
      Finset.add_sum_erase _ _ hpN
    have e3 : ∑ q ∈ N.primeFactors.erase p, dp₀ q = ∑ q ∈ N.primeFactors.erase p, dp q :=
      Finset.sum_congr rfl fun q hq => hdp₀q q (Finset.ne_of_mem_erase hq)
    rw [hdp₀p] at e1
    omega
  have hpk : p ^ dp p ∣ N := (hdp p hpN).2
  have hpk' : p ^ (dp p - 1 + 1) ∣ N := by rwa [Nat.sub_add_cancel (by omega)]
  have hdp₀ : ∀ q ∈ N.primeFactors, 1 ≤ dp₀ q ∧ q ^ dp₀ q ∣ N := by
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      rw [hdp₀p]
      exact ⟨by omega, (pow_dvd_pow q (Nat.sub_le _ _)).trans hpk⟩
    · rw [hdp₀q q hqp]
      exact hdp q hq
  have hIH := ih (∑ q ∈ N.primeFactors, dp₀ q) (by omega) dp₀ rfl hdp₀
  -- the step identity from `dp₀` to `dp`
  have hpdvd : p ∣ N := Nat.dvd_of_mem_primeFactors hpN
  have hpNp : p ∣ N / p := by
    have h2 : p ^ (1 + 1) ∣ N := (pow_dvd_pow p hp2).trans hpk
    simpa using pow_dvd_div_self h2
  have hstep := acR_step σ hp hpdvd hN (e := dp₀) (e' := dp) (by rw [hdp₀p]; omega)
    (fun q _ hq => (hdp₀q q hq).symm) (Or.inl hpNp)
  have hNp : N / p ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hpdvd) hp.pos).ne'
  have hpos : 0 < (σ : ℤ) ^ (N / p) - abelianRHS (N / p) dp₀ σ := by
    refine acR_pos hσ hNp dp₀ fun q hq => ?_
    have hqN : q ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq,
        (Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd hpdvd), hN⟩
    refine ⟨(hdp₀ q hqN).1, ?_⟩
    by_cases hqp : q = p
    · subst hqp
      rw [hdp₀p]
      exact pow_dvd_div_self hpk'
    · exact pow_dvd_div_of_ne (Nat.prime_of_mem_primeFactors hq) hp hqp hpdvd (hdp₀ q hqN).2
  have hfac : (0 : ℤ) ≤ (p : ℤ) ^ dp₀ p * ((σ : ℤ) ^ (N / p) - abelianRHS (N / p) dp₀ σ) :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg p) _) hpos.le
  linarith

end ShiftSym.P13.Mono

namespace ShiftSym.P13

open ShiftSym.P13.Mono

/-- **Frozen `rectCardStatement`, machine-checked**: a rectangular torus has order `∏ n_i`. -/
theorem rectCard_proved (d : ℕ) (n : Fin d → ℕ) : rectCardStatement d n :=
  fun _ => card_rect n

/-- **Frozen `freeActionStatement`, machine-checked**: `G` acts freely on the aperiodic
configurations. -/
theorem freeAction_proved (G : Type*) [AddCommGroup G] (σ : ℕ) : freeActionStatement G σ := by
  intro s hs v
  refine ⟨not_isShiftSymmetricG_tr hs v, fun hv => ?_⟩
  by_contra hne
  exact hs ⟨v, hne, hv⟩

/-- **Frozen `monotoneStatement` (Corollary 4.8(ii)), machine-checked**:
`|S_{G'}| - |S_G| = p^{d_p(G)} ac(G'') > 0`. -/
theorem monotone_proved (G G' G'' : Type*) [AddCommGroup G] [Finite G] [AddCommGroup G']
    [Finite G'] [AddCommGroup G''] [Finite G''] (σ p : ℕ) : monotoneStatement G G' G'' σ p := by
  intro hσ hp hcard' hrank_p hrank_q hcard'' hrank''
  have hN : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hpN : p ∣ Nat.card G := Dvd.intro_left _ hcard''
  have hdiv : Nat.card G / p = Nat.card G'' := by
    rw [← hcard'', Nat.mul_div_cancel _ hp.pos]
  have hcond : p ∣ Nat.card G / p ∨ pRank G p = 0 := by
    by_cases hd : p ∣ Nat.card G / p
    · exact Or.inl hd
    · right
      rw [← hrank'' p hp]
      by_contra h0
      apply hd
      rw [hdiv]
      exact (dvd_pow_self p h0).trans (pRank_pow_dvd hp)
  have hstep := acR_step σ hp hpN hN (e := pRank G) (e' := pRank G') hrank_p hrank_q hcond
  have eG := abelianEnum_proved G σ (by omega)
  have eG' := abelianEnum_proved G' σ (by omega)
  have eG'' := abelianEnum_proved G'' σ (by omega)
  rw [hcard'] at eG'
  rw [hdiv, abelianRHS_congr (N := Nat.card G'') (fun q hq => (hrank'' q hq).symm) σ,
    ← eG''] at hstep
  refine ⟨?_, ac_pos hσ⟩
  rw [eG, eG']
  linear_combination hstep

/-- **Frozen `stepStrictStatement` (Corollary 4.8(ii), strict increase), machine-checked**:
raising one rank strictly increases the count; the intermediate group of order `N/p` is the
rectangular torus of `exists_torus`. -/
theorem stepStrict_proved (G G' : Type*) [AddCommGroup G] [Finite G] [AddCommGroup G']
    [Finite G'] (σ p : ℕ) : stepStrictStatement G G' σ p := by
  intro hσ hp hcard' hrank_p hrank_q
  set N := Nat.card G with hNdef
  have hN : N ≠ 0 := Nat.card_pos.ne'
  have hpa : p ^ (pRank G p + 1) ∣ N := by
    rw [← hrank_p, ← hcard']
    exact pRank_pow_dvd hp
  have hpN : p ∣ N := (dvd_pow_self p (Nat.succ_ne_zero _)).trans hpa
  have hpaN : p ^ pRank G p ∣ N / p := pow_dvd_div_self hpa
  have hcond : p ∣ N / p ∨ pRank G p = 0 := by
    rcases Nat.eq_zero_or_pos (pRank G p) with h0 | hpos
    · exact Or.inr h0
    · exact Or.inl ((dvd_pow_self p hpos.ne').trans hpaN)
  have hstep := acR_step σ hp hpN hN (e := pRank G) (e' := pRank G') hrank_p hrank_q hcond
  have hNp : N / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hpN) hp.pos).ne'
  have hpos : 0 < (σ : ℤ) ^ (N / p) - abelianRHS (N / p) (pRank G) σ := by
    refine acR_pos hσ hNp (pRank G) fun q hq => ?_
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqN : q ∣ N := (Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd hpN)
    refine ⟨one_le_pRank hqp hqN, ?_⟩
    by_cases hqe : q = p
    · subst hqe
      exact hpaN
    · exact pow_dvd_div_of_ne hqp hp hqe hpN (pRank_pow_dvd hqp)
  have eG := abelianEnum_proved G σ (by omega)
  have eG' := abelianEnum_proved G' σ (by omega)
  rw [hcard'] at eG'
  have hfac : (0 : ℤ) < (p : ℤ) ^ pRank G p * ((σ : ℤ) ^ (N / p) - abelianRHS (N / p) (pRank G) σ) :=
    mul_pos (pow_pos (by exact_mod_cast hp.pos) _) hpos
  have hlt : (Nat.card {s : G → Fin σ // IsShiftSymmetricG s} : ℤ)
      < Nat.card {s : G' → Fin σ // IsShiftSymmetricG s} := by
    rw [eG, eG']
    linarith
  exact_mod_cast hlt

/-- **Frozen `cyclicMinStatement` (Corollary 4.8(ii), cyclic minimum), machine-checked**:
`|S_{Z_N}| ≤ |S_G|` for every finite abelian group `G` of order `N`. -/
theorem cyclicMin_proved (G : Type*) [AddCommGroup G] [Finite G] (σ : ℕ) :
    cyclicMinStatement G σ := by
  intro hσ
  set N := Nat.card G with hNdef
  have hN : N ≠ 0 := Nat.card_pos.ne'
  have : NeZero N := ⟨hN⟩
  have eZ := abelianEnum_proved (ZMod N) σ (by omega)
  have eG := abelianEnum_proved G σ (by omega)
  rw [Nat.card_zmod] at eZ
  have hrZ : ∀ q ∈ N.primeFactors, pRank (ZMod N) q = 1 := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    unfold pRank
    rw [card_zmod_torsion (Nat.one_le_iff_ne_zero.mpr hN) hqp,
      if_pos (Nat.dvd_of_mem_primeFactors hq), hqp.factorization_self]
  rw [abelianRHS_congr_pf hrZ] at eZ
  have hle := abelianRHS_one_le hσ hN _ (pRank G) rfl fun q hq => by
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    exact ⟨one_le_pRank hqp (Nat.dvd_of_mem_primeFactors hq), pRank_pow_dvd hqp⟩
  have hZ : (Nat.card {s : ZMod N → Fin σ // IsShiftSymmetricG s} : ℤ)
      ≤ Nat.card {s : G → Fin σ // IsShiftSymmetricG s} := by
    rw [eZ, eG]
    exact hle
  exact_mod_cast hZ

end ShiftSym.P13
