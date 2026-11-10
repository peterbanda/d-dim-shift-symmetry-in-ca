/-
Paper group 13 (Section 4.5; moved from extension group A1) (AbelianEnum) — the statements around the main theorem.

Proofs of the frozen statements of `Shiftsym/Paper/S13_AbelianGroups.lean` other than
Theorem 4.7 itself, `kActive` and `pRankPow` (proved in other `P13_AbelianGroups_*` modules):

* `bridge_proved`      — `IsShiftSymmetricG` on `Lat n d` is the core `IsShiftSymmetric`;
* `square_proved`      — Corollary (a): on `Z_n^d` the right-hand side is `enumerationRHS`;
* `rectRank_proved`    — the `p`-ranks of `Z_{n_1} × ⋯ × Z_{n_d}`: `|G[p]| = p ^ #{i | p ∣ n_i}`;
* `orbitCount_proved`  — Corollary (e), the orbit count: `G` acts freely on the aperiodic
  configurations, every orbit has `N` elements;
* `freeOrbits_proved`  — Corollary (e): `N ∣ σ^N − |S_G|`.

And the reductions to Theorem A1, which take it as a HYPOTHESIS (it is proved elsewhere):
`rectEnum_of_abelianEnum`, `onlyRanks_of_abelianEnum`, `cardTwoPrime_of_rectEnum` (with its
helpers `factorization_two_three`, `bigOmega_two_three`, `coeffA_two_three`, `abelianRHS_48`), plus the
convenience forms `rectEnum_of_main`, `cardTwoPrime_of_main` taking the main theorem for all
groups in `Type`.
-/
import Shiftsym.Paper.S13_AbelianGroups
import Shiftsym.Lemmas.Torsion

namespace ShiftSym.P13

open ShiftSym

/-! ### The bridge to the core definitions -/

theorem bridge_proved (n d σ : ℕ) : bridgeStatement n d σ := by
  intro s
  unfold IsShiftSymmetricG IsShiftSymmetric
  simp only [funext_iff, shift_apply]

/-! ### Congruence of the right-hand side in the ranks -/

theorem rankRad_congr {N : ℕ} {dp dp' : ℕ → ℕ} (h : ∀ p, p.Prime → dp p = dp' p) :
    rankRad N dp = rankRad N dp' :=
  Finset.prod_congr rfl fun p hp => by rw [h p (Nat.prime_of_mem_primeFactors hp)]

theorem coeffA_congr {dp dp' : ℕ → ℕ} (h : ∀ p, p.Prime → dp p = dp' p) (k : ℕ) :
    coeffA dp k = coeffA dp' k := by
  unfold coeffA
  congr 1
  exact Finset.prod_congr rfl fun p hp => by rw [h p (Nat.prime_of_mem_primeFactors hp)]

/-- The right-hand side only reads the ranks at primes. -/
theorem abelianRHS_congr {N : ℕ} {dp dp' : ℕ → ℕ} (h : ∀ p, p.Prime → dp p = dp' p) (σ : ℕ) :
    abelianRHS N dp σ = abelianRHS N dp' σ := by
  unfold abelianRHS
  rw [rankRad_congr h]
  exact Finset.sum_congr rfl fun k _ => by rw [coeffA_congr h]

/-! ### Corollary (a): the square torus -/

theorem square_proved (n d σ : ℕ) : squareStatement n d σ := by
  intro _
  unfold abelianRHS enumerationRHS
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [rankRad]
  · have hpf : (n ^ d).primeFactors = n.primeFactors := Nat.primeFactors_pow n hd.ne'
    have hrank : ∀ p, p ∣ n → rectRank (fun _ : Fin d => n) p = d := by
      intro p hp
      simp [rectRank, hp]
    have hR : rankRad (n ^ d) (rectRank fun _ : Fin d => n) = rad n ^ d := by
      rw [rankRad, hpf, rad, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [hrank p (Nat.dvd_of_mem_primeFactors hp)]
    rw [hR]
    refine Finset.sum_congr rfl fun h hh => ?_
    congr 1
    unfold coeffA coeffOf
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpn : p ∣ n := by
      have hph : p ∣ h := Nat.dvd_of_mem_primeFactors hp
      have hhn : h ∣ n ^ d := dvd_pow_of_mem_divisors_rad (Finset.mem_of_mem_erase hh)
      exact (Nat.prime_of_mem_primeFactors hp).dvd_of_dvd_pow (hph.trans hhn)
    rw [hrank p hpn]

/-! ### The `p`-ranks of a rectangular group -/

/-- `|ZMod m [p]|` is `p` if `p ∣ m` and `1` otherwise. -/
theorem card_zmod_torsion {m p : ℕ} (hm : 1 ≤ m) (hp : p.Prime) :
    Nat.card {x : ZMod m // p • x = 0} = if p ∣ m then p else 1 := by
  split_ifs with hdvd
  · have : NeZero m := ⟨by omega⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    have e : ZMod p ≃ {x : ZMod m // p • x = 0} := (zmodTorsionEquiv hdvd).toEquiv
    rw [← Nat.card_congr e, Nat.card_zmod]
  · have hcop : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hp).2 hdvd
    have hu : IsUnit (p : ZMod m) := (ZMod.isUnit_iff_coprime p m).2 hcop
    have h0 : ∀ x : {x : ZMod m // p • x = 0}, x = ⟨0, smul_zero p⟩ := by
      rintro ⟨x, hx⟩
      apply Subtype.ext
      rw [nsmul_eq_mul] at hx
      exact (hu.mul_right_eq_zero).1 hx
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨⟨0, smul_zero p⟩, h0⟩

/-- `|G[p]| = p ^ #{i | p ∣ n_i}` for `G = ∀ i, ZMod (n i)`. -/
theorem card_pi_torsion {d : ℕ} (n : Fin d → ℕ) {p : ℕ} (hn : ∀ i, 1 ≤ n i) (hp : p.Prime) :
    Nat.card {g : (∀ i, ZMod (n i)) // p • g = 0} = p ^ rectRank n p := by
  have e : {g : (∀ i, ZMod (n i)) // p • g = 0} ≃ ∀ i, {x : ZMod (n i) // p • x = 0} :=
    (Equiv.subtypeEquivRight fun g => by
      simp only [funext_iff, Pi.smul_apply, Pi.zero_apply]).trans
      (Equiv.subtypePiEquivPi (p := fun i (x : ZMod (n i)) => p • x = 0))
  rw [Nat.card_congr e, Nat.card_pi]
  simp only [card_zmod_torsion (hn _) hp]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rfl

theorem rectRank_proved (d : ℕ) (n : Fin d → ℕ) (p : ℕ) : rectRankStatement d n p := by
  intro hn hp
  unfold pRank
  rw [card_pi_torsion n hn hp, hp.factorization_pow]
  simp

/-! ### Corollary (e): free orbits on the aperiodic configurations -/

section Orbits

variable {G : Type*} [AddCommGroup G] {σ : ℕ}

/-- The translate `τ_v s = (u ↦ s (u + v))`. -/
def tr (s : G → Fin σ) (v : G) : G → Fin σ := fun u => s (u + v)

theorem tr_tr (s : G → Fin σ) (v w : G) : tr (tr s v) w = tr s (v + w) := by
  funext u
  simp only [tr]
  congr 1
  abel

theorem not_isShiftSymmetricG_tr {s : G → Fin σ} (hs : ¬ IsShiftSymmetricG s) (v : G) :
    ¬ IsShiftSymmetricG (tr s v) := by
  rintro ⟨w, hw, h⟩
  apply hs
  refine ⟨w, hw, fun x => ?_⟩
  have hx := h (x - v)
  simp only [tr] at hx
  rwa [show x - v + w + v = x + w by abel, show x - v + v = x by abel] at hx

theorem tr_injective {s : G → Fin σ} (hs : ¬ IsShiftSymmetricG s) :
    Function.Injective (tr s) := by
  intro v w hvw
  by_contra hne
  apply hs
  refine ⟨v - w, sub_ne_zero.mpr hne, fun x => ?_⟩
  have hx := congrFun hvw (x - w)
  simp only [tr] at hx
  rwa [show x - w + v = x + (v - w) by abel, show x - w + w = x by abel] at hx

theorem range_tr_tr (s : G → Fin σ) (v : G) :
    Set.range (tr (tr s v)) = Set.range (tr s) := by
  ext t
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨v + w, (tr_tr s v w).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨w - v, ?_⟩
    rw [tr_tr]
    congr 1
    abel

theorem mem_range_tr_self (s : G → Fin σ) : s ∈ Set.range (tr s) :=
  ⟨0, by funext u; simp [tr]⟩

variable (G σ)

/-- The orbit sets of the aperiodic configurations (as in `orbitCountStatement`). -/
abbrev Orb : Type _ :=
  {O : Set (G → Fin σ) //
    ∃ s : G → Fin σ, ¬ IsShiftSymmetricG s ∧ O = Set.range (fun v : G => fun u : G => s (u + v))}

/-- The aperiodic configurations. -/
abbrev Aper : Type _ := {s : G → Fin σ // ¬ IsShiftSymmetricG s}

variable {G σ}

/-- The orbit of an aperiodic configuration. -/
def orbOf (a : Aper G σ) : Orb G σ := ⟨Set.range (tr a.1), a.1, a.2, rfl⟩

/-- Every fibre of `orbOf` is a copy of `G`: the action is free. -/
theorem card_fiber_orbOf (O : Orb G σ) :
    Nat.card {a : Aper G σ // orbOf a = O} = Nat.card G := by
  obtain ⟨O, s, hs, rfl⟩ := O
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun v => ⟨⟨tr s v, not_isShiftSymmetricG_tr hs v⟩, Subtype.ext (range_tr_tr s v)⟩)
    ⟨?_, ?_⟩)
  · intro v w h
    exact tr_injective hs (congrArg (fun a => a.1.1) h)
  · rintro ⟨⟨t, ht⟩, hO⟩
    have h2 : Set.range (tr t) = Set.range (tr s) := congrArg Subtype.val hO
    have hmem : t ∈ Set.range (tr s) := h2 ▸ mem_range_tr_self t
    obtain ⟨v, rfl⟩ := hmem
    exact ⟨v, rfl⟩

theorem card_aper [Finite G] : Nat.card (Aper G σ) = Nat.card (Orb G σ) * Nat.card G := by
  have : Fintype (Orb G σ) := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (orbOf (G := G) (σ := σ))), Nat.card_sigma]
  simp only [card_fiber_orbOf, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card (α := Orb G σ)]

theorem card_sym_add_card_aper [Finite G] :
    Nat.card {s : G → Fin σ // IsShiftSymmetricG s} + Nat.card (Aper G σ) = σ ^ Nat.card G := by
  classical
  rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl _), Nat.card_fun, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end Orbits

theorem orbitCount_proved (G : Type*) [AddCommGroup G] [Finite G] (σ : ℕ) :
    orbitCountStatement G σ := by
  unfold orbitCountStatement
  have h1 := card_sym_add_card_aper (G := G) (σ := σ)
  have h2 := card_aper (G := G) (σ := σ)
  have h3 : (Nat.card (Orb G σ) : ℤ) * Nat.card G = (Nat.card (Aper G σ) : ℤ) := by
    exact_mod_cast h2.symm
  have h4 : ((Nat.card {s : G → Fin σ // IsShiftSymmetricG s} : ℕ) : ℤ)
      + (Nat.card (Aper G σ) : ℤ) = (σ : ℤ) ^ Nat.card G := by
    exact_mod_cast h1
  rw [h3]
  linarith

theorem freeOrbits_proved (G : Type*) [AddCommGroup G] [Finite G] (σ : ℕ) :
    freeOrbitsStatement G σ :=
  Dvd.intro_left _ (orbitCount_proved G σ)

/-! ### Reductions to Theorem A1 (taken as a hypothesis) -/

theorem card_rect {d : ℕ} (n : Fin d → ℕ) : Nat.card (∀ i : Fin d, ZMod (n i)) = ∏ i, n i := by
  rw [Nat.card_pi]
  simp only [Nat.card_zmod]

/-- Rectangular form from Theorem A1 for the group `∀ i, ZMod (n i)` (finite when every
`n i ≥ 1`; the instance is a binder because `abelianEnumStatement` needs it). -/
theorem rectEnum_of_abelianEnum (d : ℕ) (n : Fin d → ℕ) (σ : ℕ)
    [Finite (∀ i : Fin d, ZMod (n i))]
    (hA : abelianEnumStatement (∀ i : Fin d, ZMod (n i)) σ) : rectEnumStatement d n σ := by
  intro hn hσ
  rw [hA hσ, card_rect]
  exact abelianRHS_congr (fun p hp => rectRank_proved d n p hn hp) σ

/-- Rectangular form from Theorem A1 stated for all finite abelian groups in `Type`. -/
theorem rectEnum_of_main
    (hA : ∀ (G : Type) [AddCommGroup G] [Finite G] (σ : ℕ), abelianEnumStatement G σ)
    (d : ℕ) (n : Fin d → ℕ) (σ : ℕ) : rectEnumStatement d n σ := by
  intro hn hσ
  have : ∀ i, NeZero (n i) := fun i => ⟨by have := hn i; omega⟩
  exact rectEnum_of_abelianEnum d n σ (hA _ σ) hn hσ

theorem onlyRanks_of_abelianEnum (G H : Type*) [AddCommGroup G] [Finite G] [AddCommGroup H]
    [Finite H] (σ : ℕ) (hG : abelianEnumStatement G σ) (hH : abelianEnumStatement H σ) :
    onlyRanksStatement G H σ := by
  intro hcard hrank
  rcases Nat.eq_zero_or_pos σ with rfl | hσ
  · have : IsEmpty (G → Fin 0) := inferInstance
    have : IsEmpty (H → Fin 0) := inferInstance
    simp
  · have h := (hG hσ).trans ((abelianRHS_congr hrank σ).trans (hcard ▸ (hH hσ).symm))
    exact_mod_cast h

/-! ### The instance `Z_2 × Z_24`, `Z_4 × Z_12` -/

/-- `2 ^ a * 3 ^ b` factors as `2 ^ a` times `3 ^ b`. -/
theorem factorization_two_three (a b : ℕ) :
    (2 ^ a * 3 ^ b).factorization = Finsupp.single 2 a + Finsupp.single 3 b := by
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow]

theorem bigOmega_two_three (a b : ℕ) : bigOmega (2 ^ a * 3 ^ b) = a + b := by
  unfold bigOmega
  rw [factorization_two_three, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]

/-- The coefficient of the divisor `2 ^ a * 3 ^ b` (a prime absent from `h` contributes
`r_d(p, 0) = 1`). -/
theorem coeffA_two_three (dp : ℕ → ℕ) (a b : ℕ) :
    coeffA dp (2 ^ a * 3 ^ b)
      = (-1 : ℤ) ^ (1 + (a + b)) * ((rdCoeff 2 a (dp 2) : ℤ) * rdCoeff 3 b (dp 3)) := by
  have hf := factorization_two_three a b
  have hsub : (2 ^ a * 3 ^ b).primeFactors ⊆ {2, 3} := by
    intro p hp
    rw [← Nat.support_factorization, hf, Finsupp.mem_support_iff] at hp
    by_contra hne
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
    exact hp (by simp [Ne.symm hne.1, Ne.symm hne.2])
  rw [coeffA, bigOmega_two_three]
  congr 1
  rw [Finset.prod_subset hsub, Finset.prod_pair (by norm_num), hf]
  · simp
  · intro p _ hp
    rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
    rw [hp, rdCoeff, gaussBinom]
    simp

/-- The right-hand side for `N = 48` with `d_2 = 2`, `d_3 = 1`: `R = 12`, and the divisors
`2, 3, 4, 6, 12` carry the coefficients `3, 1, -2, -3, 2`. -/
theorem abelianRHS_48 {dp : ℕ → ℕ} (h2 : dp 2 = 2) (h3 : dp 3 = 1) :
    abelianRHS 48 dp 2 = 50388256 := by
  have hR : rankRad 48 dp = 12 := by
    rw [rankRad, show (48 : ℕ) = 2 ^ 4 * 3 ^ 1 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three,
      Finset.prod_union (by decide), Finset.prod_singleton, Finset.prod_singleton, h2, h3]
    norm_num
  have hdiv : (12 : ℕ).divisors.erase 1 = {2, 3, 4, 6, 12} := by decide
  have c2 : coeffA dp 2 = 3 := by
    rw [show (2 : ℕ) = 2 ^ 1 * 3 ^ 0 by norm_num, coeffA_two_three, h2, h3]
    decide
  have c3 : coeffA dp 3 = 1 := by
    rw [show (3 : ℕ) = 2 ^ 0 * 3 ^ 1 by norm_num, coeffA_two_three, h2, h3]
    decide
  have c4 : coeffA dp 4 = -2 := by
    rw [show (4 : ℕ) = 2 ^ 2 * 3 ^ 0 by norm_num, coeffA_two_three, h2, h3]
    decide
  have c6 : coeffA dp 6 = -3 := by
    rw [show (6 : ℕ) = 2 ^ 1 * 3 ^ 1 by norm_num, coeffA_two_three, h2, h3]
    decide
  have c12 : coeffA dp 12 = 2 := by
    rw [show (12 : ℕ) = 2 ^ 2 * 3 ^ 1 by norm_num, coeffA_two_three, h2, h3]
    decide
  rw [abelianRHS, hR, hdiv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    c2, c3, c4, c6, c12]
  norm_num

theorem cardTwoPrime_of_rectEnum (h1 : rectEnumStatement 2 ![2, 24] 2)
    (h2 : rectEnumStatement 2 ![4, 12] 2) : cardTwoPrimeStatement := by
  have e1 := h1 (by decide) (by norm_num)
  have e2 := h2 (by decide) (by norm_num)
  rw [show (∏ i, ![2, 24] i) = 48 by decide,
    abelianRHS_48 (show rectRank ![2, 24] 2 = 2 by decide)
      (show rectRank ![2, 24] 3 = 1 by decide)] at e1
  rw [show (∏ i, ![4, 12] i) = 48 by decide,
    abelianRHS_48 (show rectRank ![4, 12] 2 = 2 by decide)
      (show rectRank ![4, 12] 3 = 1 by decide)] at e2
  exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩

/-- The two-prime instance from Theorem A1 stated for all finite abelian groups in `Type`. -/
theorem cardTwoPrime_of_main
    (hA : ∀ (G : Type) [AddCommGroup G] [Finite G] (σ : ℕ), abelianEnumStatement G σ) :
    cardTwoPrimeStatement :=
  cardTwoPrime_of_rectEnum (rectEnum_of_main hA 2 ![2, 24] 2) (rectEnum_of_main hA 2 ![4, 12] 2)

end ShiftSym.P13
