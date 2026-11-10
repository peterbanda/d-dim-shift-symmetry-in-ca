/-
Phase H, group 05 (KActive) — proof helper module 3 of 3.

The 2019 Eqs. (30)–(33) (Banda–Caughman–Cenek–Teuscher, arXiv:1703.09030v2),
read with the §5 convention, are rewritings of the `d = 2` right-hand side
of Theorem 5.1:
* `eq30RHS = eq31RHS`: fiber `u ↦ min(u, 2)` (coordinatewise); the fiber
  over `v` is `{v ⊴ u ⊴ top(v)}` and `h(u) = h(min(u,2))`;
* `eq31RHS = eq32RHS`: the inner sum factorizes; per coordinate
  `Σ_{j=v_i}^{top(i)} (−1)^j binom(r_i+1, j) = (−1)^{v_i} r(i)`;
* `eq32RHS = kActiveRHS n 2`: rank vectors on the primes of `n` whose
  support leaves the primes of `gcd(k,n)` contribute `0` (then `h(v) ∤ k`),
  and `r_2(p, v) = 1, p+1, p` for `v = 0, 1, 2`;
* `eq33RHS = eq32RHS` at `σ = 2`;
* an evaluation lemma for index sets over a single prime.
-/
import Shiftsym.Paper.S05_KActive

namespace ShiftSym.P05

open ShiftSym

/-! ### Eq. (33) is Eq. (32) at `σ = 2` -/

theorem eq33RHS_eq_eq32RHS (n k : ℕ) : eq33RHS n k = eq32RHS n k 2 := by
  unfold eq33RHS eq32RHS
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 2
  unfold convBinom convTerm
  split_ifs <;> norm_num

/-! ### Eq. (31) = Eq. (32) -/

theorem inner_coord_sum {g : ℕ} (v : g.primeFactors → ℕ) (r : g.primeFactors)
    (hv : v r ≤ 2) :
    ∑ j ∈ Finset.Icc (v r) (top2019 v r), (-1 : ℤ) ^ j * ((((r : ℕ) + 1).choose j : ℕ) : ℤ)
      = (-1 : ℤ) ^ (v r) * (coef2019 r (v r) : ℤ) := by
  have hr : 2 ≤ (r : ℕ) := (Nat.prime_of_mem_primeFactors r.2).two_le
  unfold top2019
  generalize (r : ℕ) = q at hr ⊢
  generalize v r = x at hv ⊢
  interval_cases x
  · simp [coef2019]
  · simp [coef2019]
  · simp only [show ¬ (2 < 2) from by omega, if_false]
    have hsplit := Finset.sum_Ico_consecutive
      (fun j => (-1 : ℤ) ^ j * (((q + 1).choose j : ℕ) : ℤ)) (Nat.zero_le 2)
      (show 2 ≤ q + 2 by omega)
    have hfull : ∑ j ∈ Finset.Ico 0 (q + 2), (-1 : ℤ) ^ j * (((q + 1).choose j : ℕ) : ℤ) = 0 := by
      rw [← Finset.range_eq_Ico]
      exact Int.alternating_sum_range_choose_of_ne (by omega)
    have hIcc : Finset.Icc 2 (q + 1) = Finset.Ico 2 (q + 2) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hlow : ∑ j ∈ Finset.Ico 0 2, (-1 : ℤ) ^ j * (((q + 1).choose j : ℕ) : ℤ) = -(q : ℤ) := by
      simp [Finset.sum_range_succ]
    rw [hIcc]
    simp only [coef2019, show (2 : ℕ) ≠ 0 from by omega, show (2 : ℕ) ≠ 1 from by omega,
      if_false, if_true]
    linarith

theorem eq31RHS_eq_eq32RHS (n k σ : ℕ) : eq31RHS n k σ = eq32RHS n k σ := by
  unfold eq31RHS eq32RHS
  refine Finset.sum_congr rfl fun v hv => ?_
  have hv2 : ∀ r, v r ≤ 2 := fun r => by
    have := Fintype.mem_piFinset.mp (Finset.mem_of_mem_erase hv) r
    rw [Finset.mem_range] at this
    omega
  have hterm : ∀ u ∈ idxInner2019 v,
      (-1 : ℤ) ^ (1 + absVec u) * convTerm (n ^ 2) k (h2019 v) σ
        * ∏ r : (Nat.gcd k n).primeFactors, ((((r : ℕ) + 1).choose (u r) : ℕ) : ℤ)
      = -convTerm (n ^ 2) k (h2019 v) σ
        * ∏ r : (Nat.gcd k n).primeFactors,
            ((-1 : ℤ) ^ (u r) * ((((r : ℕ) + 1).choose (u r) : ℕ) : ℤ)) := by
    intro u _
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, absVec, pow_add, pow_one]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, idxInner2019]
  rw [show (∑ u ∈ Fintype.piFinset fun r => Finset.Icc (v r) (top2019 v r),
        ∏ r, (-1 : ℤ) ^ u r * ((((r : ℕ) + 1).choose (u r) : ℕ) : ℤ))
      = ∏ r, ∑ j ∈ Finset.Icc (v r) (top2019 v r),
          (-1 : ℤ) ^ j * ((((r : ℕ) + 1).choose j : ℕ) : ℤ) from
      (Finset.prod_univ_sum (fun r => Finset.Icc (v r) (top2019 v r))
        (fun r j => (-1 : ℤ) ^ j * ((((r : ℕ) + 1).choose j : ℕ) : ℤ))).symm]
  rw [Finset.prod_congr rfl (fun (r : (Nat.gcd k n).primeFactors) _ =>
    inner_coord_sum v r (hv2 r))]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, absVec, pow_add, pow_one]
  ring

/-! ### Eq. (30) = Eq. (31) -/

theorem min_two_cases (x : ℕ) : (x ≤ 2 ∧ min x 2 = x) ∨ (2 ≤ x ∧ min x 2 = 2) := by
  rcases le_total x 2 with h | h
  · exact Or.inl ⟨h, min_eq_left h⟩
  · exact Or.inr ⟨h, min_eq_right h⟩

/-- coordinatewise `min(u, 2)` -/
def min2 {g : ℕ} (u : g.primeFactors → ℕ) : g.primeFactors → ℕ := fun r => min (u r) 2

theorem h2019_min2 {g : ℕ} (u : g.primeFactors → ℕ) : h2019 (min2 u) = h2019 u := by
  unfold h2019 min2
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [min_assoc, min_self]

theorem fiber_min2 (n k : ℕ) {v : (Nat.gcd k n).primeFactors → ℕ} (hv : v ∈ idxTwo2019 n k) :
    (idxThirty2019 n k).filter (fun u => min2 u = v) = idxInner2019 v := by
  have hv2 : ∀ r, v r ≤ 2 := fun r => by
    have := Fintype.mem_piFinset.mp (Finset.mem_of_mem_erase hv) r
    rw [Finset.mem_range] at this
    omega
  have hv0 : v ≠ 0 := Finset.ne_of_mem_erase hv
  ext u
  simp only [idxThirty2019, idxInner2019, Finset.mem_filter, Finset.mem_erase,
    Fintype.mem_piFinset, Finset.mem_range, Finset.mem_Icc, top2019, min2, funext_iff]
  constructor
  · rintro ⟨⟨-, hu⟩, hm⟩ r
    have h1 := hu r
    have h2 := hm r
    have h3 := hv2 r
    rcases min_two_cases (u r) with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> rw [h5] at h2 <;>
      split_ifs with hlt <;> constructor <;> omega
  · intro h
    have hu : ∀ r : (Nat.gcd k n).primeFactors, v r ≤ u r ∧ u r ≤ (if v r < 2 then v r else (r : ℕ) + 1) := h
    refine ⟨⟨?_, fun r => ?_⟩, fun r => ?_⟩
    · intro hu0
      apply hv0
      funext r
      have := (hu r).1
      rw [hu0] at this
      simp only [Pi.zero_apply, nonpos_iff_eq_zero] at this ⊢
      exact this
    · have h1 := hu r
      have h3 := hv2 r
      split_ifs at h1 <;> omega
    · have h1 := hu r
      have h3 := hv2 r
      rcases min_two_cases (u r) with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> rw [h5] <;>
        split_ifs at h1 <;> omega

theorem eq30RHS_eq_eq31RHS (n k σ : ℕ) : eq30RHS n k σ = eq31RHS n k σ := by
  have hmaps : ∀ u ∈ idxThirty2019 n k, min2 u ∈ idxTwo2019 n k := by
    intro u hu
    simp only [idxThirty2019, idxTwo2019, Finset.mem_erase, Fintype.mem_piFinset,
      Finset.mem_range, min2] at hu ⊢
    refine ⟨?_, fun r => lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
    intro h0
    apply hu.1
    funext r
    have h := congrFun h0 r
    simp only [min2, Pi.zero_apply] at h ⊢
    rcases min_two_cases (u r) with ⟨_, h5⟩ | ⟨_, h5⟩
    · rw [h5] at h; exact h
    · rw [h5] at h; exact absurd h (by norm_num)
  unfold eq30RHS eq31RHS
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [fiber_min2 n k hv]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hm : min2 u = v := by
    rw [← fiber_min2 n k hv] at hu
    exact (Finset.mem_filter.mp hu).2
  rw [← h2019_min2 u, hm]
  ring

/-! ### Eq. (32) = Theorem 5.1 at `d = 2` -/

section Reindex

variable {G P : Finset ℕ}

/-- extension by zero from `G` to `P` -/
def extZ (G P : Finset ℕ) (w : G → ℕ) : P → ℕ :=
  fun p => if hp : (p : ℕ) ∈ G then w ⟨p, hp⟩ else 0

theorem prod_extZ {M : Type*} [CommMonoid M] (hGP : G ⊆ P) (F : ℕ → ℕ → M)
    (hF : ∀ p, F p 0 = 1) (w : G → ℕ) :
    ∏ p : P, F p (extZ G P w p) = ∏ r : G, F r (w r) := by
  set W : ℕ → ℕ := fun x => if hx : x ∈ G then w ⟨x, hx⟩ else 0 with hW
  have h1 : ∏ p : P, F p (extZ G P w p) = ∏ x ∈ P, F x (W x) :=
    Finset.prod_coe_sort P (fun x => F x (W x))
  have h2 : ∏ r : G, F r (w r) = ∏ x ∈ G, F x (W x) := by
    rw [← Finset.prod_coe_sort G (fun x => F x (W x))]
    refine Finset.prod_congr rfl fun r _ => ?_
    simp only [hW, dif_pos r.2]
  rw [h1, h2]
  symm
  refine Finset.prod_subset hGP fun x _ hx => ?_
  simp only [hW, dif_neg hx, hF]

theorem sum_extZ (hGP : G ⊆ P) (w : G → ℕ) :
    ∑ p : P, extZ G P w p = ∑ r : G, w r := by
  set W : ℕ → ℕ := fun x => if hx : x ∈ G then w ⟨x, hx⟩ else 0 with hW
  have h1 : ∑ p : P, extZ G P w p = ∑ x ∈ P, W x :=
    Finset.sum_coe_sort P W
  have h2 : ∑ r : G, w r = ∑ x ∈ G, W x := by
    rw [← Finset.sum_coe_sort G W]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hW, dif_pos r.2]
  rw [h1, h2]
  symm
  refine Finset.sum_subset hGP fun x _ hx => ?_
  simp only [hW, dif_neg hx]

end Reindex

theorem rdCoeff_two_eq_coef {p e : ℕ} (he : e ≤ 2) : rdCoeff p e 2 = coef2019 p e := by
  interval_cases e <;> simp [rdCoeff, gaussBinom, coef2019]; ring

theorem eq32RHS_eq_kActiveRHS (n k σ : ℕ) (hn : n ≠ 0) :
    eq32RHS n k σ = kActiveRHS n 2 σ k := by
  set G := (Nat.gcd k n).primeFactors with hG
  set P := n.primeFactors with hP
  have hgn : Nat.gcd k n ≠ 0 := Nat.gcd_ne_zero_right hn
  have hGP : G ⊆ P := Nat.primeFactors_mono (Nat.gcd_dvd_right k n) hn
  -- Step A: rank vectors with support outside `G` contribute nothing
  have hA : kActiveRHS n 2 σ k
      = ∑ v ∈ ((rankVectors n 2).erase 0).filter (fun v => ∀ p : P, (p : ℕ) ∉ G → v p = 0),
          kActiveSummand n 2 σ k v := by
    unfold kActiveRHS
    symm
    refine Finset.sum_filter_of_ne fun v _ hne p hpG => ?_
    by_contra hvp
    apply hne
    unfold kActiveSummand
    rw [if_neg]
    rintro ⟨hdvd, -⟩
    apply hpG
    have hpp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have hph : (p : ℕ) ∣ hVec v := by
      unfold hVec
      exact (dvd_pow_self (p : ℕ) hvp).trans
        (Finset.dvd_prod_of_mem (fun q : P => (q : ℕ) ^ v q) (Finset.mem_univ p))
    have hpk : (p : ℕ) ∣ k := hph.trans hdvd
    have hpn : (p : ℕ) ∣ n := Nat.dvd_of_mem_primeFactors p.2
    exact Nat.mem_primeFactors.mpr ⟨hpp, Nat.dvd_gcd hpk hpn, hgn⟩
  rw [hA]
  unfold eq32RHS idxTwo2019
  refine Finset.sum_nbij' (extZ G P) (fun v r => v ⟨r, hGP r.2⟩) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro w hw
    simp only [Finset.mem_erase, Fintype.mem_piFinset, Finset.mem_range] at hw
    simp only [Finset.mem_filter, Finset.mem_erase, rankVectors, Fintype.mem_piFinset,
      Finset.mem_range]
    refine ⟨⟨?_, fun p => ?_⟩, fun p hp => ?_⟩
    · intro h0
      apply hw.1
      funext r
      have := congrFun h0 ⟨r, hGP r.2⟩
      simp only [extZ, Pi.zero_apply] at this
      simpa using this
    · unfold extZ
      split_ifs with h
      · have := hw.2 ⟨p, h⟩; omega
      · omega
    · simp only [extZ, dif_neg hp]
  · -- backward membership
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_erase, rankVectors, Fintype.mem_piFinset,
      Finset.mem_range] at hv
    simp only [Finset.mem_erase, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨?_, fun r => hv.1.2 _⟩
    intro h0
    apply hv.1.1
    funext p
    by_cases hp : (p : ℕ) ∈ G
    · have := congrFun h0 ⟨p, hp⟩
      simpa using this
    · simpa using hv.2 p hp
  · -- left inverse
    intro w _
    funext r
    simp [extZ]
  · -- right inverse
    intro v hv
    simp only [Finset.mem_filter] at hv
    funext p
    unfold extZ
    split_ifs with hp
    · rfl
    · exact (hv.2 p hp).symm
  · -- values
    intro w hw
    have hw2 : ∀ r, w r ≤ 2 := fun r => by
      have := Fintype.mem_piFinset.mp (Finset.mem_of_mem_erase hw) r
      rw [Finset.mem_range] at this
      omega
    rw [kActiveSummand_eq_convTerm]
    have habs : absVec (extZ G P w) = absVec w := sum_extZ hGP w
    have hh : hVec (extZ G P w) = h2019 w := by
      unfold hVec h2019
      rw [prod_extZ hGP (fun p e => p ^ e) (fun p => pow_zero p) w]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [min_eq_left (hw2 r)]
    have hc : ∏ p : P, (rdCoeff p (extZ G P w p) 2 : ℤ) = ∏ r : G, (coef2019 r (w r) : ℤ) := by
      rw [prod_extZ hGP (fun p e => (rdCoeff p e 2 : ℤ)) (fun p => by simp [rdCoeff, gaussBinom]) w]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [rdCoeff_two_eq_coef (hw2 r)]
    rw [habs, hh, hc]
    ring

/-! ### Index sets over a single prime -/

theorem sum_idxTwo_singleton {g q : ℕ} (hq : g.primeFactors = {q})
    (F : (g.primeFactors → ℕ) → ℤ) :
    ∑ v ∈ (Fintype.piFinset fun _ : g.primeFactors => Finset.range 3).erase 0, F v
      = F (fun _ => 1) + F (fun _ => 2) := by
  have hqmem : q ∈ g.primeFactors := by rw [hq]; exact Finset.mem_singleton_self q
  set q' : g.primeFactors := ⟨q, hqmem⟩
  have hx : ∀ x : ℕ, x ∈ g.primeFactors → x = q := fun x hxg => by
    rw [hq] at hxg; exact Finset.mem_singleton.mp hxg
  have hall : ∀ r : g.primeFactors, r = q' := fun r => Subtype.ext (hx r.1 r.2)
  have hconst : ∀ v : g.primeFactors → ℕ, v = fun _ => v q' := by
    intro v; funext r; rw [hall r]
  rw [← Finset.sum_pair (show (1 : ℕ) ≠ 2 by omega) (f := fun x => F (fun _ => x))]
  refine Finset.sum_nbij' (fun v => v q') (fun x _ => x) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_erase, Fintype.mem_piFinset, Finset.mem_range] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have h3 := hv.2 q'
    have h0 : v q' ≠ 0 := by
      intro h
      apply hv.1
      rw [hconst v, h]
      rfl
    omega
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_erase, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨?_, fun _ => by omega⟩
    intro h
    have := congrFun h q'
    simp only [Pi.zero_apply] at this
    omega
  · intro v _
    exact (hconst v).symm
  · intro x _
    rfl
  · intro v _
    exact congrArg F (hconst v)

theorem absVec_const_singleton {g q : ℕ} (hq : g.primeFactors = {q}) (c : ℕ) :
    absVec (fun _ : g.primeFactors => c) = c := by
  unfold absVec
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hq, Finset.card_singleton,
    smul_eq_mul, one_mul]

theorem h2019_const_singleton {g q : ℕ} (hq : g.primeFactors = {q}) (c : ℕ) :
    h2019 (fun _ : g.primeFactors => c) = q ^ min c 2 := by
  unfold h2019
  rw [Finset.prod_coe_sort g.primeFactors (fun r => r ^ min c 2), hq, Finset.prod_singleton]

theorem prod_singleton_coe {g q : ℕ} (hq : g.primeFactors = {q}) (F : ℕ → ℤ) :
    ∏ r : g.primeFactors, F r = F q := by
  rw [Finset.prod_coe_sort g.primeFactors F, hq, Finset.prod_singleton]

end ShiftSym.P05
