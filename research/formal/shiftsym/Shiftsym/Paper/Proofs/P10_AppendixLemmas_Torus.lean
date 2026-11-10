/-
Phase H, group 10 (Appendix A) — proof helpers, part 4 ("Torus").

The rectangular torus `T_j = (Z/n)^{d−j} × (Z/(n/p))^j` (`p = p_{m+1}`) as the quotient of
`Z_n^d` by the kernel `K` of the explicit projection `proj` (`|K| = p^j`):
* `rectTorus_proved'`  — `N_j` cells, `p_i ∣ n`, `p_i ∣ n/p`, `p_i`-torsion `≃+ F_{p_i}^d`;
* `fixedByLow_iff`, `card_fixedByLow` — configurations of `T_j` fixed by an order-`p_i`
  cyclic subgroup (`i < m`) ↔ configurations of `Z_n^d` in `Fix(K) ∩ ⋃_C Fix(C)`;
* `unionInterpretation_proved'` — the union interpretation (with the core lemma);
* `lemA1Sandwich_proved'`, `lemA1UnionBound_proved'` — Lemma A.1 (counting + Boole).

No `sorry`; only the standard axioms.
-/
import Shiftsym.Paper.Proofs.P10_AppendixLemmas_Core

open scoped Classical

namespace ShiftSym.P10

open Finset Module Function

variable {n d P j : ℕ}

/-- The quotient map `Z_n^d → T_j = (Z/n)^{d−j} × (Z/(n/P))^j`. -/
def proj (n d P j : ℕ) (hPn : P ∣ n) (hj : j ≤ d) : Lat n d →+ RectTorus n d P j where
  toFun u := (fun i => u ⟨i, by omega⟩,
    fun i => ZMod.castHom (Nat.div_dvd_of_dvd hPn) (ZMod (n / P)) (u ⟨d - j + i, by omega⟩))
  map_zero' := by
    ext i
    · rfl
    · simp
  map_add' u v := by
    ext i
    · rfl
    · exact map_add _ _ _

theorem proj_surjective (hn : n ≠ 0) (hPn : P ∣ n) (hj : j ≤ d) :
    Function.Surjective (proj n d P j hPn hj) := by
  have hnP : n / P ≠ 0 := by
    intro h
    rcases Nat.div_eq_zero_iff.mp h with h0 | hlt
    · subst h0; simp at hPn; exact hn hPn
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hPn) (not_le.mpr hlt)
  have : NeZero (n / P) := ⟨hnP⟩
  rintro ⟨a, b⟩
  refine ⟨fun x => if h : (x : ℕ) < d - j then a ⟨x, h⟩
    else (((b ⟨x - (d - j), by omega⟩).val : ℕ) : ZMod n), ?_⟩
  ext i
  · simp [proj]
  · have h1 : ¬ (d - j + (i : ℕ) < d - j) := by omega
    simp only [proj, AddMonoidHom.coe_mk, ZeroHom.coe_mk, dif_neg h1]
    rw [map_natCast]
    have h2 : (⟨d - j + (i : ℕ) - (d - j), by omega⟩ : Fin j) = i := by
      apply Fin.ext; simp
    rw [h2, ZMod.natCast_zmod_val]

theorem card_rectTorus (hn : n ≠ 0) (hPn : P ∣ n) :
    Nat.card (RectTorus n d P j) = n ^ (d - j) * (n / P) ^ j := by
  have hnP : n / P ≠ 0 := by
    intro h
    rcases Nat.div_eq_zero_iff.mp h with h0 | hlt
    · subst h0; simp at hPn; exact hn hPn
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hPn) (not_le.mpr hlt)
  have : NeZero (n / P) := ⟨hnP⟩
  have : NeZero n := ⟨hn⟩
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fun]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- The kernel of the quotient map has order `P^j`. -/
theorem card_ker_proj (hn : n ≠ 0) (hPn : P ∣ n) (hj : j ≤ d) :
    Nat.card (proj n d P j hPn hj).ker = P ^ j := by
  have : NeZero n := ⟨hn⟩
  have hP0 : P ≠ 0 := by rintro rfl; simp at hPn; exact hn hPn
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (proj n d P j hPn hj).ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _
    (proj_surjective hn hPn hj)).toEquiv, card_rectTorus hn hPn, card_lat] at h1
  have h2 : n ^ d = n ^ (d - j) * (n / P) ^ j * P ^ j := by
    rw [mul_assoc, ← mul_pow, Nat.div_mul_cancel hPn, ← pow_add]
    congr 1; omega
  rw [h2] at h1
  have hne : n ^ (d - j) * (n / P) ^ j ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ hn) (pow_ne_zero _ ?_)
    intro h
    rcases Nat.div_eq_zero_iff.mp h with h0 | hlt
    · exact hP0 h0
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hPn) (not_le.mpr hlt)
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h1).symm


theorem div_ne_zero' (hn : n ≠ 0) (hPn : P ∣ n) : n / P ≠ 0 := by
  intro h
  rcases Nat.div_eq_zero_iff.mp h with h0 | hlt
  · subst h0; simp at hPn; exact hn hPn
  · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hPn) (not_le.mpr hlt)

theorem coprime_Pj {m i : ℕ} (hmk : m < kOf n) (hi : i < m) (j : ℕ) :
    Nat.Coprime (primeAt n m ^ j) (primeAt n i) := by
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_primes (primeAt_prime hmk) (primeAt_prime (by omega))]
  intro h
  exact absurd (primeAt_inj hmk (by omega) h) (by omega)

theorem ker_le_torsion [NeZero n] (hPn : P ∣ n) (hj : j ≤ d) :
    (proj n d P j hPn hj).ker ≤ latTorsion n d (P ^ j) := by
  have h := le_latTorsion_card (proj n d P j hPn hj).ker
  rwa [card_ker_proj (NeZero.ne n) hPn hj] at h

theorem nsmul_prime_eq_zero {G : Type*} [AddCommGroup G] {H : AddSubgroup G} [Finite H]
    {p : ℕ} (hcard : Nat.card H = p) {x : G} (hx : x ∈ H) : p • x = 0 := by
  rw [← hcard]
  exact (addOrderOf_dvd_iff_nsmul_eq_zero).mp (AddSubgroup.addOrderOf_dvd_natCard H hx)

theorem addOrderOf_eq_prime' {G : Type*} [AddCommGroup G] {p : ℕ} (hp : p.Prime) {x : G}
    (hx : p • x = 0) (hx0 : x ≠ 0) : addOrderOf x = p := by
  rcases hp.eq_one_or_self_of_dvd _ ((addOrderOf_dvd_iff_nsmul_eq_zero).mpr hx) with h | h
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hx0
  · exact h

/-- **FL**: a configuration of `T_j` is fixed by an order-`p_i` cyclic subgroup (`i < m`) iff
its pull-back to `Z_n^d` lies in the union of the fixed sets of the order-`p_i` subgroups. -/
theorem fixedByLow_iff [NeZero n] {m : ℕ} (hmk : m < kOf n) (hj : j ≤ d) (σ : ℕ)
    (s : RectTorus n d (primeAt n m) j → Fin σ) :
    FixedByLowPrime n d σ m j s ↔
      (s ∘ proj n d (primeAt n m) j (primeAt_dvd hmk) hj)
        ∈ (lowSubs n d m).biUnion (fixedByA (Fin σ)) := by
  set π := proj n d (primeAt n m) j (primeAt_dvd hmk) hj with hπ
  have hsurj : Function.Surjective π := proj_surjective (NeZero.ne n) _ hj
  have : NeZero (n / primeAt n m) := ⟨div_ne_zero' (NeZero.ne n) (primeAt_dvd hmk)⟩
  constructor
  · rintro ⟨i, hi, H, _, hcard, hinv⟩
    have hpi : (primeAt n i).Prime := primeAt_prime (by omega)
    obtain ⟨h', hh'H, hh'0⟩ : ∃ h' ∈ H, h' ≠ 0 :=
      (AddSubgroup.bot_or_exists_ne_zero H).resolve_left (fun hb => by
        rw [hb, AddSubgroup.card_bot] at hcard; exact hpi.one_lt.ne hcard)
    have hpih' : primeAt n i • h' = 0 := nsmul_prime_eq_zero hcard hh'H
    obtain ⟨u0, hu0⟩ := hsurj h'
    obtain ⟨a, b, hab⟩ : IsCoprime ((primeAt n m ^ j : ℕ) : ℤ) (primeAt n i : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (coprime_Pj hmk hi j)
    set u : Lat n d := (a * ((primeAt n m ^ j : ℕ) : ℤ)) • u0 with hu
    have hpu : π u = h' := by
      rw [hu, map_zsmul, hu0]
      have e1 : a * ((primeAt n m ^ j : ℕ) : ℤ) = 1 - b * (primeAt n i : ℤ) := by linarith
      rw [e1, sub_smul, one_smul, mul_smul, natCast_zsmul, hpih', smul_zero, sub_zero]
    have hu0K : primeAt n i • u0 ∈ π.ker := by
      rw [AddMonoidHom.mem_ker, map_nsmul, hu0, hpih']
    have hK0 : (primeAt n m ^ j) • (primeAt n i • u0) = 0 :=
      (mem_latTorsion.mp (ker_le_torsion _ hj hu0K))
    have hpiu : primeAt n i • u = 0 := by
      rw [← natCast_zsmul, hu, smul_smul,
        show (primeAt n i : ℤ) * (a * ((primeAt n m ^ j : ℕ) : ℤ))
          = a * (((primeAt n m ^ j : ℕ) : ℤ) * (primeAt n i : ℤ)) by ring,
        mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hK0, smul_zero]
    have hu_ne : u ≠ 0 := fun h => hh'0 (by rw [← hpu, h, map_zero])
    have hord := addOrderOf_eq_prime' hpi hpiu hu_ne
    refine Finset.mem_biUnion.mpr ⟨AddSubgroup.zmultiples u, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, i, hi, by rw [Nat.card_zmultiples, hord]⟩
      rw [mem_primeOrderSubs, Nat.card_zmultiples, hord]; exact hpi
    · rw [mem_fixedByA]
      apply AddSubgroup.zmultiples_le.mpr
      rw [mem_stab]
      funext x
      simp only [shift_apply, comp_apply, map_add, hpu]
      exact hinv h' hh'H (π x)
  · intro hmem
    obtain ⟨C, hC, hfix⟩ := Finset.mem_biUnion.mp hmem
    obtain ⟨hCP, i, hi, hCi⟩ := Finset.mem_filter.mp hC
    have hpi : (primeAt n i).Prime := primeAt_prime (by omega)
    obtain ⟨u, huC, hu0⟩ : ∃ u ∈ C, u ≠ 0 :=
      (AddSubgroup.bot_or_exists_ne_zero C).resolve_left (fun hb => by
        rw [hb, AddSubgroup.card_bot] at hCi; exact hpi.one_lt.ne hCi)
    have hpiu : primeAt n i • u = 0 := nsmul_prime_eq_zero hCi huC
    have hpu0 : π u ≠ 0 := by
      intro h
      have h1 : u ∈ latTorsion n d (primeAt n m ^ j) := ker_le_torsion _ hj h
      have h2 : u ∈ latTorsion n d (primeAt n i) := le_torsion_of_card_prime hCi huC
      have h3 : u ∈ latTorsion n d (primeAt n m ^ j) ⊓ latTorsion n d (primeAt n i) := ⟨h1, h2⟩
      rw [latTorsion_inf_coprime (coprime_Pj hmk hi j)] at h3
      exact hu0 h3
    have hpiu' : primeAt n i • π u = 0 := by rw [← map_nsmul, hpiu, map_zero]
    have hord := addOrderOf_eq_prime' hpi hpiu' hpu0
    refine ⟨i, hi, AddSubgroup.zmultiples (π u), inferInstance,
      by rw [Nat.card_zmultiples, hord], ?_⟩
    intro h hh y
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hh
    obtain ⟨x, rfl⟩ := hsurj y
    have hstab : k • u ∈ stab (s ∘ π) := (mem_fixedByA.mp hfix) (C.zsmul_mem huC k)
    have := congrFun (mem_stab.mp hstab) x
    rw [shift_apply, comp_apply, comp_apply, map_add, map_zsmul] at this
    exact this

/-- Configurations of `T_j` fixed by an order-`p_i` cyclic subgroup (`i < m`) are counted on
`Z_n^d` by `Fix(ker π) ∩ ⋃ Fix(C)`. -/
theorem card_fixedByLow [NeZero n] {m : ℕ} (hmk : m < kOf n) (hj : j ≤ d) (σ : ℕ) :
    Nat.card {s : RectTorus n d (primeAt n m) j → Fin σ // FixedByLowPrime n d σ m j s}
      = (fixedByA (Fin σ) (proj n d (primeAt n m) j (primeAt_dvd hmk) hj).ker
          ∩ (lowSubs n d m).biUnion (fixedByA (Fin σ))).card := by
  set π := proj n d (primeAt n m) j (primeAt_dvd hmk) hj with hπ
  have hsurj : Function.Surjective π := proj_surjective (NeZero.ne n) _ hj
  have hcomp : ∀ s : RectTorus n d (primeAt n m) j → Fin σ, s ∘ π ∈ fixedByA (Fin σ) π.ker := by
    intro s
    rw [mem_fixedByA]
    intro k hk
    rw [mem_stab]
    funext x
    simp only [shift_apply, comp_apply, map_add, (AddMonoidHom.mem_ker).mp hk, add_zero]
  have hlift : ∀ t : Config n d (Fin σ), t ∈ fixedByA (Fin σ) π.ker →
      (fun y => t (surjInv hsurj y)) ∘ π = t := by
    intro t ht
    funext x
    have hk : surjInv hsurj (π x) - x ∈ π.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, surjInv_eq hsurj, sub_self]
    have := congrFun (mem_stab.mp ((mem_fixedByA.mp ht) hk)) x
    simp only [shift_apply, add_sub_cancel] at this
    exact this
  let e : {s : RectTorus n d (primeAt n m) j → Fin σ // FixedByLowPrime n d σ m j s} ≃
      {t // t ∈ fixedByA (Fin σ) π.ker ∩ (lowSubs n d m).biUnion (fixedByA (Fin σ))} :=
    { toFun := fun s => ⟨s.1 ∘ π, Finset.mem_inter.mpr
        ⟨hcomp s.1, (fixedByLow_iff hmk hj σ s.1).mp s.2⟩⟩
      invFun := fun t => ⟨fun y => t.1 (surjInv hsurj y), (fixedByLow_iff hmk hj σ _).mpr (by
        rw [← hπ, hlift t.1 (Finset.mem_inter.mp t.2).1]; exact (Finset.mem_inter.mp t.2).2)⟩
      left_inv := fun s => Subtype.ext (funext fun y => by simp [surjInv_eq hsurj])
      right_inv := fun t => Subtype.ext (hlift t.1 (Finset.mem_inter.mp t.2).1) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]


/-! ### The rectangular torus: cells and torsion -/

/-- `p`-torsion of a product is the product of the `p`-torsions (here for `T_j`). -/
def torsionProdEquiv (A B : Type*) [AddCommGroup A] [AddCommGroup B] (q : ℕ) :
    ↥(AddSubgroup.torsionBy (A × B) (q : ℤ)) ≃+
      ↥(AddSubgroup.torsionBy A (q : ℤ)) × ↥(AddSubgroup.torsionBy B (q : ℤ)) where
  toFun x := (⟨x.1.1, by
      have h := AddSubgroup.torsionBy.nsmul_iff.mp x.2
      exact AddSubgroup.torsionBy.nsmul_iff.mpr (by simpa using congrArg Prod.fst h)⟩,
    ⟨x.1.2, by
      have h := AddSubgroup.torsionBy.nsmul_iff.mp x.2
      exact AddSubgroup.torsionBy.nsmul_iff.mpr (by simpa using congrArg Prod.snd h)⟩)
  invFun y := ⟨(y.1.1, y.2.1), by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    have h1 := AddSubgroup.torsionBy.nsmul_iff.mp y.1.2
    have h2 := AddSubgroup.torsionBy.nsmul_iff.mp y.2.2
    ext <;> simp [h1, h2]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- `torsionBy (Z/n)^e q` is the certified `latTorsion`. -/
def torsionLatEquiv (n e q : ℕ) :
    ↥(AddSubgroup.torsionBy (Lat n e) (q : ℤ)) ≃+ ↥(latTorsion n e q) where
  toFun x := ⟨x.1, mem_latTorsion.mpr (AddSubgroup.torsionBy.nsmul_iff.mp x.2)⟩
  invFun y := ⟨y.1, AddSubgroup.torsionBy.nsmul_iff.mpr (mem_latTorsion.mp y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem torsion_rect_iso {q : ℕ} [NeZero n] [NeZero q] (hP : n / P ≠ 0) (hj : j ≤ d)
    (hqn : q ∣ n) (hqnP : q ∣ n / P) :
    Nonempty (↥(AddSubgroup.torsionBy (RectTorus n d P j) (q : ℤ)) ≃+ (Fin d → ZMod q)) := by
  have : NeZero (n / P) := ⟨hP⟩
  let e1 := torsionProdEquiv (Fin (d - j) → ZMod n) (Fin j → ZMod (n / P)) q
  let e2 : ↥(AddSubgroup.torsionBy (Fin (d - j) → ZMod n) (q : ℤ)) ≃+ (Fin (d - j) → ZMod q) :=
    (torsionLatEquiv n (d - j) q).trans (latTorsionEquiv hqn)
  let e3 : ↥(AddSubgroup.torsionBy (Fin j → ZMod (n / P)) (q : ℤ)) ≃+ (Fin j → ZMod q) :=
    (torsionLatEquiv (n / P) j q).trans (latTorsionEquiv hqnP)
  let e4 : ((Fin (d - j) → ZMod q) × (Fin j → ZMod q)) ≃+ (Fin d → ZMod q) :=
    (RingEquiv.sumArrowEquivProdArrow (α := Fin (d - j)) (β := Fin j) (R := ZMod q)).symm.toAddEquiv.trans
      (RingEquiv.piCongrLeft (fun _ => ZMod q)
        (finSumFinEquiv.trans (finCongr (by omega)))).toAddEquiv
  exact ⟨e1.trans ((e2.prodCongr e3).trans e4)⟩

theorem rectTorus_proved' : rectTorusStatement := by
  intro n d m j hn hd hm1 hmk hj1 hjd
  have hn0 : n ≠ 0 := by omega
  have : NeZero n := ⟨hn0⟩
  set P := primeAt n m with hPdef
  have hPn : P ∣ n := primeAt_dvd hmk
  have hP : P.Prime := primeAt_prime hmk
  refine ⟨?_, fun i hi => ?_⟩
  · rw [card_rectTorus hn0 hPn, Nj]
    push_cast
    rw [Nat.cast_div hPn (by exact_mod_cast hP.ne_zero), div_pow]
    have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne_zero
    have e : (n : ℝ) ^ d = (n : ℝ) ^ (d - j) * (n : ℝ) ^ j := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    field_simp
  · have hpi := primeAt_prime (n := n) (by omega : i < kOf n)
    have hqn : primeAt n i ∣ n := primeAt_dvd (by omega)
    have hcop : Nat.Coprime (primeAt n i) P := by
      rw [Nat.coprime_primes hpi hP]
      intro h; exact absurd (primeAt_inj (by omega) hmk h) (by omega)
    have hqnP : primeAt n i ∣ n / P := by
      apply hcop.dvd_of_dvd_mul_right
      rw [Nat.div_mul_cancel hPn]; exact hqn
    have : NeZero (primeAt n i) := ⟨hpi.ne_zero⟩
    exact ⟨hqn, hqnP, torsion_rect_iso (div_ne_zero' hn0 hPn) hjd hqn hqnP⟩


/-! ### Union interpretation and Lemma A.1 -/

theorem coprime_card_ker [NeZero n] {m : ℕ} (hmk : m < kOf n) (hj : j ≤ d) :
    Nat.Coprime (Nat.card (proj n d (primeAt n m) j (primeAt_dvd hmk) hj).ker) (primeProd n m) := by
  rw [card_ker_proj (NeZero.ne n) _ hj]
  unfold primeProd
  apply Nat.Coprime.prod_right
  intro i hi
  exact coprime_Pj hmk (Finset.mem_range.mp hi) j

theorem Pj_mul_dvd {m : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hm1 : 1 ≤ m) (hmk : m < kOf n)
    (hj1 : 1 ≤ j) (hjd : j ≤ d) (v : Fin m → Fin (d + 1)) :
    primeAt n m ^ j * ∏ i : Fin m, primeAt n i ^ ((v i : Fin (d + 1)) : ℕ) ∣ n ^ d := by
  obtain ⟨h1, -, h3⟩ := exponentIntegrality_proved' n d m j hn hd hm1 hmk hj1 hjd
  have := Nat.mul_dvd_mul_left (primeAt n m ^ j) (h3 v)
  rwa [Nat.mul_div_cancel' h1] at this

/-- `q^m(p^{-j})` is the number of configurations of `Z_n^d` fixed by `ker π` and by some
order-`p_i` subgroup, `i < m`. -/
theorem qTrunc_P_eq_card [NeZero n] {m : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hm1 : 1 ≤ m)
    (hmk : m < kOf n) (hj1 : 1 ≤ j) (hjd : j ≤ d) (σ : ℕ) :
    qTrunc n d σ m ((primeAt n m : ℝ) ^ (-(j : ℤ)))
      = ((fixedByA (Fin σ) (proj n d (primeAt n m) j (primeAt_dvd hmk) hjd).ker
          ∩ (lowSubs n d m).biUnion (fixedByA (Fin σ))).card : ℝ) := by
  have hcore := core_card (d := d) (le_of_lt hmk) σ _ (coprime_card_ker hmk hjd)
  rw [card_ker_proj (NeZero.ne n) _ hjd] at hcore
  have hbr := qTruncZBridge_proved' n d σ m (primeAt n m ^ j) hn (le_of_lt hmk)
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (primeAt_prime hmk).ne_zero))
    (Pj_mul_dvd hn hd hm1 hmk hj1 hjd)
  have hc : (primeAt n m : ℝ) ^ (-(j : ℤ)) = (((primeAt n m ^ j : ℕ) : ℝ))⁻¹ := by
    rw [zpow_neg, zpow_natCast]; push_cast; rfl
  rw [hc, hbr, ← hcore]
  push_cast
  rfl

theorem unionInterpretation_proved' : unionInterpretationStatement := by
  intro n d σ m j hn hd _ hm1 hmk hj1 hjd
  have : NeZero n := ⟨by omega⟩
  rw [card_fixedByLow hmk hjd σ, qTrunc_P_eq_card hn hd hm1 hmk hj1 hjd σ]

theorem Nj_eq_nat {m : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hm1 : 1 ≤ m) (hmk : m < kOf n)
    (hj1 : 1 ≤ j) (hjd : j ≤ d) :
    Nj n d (primeAt n m) j = ((n ^ d / primeAt n m ^ j : ℕ) : ℝ) := by
  obtain ⟨h1, -, -⟩ := exponentIntegrality_proved' n d m j hn hd hm1 hmk hj1 hjd
  rw [Nj, Nat.cast_div h1 (by exact_mod_cast pow_ne_zero _ (primeAt_prime hmk).ne_zero)]
  push_cast; rfl

theorem lemA1Sandwich_proved' : lemA1SandwichStatement := by
  intro n d σ m j hn hd _ hm1 hmk hj1 hjd
  have : NeZero n := ⟨by omega⟩
  rw [qTrunc_P_eq_card hn hd hm1 hmk hj1 hjd σ]
  refine ⟨Nat.cast_nonneg _, ?_⟩
  rw [Nj_eq_nat hn hd hm1 hmk hj1 hjd, Real.rpow_natCast]
  have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := fixedByA (Fin σ)
    (proj n d (primeAt n m) j (primeAt_dvd hmk) hjd).ker)
    (s₂ := (lowSubs n d m).biUnion (fixedByA (Fin σ))))
  rw [card_fixedByA_fin, card_ker_proj (by omega) _ hjd] at hle
  exact_mod_cast hle

/-- The restricted family is the disjoint union of the order-`p_i` families, `i < m`. -/
theorem lowSubs_eq_biUnion [NeZero n] {m : ℕ} :
    lowSubs n d m = (Finset.range m).biUnion (fun i => linesP n d (primeAt n i)) := by
  ext C
  simp only [lowSubs, linesP, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨hC, i, hi, hCi⟩; exact ⟨i, hi, hC, hCi⟩
  · rintro ⟨i, hi, hC, hCi⟩; exact ⟨hC, i, hi, hCi⟩

theorem card_linesP [NeZero n] {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    (linesP n d p).card = gaussBinom p d 1 := by
  rw [← card_orderP_subgroups (d := d) hp hpn, Nat.card_eq_fintype_card, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun C => mem_linesP hp)

theorem lemA1UnionBound_proved' : lemA1UnionBoundStatement := by
  intro n d σ m hn hd _ hm1 hmk
  have : NeZero n := ⟨by omega⟩
  set P := primeAt n m with hPdef
  set K := (proj n d P 1 (primeAt_dvd hmk) hd).ker with hK
  rw [show ((P : ℝ) ^ (-(1 : ℤ))) = (P : ℝ) ^ (-((1 : ℕ) : ℤ)) by norm_num,
    qTrunc_P_eq_card hn hd hm1 hmk le_rfl hd σ]
  have hcardK : Nat.card K = P := by rw [hK, card_ker_proj (by omega) _ hd, pow_one]
  -- Boole's inequality
  have hboole : (fixedByA (Fin σ) K ∩ (lowSubs n d m).biUnion (fixedByA (Fin σ))).card
      ≤ ∑ C ∈ lowSubs n d m, (fixedByA (Fin σ) K ∩ fixedByA (Fin σ) C).card := by
    rw [Finset.inter_biUnion]; exact Finset.card_biUnion_le
  -- each term
  have hterm : ∀ i ∈ Finset.range m, ∀ C ∈ linesP n d (primeAt n i),
      (fixedByA (Fin σ) K ∩ fixedByA (Fin σ) C).card = σ ^ (n ^ d / (P * primeAt n i)) := by
    intro i hi C hC
    have hi' := Finset.mem_range.mp hi
    have hCi : Nat.card C = primeAt n i :=
      (mem_linesP (primeAt_prime (by omega))).mp hC
    rw [card_fix_inter, card_sup_coprime K C (le_latTorsion_card C)
      (by rw [hcardK, hCi]; simpa using coprime_Pj hmk hi' 1), hcardK, hCi]
  have hsum : ∑ C ∈ lowSubs n d m, (fixedByA (Fin σ) K ∩ fixedByA (Fin σ) C).card
      = ∑ i ∈ Finset.range m, gaussBinom (primeAt n i) d 1 * σ ^ (n ^ d / (P * primeAt n i)) := by
    rw [lowSubs_eq_biUnion, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.sum_congr rfl (hterm i hi), Finset.sum_const, smul_eq_mul,
        card_linesP (primeAt_prime (by have := Finset.mem_range.mp hi; omega))
          (primeAt_dvd (by have := Finset.mem_range.mp hi; omega))]
    · intro i hi i' hi' hii'
      rw [Function.onFun, Finset.disjoint_left]
      intro C hC hC'
      have h1 := (mem_linesP (primeAt_prime (by have := Finset.mem_range.mp hi; omega))).mp hC
      have h2 := (mem_linesP (primeAt_prime (by have := Finset.mem_range.mp hi'; omega))).mp hC'
      exact hii' (primeAt_inj (by have := Finset.mem_range.mp hi; omega)
        (by have := Finset.mem_range.mp hi'; omega) (h1.symm.trans h2))
  have hle := hboole.trans hsum.le
  calc ((fixedByA (Fin σ) K ∩ (lowSubs n d m).biUnion (fixedByA (Fin σ))).card : ℝ)
      ≤ ((∑ i ∈ Finset.range m, gaussBinom (primeAt n i) d 1 * σ ^ (n ^ d / (P * primeAt n i)) : ℕ) : ℝ) := by
        exact_mod_cast hle
    _ = ∑ i ∈ Finset.range m, (gaussBinom (primeAt n i) d 1 : ℝ) *
          (σ : ℝ) ^ (Nj n d P 1 / (primeAt n i : ℝ)) := by
        push_cast
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi' := Finset.mem_range.mp hi
        have hpi := primeAt_prime (n := n) (by omega : i < kOf n)
        have hdvd : P * primeAt n i ∣ n ^ d := by
          have hcop : Nat.Coprime P (primeAt n i) := by simpa using coprime_Pj hmk hi' 1
          exact (hcop.mul_dvd_of_dvd_of_dvd (primeAt_dvd hmk) (primeAt_dvd (by omega))).trans
            (dvd_pow_self n (by omega))
        congr 1
        rw [← Real.rpow_natCast]
        congr 1
        rw [Nat.cast_div hdvd (by exact_mod_cast (Nat.mul_ne_zero (primeAt_prime hmk).ne_zero hpi.ne_zero)),
          Nj, pow_one]
        push_cast
        rw [div_div]

end ShiftSym.P10
