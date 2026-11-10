/-
Phase H, group 03 — proofs of the frozen statements of
`Shiftsym/Paper/S03_MobiusCoefficients.lean` (paper §4.1 Lemma 4.1 with
eq. (cr) and its proof-internal claims, Definition 4.2, Table 1, Remark
"Duality").

Route: the paper's own self-contained proof, reusing the certified
development (`Lemmas/MobiusSum.lean`: `sum_spanSum_le`, `spanSum_eq_mobius`,
`alt_sum_le`, `gaussBinom_alt_sum`, `spanSum_rank_classified`;
`Lemmas/GaussCount.lean`: `card_submodule_finrank`,
`card_finrank_submodule_generic`; `Lemmas/Bridge.lean`: the
subgroup/submodule dictionary `ofMod`/`toMod`).

* `f = spanSum` (the frozen `spanJ J` is the lattice join `J.sup id`, and the
  frozen `lines V` is the certified `linesF V`);
* mathlib's `IncidenceAlgebra.mu ℤ ⊥ V` equals `spanSum V` by well-founded
  induction on `V`, since both satisfy `Σ_{⊥ ≤ W ≤ V} = δ_{V,⊥}`
  (`IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne` vs `sum_spanSum_le`);
* eq. (cr): classify the subsets `J` of `lines(𝔽_p^d)` by `span J`
  (`Finset.sum_fiberwise_of_maps_to`), then `spanSum_rank_classified`;
* Gaussian-binomial symmetry for prime `p`: the dual annihilator is a
  bijection between `r`-dimensional subspaces of `V` and
  `(d-r)`-dimensional subspaces of `Dual V` (`dim Dual V = d`), and both
  are counted by the certified Grassmannian count;
* the lattice reading of Duality via `ofMod`/`toMod` (Bridge.lean).
-/
import Shiftsym.Paper.S03_MobiusCoefficients
import Shiftsym.Lemmas.MobiusSum
import Shiftsym.Lemmas.Bridge

open scoped Classical

namespace ShiftSym.P03

open ShiftSym Module

/-! ## Dictionary between the frozen objects and the certified ones -/

theorem spanJ_eq_sup {p d : ℕ} (J : Finset (Submodule (ZMod p) (Fin d → ZMod p))) :
    spanJ J = J.sup id := by
  unfold spanJ
  rw [Submodule.span_iUnion₂]
  simp only [Submodule.span_eq]
  rw [Finset.sup_eq_iSup]
  rfl

theorem le_spanJ {p d : ℕ} {J : Finset (Submodule (ZMod p) (Fin d → ZMod p))}
    {L : Submodule (ZMod p) (Fin d → ZMod p)} (hL : L ∈ J) : L ≤ spanJ J := by
  rw [spanJ_eq_sup]
  exact Finset.le_sup (f := id) hL

theorem lines_eq_linesF {p d : ℕ} [Fact p.Prime]
    (V : Submodule (ZMod p) (Fin d → ZMod p)) : lines V = linesF V := by
  ext L
  simp [lines, mem_linesF]

theorem lines_eq_empty_iff {p d : ℕ} [Fact p.Prime]
    (V : Submodule (ZMod p) (Fin d → ZMod p)) : lines V = ∅ ↔ V = ⊥ := by
  rw [lines_eq_linesF]
  constructor
  · intro h
    by_contra hV
    exact (Finset.nonempty_iff_ne_empty.mp (linesF_nonempty hV)) h
  · rintro rfl
    exact linesF_bot

theorem f_eq_spanSum {p d : ℕ} [Fact p.Prime]
    (V : Submodule (ZMod p) (Fin d → ZMod p)) : signedSpanCount V = spanSum V := by
  unfold signedSpanCount spanSum
  rw [Finset.sum_filter, lines_eq_linesF]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [spanJ_eq_sup]

/-- The partition recursion for `f`. -/
theorem sum_f_le {p d : ℕ} [Fact p.Prime]
    (V : Submodule (ZMod p) (Fin d → ZMod p)) :
    ∑ W ∈ Finset.univ.filter (· ≤ V), signedSpanCount W = if V = ⊥ then 1 else 0 := by
  rw [Finset.sum_congr rfl (fun W _ => f_eq_spanSum W)]
  exact sum_spanSum_le V

theorem filter_le_eq_insert {p d : ℕ} [Fact p.Prime]
    (V : Submodule (ZMod p) (Fin d → ZMod p)) :
    Finset.univ.filter (· ≤ V) = insert V (Finset.univ.filter (· < V)) := by
  ext U
  simp [le_iff_lt_or_eq, or_comm]

theorem notMem_filter_lt {p d : ℕ} [Fact p.Prime]
    (V : Submodule (ZMod p) (Fin d → ZMod p)) :
    V ∉ Finset.univ.filter (· < V) := by
  simp

/-- Mathlib's Möbius function of the subspace lattice equals `spanSum`. -/
theorem mu_eq_spanSum {p d : ℕ} [Fact p.Prime]
    (V : Submodule (ZMod p) (Fin d → ZMod p)) :
    IncidenceAlgebra.mu ℤ (⊥ : Submodule (ZMod p) (Fin d → ZMod p)) V = spanSum V := by
  induction V using WellFoundedLT.induction with
  | _ V IH =>
    have hrec := sum_spanSum_le V
    by_cases hV : V = ⊥
    · subst hV
      simp [spanSum_bot]
    · rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne (Ne.symm hV)]
      have hIco : Finset.Ico (⊥ : Submodule (ZMod p) (Fin d → ZMod p)) V
          = Finset.univ.filter (· < V) := by
        ext U; simp
      rw [hIco, Finset.sum_congr rfl (fun U hU => IH U (Finset.mem_filter.mp hU).2)]
      rw [filter_le_eq_insert, Finset.sum_insert (notMem_filter_lt V), if_neg hV] at hrec
      linarith

/-! ## Lemma 4.1 -/

theorem lemMobiusFEqMu_proved : lemMobiusFEqMuStatement := by
  intro p d hp _ V r _
  have : Fact p.Prime := ⟨hp⟩
  rw [f_eq_spanSum, mu_eq_spanSum]

theorem lemMobiusMuClosedForm_proved : lemMobiusMuClosedFormStatement := by
  intro p d hp _ V r hr
  have : Fact p.Prime := ⟨hp⟩
  rw [mu_eq_spanSum, spanSum_eq_mobius, ZMod.card, hr]

/-- Classification of the subsets of `lines(𝔽_p^d)` by their span. -/
theorem cr_eq_sum_f {p d : ℕ} [Fact p.Prime] (r : ℕ) :
    cr p d r = ∑ V ∈ Finset.univ.filter
        (fun V : Submodule (ZMod p) (Fin d → ZMod p) => finrank (ZMod p) V = r),
        signedSpanCount V := by
  unfold cr signedSpanCount
  symm
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (lines (⊤ : Submodule (ZMod p) (Fin d → ZMod p))).powerset.filter
      (fun J => rkJ J = r))
    (t := Finset.univ.filter
      (fun V : Submodule (ZMod p) (Fin d → ZMod p) => finrank (ZMod p) V = r))
    (g := spanJ) ?maps]
  case maps =>
    intro J hJ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ ⊢
    exact hJ.2
  refine Finset.sum_congr rfl fun V hV => ?_
  have hVr : finrank (ZMod p) V = r := (Finset.mem_filter.mp hV).2
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext J
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hJ, hspan⟩
    refine ⟨⟨fun L hL => ?_, ?_⟩, hspan⟩
    · have h := hJ hL
      simp only [lines, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
      exact ⟨h.1, le_top⟩
    · rw [rkJ, hspan, hVr]
  · rintro ⟨⟨hJ, _⟩, hspan⟩
    refine ⟨fun L hL => ?_, hspan⟩
    have h := hJ hL
    simp only [lines, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact ⟨h.1, hspan ▸ le_spanJ hL⟩

theorem lemMobiusCr_proved : lemMobiusCrStatement := by
  intro p d hp _ r hr
  have : Fact p.Prime := ⟨hp⟩
  rw [cr_eq_sum_f, Finset.sum_congr rfl (fun V _ => f_eq_spanSum V)]
  have hd : finrank (ZMod p) (Fin d → ZMod p) = d := Module.finrank_fin_fun _
  have h := spanSum_rank_classified (K := ZMod p) (V := Fin d → ZMod p)
    (r := r) (by rw [hd]; exact hr)
  rw [ZMod.card, hd] at h
  exact h

theorem lemMobius_proved : lemMobiusStatement :=
  ⟨lemMobiusFEqMu_proved, lemMobiusMuClosedForm_proved, lemMobiusCr_proved⟩

/-! ## Proof-internal claims of Lemma 4.1 -/

theorem lemMobiusProofPartition_proved : lemMobiusProofPartitionStatement := by
  intro p d hp _ V
  have : Fact p.Prime := ⟨hp⟩
  have hiff := lines_eq_empty_iff V
  have hpow : ∑ J ∈ (lines V).powerset, (-1 : ℤ) ^ J.card = if V = ⊥ then 1 else 0 := by
    rw [Finset.sum_powerset_neg_one_pow_card]
    by_cases hV : V = ⊥
    · rw [if_pos hV, if_pos (hiff.mpr hV)]
    · rw [if_neg hV, if_neg (fun h => hV (hiff.mp h))]
  have hzero : (1 - 1 : ℤ) ^ (lines V).card = if V = ⊥ then 1 else 0 := by
    rw [sub_self]
    by_cases hV : V = ⊥
    · rw [if_pos hV, Finset.card_eq_zero.mpr (hiff.mpr hV), pow_zero]
    · rw [if_neg hV, zero_pow]
      rw [Ne, Finset.card_eq_zero]
      exact fun h => hV (hiff.mp h)
  refine ⟨?_, ?_, hzero, ?_⟩
  · rw [sum_f_le, hpow]
  · rw [hpow, hzero]
  · rw [Finset.nonempty_iff_ne_empty, Ne, hiff]

theorem lemMobiusProofQBinom_proved : lemMobiusProofQBinomStatement := by
  intro p _ R
  have hprod : ∏ i ∈ Finset.range R, (1 - (p : ℤ) ^ i) = if R = 0 then 1 else 0 := by
    cases R with
    | zero => simp
    | succ R =>
      rw [if_neg (Nat.succ_ne_zero R)]
      exact Finset.prod_eq_zero (i := 0) (by simp) (by simp)
  refine ⟨?_, hprod⟩
  rw [hprod, ← gaussBinom_alt_sum p R]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem lemMobiusProofClosedRecursion_proved : lemMobiusProofClosedRecursionStatement := by
  intro p d hp _ V
  have : Fact p.Prime := ⟨hp⟩
  have h := alt_sum_le (K := ZMod p) V
  rw [ZMod.card] at h
  rw [h]
  by_cases hV : V = ⊥
  · rw [if_pos hV, if_pos]
    rw [hV, finrank_bot]
  · rw [if_neg hV, if_neg]
    rw [Submodule.finrank_eq_zero]
    exact hV

theorem lemMobiusProofUnique_proved : lemMobiusProofUniqueStatement := by
  intro p d hp _ g hg V
  have : Fact p.Prime := ⟨hp⟩
  induction V using WellFoundedLT.induction with
  | _ V IH =>
    have h1 := hg V
    have h2 := sum_f_le V
    rw [filter_le_eq_insert, Finset.sum_insert (notMem_filter_lt V),
      Finset.sum_congr rfl (fun U hU => IH U (Finset.mem_filter.mp hU).2)] at h1
    rw [filter_le_eq_insert, Finset.sum_insert (notMem_filter_lt V)] at h2
    linarith

theorem lemMobiusProofClassify_proved : lemMobiusProofClassifyStatement := by
  intro p d hp _ r hr
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨cr_eq_sum_f r, card_submodule_finrank hp hr⟩

/-! ## Definition 4.2 and Table 1 -/

/-- The binomial coefficients `C(v,2)` occurring in Definition 4.2 and Table 1. -/
theorem choose_two_vals : Nat.choose 0 2 = 0 ∧ Nat.choose 1 2 = 0 ∧ Nat.choose 2 2 = 1 ∧
    Nat.choose 3 2 = 3 ∧ Nat.choose 4 2 = 6 := by decide

theorem defCoeffZero_proved : defCoeffZeroStatement := by
  intro p d _ _
  simp [rdCoeff, gaussBinom]

theorem defCoeffD2_proved : defCoeffD2Statement := by
  intro p _
  obtain ⟨c0, c1, c2, -, -⟩ := choose_two_vals
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rdCoeff, gaussBinom, c0, c1, c2] <;> ring

theorem defCoeffE19_proved : defCoeffE19Statement := by
  intro p _ v hv
  obtain ⟨c0, c1, c2, -, -⟩ := choose_two_vals
  interval_cases v <;> simp only [rdCoeff, gaussBinom, banda2019E19Coeff, c0, c1, c2,
    if_true, if_false, one_ne_zero, two_ne_zero, OfNat.ofNat_ne_one] <;> ring

theorem defCoeff_proved : defCoeffStatement :=
  ⟨defCoeffZero_proved, defCoeffD2_proved, defCoeffE19_proved⟩

theorem table1Row1_proved : table1Row1Statement := by
  intro p _
  refine ⟨?_, ?_⟩ <;> simp [rdCoeff, gaussBinom]

theorem table1Row2_proved : table1Row2Statement := defCoeffD2_proved

theorem table1Row3_proved : table1Row3Statement := by
  intro p _
  obtain ⟨c0, c1, c2, c3, -⟩ := choose_two_vals
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [rdCoeff, gaussBinom, c0, c1, c2, c3] <;> ring

theorem table1Row4_proved : table1Row4Statement := by
  intro p _
  obtain ⟨c0, c1, c2, c3, c4⟩ := choose_two_vals
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [rdCoeff, gaussBinom, c0, c1, c2, c3, c4] <;> ring

theorem table1_proved : table1Statement :=
  ⟨table1Row1_proved, table1Row2_proved, table1Row3_proved, table1Row4_proved⟩

/-! ## Remark "Duality" -/

section DualCount

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

omit [Fintype K] in
/-- The dual annihilator matches the `r`-dimensional subspaces of `V` with the
`(dim V - r)`-dimensional subspaces of `Dual K V`. -/
theorem card_finrank_eq_card_dual {r : ℕ} (hr : r ≤ finrank K V) :
    Nat.card {W : Submodule K V // finrank K W = r}
      = Nat.card {Φ : Submodule K (Module.Dual K V) // finrank K Φ = finrank K V - r} := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  refine Nat.card_congr
    { toFun := fun W => ⟨W.1.dualAnnihilator, by
        have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W.1
        have h2 := W.2
        omega⟩
      invFun := fun Φ => ⟨Φ.1.dualCoannihilator, by
        have h := Subspace.finrank_add_finrank_dualCoannihilator_eq Φ.1
        have h2 := Φ.2
        omega⟩
      left_inv := fun W => Subtype.ext Subspace.dualAnnihilator_dualCoannihilator_eq
      right_inv := fun Φ => Subtype.ext Subspace.dualCoannihilator_dualAnnihilator_eq }

end DualCount

/-- Gaussian-binomial symmetry `[d r]_p = [d d-r]_p` (`p` prime, `r ≤ d`). -/
theorem gaussBinom_symm_prime {p d r : ℕ} (hp : p.Prime) (hr : r ≤ d) :
    gaussBinom p d r = gaussBinom p d (d - r) := by
  have : Fact p.Prime := ⟨hp⟩
  have hd : finrank (ZMod p) (Fin d → ZMod p) = d := Module.finrank_fin_fun _
  have hdual : finrank (ZMod p) (Module.Dual (ZMod p) (Fin d → ZMod p)) = d := by
    rw [Subspace.dual_finrank_eq, hd]
  have : Finite (Module.Dual (ZMod p) (Fin d → ZMod p)) := Module.finite_of_finite (ZMod p)
  have h1 := card_finrank_eq_card_dual (K := ZMod p) (V := Fin d → ZMod p) (r := r)
    (by rw [hd]; exact hr)
  have h2 := card_finrank_submodule_generic (K := ZMod p)
    (V := Module.Dual (ZMod p) (Fin d → ZMod p)) (r := d - r)
    (by rw [hdual]; exact Nat.sub_le d r)
  rw [card_submodule_finrank hp hr, hd, h2, ZMod.card, hdual] at h1
  exact h1

theorem dualityGauss_proved : dualityGaussStatement := by
  intro p d r hp _ hr
  exact gaussBinom_symm_prime hp hr

theorem dualitySubspace_proved : dualitySubspaceStatement := by
  intro p d r hp _ hr
  rw [card_submodule_finrank hp hr, card_submodule_finrank hp (Nat.sub_le d r)]
  exact gaussBinom_symm_prime hp hr

/-- Subgroups of `(ℤ/nℤ)^d` inside the `p`-torsion with `p^r` elements
correspond to `r`-dimensional subspaces of `𝔽_p^d` (`ofMod`/`toMod`). -/
theorem card_torsion_subgroups {n d p r : ℕ} [NeZero n] [Fact p.Prime] (hpn : p ∣ n) :
    Nat.card {H : AddSubgroup (Lat n d) // (∀ x ∈ H, p • x = 0) ∧ Nat.card H = p ^ r}
      = Nat.card {U : Submodule (ZMod p) (Fin d → ZMod p) // finrank (ZMod p) U = r} := by
  have hp : p.Prime := Fact.out
  have hle : ∀ H : AddSubgroup (Lat n d),
      (∀ x ∈ H, p • x = 0) ↔ H ≤ latTorsion n d p := fun H =>
    ⟨fun h _ hx => mem_latTorsion.mpr (h _ hx), fun h _ hx => mem_latTorsion.mp (h hx)⟩
  refine Nat.card_congr
    { toFun := fun H => ⟨toMod hpn H.1, by
        have h1 := card_toMod hpn ((hle H.1).mp H.2.1)
        rw [H.2.2, card_submodule_pow] at h1
        exact Nat.pow_right_injective hp.two_le h1⟩
      invFun := fun U => ⟨ofMod hpn U.1, by
        refine ⟨(hle _).mpr (ofMod_le_torsion hpn U.1), ?_⟩
        rw [card_ofMod, card_submodule_pow, U.2]⟩
      left_inv := fun H => Subtype.ext (ofMod_toMod hpn ((hle H.1).mp H.2.1))
      right_inv := fun U => Subtype.ext (toMod_ofMod hpn U.1) }

theorem dualityLattice_proved : dualityLatticeStatement := by
  intro n d p r hn _ hp hpn hr
  have : NeZero n := ⟨by omega⟩
  have : Fact p.Prime := ⟨hp⟩
  rw [card_torsion_subgroups hpn, card_torsion_subgroups hpn,
    card_submodule_finrank hp hr, card_submodule_finrank hp (Nat.sub_le d r)]
  exact gaussBinom_symm_prime hp hr

theorem duality_proved : dualityStatement :=
  ⟨dualityGauss_proved, dualitySubspace_proved, dualityLattice_proved⟩

end ShiftSym.P03
