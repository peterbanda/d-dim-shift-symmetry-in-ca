/-
Grassmannian count (Phase C item 5, the paper's Gaussian-binomial
interface): the `r`-dimensional subspaces of a `d`-dimensional space over
a field with `q` elements number `[d r]_q = gaussBinom q d r`.

Route (no Grassmannian in mathlib): fiber the linearly independent
`r`-tuples (counted by mathlib's `card_linearIndependent`) over their
span; each fiber is the set of bases of one `r`-dimensional subspace,
counted by the same theorem at dimension `r`. The quotient identity
`[d r]_q · ∏(q^r − q^i) = ∏(q^d − q^i)` is proved in ℤ by double
induction (closed by `linear_combination`) and transferred to ℕ.
-/
import Shiftsym.Statement

namespace ShiftSym

open Module Submodule

/-! ### The product identity -/

theorem gaussBinom_eq_zero_of_lt : ∀ {d r : ℕ}, d < r → ∀ {q : ℕ},
    gaussBinom q d r = 0
  | 0, _ + 1, _, _ => rfl
  | d + 1, r + 1, h, q => by
    have hdr : d < r := Nat.lt_of_succ_lt_succ h
    have h1 : gaussBinom q d r = 0 := gaussBinom_eq_zero_of_lt hdr
    have h2 : gaussBinom q d (r + 1) = 0 :=
      gaussBinom_eq_zero_of_lt (Nat.lt_succ_of_lt hdr)
    simp [gaussBinom, h1, h2]

private theorem prod_split (x : ℤ) (e r : ℕ) :
    ∏ i : Fin (r + 1), (x ^ (e + 1) - x ^ (i : ℕ))
      = (x ^ (e + 1) - 1) * x ^ r * ∏ i : Fin r, (x ^ e - x ^ (i : ℕ)) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, pow_zero, Fin.val_succ]
  have key : ∀ i : Fin r, x ^ (e + 1) - x ^ ((i : ℕ) + 1)
      = x * (x ^ e - x ^ (i : ℕ)) := by
    intro i
    rw [pow_succ, pow_succ]
    ring
  rw [Finset.prod_congr rfl (fun i _ => key i), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem gaussBinom_mul_prod_int (q : ℕ) : ∀ d r : ℕ,
    (gaussBinom q d r : ℤ) * ∏ i : Fin r, ((q : ℤ) ^ r - (q : ℤ) ^ (i : ℕ))
      = ∏ i : Fin r, ((q : ℤ) ^ d - (q : ℤ) ^ (i : ℕ)) := by
  intro d
  induction d with
  | zero =>
    intro r
    cases r with
    | zero => simp [gaussBinom]
    | succ r =>
      have h0 : gaussBinom q 0 (r + 1) = 0 := rfl
      rw [h0, Nat.cast_zero, zero_mul]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (r + 1)))
      simp
  | succ d ih =>
    intro r
    cases r with
    | zero => simp [gaussBinom]
    | succ r =>
      have ih1 := ih r
      have ih2 := ih (r + 1)
      have hgN : gaussBinom q (d + 1) (r + 1)
          = gaussBinom q d r + q ^ (r + 1) * gaussBinom q d (r + 1) := by
        simp [gaussBinom]
      rw [hgN, prod_split ((q : ℤ)) r r, prod_split ((q : ℤ)) d r]
      rw [prod_split ((q : ℤ)) r r] at ih2
      have hsplit : (∏ i : Fin (r + 1), ((q : ℤ) ^ d - (q : ℤ) ^ (i : ℕ)))
          = (∏ i : Fin r, ((q : ℤ) ^ d - (q : ℤ) ^ (i : ℕ)))
            * ((q : ℤ) ^ d - (q : ℤ) ^ r) := by
        rw [Fin.prod_univ_castSucc]
        simp
      rw [hsplit] at ih2
      push_cast
      linear_combination (((q : ℤ) ^ (r + 1) - 1) * (q : ℤ) ^ r) * ih1
        + (q : ℤ) ^ (r + 1) * ih2

/-- The counting identity in ℕ: `[d r]_q · ∏_{i<r}(q^r − q^i)
= ∏_{i<r}(q^d − q^i)`, for `q ≥ 1`, `r ≤ d`. -/
theorem gaussBinom_mul_prod {q : ℕ} (hq : 1 ≤ q) {d r : ℕ} (hrd : r ≤ d) :
    gaussBinom q d r * ∏ i : Fin r, (q ^ r - q ^ (i : ℕ))
      = ∏ i : Fin r, (q ^ d - q ^ (i : ℕ)) := by
  have hZ := gaussBinom_mul_prod_int q d r
  have cast1 : ((∏ i : Fin r, (q ^ r - q ^ (i : ℕ)) : ℕ) : ℤ)
      = ∏ i : Fin r, ((q : ℤ) ^ r - (q : ℤ) ^ (i : ℕ)) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq i.2.le)]
    push_cast
    ring
  have cast2 : ((∏ i : Fin r, (q ^ d - q ^ (i : ℕ)) : ℕ) : ℤ)
      = ∏ i : Fin r, ((q : ℤ) ^ d - (q : ℤ) ^ (i : ℕ)) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq (le_trans i.2.le hrd))]
    push_cast
    ring
  have : ((gaussBinom q d r * ∏ i : Fin r, (q ^ r - q ^ (i : ℕ)) : ℕ) : ℤ)
      = ((∏ i : Fin r, (q ^ d - q ^ (i : ℕ)) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, cast1, cast2]
    exact hZ
  exact_mod_cast this

/-! ### The subspace count -/

section Count

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
  [Finite V] {r : ℕ}

/-- Map an independent `r`-tuple to its span, which has rank `r`. -/
def spanMap (s : {s : Fin r → V // LinearIndependent K s}) :
    {W : Submodule K V // finrank K W = r} :=
  ⟨Submodule.span K (Set.range s.1), by
    rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩

/-- The fiber of `spanMap` over `W` is the set of independent `r`-tuples
valued in `W` (i.e., the bases of `W`). -/
def spanFiberEquiv (W : {W : Submodule K V // finrank K W = r}) :
    {x : {s : Fin r → V // LinearIndependent K s} // spanMap x = W}
      ≃ {t : Fin r → W.1 // LinearIndependent K t} where
  toFun x := ⟨fun i => ⟨x.1.1 i, by
      have hsp : Submodule.span K (Set.range x.1.1) = W.1 :=
        congrArg Subtype.val x.2
      exact hsp ▸ Submodule.subset_span (Set.mem_range_self i)⟩, by
    exact LinearIndependent.of_comp W.1.subtype x.1.2⟩
  invFun t := ⟨⟨fun i => (t.1 i : V),
      t.2.map' W.1.subtype (Submodule.ker_subtype W.1)⟩,
    Subtype.ext (by
      have h1 : Set.range (fun i => ((t.1 i : V)))
          = W.1.subtype '' Set.range t.1 := by
        rw [← Set.range_comp]
        rfl
      have h2 : Submodule.span K (Set.range t.1) = ⊤ := by
        haveI : FiniteDimensional K W.1 := Module.Finite.of_finite
        exact t.2.span_eq_top_of_card_eq_finrank'
          (by rw [Fintype.card_fin, W.2])
      show Submodule.span K (Set.range (fun i => ((t.1 i : V)))) = W.1
      rw [h1, Submodule.span_image, h2, Submodule.map_subtype_top])⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv t := Subtype.ext (funext fun i => Subtype.ext rfl)

/-- **Grassmannian count, generic form**: the rank-`r` submodules of a
finite vector space number `[n r]_q` with `q = |K|`, `n = dim V`. -/
theorem card_finrank_submodule_generic (hr : r ≤ finrank K V) :
    Nat.card {W : Submodule K V // finrank K W = r}
      = gaussBinom (Fintype.card K) (finrank K V) r := by
  classical
  haveI : Finite (Submodule K V) :=
    Finite.of_injective (fun W => (W : Set V)) SetLike.coe_injective
  haveI : Fintype {W : Submodule K V // finrank K W = r} :=
    Fintype.ofFinite _
  set q := Fintype.card K with hq
  set n := finrank K V with hn
  -- total: independent r-tuples in V
  have htot : Nat.card {s : Fin r → V // LinearIndependent K s}
      = ∏ i : Fin r, (q ^ n - q ^ (i : ℕ)) := card_linearIndependent hr
  -- fibering over the span
  have h1 : Nat.card {s : Fin r → V // LinearIndependent K s}
      = ∑ W : {W : Submodule K V // finrank K W = r},
          Nat.card {x : {s : Fin r → V // LinearIndependent K s} //
            spanMap x = W} :=
    (Nat.card_congr (Equiv.sigmaFiberEquiv
      (spanMap (K := K) (V := V) (r := r))).symm).trans Nat.card_sigma
  -- each fiber: bases of W
  have hfib : ∀ W : {W : Submodule K V // finrank K W = r},
      Nat.card {x : {s : Fin r → V // LinearIndependent K s} //
        spanMap x = W} = ∏ i : Fin r, (q ^ r - q ^ (i : ℕ)) := by
    intro W
    rw [Nat.card_congr (spanFiberEquiv W)]
    have hW := card_linearIndependent (K := K) (V := W.1)
      (k := r) (by rw [W.2])
    rwa [W.2] at hW
  rw [htot] at h1
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] at h1
  -- cancel the positive basis count
  have hq2 : 1 < q := Fintype.one_lt_card
  have hpos : 0 < ∏ i : Fin r, (q ^ r - q ^ (i : ℕ)) := by
    apply Finset.prod_pos
    intro i _
    exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hq2 i.2)
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← h1, ← gaussBinom_mul_prod hq2.le hr]

end Count

/-- **Grassmannian count for `(Z/pZ)^d`** (paper Lemma 4.1 interface):
the rank-`r` subspaces number `[d r]_p`. -/
theorem card_submodule_finrank {p d r : ℕ} (hpp : p.Prime) (hr : r ≤ d) :
    Nat.card {W : Submodule (ZMod p) (Fin d → ZMod p) //
        finrank (ZMod p) W = r}
      = gaussBinom p d r := by
  haveI := Fact.mk hpp
  have h := card_finrank_submodule_generic (K := ZMod p)
    (V := Fin d → ZMod p) (r := r)
    (by rw [Module.finrank_fin_fun]; exact hr)
  rwa [ZMod.card, Module.finrank_fin_fun] at h

end ShiftSym
