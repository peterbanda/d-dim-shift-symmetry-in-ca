/-
Phase H, group 12 — proofs: the necklace identification in Remark 4.5(ii)
(non-primitive words = words fixed by a nontrivial rotation; the number of
primitive words; the factor `n` between primitive words and primitive
necklaces; the Moreau–Witt necklace count).

Route: the set-level equivalence is group 04's `P04.isNonPrimitive_iff`
transported along `P04.wordEquiv`; the primitive-word count is the complement
of the certified `|S_n|` count (`P04.remark45d1Count_proved`) inside the
`σ^n` words; the factor `n` comes from an explicit bijection
`PrimNecklace n σ × Lat n 1 ≃ PrimWord n σ`, `(c, v) ↦ shift v (rep c)`,
which is a bijection because the rotation action on primitive words is free
(a nonzero `v` fixing a word would make it shift-symmetric) and
"is a rotation of" is an equivalence relation (so the classes of the `Quot`
are exactly the rotation orbits).
-/
import Shiftsym.Paper.S12_Necklaces
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Words

open Finset

namespace ShiftSym.P12

open ShiftSym

/-! ### Set-level equivalence (proper powers ↔ fixed by a nontrivial rotation) -/

theorem nonPrimitiveIffRotation_proved : nonPrimitiveIffRotationStatement := by
  intro n σ hn s
  have : NeZero n := ⟨by omega⟩
  have h := P04.isNonPrimitive_iff (n := n) (σ := σ) (P04.wordEquiv.symm s)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-! ### Number of primitive words -/

theorem card_config_one {n σ : ℕ} (hn : 1 ≤ n) :
    Nat.card (Config n 1 (Fin σ)) = σ ^ n := by
  have : NeZero n := ⟨by omega⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun, ZMod.card,
    Fintype.card_fin, Fintype.card_fin, pow_one]

theorem card_primWord_add {n σ : ℕ} (hn : 1 ≤ n) :
    Nat.card (PrimWord n σ) + numSS n 1 σ = σ ^ n := by
  classical
  have : NeZero n := ⟨by omega⟩
  rw [← card_config_one (σ := σ) hn, numSS, PrimWord, add_comm, ← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl _)

theorem primitiveWordCount_proved : primitiveWordCountStatement := by
  intro n σ hn hσ
  have h1 := card_primWord_add (σ := σ) hn
  have h2 := P04.remark45d1Count_proved n σ hn hσ
  have h3 : ((Nat.card (PrimWord n σ) + numSS n 1 σ : ℕ) : ℤ) = ((σ ^ n : ℕ) : ℤ) := by
    rw [h1]
  push_cast at h3
  rw [h2, P04.moreauWittComplement] at h3
  linarith

/-! ### The factor `n`: the rotation action on primitive words is free -/

section Factor

variable {n σ : ℕ}

theorem shift_neg_shift (v : Lat n 1) (s : Config n 1 (Fin σ)) :
    shift (-v) (shift v s) = s := by
  rw [← shift_add, neg_add_cancel, shift_zero]

theorem shift_injective (v : Lat n 1) :
    Function.Injective (shift v : Config n 1 (Fin σ) → Config n 1 (Fin σ)) := by
  intro a b h
  rw [← shift_neg_shift v a, h, shift_neg_shift]

/-- Rotations preserve primitivity. -/
theorem not_isShiftSymmetric_shift {s : Config n 1 (Fin σ)} (hs : ¬ IsShiftSymmetric s)
    (v : Lat n 1) : ¬ IsShiftSymmetric (shift v s) := by
  rintro ⟨u, hu, hfix⟩
  apply hs
  refine ⟨u, hu, ?_⟩
  apply shift_injective v
  rw [← shift_add, add_comm, shift_add, hfix]

/-- Freeness: two rotations of a primitive word agree only if the rotations
are equal. -/
theorem shift_eq_shift_of_prim {s : Config n 1 (Fin σ)} (hs : ¬ IsShiftSymmetric s)
    {v w : Lat n 1} (h : shift v s = shift w s) : v = w := by
  by_contra hne
  apply hs
  refine ⟨-w + v, ?_, ?_⟩
  · intro h0
    apply hne
    have := congrArg (w + ·) h0
    simpa [← add_assoc] using this
  · rw [shift_add, h, shift_neg_shift]

theorem isRotationOf_equivalence : Equivalence (@IsRotationOf n σ) where
  refl a := ⟨0, shift_zero _⟩
  symm := by
    rintro a b ⟨v, hv⟩
    exact ⟨-v, by rw [← hv, shift_neg_shift]⟩
  trans := by
    rintro a b c ⟨v, hv⟩ ⟨w, hw⟩
    exact ⟨w + v, by rw [shift_add, hv, hw]⟩

theorem isRotationOf_of_mk_eq {a b : PrimWord n σ}
    (h : Quot.mk (@IsRotationOf n σ) a = Quot.mk _ b) : IsRotationOf a b :=
  (isRotationOf_equivalence.eqvGen_iff).1 (Quot.eqvGen_exact h)

/-- `(c, v) ↦ shift v (rep c)`. -/
noncomputable def neckMap : PrimNecklace n σ × Lat n 1 → PrimWord n σ :=
  fun p => ⟨shift p.2 (Quot.out p.1).1, not_isShiftSymmetric_shift (Quot.out p.1).2 p.2⟩

theorem neckMap_bijective : Function.Bijective (@neckMap n σ) := by
  constructor
  · rintro ⟨c, v⟩ ⟨c', v'⟩ h
    have hval : shift v (Quot.out c).1 = shift v' (Quot.out c').1 :=
      congrArg Subtype.val h
    have hcc : c = c' := by
      rw [← Quot.out_eq c, ← Quot.out_eq c']
      apply Quot.sound
      refine ⟨-v' + v, ?_⟩
      rw [shift_add, hval, shift_neg_shift]
    subst hcc
    have hvv : v = v' := shift_eq_shift_of_prim (Quot.out c).2 hval
    rw [hvv]
  · intro w
    obtain ⟨v, hv⟩ := isRotationOf_of_mk_eq (a := Quot.out (Quot.mk (@IsRotationOf n σ) w))
      (b := w) (Quot.out_eq _)
    exact ⟨⟨Quot.mk _ w, v⟩, Subtype.ext hv⟩

theorem card_lat_one (hn : 1 ≤ n) : Nat.card (Lat n 1) = n := by
  have : NeZero n := ⟨by omega⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin, pow_one]

end Factor

theorem primitiveNecklaceFactor_proved : primitiveNecklaceFactorStatement := by
  intro n σ hn _hσ
  rw [← Nat.card_congr (Equiv.ofBijective _ (@neckMap_bijective n σ)), Nat.card_prod,
    card_lat_one hn, mul_comm]

/-! ### The Moreau–Witt necklace count -/

theorem moreauWittNecklace_proved : moreauWittNecklaceStatement := by
  intro n σ hn hσ
  rw [← primitiveWordCount_proved n σ hn hσ, primitiveNecklaceFactor_proved n σ hn hσ]
  push_cast
  ring

theorem remark45Necklace_proved : remark45NecklaceStatement :=
  ⟨nonPrimitiveIffRotation_proved, primitiveWordCount_proved,
    primitiveNecklaceFactor_proved, moreauWittNecklace_proved⟩

end ShiftSym.P12
