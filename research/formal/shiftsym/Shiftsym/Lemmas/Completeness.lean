/-
Completeness, element form (paper Lemma 3.4, claim C005 first half):
a configuration is shift-symmetric iff it is fixed by some translation of
prime order, and that order divides `n`.

Route: every `v : Lat n d` satisfies `n • v = 0`, so `addOrderOf v ∣ n`;
for `v ≠ 0` the order `o` is `> 1`, and `(o / minFac o) • v` has order
exactly `minFac o`, still fixing `s` since stabilizers are subgroups.
-/
import Shiftsym.Definitions

namespace ShiftSym

variable {n d : ℕ} {A : Type*}

/-- The exponent of `(Z/nZ)^d` divides `n`: `n • v = 0`. -/
theorem nsmul_self_lat (v : Lat n d) : n • v = 0 := by
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  rw [ZMod.natCast_self, zero_mul]

/-- Orders of translations divide `n`. -/
theorem addOrderOf_lat_dvd (v : Lat n d) : addOrderOf v ∣ n :=
  addOrderOf_dvd_of_nsmul_eq_zero (nsmul_self_lat v)

/-- **Completeness, element form** (paper Lemma 3.4): shift-symmetry is
witnessed by a translation of prime order dividing `n`. -/
theorem isShiftSymmetric_iff_prime_order [NeZero n] (s : Config n d A) :
    IsShiftSymmetric s ↔
      ∃ v : Lat n d,
        (addOrderOf v).Prime ∧ addOrderOf v ∣ n ∧ shift v s = s := by
  constructor
  · rintro ⟨v, hv0, hvfix⟩
    set o := addOrderOf v with ho
    have ho1 : o ≠ 1 := fun h =>
      hv0 (AddMonoid.addOrderOf_eq_one_iff.mp (ho ▸ h))
    have hopos : 0 < o := by
      rcases Nat.eq_zero_or_pos o with h | h
      · exact absurd (Nat.eq_zero_of_zero_dvd (h ▸ addOrderOf_lat_dvd v))
          (NeZero.ne n)
      · exact h
    set p := o.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime ho1
    have hpd : p ∣ o := Nat.minFac_dvd o
    have hdivpos : 0 < o / p :=
      Nat.div_pos (Nat.minFac_le hopos) hp.pos
    refine ⟨(o / p) • v, ?_, ?_, ?_⟩
    · -- the order of `(o/p) • v` is exactly `p`
      have hzero : p • ((o / p) • v) = 0 := by
        rw [← mul_nsmul, Nat.div_mul_cancel hpd, ho]
        exact addOrderOf_nsmul_eq_zero v
      have hdvd : addOrderOf ((o / p) • v) ∣ p :=
        addOrderOf_dvd_of_nsmul_eq_zero hzero
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | hself
      · -- order 1 would force `(o/p) • v = 0`, contradicting `o/p < o`
        exfalso
        have hw0 : (o / p) • v = 0 := AddMonoid.addOrderOf_eq_one_iff.mp h1
        have : o ∣ o / p :=
          ho ▸ addOrderOf_dvd_of_nsmul_eq_zero hw0
        have hlt : o / p < o := Nat.div_lt_self hopos hp.one_lt
        exact absurd (Nat.le_of_dvd hdivpos this) (not_le.mpr hlt)
      · rw [hself]; exact hp
    · -- that order divides `n`
      exact addOrderOf_lat_dvd _
    · -- `(o/p) • v` still fixes `s`
      exact (stab s).nsmul_mem (mem_stab.mpr hvfix) (o / p)
  · rintro ⟨v, hp, -, hfix⟩
    refine ⟨v, fun h0 => ?_, hfix⟩
    rw [h0, addOrderOf_zero] at hp
    exact Nat.not_prime_one hp

end ShiftSym
