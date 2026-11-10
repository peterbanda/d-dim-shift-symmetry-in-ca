/-
Phase H, group 04 — **proofs of every frozen statement of
`Shiftsym/Paper/S04_EnumerationCorollaries.lean`** (paper lines 397–500:
Theorem 4.3's integrality sentence, Corollary 4.4, Remark 4.5, the claims of
§4.3 "Alternative derivation via the subgroup lattice", the §4.4 reference
values).

Each `theorem <X>_proved : <X>Statement` below proves the frozen `Prop`
verbatim. The work is done in the helper modules:
* `P04_EnumerationCorollaries_Formula` — rank-vector ↔ divisor bridge,
  exponents, Corollary 4.4, formula parts of Remark 4.5, reference values;
* `P04_EnumerationCorollaries_Words` — `d = 1` (Moreau–Witt, non-primitive
  words);
* `P04_EnumerationCorollaries_Lattice` — primary decomposition of `L(A)`;
* `P04_EnumerationCorollaries_Mobius` — Möbius count (CG Lemma 7(i)),
  multiplicativity of `μ`, Hall's evaluation, elementary abelian count;
* `P04_EnumerationCorollaries_Second` — the second derivation of eq. (2)
  along the paper's §4.3 route (multiplicativity + Hall + `[d r]_p`),
  independent of `enumeration_proved`.

Only the certified development (`enumeration_proved`,
`enumerationRHS_prime`, the `ofMod`/`toMod` dictionary, `alt_sum_le`,
`card_submodule_finrank`, `latTorsionEquiv`, `card_fixedBy_div`) and mathlib
are used. No `sorry`, no axioms beyond propext / Classical.choice /
Quot.sound.
-/
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Words
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Mobius
import Shiftsym.Paper.Proofs.P04_EnumerationCorollaries_Second

open Finset

namespace ShiftSym.P04

open ShiftSym

/-! ## Theorem 4.3: exponents, and the rank-vector form of eq. (2) -/

theorem exponentsInteger_proved : exponentsIntegerStatement := by
  intro n d _ _ v hv
  exact ⟨_, (exponent_cast n d hv).symm⟩

theorem exponentEncoding_proved : exponentEncodingStatement := by
  intro n d v hv
  exact exponent_cast n d hv

theorem rankVectorReindex_proved : rankVectorReindexStatement := by
  intro n d σ
  exact mainFormulaRHS_eq_enumerationRHS n d σ

/-! ## Corollary 4.4 -/

theorem cor44General_proved : cor44GeneralStatement := by
  intro p d σ hp hd hσ
  exact numSS_prime hp hd hσ

theorem cor44d1_proved : cor44d1Statement := by
  intro p σ hp hσ
  have h := numSS_prime hp le_rfl hσ
  rw [cor44RHS_one] at h
  exact_mod_cast h

theorem cor44d2_proved : cor44d2Statement := by
  intro p σ hp hσ
  rw [numSS_prime hp (by norm_num) hσ, cor44RHS_two]

theorem cor44d3_proved : cor44d3Statement := by
  intro p σ hp hσ
  rw [numSS_prime hp (by norm_num) hσ, cor44RHS_three]

theorem cor44_proved : cor44Statement :=
  ⟨cor44General_proved, cor44d1_proved, cor44d2_proved, cor44d3_proved⟩

theorem banda2019CorE20_proved : banda2019CorE20Statement := by
  intro n σ hn hσ
  rw [cor44d2_proved n σ hn hσ]
  ring

/-! ## Remark 4.5(i) -/

theorem acComplement_proved : acComplementStatement := by
  intro n d σ hn _ _
  haveI : NeZero n := ⟨by omega⟩
  exact acount_eq

theorem cgLemma7iv_proved : cgLemma7ivStatement := by
  intro p m q hp hm hq
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [acount_eq, numSS_prime hp hm (by omega), cor44_complement]

theorem remark45iIdentity_proved : remark45iIdentityStatement := by
  intro p d σ _ _ _
  exact cor44_complement p d σ

theorem remark45i_proved : remark45iStatement :=
  ⟨acComplement_proved, cgLemma7iv_proved, remark45iIdentity_proved⟩

/-! ## Remark 4.5(ii) -/

theorem remark45n1_proved : remark45n1Statement := by
  intro d σ _ _
  exact ⟨numSS_one d σ, mainFormulaRHS_one d σ⟩

theorem perPrimeIdentity_proved : perPrimeIdentityStatement := by
  intro p d _ hp hd
  exact perPrime_signed hp hd

theorem perPrimeIdentityClosed_proved : perPrimeIdentityClosedStatement := by
  intro p d _ hd
  exact perPrime_closed hd

theorem remark45sigma1RHS_proved : remark45sigma1RHSStatement := by
  intro n d hn hd
  exact mainFormulaRHS_sigma_one hn hd

theorem remark45sigma1LHS_proved : remark45sigma1LHSStatement := by
  intro n d hn hd
  exact numSS_sigma_one hn hd

theorem banda2019ThmE19_proved : banda2019ThmE19Statement := by
  intro n σ hn hσ
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    rw [numSS_one, e19RHS_one, Nat.cast_zero]
  · rw [numSS_eq_mainFormulaRHS h (by norm_num) hσ, mainFormulaRHS_two_eq_e19RHS]

theorem remark45d2Coeff_proved : remark45d2CoeffStatement := by
  intro p v _ hv
  exact rdCoeff_two_eq_e19r hv

theorem remark45d2Formula_proved : remark45d2FormulaStatement := by
  intro n σ _ _
  exact mainFormulaRHS_two_eq_e19RHS n σ

theorem remark45d1Formula_proved : remark45d1FormulaStatement := by
  intro n σ hn _
  exact mainFormulaRHS_one_eq n σ (by omega)

theorem remark45d1Count_proved : remark45d1CountStatement := by
  intro n σ hn hσ
  exact numSS_d_one hn hσ

theorem classicalNonprimitiveCount_proved : classicalNonprimitiveCountStatement := by
  intro n σ hn hσ
  exact card_nonPrimitive_eq hn hσ

theorem remark45ii_proved : remark45iiStatement :=
  ⟨remark45n1_proved, perPrimeIdentity_proved, perPrimeIdentityClosed_proved,
    remark45sigma1RHS_proved, remark45sigma1LHS_proved, banda2019ThmE19_proved,
    remark45d2Coeff_proved, remark45d2Formula_proved, remark45d1Formula_proved,
    remark45d1Count_proved, classicalNonprimitiveCount_proved⟩

/-! ## Remark 4.5(iii) -/

theorem a323863Complement_proved : a323863ComplementStatement := by
  intro n hn
  exact a323863_eq hn

theorem oeisIsraelFormula_proved : oeisIsraelFormulaStatement := by
  intro p hp
  rw [a323863_eq hp.one_lt.le, cor44d2_proved p 2 hp (by norm_num)]
  push_cast
  ring

theorem remark45iiiIdentity_proved : remark45iiiIdentityStatement := by
  intro p _
  rw [cor44RHS_two]
  push_cast
  ring

theorem remark45iii_proved : remark45iiiStatement :=
  ⟨a323863Complement_proved, oeisIsraelFormula_proved, remark45iiiIdentity_proved⟩

theorem remark45_proved : remark45Statement :=
  ⟨remark45i_proved, remark45ii_proved, remark45iii_proved⟩

/-! ## §4.3: the alternative derivation via the subgroup lattice -/

theorem cgLemma7i_proved : cgLemma7iStatement := by
  intro G _ _ q _
  exact cgLemma7i G q

theorem acLatMobius_proved : acLatMobiusStatement := by
  intro n d σ _ _ _ _
  exact acount_mobius n d σ

theorem primaryIso_proved : primaryIsoStatement := by
  intro n d p hn _ hp _
  haveI : NeZero n := ⟨by omega⟩
  exact ⟨primCompEquiv hp⟩

theorem subgroupSplit_proved : subgroupSplitStatement := by
  intro n d hn _ K
  exact subgroup_split hn K

theorem primaryComponentsMultiples_proved : primaryComponentsMultiplesStatement := by
  intro n d hn _ x
  exact primary_multiples hn x

theorem subgroupLatticeProduct_proved : subgroupLatticeProductStatement := by
  intro n d hn _
  exact lattice_product hn

theorem mobiusMultiplicative_proved : mobiusMultiplicativeStatement := by
  intro n d _ hn _ H K
  rw [subgroupMu_eq_cmu, ← Finset.prod_coe_sort]
  exact cmu_mult hn H K

theorem hallMobius_proved : hallMobiusStatement := by
  intro n d p _ _ _ hp hpn K hK
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact hall hpn K hK

theorem elemAbelianCount_proved : elemAbelianCountStatement := by
  intro n d p _ _ _ hp hpn r hr
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact elemAbelian_count hpn hr

/-- Proved along the paper's own route (§4.3: multiplicativity of `μ`, Hall's
evaluation on each `A_p`, the `[d r]_p` count), without using the certified
first derivation `enumeration_proved`; see `secondDerivation_independent`. -/
theorem secondDerivationSum_proved : secondDerivationSumStatement := by
  intro n d σ _ hn _ _
  exact secondDerivation_independent hn σ

/-- Cross-check (not needed for the gate): the same identity via CG Lemma 7(i),
the complement form and the certified Theorem 4.3. -/
theorem secondDerivationSum_via_thm43 : secondDerivationSumStatement := by
  intro n d σ _ hn hd hσ
  rw [← acount_mobius, acount_eq, ← numSS_eq_mainFormulaRHS hn hd hσ]
  ring

theorem secondDerivation_proved : secondDerivationStatement :=
  ⟨cgLemma7i_proved, acLatMobius_proved, primaryIso_proved, subgroupSplit_proved,
    primaryComponentsMultiples_proved, subgroupLatticeProduct_proved,
    mobiusMultiplicative_proved, hallMobius_proved, elemAbelianCount_proved,
    secondDerivationSum_proved⟩

/-! ## §4.4 reference values (σ = 2) -/

theorem refValue22_proved : refValue22Statement := by
  have h := numSS_prime Nat.prime_two (d := 2) (σ := 2) (by norm_num) (by norm_num)
  rw [show cor44RHS 2 2 2 = 8 by decide] at h
  exact_mod_cast h

theorem refValue32_proved : refValue32Statement := by
  have h := numSS_prime Nat.prime_three (d := 2) (σ := 2) (by norm_num) (by norm_num)
  rw [show cor44RHS 3 2 2 = 26 by decide] at h
  exact_mod_cast h

theorem refValue52_proved : refValue52Statement := by
  have h := numSS_prime (p := 5) (by norm_num) (d := 2) (σ := 2) (by norm_num) (by norm_num)
  rw [show cor44RHS 5 2 2 = 182 by decide] at h
  exact_mod_cast h

theorem refValue23_proved : refValue23Statement := by
  have h := numSS_prime Nat.prime_two (d := 3) (σ := 2) (by norm_num) (by norm_num)
  rw [show cor44RHS 2 3 2 = 72 by decide] at h
  exact_mod_cast h

theorem refValue33_proved : refValue33Statement := by
  have h := numSS_prime Nat.prime_three (d := 3) (σ := 2) (by norm_num) (by norm_num)
  rw [show cor44RHS 3 3 2 = 6398 by decide] at h
  exact_mod_cast h

theorem refValue62_proved : refValue62Statement := by
  have h := numSS_eq_enumerationRHS (n := 6) (d := 2) (σ := 2) (by norm_num) (by norm_num)
    (by norm_num)
  rw [enumerationRHS_six] at h
  exact_mod_cast h

theorem referenceValues_proved : referenceValuesStatement :=
  ⟨refValue22_proved, refValue32_proved, refValue52_proved, refValue23_proved,
    refValue33_proved, refValue62_proved⟩

end ShiftSym.P04
