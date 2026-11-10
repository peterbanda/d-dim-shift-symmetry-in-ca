/-
Audit module: every
machine-checked theorem is listed with its axioms printed. Acceptance:
no `sorryAx`, no unapproved axioms (propext, Classical.choice,
Quot.sound are the approved mathlib foundations).
-/
import Shiftsym.Lemmas.Dynamics
import Shiftsym.Lemmas.FixedCount
import Shiftsym.Lemmas.Completeness
import Shiftsym.Lemmas.Torsion
import Shiftsym.Lemmas.Crt
import Shiftsym.Lemmas.Lines
import Shiftsym.Lemmas.GaussCount
import Shiftsym.Lemmas.MobiusSum
import Shiftsym.Lemmas.Assembly
import Shiftsym.Lemmas.Primary
import Shiftsym.Lemmas.Bridge
import Shiftsym.Lemmas.Evaluate
import Shiftsym.Lemmas.Ineq
import Shiftsym.Lemmas.PrimeCase
import Shiftsym.Lemmas.LowerBound
import Shiftsym.Statement
import Shiftsym.StatementE1
import Shiftsym.Lemmas.Relative

#check @ShiftSym.stab_le_stab_apply
#check @ShiftSym.isShiftSymmetric_apply
#check @ShiftSym.stab_inf_mono
#check @ShiftSym.caMap_equivariant
#check @ShiftSym.card_fixedBy
#check @ShiftSym.card_fixedBy_div
#check @ShiftSym.isShiftSymmetric_iff_prime_order
#check @ShiftSym.isShiftSymmetric_iterate
#check @ShiftSym.iterate_ne_of_not_isShiftSymmetric
#check @ShiftSym.dvd_pow_of_mem_divisors_rad
#check @ShiftSym.latTorsionEquiv
#check @ShiftSym.card_latTorsion
#check @ShiftSym.card_addOrderOf_eq_prime
#check @ShiftSym.latPrimarySplit
#check @ShiftSym.card_orderP_subgroups
#check @ShiftSym.gaussBinom_geom
#check @ShiftSym.gaussBinom_mul_prod
#check @ShiftSym.card_submodule_finrank
#check @ShiftSym.gaussBinom_alt_sum
#check @ShiftSym.spanSum_eq_mobius
#check @ShiftSym.sum_spanSum_le
#check @ShiftSym.spanSum_rank_classified
#check @ShiftSym.card_shiftSymmetric_IE
#check @ShiftSym.isShiftSymmetric_iff_mem_biUnion
#check @ShiftSym.latTorsion_inf_coprime
#check @ShiftSym.card_univ_sup_of_torsion
#check @ShiftSym.toMod_ofMod
#check @ShiftSym.ofMod_toMod
#check @ShiftSym.card_ofMod
#check @ShiftSym.spanSum_transport
#check @ShiftSym.enumeration_proved
#check @ShiftSym.gaussBinom_le_pow
#check @ShiftSym.envelope_coeff_lt_two_pow
#check @ShiftSym.enumerationRHS_prime
#check @ShiftSym.card_SS_ge_fix
#check @ShiftSym.lowerBound_proved
#check @ShiftSym.enumerationStatement
#check @ShiftSym.lowerBoundStatement
-- Companion interface: relative enumeration used by the main paper
#check @ShiftSym.card_filter_shiftSymmetric_IE
#check @ShiftSym.relative_regroup
#check @ShiftSym.relativeEnumeration_proved
#check @ShiftSym.mobiusCoeff_eq
#check @ShiftSym.card_shiftSymmetric_eq_tuple_sum
#check @ShiftSym.relativeEnumerationStatement

#print axioms ShiftSym.stab_le_stab_apply
#print axioms ShiftSym.isShiftSymmetric_apply
#print axioms ShiftSym.stab_inf_mono
#print axioms ShiftSym.caMap_equivariant
#print axioms ShiftSym.card_fixedBy
#print axioms ShiftSym.card_fixedBy_div
#print axioms ShiftSym.isShiftSymmetric_iff_prime_order
#print axioms ShiftSym.isShiftSymmetric_iterate
#print axioms ShiftSym.iterate_ne_of_not_isShiftSymmetric
#print axioms ShiftSym.dvd_pow_of_mem_divisors_rad
#print axioms ShiftSym.card_latTorsion
#print axioms ShiftSym.card_addOrderOf_eq_prime
#print axioms ShiftSym.latPrimarySplit
#print axioms ShiftSym.card_latPrimarySplit
#print axioms ShiftSym.card_orderP_subgroups
#print axioms ShiftSym.sub_one_mul_gaussBinom
#print axioms ShiftSym.gaussBinom_mul_prod
#print axioms ShiftSym.card_submodule_finrank
#print axioms ShiftSym.gaussBinom_alt_sum
#print axioms ShiftSym.spanSum_eq_mobius
#print axioms ShiftSym.spanSum_rank_classified
#print axioms ShiftSym.card_shiftSymmetric_IE
#print axioms ShiftSym.latTorsion_inf_coprime
#print axioms ShiftSym.card_univ_sup_of_torsion
#print axioms ShiftSym.spanSum_transport
#print axioms ShiftSym.enumeration_proved
#print axioms ShiftSym.gaussBinom_le_pow
#print axioms ShiftSym.envelope_coeff_lt_two_pow
#print axioms ShiftSym.enumerationRHS_prime
#print axioms ShiftSym.card_SS_ge_fix
#print axioms ShiftSym.lowerBound_proved
#print axioms ShiftSym.card_filter_shiftSymmetric_IE
#print axioms ShiftSym.relative_regroup
#print axioms ShiftSym.relativeEnumeration_proved
#print axioms ShiftSym.mobiusCoeff_eq
#print axioms ShiftSym.card_shiftSymmetric_eq_tuple_sum
