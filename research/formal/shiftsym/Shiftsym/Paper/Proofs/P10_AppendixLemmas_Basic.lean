/-
Phase H, group 10 (Appendix A) — proof helpers, part 1 ("Basic").

* facts about the increasing prime list `primeAt` (via `Finset.orderEmbOfFin`);
* the easy consequences of the certified lower bound (`primeEquality`, `strictComposite`,
  `F_1 = σ`, `|S_p| = σ` at `d = 1`, `F_2`, the `d = 1` composite claim);
* the `q`-Pascal = product-formula bridge for Gaussian binomials;
* divisibility / exponent integrality, the integer-shadow bridge `qTrunc = qTruncZ`;
* the decomposition identity (eq:decomp) of Lemma A.3.

No `sorry`; only the standard axioms.
-/
import Shiftsym.Paper.S10_AppendixLemmas
import Shiftsym.Lemmas.LowerBound
import Shiftsym.Lemmas.Relative

open scoped Classical

namespace ShiftSym.P10

open Finset

theorem card_pf (n : ℕ) : n.primeFactors.card = kOf n := rfl

/-- The increasing enumeration of the prime factors. -/
noncomputable def pemb (n : ℕ) : Fin (kOf n) ↪o ℕ := n.primeFactors.orderEmbOfFin (card_pf n)

theorem primeAt_eq_emb {n i : ℕ} (hi : i < kOf n) :
    primeAt n i = pemb n ⟨i, hi⟩ := by
  rw [primeAt, pemb, Finset.orderEmbOfFin_apply, List.getD_eq_getElem]
  rfl

theorem primeAt_mem {n i : ℕ} (hi : i < kOf n) : primeAt n i ∈ n.primeFactors := by
  rw [primeAt_eq_emb hi]; exact Finset.orderEmbOfFin_mem _ _ _

theorem primeAt_prime {n i : ℕ} (hi : i < kOf n) : (primeAt n i).Prime :=
  Nat.prime_of_mem_primeFactors (primeAt_mem hi)

theorem primeAt_dvd {n i : ℕ} (hi : i < kOf n) : primeAt n i ∣ n :=
  Nat.dvd_of_mem_primeFactors (primeAt_mem hi)

theorem primeAt_lt {n i j : ℕ} (hij : i < j) (hj : j < kOf n) :
    primeAt n i < primeAt n j := by
  rw [primeAt_eq_emb (lt_trans hij hj), primeAt_eq_emb hj]
  exact (pemb n).strictMono (Fin.mk_lt_mk.mpr hij)

theorem primeAt_inj {n i j : ℕ} (hi : i < kOf n) (hj : j < kOf n)
    (h : primeAt n i = primeAt n j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd h (primeAt_lt hij hj).ne
  · exact hij
  · exact absurd h (primeAt_lt hij hi).ne'

theorem exists_primeAt {n p : ℕ} (hp : p ∈ n.primeFactors) :
    ∃ i < kOf n, primeAt n i = p := by
  have : p ∈ Set.range (pemb n) := by
    rw [pemb, Finset.range_orderEmbOfFin]; exact hp
  obtain ⟨⟨i, hi⟩, hip⟩ := this
  exact ⟨i, hi, by rw [primeAt_eq_emb hi]; exact hip⟩

theorem kOf_pos {n : ℕ} (hn : 2 ≤ n) : 0 < kOf n := by
  unfold kOf
  rw [Finset.card_pos]
  exact ⟨n.minFac, Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩⟩

theorem primeAt_zero {n : ℕ} (hn : 2 ≤ n) : primeAt n 0 = n.minFac := by
  have hk := kOf_pos hn
  have hmem := primeAt_mem hk
  apply le_antisymm
  · -- minFac is a prime factor, so it is some primeAt n j, and primeAt n 0 ≤ that
    obtain ⟨j, hj, hjp⟩ := exists_primeAt (Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩)
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; exact hjp.le
    · rw [← hjp]; exact (primeAt_lt hpos hj).le
  · exact Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hmem).two_le
      (Nat.dvd_of_mem_primeFactors hmem)


/-! ### Easy consequences of the certified lower bound -/

theorem numSS_eq_filter (n d σ : ℕ) [NeZero n] :
    numSS n d σ = (Finset.univ.filter
      (fun s : Config n d (Fin σ) => IsShiftSymmetric s)).card :=
  natCard_shiftSymmetric_eq_filterCard σ

theorem primeEquality_proved' : primeEqualityStatement := by
  intro n d σ hp hd hσ
  exact (lowerBound_proved n d σ hp.two_le hd hσ).2.mpr hp

theorem strictComposite_proved' : strictCompositeStatement := by
  intro n d σ hc hd hσ
  have h := lowerBound_proved n d σ hc.1 hd hσ
  exact lt_of_le_of_ne h.1 (fun heq => hc.2 (h.2.mp heq))

theorem envelopeD1_proved' : envelopeD1Statement := by
  intro n σ _ _
  simp [lowerEnvelope, rdCoeff, gaussBinom]

theorem primeD1_proved' : primeD1Statement := by
  intro p σ hp hσ
  have h1 := primeEquality_proved' p 1 σ hp le_rfl hσ
  rw [envelopeD1_proved' p σ hp.two_le hσ] at h1
  exact_mod_cast h1.symm

theorem envelopeD2_proved' : envelopeD2Statement := by
  intro n σ _ _
  rw [lowerEnvelope, show Finset.Icc 1 2 = {1, 2} from rfl, Finset.sum_insert (by simp),
    Finset.sum_singleton]
  simp [rdCoeff, gaussBinom]
  ring

theorem minFac_div_ge_two {n : ℕ} (hc : IsComposite n) : 2 ≤ n / n.minFac := by
  have pp : n.minFac.Prime := Nat.minFac_prime (by have := hc.1; omega)
  have hsq : n.minFac * n.minFac ≤ n := by
    have h := Nat.minFac_sq_le_self (by have := hc.1; omega : 0 < n) hc.2
    calc n.minFac * n.minFac = n.minFac ^ 2 := (sq _).symm
    _ ≤ n := h
  rw [Nat.le_div_iff_mul_le pp.pos]
  calc 2 * n.minFac ≤ n.minFac * n.minFac := Nat.mul_le_mul_right _ pp.two_le
  _ ≤ n := hsq

theorem compositeD1_proved' : compositeD1Statement := by
  intro n σ hc hσ
  have : NeZero n := ⟨by have := hc.1; omega⟩
  rw [primeAt_zero hc.1]
  have pp : n.minFac.Prime := Nat.minFac_prime (by have := hc.1; omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [numSS_eq_filter]
    have := card_SS_ge_fix (n := n) (d := 1) σ pp (Nat.minFac_dvd n) le_rfl
    simpa using this
  · exact Nat.pow_le_pow_right (by omega) (minFac_div_ge_two hc)
  · calc σ = σ ^ 1 := (pow_one σ).symm
    _ < σ ^ 2 := Nat.pow_lt_pow_right (by omega) (by norm_num)

/-! ### `q`-Pascal = product formula -/

theorem pow_sub_one_ne {q : ℝ} (hq : 2 ≤ q) (i : ℕ) : q ^ (i + 1) - 1 ≠ 0 := by
  have : (2 : ℝ) ≤ q ^ (i + 1) := by
    calc (2 : ℝ) ≤ q := hq
    _ = q ^ 1 := (pow_one q).symm
    _ ≤ q ^ (i + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  linarith

theorem gaussProd_zero_right (q : ℝ) (d : ℕ) : gaussProd q d 0 = 1 := by
  simp [gaussProd]

theorem gaussProd_succ_right (q : ℝ) (d r : ℕ) :
    gaussProd q d (r + 1) = gaussProd q d r * ((q ^ (d - r) - 1) / (q ^ (r + 1) - 1)) := by
  rw [gaussProd, Finset.prod_range_succ]; rfl

theorem gaussProd_eq_zero_of_lt (q : ℝ) {d r : ℕ} (h : d < r) : gaussProd q d r = 0 := by
  rw [gaussProd]
  apply Finset.prod_eq_zero (i := d) (Finset.mem_range.mpr h)
  simp

theorem gaussProd_succ_succ (q : ℝ) (d r : ℕ) :
    gaussProd q (d + 1) (r + 1) = gaussProd q d r * ((q ^ (d + 1) - 1) / (q ^ (r + 1) - 1)) := by
  unfold gaussProd
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_range_succ',
    Finset.prod_range_succ (fun i => q ^ (i + 1) - 1)]
  have h1 : ∀ i ∈ Finset.range r, q ^ (d + 1 - (i + 1)) - 1 = q ^ (d - i) - 1 := by
    intro i _; congr 2; omega
  rw [Finset.prod_congr rfl h1]
  simp only [Nat.sub_zero]
  rw [div_mul_div_comm]

theorem gaussProd_pascal {q : ℝ} (hq : 2 ≤ q) (d r : ℕ) :
    gaussProd q (d + 1) (r + 1) = gaussProd q d r + q ^ (r + 1) * gaussProd q d (r + 1) := by
  rw [gaussProd_succ_succ, gaussProd_succ_right]
  by_cases hrd : r ≤ d
  · have hne := pow_sub_one_ne hq r
    have hpow : q ^ (r + 1) * q ^ (d - r) = q ^ (d + 1) := by
      rw [← pow_add]; congr 1; omega
    have hsplit : q ^ (d + 1) - 1 = (q ^ (r + 1) - 1) + q ^ (r + 1) * (q ^ (d - r) - 1) := by
      rw [mul_sub, hpow]; ring
    rw [hsplit, div_eq_mul_inv, div_eq_mul_inv, add_mul, mul_inv_cancel₀ hne]
    ring
  · rw [gaussProd_eq_zero_of_lt q (by omega : d < r)]
    ring

theorem gaussBinomEqProd_proved' : gaussBinomEqProdStatement := by
  intro q d r hq
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  induction d generalizing r with
  | zero =>
    cases r with
    | zero => simp [gaussBinom, gaussProd_zero_right]
    | succ r =>
      rw [gaussProd_eq_zero_of_lt _ (by omega : 0 < r + 1)]
      simp [gaussBinom]
  | succ d ih =>
    cases r with
    | zero => simp [gaussBinom, gaussProd_zero_right]
    | succ r =>
      rw [gaussProd_pascal hq', ← ih r, ← ih (r + 1)]
      simp only [gaussBinom]
      push_cast
      ring


/-! ### Divisibility and exponent integrality -/

theorem prod_primeAt_pow_dvd {n m d x : ℕ} (hm : m ≤ kOf n) (hx : x ≠ 0)
    (hfac : ∀ i < m, d ≤ x.factorization (primeAt n i)) (v : Fin m → Fin (d + 1)) :
    (∏ i : Fin m, primeAt n i ^ ((v i : Fin (d + 1)) : ℕ)) ∣ x := by
  rw [← Int.natCast_dvd_natCast]
  push_cast
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [show ((primeAt n i : ℤ) ^ ((v i : Fin (d + 1)) : ℕ)) =
        ((primeAt n i ^ ((v i : Fin (d + 1)) : ℕ) : ℕ) : ℤ) by push_cast; rfl,
      show ((primeAt n j : ℤ) ^ ((v j : Fin (d + 1)) : ℕ)) =
        ((primeAt n j ^ ((v j : Fin (d + 1)) : ℕ) : ℕ) : ℤ) by push_cast; rfl,
      Nat.isCoprime_iff_coprime]
    apply Nat.Coprime.pow
    rw [Nat.coprime_primes (primeAt_prime (by omega)) (primeAt_prime (by omega))]
    intro h
    exact hij (Fin.ext (primeAt_inj (by omega) (by omega) h))
  · intro i _
    rw [show ((primeAt n i : ℤ) ^ ((v i : Fin (d + 1)) : ℕ)) =
        ((primeAt n i ^ ((v i : Fin (d + 1)) : ℕ) : ℕ) : ℤ) by push_cast; rfl,
      Int.natCast_dvd_natCast]
    rw [(primeAt_prime (by omega)).pow_dvd_iff_le_factorization hx]
    exact le_trans (Nat.lt_succ_iff.mp (v i).2) (hfac i i.2)

theorem factorization_pow_ge {n d i : ℕ} (hn : n ≠ 0) (hi : i < kOf n) :
    d ≤ (n ^ d).factorization (primeAt n i) := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have h1 : 1 ≤ n.factorization (primeAt n i) :=
    (primeAt_prime hi).factorization_pos_of_dvd hn (primeAt_dvd hi)
  calc d = d * 1 := (mul_one d).symm
  _ ≤ d * n.factorization (primeAt n i) := Nat.mul_le_mul_left _ h1

theorem prod_primeAt_pow_dvd_pow {n m d : ℕ} (hn : n ≠ 0) (hm : m ≤ kOf n)
    (v : Fin m → Fin (d + 1)) :
    (∏ i : Fin m, primeAt n i ^ ((v i : Fin (d + 1)) : ℕ)) ∣ n ^ d :=
  prod_primeAt_pow_dvd hm (pow_ne_zero _ hn) (fun i hi => factorization_pow_ge hn (by omega)) v

theorem exponentIntegrality_proved' : exponentIntegralityStatement := by
  intro n d m j hn hd hm1 hmk hj1 hjd
  have hn0 : n ≠ 0 := by omega
  have hP := primeAt_prime hmk
  have hPj : primeAt n m ^ j ∣ n ^ d :=
    (pow_dvd_pow _ hjd).trans (pow_dvd_pow_of_dvd (primeAt_dvd hmk) d)
  have hfac : ∀ i < m, (n ^ d / primeAt n m ^ j).factorization (primeAt n i)
      = d * n.factorization (primeAt n i) := by
    intro i hi
    rw [Nat.factorization_div hPj, Finsupp.tsub_apply, Nat.factorization_pow,
      Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
      hP.factorization, Finsupp.single_apply, if_neg, mul_zero, Nat.sub_zero]
    intro h
    exact absurd (primeAt_inj hmk (by omega) h) (by omega)
  refine ⟨hPj, hfac, fun v => ?_⟩
  have hx : n ^ d / primeAt n m ^ j ≠ 0 := by
    intro h0
    have := Nat.div_mul_cancel hPj
    rw [h0, zero_mul] at this
    exact pow_ne_zero d hn0 this.symm
  apply prod_primeAt_pow_dvd (by omega) hx
  intro i hi
  rw [hfac i hi]
  exact (factorization_pow_ge (d := d) hn0 (by omega : i < kOf n)).trans_eq
    (by rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul])

/-! ### The integer shadow bridge -/

theorem rpow_eq_pow_of_eq (b x : ℝ) (k : ℕ) (h : x = k) : b ^ x = b ^ k := by
  rw [h, Real.rpow_natCast]

theorem qTruncZBridge_proved' : qTruncZBridgeStatement := by
  intro n d σ m e hn hm he hdvd
  unfold qTrunc qTruncZ
  push_cast
  refine Finset.sum_congr rfl (fun v _ => ?_)
  congr 1
  apply rpow_eq_pow_of_eq
  have hp0 : ∀ i : Fin m, (primeAt n i : ℝ) ≠ 0 := fun i => by
    exact_mod_cast (primeAt_prime (by omega : (i : ℕ) < kOf n)).ne_zero
  have hden : ((e * ∏ i : Fin m, primeAt n i ^ ((v i : Fin (d + 1)) : ℕ) : ℕ) : ℝ) ≠ 0 := by
    push_cast
    exact mul_ne_zero (by exact_mod_cast (by omega : e ≠ 0))
      (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hp0 i))
  rw [Nat.cast_div (hdvd v) hden]
  push_cast
  simp only [zpow_neg, zpow_natCast, Finset.prod_inv_distrib]
  rw [div_eq_mul_inv, mul_inv]
  ring


/-! ### The decomposition identity (eq:decomp) -/

/-- The summand of `q^m(c)`, for every `v` (including `v = 0`). -/
noncomputable def qTerm (n d σ m : ℕ) (c : ℝ) (v : Fin m → Fin (d + 1)) : ℝ :=
  (-1 : ℝ) ^ (1 + ∑ i : Fin m, ((v i : Fin (d + 1)) : ℕ)) *
      (∏ i : Fin m, (rdCoeff (primeAt n i) ((v i : Fin (d + 1)) : ℕ) d : ℝ)) *
      (σ : ℝ) ^ (c * (n : ℝ) ^ d *
        ∏ i : Fin m, (primeAt n i : ℝ) ^ (-(((v i : Fin (d + 1)) : ℕ) : ℤ)))

theorem qTrunc_eq_full (n d σ m : ℕ) (c : ℝ) :
    qTrunc n d σ m c = ∑ v, qTerm n d σ m c v + (σ : ℝ) ^ (c * (n : ℝ) ^ d) := by
  have h0 : qTerm n d σ m c 0 = -(σ : ℝ) ^ (c * (n : ℝ) ^ d) := by
    simp [qTerm, rdCoeff, gaussBinom]
  have hq : qTrunc n d σ m c = ∑ v ∈ (Finset.univ : Finset (Fin m → Fin (d + 1))).erase 0,
      qTerm n d σ m c v := rfl
  rw [hq, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin m → Fin (d + 1))), h0]
  ring

theorem qTerm_snoc (n d σ m : ℕ) (c : ℝ) (j : Fin (d + 1)) (v : Fin m → Fin (d + 1)) :
    qTerm n d σ (m + 1) c (Fin.snoc (α := fun _ => Fin (d + 1)) v j)
      = (-1 : ℝ) ^ (j : ℕ) * (rdCoeff (primeAt n m) j d : ℝ) *
          qTerm n d σ m (c * (primeAt n m : ℝ) ^ (-((j : ℕ) : ℤ))) v := by
  unfold qTerm
  rw [Fin.sum_univ_castSucc, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have hexp : c * (n : ℝ) ^ d * ((∏ i : Fin m, (primeAt n i : ℝ) ^ (-(((v i : Fin (d + 1)) : ℕ) : ℤ)))
      * (primeAt n m : ℝ) ^ (-((j : ℕ) : ℤ)))
      = c * (primeAt n m : ℝ) ^ (-((j : ℕ) : ℤ)) * (n : ℝ) ^ d *
          ∏ i : Fin m, (primeAt n i : ℝ) ^ (-(((v i : Fin (d + 1)) : ℕ) : ℤ)) := by ring
  rw [hexp, show 1 + (∑ i : Fin m, ((v i : Fin (d + 1)) : ℕ) + (j : ℕ))
      = (1 + ∑ i : Fin m, ((v i : Fin (d + 1)) : ℕ)) + (j : ℕ) by ring, pow_add]
  ring

theorem full_succ (n d σ m : ℕ) (c : ℝ) :
    ∑ v, qTerm n d σ (m + 1) c v
      = ∑ j : Fin (d + 1), (-1 : ℝ) ^ (j : ℕ) * (rdCoeff (primeAt n m) j d : ℝ) *
          ∑ v, qTerm n d σ m (c * (primeAt n m : ℝ) ^ (-((j : ℕ) : ℤ))) v := by
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Fin (d + 1)))
    (fun x => qTerm n d σ (m + 1) c (Fin.snocEquiv (fun _ => Fin (d + 1)) x)) _ (fun x => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  exact qTerm_snoc n d σ m c j v

theorem decomposition_proved' : decompositionStatement := by
  intro n d σ m _ _ _ _ _ _
  unfold qm
  rw [qTrunc_eq_full, qTrunc_eq_full, full_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
  have hr0 : (rdCoeff (primeAt n m) 0 d : ℝ) = 1 := by simp [rdCoeff, gaussBinom]
  rw [hr0]
  simp only [Nat.cast_zero, neg_zero, zpow_zero, one_mul]
  have hIcc : ∀ g : ℕ → ℝ, ∑ j ∈ Finset.Icc 1 d, g j = ∑ j : Fin d, g (j + 1) := by
    intro g
    rw [Fin.sum_univ_eq_sum_range (fun j => g (j + 1)), ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  rw [hIcc]
  have hterm : ∀ j : Fin d,
      (-1 : ℝ) ^ ((j : ℕ) + 1) * (rdCoeff (primeAt n m) ((j : ℕ) + 1) d : ℝ) *
        ∑ v, qTerm n d σ m ((primeAt n m : ℝ) ^ (-(((j : ℕ) + 1 : ℕ) : ℤ))) v
      = (-1 : ℝ) ^ ((j : ℕ) + 1 + 1) * (rdCoeff (primeAt n m) ((j : ℕ) + 1) d : ℝ) *
        ((σ : ℝ) ^ (Nj n d (primeAt n m) ((j : ℕ) + 1)) -
          qTrunc n d σ m ((primeAt n m : ℝ) ^ (-(((j : ℕ) + 1 : ℕ) : ℤ)))) := by
    intro j
    rw [qTrunc_eq_full]
    have hN : Nj n d (primeAt n m) ((j : ℕ) + 1)
        = (primeAt n m : ℝ) ^ (-(((j : ℕ) + 1 : ℕ) : ℤ)) * (n : ℝ) ^ d := by
      rw [Nj, zpow_neg, zpow_natCast, div_eq_mul_inv, mul_comm]
    rw [hN, pow_succ (-1 : ℝ) ((j : ℕ) + 1)]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  ring

end ShiftSym.P10
