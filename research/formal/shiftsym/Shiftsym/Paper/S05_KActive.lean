/-
Phase H, group 05 (KActive) — FROZEN STATEMENTS, no proofs of them here.

Paper: `shift_symmetry_d_dimensions.tex` (v3.1),
* §5 "Configurations with k active cells", lines 519–560:
  preamble conventions (lines 522–528, including the remark about Eqs.
  (29)–(33) of [banda2019], lines 527–528), Theorem 5.1 `thm:kactive`
  (lines 530–541), its proof (lines 543–554, one proof-internal counting
  claim, lines 544–550, frozen as an auxiliary Prop), and the verification paragraph with
  the consistency claim `Σ_k |S^a_{n^d,k}| = |S_{n^d}|` (lines 556–559);
* §7 Corollary 7.2 `cor:dens` (density-uniform distribution),
  lines 693–702.

Frozen Props (each closed over all its parameters; a proof is
`theorem <name>_proved : <name>Statement`):
* `noFractionalExponentStatement`   — §5 convention: "the accompanying factor with
                                      fractional exponent never occurs" (lines 524–526),
                                      at EVERY occurrence the convention governs
                                      (Thm 5.1, its proof for every subgroup `H`, Cor 7.2)
* `fractionalExponentArisesStatement` — presupposition of the same parenthetical: summands
                                      with a vanishing binomial and a fractional exponent
                                      really occur (Thm 5.1 and its proof)
* `zeroPowOnlyStatement`            — §5 convention: "`0^0:=1` (relevant only at `σ=1`,
                                      `k=N`)" (line 527), the "only" half, same occurrences
* `zeroPowOccursStatement`          — the same claim, positive half: at `σ=1`, `k=N` every
                                      occurrence (Thm 5.1, its proof) is a non-annihilated `0^0`
* `zeroPowMattersStatement`         — the same claim, positive half: at `σ=1`, `k=N` the two
                                      formulas give the true counts iff `0^0` is given the value 1
* `zeroPowRelevanceStatement`       — conjunction of the three `zeroPow…` parts (the whole claim)
* `conventionClaimsStatement`       — conjunction of all claims inside the §5 convention
* `conventionScopeLiteralStatement` — AUXILIARY, supports the PAPER ISSUE on the SCOPE of
                                      the §5 convention (recorded in
                                      `noFractionalExponentStatement`): read literally
                                      ("Here and below"), the annihilation clause kills the
                                      `r = 1` summand of `F_d` in Theorem 6.1 (line 575),
                                      and the envelope so read is strictly below `|S|` at
                                      every prime `n`
* `banda2019Eq29NeedsStatement` … `banda2019Eq33NeedsStatement`
                                    — line 527–528, "This convention is also implicitly
                                      required by Eqs. (29)–(33) of [banda2019]": in each
                                      equation the convention is actually invoked
* `banda2019Eq29ValidStatement` … `banda2019Eq33ValidStatement`
                                    — the presupposition of the same sentence: read with
                                      the convention, each 2019 equation is correct
* `banda2019NeedsStatement`, `banda2019ValidStatement`, `banda2019ConventionStatement`
                                    — conjunctions (the whole sentence)
* `banda2019Eq29StandardStatement`  — AUXILIARY, supports the PAPER ISSUE on Eq. (29)
* `banda2019Eq32PrintedFalseStatement`, `banda2019Eq33PrintedFalseStatement`
                                    — AUXILIARY, support the PAPER ISSUE on Eqs. (32)–(33):
                                      as printed (`r(i)` with `p_i`) they are false
* `fixKCountStatement`              — proof-internal claim `|Fix_k(H)| = …` (lines 544–550)
* `kActiveStatement`                — Theorem 5.1
* `kActiveConsistencyStatement`     — `Σ_k |S^a_{n^d,k}| = |S_{n^d}|` (line 559)
* `kActiveRHSConsistencyStatement`  — AUXILIARY: the same check at formula level
* `densityStatement`                — Corollary 7.2, displayed formula
* `densityClosedStatement`          — Corollary 7.2, "with |S^a_k| given by Theorem 5.1"
* `corDensStatement`                — Corollary 7.2 (conjunction)

Global representation choices (repeated in each docstring where relevant):
* alphabet `Σ = Fin σ`, the fixed state `a : Fin σ` (the project-wide
  WLOG: only `|Σ| = σ` enters; any finite alphabet is a relabeling);
* `|X|` for a set of configurations / cells is `Nat.card` of the subtype
  (the genuine cardinality: `Z_n^d` is finite for `n ≥ 2`, an explicit
  antecedent everywhere, so the `Nat.card (infinite) = 0` trap cannot fire);
* signed sums live in `ℤ`, probabilities in `ℝ`; `σ − 1` is computed in
  `ℤ`/`ℝ` (no truncated `ℕ`-subtraction);
* Gaussian binomials / `r_d(p, v)` are the project's frozen `gaussBinom`
  (q-Pascal recurrence) and `rdCoeff` from `Shiftsym.Statement`, as in the
  certified Theorem 4.3 (see STATEMENT_PRESERVATION.md); the recurrence is
  cross-checked against the paper's product formula below;
* the §5 binomial convention (annihilation of the whole summand) is applied
  ONLY to the binomials `binom(N/h, k/h)` of Theorem 5.1 and its proof,
  `binom(N, k)` of Corollary 7.2 (`kActiveSummand`, `convTerm`), and the
  corresponding `binom(n²/h, k/h)` of 2019 Eqs. (29)–(33), to which the
  paper explicitly extends it (`convTerm`, `convBinom`); as worded ("Here
  and below") its scope is wider and the literal reading falsifies Theorem
  6.1 — PAPER ISSUE recorded in `noFractionalExponentStatement`, supported
  by `conventionScopeLiteralStatement`.

Review history: round 1 (fidelity review, 2026-10-15) rejected the draft on
two findings, both repaired here: (1) the two convention Props only covered
the occurrences `h = h(v)` of Theorem 5.1, not `h = |H|` (proof of Theorem
5.1) and `h = 1` (Corollary 7.2); (2) the remark about Eqs. (29)–(33) of
[banda2019] had been set aside as non-mathematical; it is now frozen.
Round 2 (fidelity review, 2026-10-16, exploit lens) rejected the round-1 file
(sha256 `cce4ab2a…aecff`) on two findings, both repaired here: (1) the claim
"`0^0:=1` (relevant only at `σ=1`, `k=N`)" had been frozen only in its
"only" half; the positive half is now frozen too (`zeroPowOccursStatement`,
`zeroPowMattersStatement`; the old Prop is renamed `zeroPowOnlyStatement`,
its body unchanged, and `zeroPowRelevanceStatement` is now the conjunction);
(2) 2019 Eqs. (32)–(33) print `r(i)` with `p_i` (primes of `n`) instead of
`r_i` (primes of `gcd(k,n)`) and are FALSE as printed; round 1 had called the
printed version "not well-indexed" (false) and recorded it as a mere
reading choice; it is now a PAPER ISSUE with AUXILIARY Props
(`banda2019Eq32/33PrintedFalseStatement`). The reviewer's optional item (the
presupposition of "the accompanying factor with fractional exponent") is
frozen as `fractionalExponentArisesStatement`. No main Prop (Theorem 5.1,
the consistency claim, Corollary 7.2, `fixKCountStatement`, the
`banda2019…Valid/Needs` Props) changed in statement.
Round 3 (fidelity review, 2026-10-16, literal lens) rejected the round-2 file
(sha256 `3a79f93e…7999`) on one finding, repaired here: the scope paragraph
of `noFractionalExponentStatement` claimed that the other binomials after
line 524 (`n^{binom(r,2)}`, line 575; `p^{binom(v,2)}`, lines 1120, 1213)
"have integer arguments and no accompanying factor" and are outside the
convention, and the file said "PAPER ISSUE: none". Both are wrong: the first
clause makes `binom(1,2)` (and `binom(0,2)`) vanish although the arguments are
integers, the `r = 1` summand of `F_d` does carry accompanying factors, and
the literal "annihilates its whole summand" then makes Theorem 6.1 false.
The scope paragraph is corrected, a PAPER ISSUE with a suggested rewording is
recorded there (and cited in `kActiveSummand`, `convTerm`, `convBinom`,
`kActiveStatement`), and the AUXILIARY `conventionScopeLiteralStatement`
(with its definition `lowerEnvelopeLit`) freezes the falsity of the literal
reading. No Prop body changed. Added: one AUXILIARY Prop, one definition,
two proved infrastructure lemmas (`choose_two_eq_zero_iff`,
`lowerEnvelopeLit_eq`) and `#guard` sanity checks.
-/
import Shiftsym.Paper.Common

namespace ShiftSym.P05

open ShiftSym

/-! ## Definitions (paper §5 preamble and §7) -/

/-- Number of cells of the configuration `s` that are in state `a`:
`#{u ∈ Z_n^d : s(u) = a}` (paper §5 preamble, "exactly `k` cells in state
`a`"). `Nat.card` of the subtype of the lattice; genuine for `n ≥ 1`. -/
noncomputable def cellsInState {n d σ : ℕ} (s : Config n d (Fin σ)) (a : Fin σ) : ℕ :=
  Nat.card {u : Lat n d // s u = a}

/-- `|S^a_{n^d,k}|` (paper §5 preamble, lines 522–523: "Fix a state `a∈Σ` and
let `S^a_{n^d,k}` be the set of shift-symmetric configurations with exactly
`k` cells in state `a`"). Alphabet `Fin σ`; `IsShiftSymmetric` is the
project's Definition 2.2 (`∃ v ≠ 0, τ_v s = s`). -/
noncomputable def numKActive (n d σ : ℕ) (a : Fin σ) (k : ℕ) : ℕ :=
  Nat.card {s : Config n d (Fin σ) // IsShiftSymmetric s ∧ cellsInState s a = k}

/-- The rank vectors `v ∈ {0,…,d}^{ω(n)}`, "one coordinate per distinct
prime factor" (Theorem 5.1). Representation: a vector is a function
`v : n.primeFactors → ℕ` with every value in `{0,…,d}` — coordinates are
labelled by the prime `p_i` itself instead of by its position `i` in the
increasing list `p_1 < ⋯ < p_{ω(n)}` (a bijection; every summand is
symmetric under relabelling since it only involves `∏_i`, `Σ_i`). -/
def rankVectors (n d : ℕ) : Finset (n.primeFactors → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (d + 1)

/-- `h(v) = ∏_i p_i^{v_i}` (Theorem 5.1). -/
def hVec {n : ℕ} (v : n.primeFactors → ℕ) : ℕ :=
  ∏ p : n.primeFactors, (p : ℕ) ^ v p

/-- `|v| = Σ_i v_i` (Theorem 4.3, line 405). -/
def absVec {n : ℕ} (v : n.primeFactors → ℕ) : ℕ :=
  ∑ p : n.primeFactors, v p

/-- The summand of Theorem 5.1 at the rank vector `v`, UNDER THE PAPER'S
§5 CONVENTION (lines 523–527): "`binom(x,y) := 0` whenever `y` is not an
integer in `{0,…,x}`; a vanishing binomial annihilates its whole summand
(so the accompanying factor with fractional exponent never occurs), and
`0^0 := 1`".

Encoding, with `h = h(v)`, `x = N/h`, `y = k/h`, `N = n^d`:
* "`y = k/h` is an integer in `{0,…,x}`" is literally the guard
  `h ∣ k ∧ k / h ≤ n ^ d / h` (`ℕ`-division; exact: `h ∣ k` by the guard and
  `h ∣ n^d` by `hVec_dvd_pow` below; `y ≥ 0` is automatic for `k : ℕ`);
  `guard_iff` below PROVES that this guard is equivalent to the paper's
  condition stated with rational quotients;
* if the guard fails the summand is `0` ("annihilates its whole summand");
* otherwise `binom(N/h, k/h)` is `Nat.choose` and `(σ−1)^{(N−k)/h}` is an
  integer power (`(N − k)/h` exact: `k ≤ N` is a hypothesis of every Prop
  using this, and `h` divides both `k` and `N`); `σ − 1` is taken in `ℤ`;
* `0^0 = 1` is Lean's `pow_zero` on `ℤ` — the paper's convention;
* SCOPE: the annihilation rule is applied to `binom(N/h(v), k/h(v))` only.
  The binomial `binom(v_i, 2)` inside `r_d(p_i, v_i) = p_i^{binom(v_i,2)}[d v_i]`
  (`rdCoeff`, defined at paper line 392, before "Here and below") is the
  ordinary `Nat.choose` and never annihilates: at `v_i ∈ {0, 1}` it is `0`
  and `p_i^0 = 1`. As worded, the §5 convention ("Here and below … a
  vanishing binomial annihilates its whole summand") reaches further and,
  read literally, falsifies Theorem 6.1; this encoding is the evidently
  intended restricted reading — see the PAPER ISSUE in
  `noFractionalExponentStatement` and the AUXILIARY
  `conventionScopeLiteralStatement`. -/
def kActiveSummand (n d σ k : ℕ) (v : n.primeFactors → ℕ) : ℤ :=
  if hVec v ∣ k ∧ k / hVec v ≤ n ^ d / hVec v then
    (-1 : ℤ) ^ (1 + absVec v) * (∏ p : n.primeFactors, (rdCoeff p (v p) d : ℤ))
      * ((n ^ d / hVec v).choose (k / hVec v) : ℤ)
      * ((σ : ℤ) - 1) ^ ((n ^ d - k) / hVec v)
  else 0

/-- Right-hand side of Theorem 5.1: the sum of `kActiveSummand` over the
rank vectors `v ≠ 0`. -/
def kActiveRHS (n d σ k : ℕ) : ℤ :=
  ∑ v ∈ (rankVectors n d).erase 0, kActiveSummand n d σ k v

/-- `C^a_k`: the configurations with exactly `k` cells in state `a`, as a
finset (used for the second stage of the density-uniform distribution of
Corollary 7.2). -/
noncomputable def configsWithK (n d σ : ℕ) [NeZero n] (a : Fin σ) (k : ℕ) :
    Finset (Config n d (Fin σ)) :=
  Finset.univ.filter fun s => cellsInState s a = k

/-- The term `binom(N/h, k/h)·(σ−1)^{(N−k)/h}` evaluated UNDER THE §5
CONVENTION, for a divisor `h` of `N` (every use below has `h ∣ N`, proved:
`hVec_dvd_pow`, `card_addSubgroup_dvd_pow`, `h2019_dvd_sq`): `0` unless
`k/h` is an integer in `{0,…,N/h}` (guard `h ∣ k ∧ k/h ≤ N/h`, proved
equivalent to the rational condition by `guard_iff_of_dvd`); otherwise
`Nat.choose` times an integer power, with `0^0 = 1` (`pow_zero`). This is
literally the expression inside `kActiveSummand` and on the right of
`fixKCountStatement` (see `kActiveSummand_eq_convTerm`). The annihilation
rule is applied here, to `binom(N/h, k/h)`, and nowhere else (restricted
reading of the §5 convention; PAPER ISSUE in
`noFractionalExponentStatement`). -/
def convTerm (N k h σ : ℕ) : ℤ :=
  if h ∣ k ∧ k / h ≤ N / h then
    ((N / h).choose (k / h) : ℤ) * ((σ : ℤ) - 1) ^ ((N - k) / h)
  else 0

/-- The binomial `binom(N/h, k/h)` alone under the §5 convention (used by
the 2019 Eq. (33), which has no power factor). Same restricted scope as
`convTerm` (PAPER ISSUE in `noFractionalExponentStatement`). -/
def convBinom (N k h : ℕ) : ℤ :=
  if h ∣ k ∧ k / h ≤ N / h then ((N / h).choose (k / h) : ℤ) else 0

/-- "`y = k/h` is an integer in `{0,…,x}`, `x = N/h`" — the condition under
which the §5 convention does NOT annihilate `binom(N/h, k/h)` — with the
quotients taken literally in `ℚ` (`y ≥ 0` is automatic for `k : ℕ`, so
"integer in `{0,…,x}`" is `∃ j : ℕ, j = y ∧ j ≤ x`). -/
def BinomNonvanishing (N k h : ℕ) : Prop :=
  ∃ j : ℕ, (j : ℚ) = (k : ℚ) / (h : ℚ) ∧ (j : ℚ) ≤ (N : ℚ) / (h : ℚ)

/-- §5 convention claim (i) at ONE occurrence `binom(N/h, k/h)(σ−1)^{(N−k)/h}`:
if the binomial does not vanish, the accompanying exponent `(N−k)/h` is not
fractional, i.e. it is an integer (quotient in `ℚ`). -/
def NoFracAt (N k h : ℕ) : Prop :=
  BinomNonvanishing N k h → ∃ m : ℤ, (m : ℚ) = ((N : ℚ) - (k : ℚ)) / (h : ℚ)

/-- §5 convention claim (ii) at ONE occurrence: if the binomial does not
vanish (so the power factor is really evaluated) and the power is `0^0`
(base `σ − 1 = 0`, exponent `(N−k)/h = 0`, in `ℚ`), then `σ = 1` and
`k = N`. -/
def ZeroPowOnlyAt (N σ k h : ℕ) : Prop :=
  BinomNonvanishing N k h →
    ((σ : ℚ) - 1 = 0 ∧ ((N : ℚ) - (k : ℚ)) / (h : ℚ) = 0) → σ = 1 ∧ k = N

/-- §5 convention claim (ii), the event itself at ONE occurrence
`binom(N/h,k/h)(σ−1)^{(N−k)/h}`: the binomial does not vanish (so the power
factor is really evaluated) and the power is `0^0` (base `σ − 1 = 0`,
exponent `(N−k)/h = 0`, in `ℚ`). `ZeroPowOnlyAt` is "this event forces
`σ = 1 ∧ k = N`" (`zeroPowOnlyAt_iff`, proved below). -/
def ZeroPowOccursAt (N σ k h : ℕ) : Prop :=
  BinomNonvanishing N k h ∧ (σ : ℚ) - 1 = 0 ∧ ((N : ℚ) - (k : ℚ)) / (h : ℚ) = 0

/-- The power `b^e` evaluated with the value of `0^0` set to `z`; every other
power is the ordinary integer power. `z = 1` is the paper's convention
(`powZ_one`, proved below). Used only to state that the value assigned to
`0^0` matters (`zeroPowMattersStatement`). -/
def powZ (z b : ℤ) (e : ℕ) : ℤ := if b = 0 ∧ e = 0 then z else b ^ e

/-- `convTerm` with `0^0 := z` (everything else literally identical);
`convTermZ 1 = convTerm` (`convTermZ_one`, proved below). -/
def convTermZ (z : ℤ) (N k h σ : ℕ) : ℤ :=
  if h ∣ k ∧ k / h ≤ N / h then
    ((N / h).choose (k / h) : ℤ) * powZ z ((σ : ℤ) - 1) ((N - k) / h)
  else 0

/-- The right-hand side of Theorem 5.1 with `0^0 := z` (everything else
literally identical); `kActiveRHSZ 1 = kActiveRHS` (`kActiveRHSZ_one`,
proved below). -/
def kActiveRHSZ (z : ℤ) (n d σ k : ℕ) : ℤ :=
  ∑ v ∈ (rankVectors n d).erase 0,
    (-1 : ℤ) ^ (1 + absVec v) * (∏ p : n.primeFactors, (rdCoeff p (v p) d : ℤ))
      * convTermZ z (n ^ d) k (hVec v) σ

/-- "`x` is an integer" for a rational `x`. -/
def IsIntQ (x : ℚ) : Prop := ∃ j : ℤ, (j : ℚ) = x

/-! ## Infrastructure lemmas (NOT paper statements; they only make the
definitions above well-formed / exact) -/

/-- `|Z_n^d| = n^d`. -/
theorem card_lat (n d : ℕ) [NeZero n] : Fintype.card (Lat n d) = n ^ d := by
  simp [Lat, ZMod.card]

/-- Integrality of `N / h(v)` in Theorem 5.1: for a rank vector
(`v_i ≤ d`), `h(v) = ∏ p_i^{v_i}` divides `n^d`. Closes the `ℕ`-division
caveat for `n ^ d / hVec v`. -/
theorem hVec_dvd_pow {n d : ℕ} {v : n.primeFactors → ℕ} (hv : v ∈ rankVectors n d) :
    hVec v ∣ n ^ d := by
  have hle : ∀ p, v p ≤ d := fun p => by
    have := Fintype.mem_piFinset.mp hv p
    simpa [Finset.mem_range, Nat.lt_succ_iff] using this
  calc hVec v = ∏ p : n.primeFactors, (p : ℕ) ^ v p := rfl
    _ ∣ ∏ p : n.primeFactors, (p : ℕ) ^ d :=
        Finset.prod_dvd_prod_of_dvd _ _ fun p _ => pow_dvd_pow _ (hle p)
    _ = (∏ p : n.primeFactors, (p : ℕ)) ^ d := Finset.prod_pow _ _ _
    _ = (∏ p ∈ n.primeFactors, p) ^ d := by
        rw [Finset.prod_coe_sort n.primeFactors (fun p => p)]
    _ ∣ n ^ d := pow_dvd_pow_of_dvd (Nat.prod_primeFactors_dvd n) d

/-- `h(v) > 0` (a product of prime powers). -/
theorem hVec_pos {n : ℕ} (v : n.primeFactors → ℕ) : 0 < hVec v :=
  Finset.prod_pos fun p _ => pow_pos (Nat.prime_of_mem_primeFactors p.2).pos _

/-- Faithfulness of the `ℕ`-encoded convention guard, for ANY positive
divisor `h` of `N`: `h ∣ k ∧ k / h ≤ N / h` is EXACTLY the paper's condition
"`k/h` is an integer in `{0,…,N/h}`" with the quotients taken in `ℚ`. -/
theorem guard_iff_of_dvd {N k h : ℕ} (hpos : 0 < h) (hdvd : h ∣ N) :
    (h ∣ k ∧ k / h ≤ N / h) ↔ BinomNonvanishing N k h := by
  have hq : (h : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hN : ((N / h : ℕ) : ℚ) = (N : ℚ) / (h : ℚ) := Nat.cast_div hdvd hq
  unfold BinomNonvanishing
  constructor
  · rintro ⟨⟨j, rfl⟩, hle⟩
    refine ⟨j, ?_, ?_⟩
    · rw [Nat.cast_mul, mul_div_cancel_left₀ _ hq]
    · have hj' : j ≤ N / h := by
        simpa [Nat.mul_div_cancel_left _ hpos] using hle
      rw [← hN]
      exact_mod_cast hj'
  · rintro ⟨j, hj, hle⟩
    have hk : k = h * j := by
      have : (k : ℚ) = (h : ℚ) * j := by
        rw [hj]; field_simp
      exact_mod_cast this
    subst hk
    refine ⟨dvd_mul_right _ _, ?_⟩
    rw [Nat.mul_div_cancel_left _ hpos]
    rw [← hN] at hle
    exact_mod_cast hle

/-- Faithfulness of the `ℕ`-encoded guard of `kActiveSummand`: for a rank
vector `v`, the guard `h ∣ k ∧ k / h ≤ n^d / h` is EXACTLY the paper's
condition "`k/h(v)` is an integer in `{0,…,N/h(v)}`" with the quotients
taken in `ℚ` (the condition under which the §5 binomial does not vanish). -/
theorem guard_iff {n d k : ℕ} {v : n.primeFactors → ℕ} (hv : v ∈ rankVectors n d) :
    (hVec v ∣ k ∧ k / hVec v ≤ n ^ d / hVec v) ↔ BinomNonvanishing (n ^ d) k (hVec v) :=
  guard_iff_of_dvd (hVec_pos v) (hVec_dvd_pow hv)

/-- Lagrange for `Z_n^d`: `|H|` divides `n^d` for every subgroup `H`. Makes
the `ℕ`-quotients `n^d / Nat.card H` (and, under the guard,
`(n^d − k) / Nat.card H`) in `fixKCountStatement` exact. -/
theorem card_addSubgroup_dvd_pow (n d : ℕ) [NeZero n] (H : AddSubgroup (Lat n d)) :
    Nat.card H ∣ n ^ d := by
  have h := AddSubgroup.card_addSubgroup_dvd_card H
  rwa [Nat.card_eq_fintype_card (α := Lat n d), card_lat] at h

/-- `|H| > 0` for every subgroup `H` of the finite group `Z_n^d`. -/
theorem card_addSubgroup_pos (n d : ℕ) [NeZero n] (H : AddSubgroup (Lat n d)) :
    0 < Nat.card H :=
  Nat.card_pos

/-- Faithfulness of the guard of `fixKCountStatement`: for every subgroup
`H`, it is exactly the rational condition "`k/|H|` is an integer in
`{0,…,N/|H|}`". -/
theorem guard_iff_subgroup {n d k : ℕ} [NeZero n] (H : AddSubgroup (Lat n d)) :
    (Nat.card H ∣ k ∧ k / Nat.card H ≤ n ^ d / Nat.card H)
      ↔ BinomNonvanishing (n ^ d) k (Nat.card H) :=
  guard_iff_of_dvd (card_addSubgroup_pos n d H) (card_addSubgroup_dvd_pow n d H)

/-- The Theorem 5.1 summand is sign × coefficient × `convTerm` (the two
encodings of the §5 convention used in this file coincide). -/
theorem kActiveSummand_eq_convTerm (n d σ k : ℕ) (v : n.primeFactors → ℕ) :
    kActiveSummand n d σ k v
      = (-1 : ℤ) ^ (1 + absVec v) * (∏ p : n.primeFactors, (rdCoeff p (v p) d : ℤ))
          * convTerm (n ^ d) k (hVec v) σ := by
  unfold kActiveSummand convTerm
  split_ifs <;> ring

/-- Faithfulness of `powZ`: with `z = 1` it is the ordinary power (`0^0 = 1`). -/
theorem powZ_one (b : ℤ) (e : ℕ) : powZ 1 b e = b ^ e := by
  unfold powZ
  split_ifs with h
  · rw [h.1, h.2, pow_zero]
  · rfl

/-- Faithfulness of `convTermZ`: with `z = 1` it is `convTerm`. -/
theorem convTermZ_one (N k h σ : ℕ) : convTermZ 1 N k h σ = convTerm N k h σ := by
  unfold convTermZ convTerm
  simp only [powZ_one]

/-- Faithfulness of `kActiveRHSZ`: with `z = 1` it is the frozen right-hand
side `kActiveRHS` of Theorem 5.1. -/
theorem kActiveRHSZ_one (n d σ k : ℕ) : kActiveRHSZ 1 n d σ k = kActiveRHS n d σ k := by
  unfold kActiveRHSZ kActiveRHS
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [convTermZ_one, kActiveSummand_eq_convTerm]

/-- The "only" and the "occurs" halves of the `0^0` claim talk about the same
event: `ZeroPowOnlyAt` is "`ZeroPowOccursAt` forces `σ = 1 ∧ k = N`". -/
theorem zeroPowOnlyAt_iff (N σ k h : ℕ) :
    ZeroPowOnlyAt N σ k h ↔ (ZeroPowOccursAt N σ k h → σ = 1 ∧ k = N) := by
  unfold ZeroPowOnlyAt ZeroPowOccursAt
  tauto

/-- For `σ ≥ 2` and `0 ≤ k ≤ N`, there is a configuration with exactly `k`
cells in state `a` (so the second stage of the density-uniform
distribution is a genuine uniform distribution on a nonempty set; this is
why Corollary 7.2 assumes `σ ≥ 2`). -/
theorem configsWithK_nonempty {n d σ : ℕ} [NeZero n] (hσ : 2 ≤ σ) (a : Fin σ) {k : ℕ}
    (hk : k ≤ n ^ d) : (configsWithK n d σ a k).Nonempty := by
  classical
  have : Nontrivial (Fin σ) := Fin.nontrivial_iff_two_le.mpr hσ
  obtain ⟨b, hb⟩ := exists_ne a
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Lat n d))) (n := k) (by rw [Finset.card_univ, card_lat]; exact hk)
  refine ⟨fun u => if u ∈ t then a else b, ?_⟩
  rw [configsWithK, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  show Nat.card {u : Lat n d // (if u ∈ t then a else b) = a} = k
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← ht]
  congr 1
  ext u
  by_cases hu : u ∈ t <;> simp [hu, hb]

/-- The density-uniform distribution of Corollary 7.2 (lines 694–696): "first
draw `k∈{0,…,N}` uniformly, then a configuration with exactly `k` cells in
state `a` uniformly". Literally the two-stage mathlib `PMF`:
`k ~ uniform(Fin (N+1))`, then `s ~ uniform(C^a_k)`, composed by
`PMF.bind`. The hypothesis `σ ≥ 2` supplies nonemptiness of every `C^a_k`
(`configsWithK_nonempty`); no fallback branch exists. -/
noncomputable def densPMF (n d σ : ℕ) [NeZero n] (hσ : 2 ≤ σ) (a : Fin σ) :
    PMF (Config n d (Fin σ)) :=
  (PMF.uniformOfFintype (Fin (n ^ d + 1))).bind fun k =>
    PMF.uniformOfFinset (configsWithK n d σ a k)
      (configsWithK_nonempty hσ a (Nat.lt_succ_iff.mp k.isLt))

/-- `P^dens_{n^d}`: the probability that a configuration drawn from the
density-uniform distribution is shift-symmetric, i.e. the outer measure of
`S_{n^d} = {s | IsShiftSymmetric s}` under `densPMF`, as a real number.
(`toReal` is faithful: a `PMF`'s outer measure is `≤ 1`, never `⊤`.) -/
noncomputable def probDens (n d σ : ℕ) [NeZero n] (hσ : 2 ≤ σ) (a : Fin σ) : ℝ :=
  ((densPMF n d σ hσ a).toOuterMeasure {s | IsShiftSymmetric s}).toReal

/-! ## Frozen statements -/

/-- **Claim inside the §5 convention, part (i)** (paper lines 523–526; not
a numbered statement).

Paper (verbatim): "Here and below, `binom(x,y):=0` whenever `y` is not an
integer in `{0,…,x}`; a vanishing binomial annihilates its whole summand
(so the accompanying factor with fractional exponent never occurs)".

Scope ("Here and below"). Claim (i) is about the binomials governed by the
convention whose accompanying factor can have a fractional exponent. These
are exactly the occurrences of the shape `binom(N/h, k/h)·(σ−1)^{(N−k)/h}`:
* (T) Theorem 5.1 (line 538): `h = h(v)` for a rank vector `v ≠ 0`;
* (P) the proof of Theorem 5.1 (line 549, which invokes "the stated
  convention"): `|Fix_k(H)| = binom(N/h,k/h)(σ−1)^{(N−k)/h}` with `h = |H|`
  for an ARBITRARY subgroup `H ≤ Z_n^d`;
* (C) Corollary 7.2 (line 699): `binom(N,k)(σ−1)^{N−k}`, i.e. `h = 1`.
The convention, as worded, also governs every other binomial symbol after
line 524 (Gaussian binomials `[d r]_q` are a different symbol):
`n^{binom(r,2)}` in `F_d` of Theorem 6.1 (line 575, `r = 1,…,d`), the
Möbius values `(−1)^r p^{binom(r,2)}` (line 1144), and the restatements
`r_d(p,v) = p^{binom(v,2)}[d v]_p` (line 1120) and
`r_d(q,j) = q^{binom(j,2)}[d j]_q` (line 1213, Lemma `lem:coef`). There every
accompanying factor (`n^{binom(r,2)}`, `[d r]_n`, `σ^{n^{d−r}}`, …) has an
integer exponent, so these occurrences cannot produce a fractional exponent
and do not enter claim (i). They do not escape the convention, however:
`binom(1,2)` and `binom(0,2)` vanish (`2 ∉ {0,1}`; integer arguments do not
prevent this), and the `r = 1` summand of `F_d` does carry accompanying
factors, which the literal annihilation clause would wipe out — see the
PAPER ISSUE below. (Round 2 had wrongly claimed that these binomials "have
integer arguments and no accompanying factor" and lie outside the
convention; that justification is withdrawn.)

Formal: for `n ≥ 2`, `d ≥ 1`, `0 ≤ k ≤ N = n^d`, at each occurrence (T),
(P), (C): if `k/h` (a rational number) is an integer in `{0,…,N/h}`
(`BinomNonvanishing`), then `(N−k)/h` is an integer (`NoFracAt`).

Delta:
* all quotients are taken literally in `ℚ` (this Prop does not use the
  `ℕ`-division encoding of `kActiveSummand`/`fixKCountStatement`; it is
  the statement that justifies that encoding);
* "not fractional" is "is an integer" (`∃ m : ℤ`); under `k ≤ N` this is
  the same as "is a natural number", since `(N−k)/h ≥ 0`;
* (P) quantifies over every `AddSubgroup H` of `Lat n d` with
  `h = Nat.card H` (positive: `card_addSubgroup_pos`; the lattice is finite
  for `n ≥ 2`); (P) at `H = ⊥` already contains (C), which is listed
  separately only to mirror the paper; since every divisor of `n^d` is a
  subgroup order of `Z_n^d`, (P) is the claim for every divisor `h ∣ N`;
* rank vectors as in `rankVectors`; `σ` does not enter claim (i);
  parameter ranges `n ≥ 2`, `d ≥ 1`, `0 ≤ k ≤ N` are those of Theorem 5.1
  (Corollary 7.2 has the same ranges of `n`, `d`, `k`).
The presupposition of the parenthetical (such factors would otherwise
occur) is frozen separately as `fractionalExponentArisesStatement`.
Review history: round 1 (literal lens) found that the draft covered only
(T); repaired to (T) ∧ (P) ∧ (C), conclusion changed from `∃ m : ℕ` to the
literal `∃ m : ℤ`. Round 3 (literal lens) found the round-2 scope analysis
false and the PAPER ISSUE below missing; the scope paragraph is corrected
and the PAPER ISSUE recorded; the Prop body is unchanged (claim (i) is the
same under the literal and the restricted reading of the scope).
PAPER ISSUE (scope of the §5 convention, paper lines 523–527; confirmed by
definition-level brute force in `s05/r3/bf_repair_r3.py` and by the
`#guard`s at the end of this file; AUXILIARY Prop
`conventionScopeLiteralStatement`). As worded, "Here and below,
`binom(x,y):=0` whenever `y` is not an integer in `{0,…,x}`; a vanishing
binomial annihilates its whole summand" governs every later binomial, not
only `binom(N/h,k/h)`. The first clause alone is harmless: for integer
arguments it agrees with the ordinary binomial (`binom(r,2) = 0` iff
`r < 2`). The annihilation clause is not. In
`F_d(n,σ) = Σ_{r=1}^{d} (−1)^{r+1} n^{binom(r,2)} [d r]_n σ^{n^{d−r}}` of
Theorem 6.1 (line 575), `binom(1,2)` vanishes, so the literal rule
annihilates the whole `r = 1` summand `[d 1]_n σ^{n^{d−1}}`. The envelope so
read is `F_d − [d 1]_n σ^{n^{d−1}}`, which is STRICTLY below `|S_{n^d}|` at
every prime `n`. Hence "with equality if and only if `n` is prime" becomes
false. Examples: `(n,d,σ) = (2,1,2), (3,2,2), (2,3,2), (2,2,3)` give
`0, −6, −40, −6`, while the brute-force counts are `|S| = 2, 26, 72, 21`. At
`d = 2` it gives `−nσ` instead of `(n+1)σ^n − nσ`, so the sentence "For
`d=2` the statement is exactly Lemma E.21" fails too. A literal reader meets
the same question at the further occurrences listed under "Scope". At line
1213 (Lemma `lem:coef`), annihilating `r_d(q,1)` would contradict the use of
"`r_d(p,1) ≥ 1`" at line 1262 and the `j = 1` term of eq. `(decomp)`, line
1241. Inside Theorem 5.1 itself, `r_d(p_i,v_i)` is not expanded (its
definition, line 392, precedes "Here and below"). If it were expanded and
the rule applied, every summand with some `v_i ∈ {0,1}` would vanish. At
`n = 2`, `d = 1` that is the whole right-hand side. The formalization
encodes the evidently intended reading. In it, the convention governs only
`binom(N/h,k/h)` (Theorem 5.1 and its proof), `binom(N,k)` (Corollary 7.2,
never vanishing there since `0 ≤ k ≤ N`) and the binomials
`binom(n²/h,k/h)` of the cited 2019 Eqs. (29)–(33): see `kActiveSummand`,
`convTerm`, `convBinom`. Every other binomial is the ordinary one (e.g. the
`Nat.choose v 2` inside `rdCoeff`) and never annihilates. Claim (i) and
this Prop are the same under either reading. The paper should say instead
(suggested wording): "In Theorem 5.1, its proof and Corollary 7.2,
`binom(N/h, k/h) := 0` whenever `k/h` is not an integer in `{0,…,N/h}`, and
such a vanishing binomial annihilates its whole summand (so the
accompanying factor with fractional exponent never occurs); `0^0:=1`
(relevant only at `σ=1`, `k=N`)." Alternatively, it could keep "Here and
below" but restrict the annihilation clause to binomials whose lower index
is not an integer. Within Theorem 5.1 and Corollary 7.2, where
`0 ≤ k ≤ N`, the two versions agree. -/
def noFractionalExponentStatement : Prop :=
  ∀ n d k : ℕ, 2 ≤ n → 1 ≤ d → k ≤ n ^ d →
    -- (T) Theorem 5.1, line 538: `h = h(v)`, `v` a rank vector `≠ 0`
    (∀ v ∈ (rankVectors n d).erase 0, NoFracAt (n ^ d) k (hVec v)) ∧
    -- (P) proof of Theorem 5.1, line 549: `h = |H|`, `H ≤ Z_n^d` arbitrary
    (∀ H : AddSubgroup (Lat n d), NoFracAt (n ^ d) k (Nat.card H)) ∧
    -- (C) Corollary 7.2, line 699: `binom(N,k)(σ−1)^{N−k}`, `h = 1`
    NoFracAt (n ^ d) k 1

/-- **Presupposition of the §5 parenthetical "(so the accompanying factor
with fractional exponent never occurs)"** (paper lines 524–526; not a
numbered statement).

Paper (verbatim): "a vanishing binomial annihilates its whole summand (so
the accompanying factor with fractional exponent never occurs)".

The definite phrase "the accompanying factor with fractional exponent"
presupposes that, within the ranges the convention governs, summands really
exist whose binomial vanishes and whose power factor `(σ−1)^{(N−k)/h}` has a
fractional exponent (otherwise the parenthetical would be idle);
`noFractionalExponentStatement` is the assertion that such a factor is never
evaluated.

Formal: there are `n ≥ 2`, `d ≥ 1`, `0 ≤ k ≤ N = n^d`, (T) a rank vector
`v ≠ 0`, and (P) a subgroup `H ≤ Z_n^d` such that, for `h = h(v)` resp.
`h = |H|`, the binomial vanishes (`¬ BinomNonvanishing`, i.e. `k/h` is not
an integer in `{0,…,N/h}`) and `(N−k)/h` is not an integer. (Witness:
`n = d = 2`, `k = 2`, `v = (2)`, `H = Z_2²`, `h = 4`, `k/h = (N−k)/h = 1/2`;
the first witness in the order `(n, d, k)` is `n = 2`, `d = 1`, `k = 1`,
`h = 2`.)

Delta: quotients in `ℚ`; `σ` does not enter; (C) (`h = 1`) never has a
fractional exponent and is not included; one common `(n, d, k)` serves (T)
and (P) (the witness above does), which is at least as strong as two
separate existentials.
Review history: round 2 (exploit lens, optional item) — added.
PAPER ISSUE: none. -/
def fractionalExponentArisesStatement : Prop :=
  ∃ n d k : ℕ, 2 ≤ n ∧ 1 ≤ d ∧ k ≤ n ^ d ∧
    -- (T) Theorem 5.1, line 538: `h = h(v)`
    (∃ v ∈ (rankVectors n d).erase 0, ¬ BinomNonvanishing (n ^ d) k (hVec v) ∧
        ¬ IsIntQ ((((n ^ d : ℕ) : ℚ) - (k : ℚ)) / (hVec v : ℚ))) ∧
    -- (P) proof of Theorem 5.1, line 549: `h = |H|`
    (∃ H : AddSubgroup (Lat n d), ¬ BinomNonvanishing (n ^ d) k (Nat.card H) ∧
        ¬ IsIntQ ((((n ^ d : ℕ) : ℚ) - (k : ℚ)) / (Nat.card H : ℚ)))

/-- **Claim inside the §5 convention, part (ii), the "only" half** (paper
line 527; not a numbered statement).

Paper (verbatim): "and `0^0:=1` (relevant only at `σ=1`, `k=N`)".

Scope: the same occurrences (T), (P), (C) as in
`noFractionalExponentStatement` (the power `(σ−1)^{(N−k)/h}` exists only
there).

Formal: a power `0^0` can occur in a non-annihilated term
`binom(N/h,k/h)(σ−1)^{(N−k)/h}` only when `σ = 1` and `k = N`: for `n ≥ 2`,
`d ≥ 1`, `σ ≥ 1`, `0 ≤ k ≤ N`, at each occurrence, if `k/h` is an integer in
`{0,…,N/h}` and the base `σ − 1` and the exponent `(N − k)/h` are both `0`,
then `σ = 1` and `k = N` (`ZeroPowOnlyAt`; equivalently, `ZeroPowOccursAt`
forces `σ = 1 ∧ k = N`, `zeroPowOnlyAt_iff`).

Delta:
* quotients and the base `σ − 1` in `ℚ`; this is the "only" half of
  "relevant only at": outside `σ = 1, k = N` the convention is not invoked
  at all (no `0^0` is evaluated), which is the strongest form and implies
  that the value assigned to `0^0` is immaterial there; the positive half
  ("relevant at `σ = 1, k = N`") is `zeroPowOccursStatement` ∧
  `zeroPowMattersStatement`, and the whole claim is
  `zeroPowRelevanceStatement`;
* (T), (P): `σ ≥ 1` (Theorem 5.1 and its proof); (C): `σ ≥ 2`, the
  hypothesis of Corollary 7.2 (there `σ − 1 ≠ 0`, consistent with the
  claim; (P) at `H = ⊥` covers `h = 1` for every `σ ≥ 1` anyway);
* (P) over every `AddSubgroup H`, `h = Nat.card H`, as in part (i).
Review history: round 1 (literal lens) found that the draft covered only
(T); repaired to (T) ∧ (P) ∧ (C). Round 2 (exploit lens): this Prop (then
named `zeroPowRelevanceStatement`) froze only the "only" half; renamed,
body unchanged, positive half added as separate Props.
PAPER ISSUE: none. -/
def zeroPowOnlyStatement : Prop :=
  ∀ n d σ k : ℕ, 2 ≤ n → 1 ≤ d → 1 ≤ σ → k ≤ n ^ d →
    -- (T) Theorem 5.1, line 538
    (∀ v ∈ (rankVectors n d).erase 0, ZeroPowOnlyAt (n ^ d) σ k (hVec v)) ∧
    -- (P) proof of Theorem 5.1, line 549
    (∀ H : AddSubgroup (Lat n d), ZeroPowOnlyAt (n ^ d) σ k (Nat.card H)) ∧
    -- (C) Corollary 7.2, line 699 (hypothesis `σ ≥ 2`)
    (2 ≤ σ → ZeroPowOnlyAt (n ^ d) σ k 1)

/-- **Claim inside the §5 convention, part (ii), positive half: `0^0`
occurs at `σ = 1`, `k = N`** (paper line 527; not a numbered statement).

Paper (verbatim): "and `0^0:=1` (relevant only at `σ=1`, `k=N`)".

"Relevant only at `σ=1`, `k=N`" says, besides the "only" half
(`zeroPowOnlyStatement`), that the convention IS relevant there (otherwise
the paper would say it is never relevant). First component of that
relevance: the convention is actually invoked — the same reading as
"required" in the `banda2019…NeedsStatement`s.

Formal: for `n ≥ 2`, `d ≥ 1`, at `σ = 1` and `k = N = n^d`, EVERY occurrence
is a non-annihilated term whose power is `0^0` (`ZeroPowOccursAt`): (T) for
every rank vector `v ≠ 0` with `h = h(v)`, and (P) for every subgroup
`H ≤ Z_n^d` with `h = |H|`.

Delta: quotients and `σ − 1` in `ℚ`; `σ = 1`, `k = N` are substituted
(they satisfy the ranges `σ ≥ 1`, `0 ≤ k ≤ N` of Theorem 5.1); (C) is not
included: Corollary 7.2 assumes `σ ≥ 2`, so `σ = 1` never arises there
(the term `binom(N,N)(σ−1)^0` at `σ = 1` is (P) at `H = ⊥`); "every
occurrence" is stronger than "some occurrence" and is what holds.
Review history: round 2 (exploit lens) — added (missing positive half).
PAPER ISSUE: none. -/
def zeroPowOccursStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d →
    -- (T) Theorem 5.1, line 538: every rank vector `v ≠ 0`
    (∀ v ∈ (rankVectors n d).erase 0, ZeroPowOccursAt (n ^ d) 1 (n ^ d) (hVec v)) ∧
    -- (P) proof of Theorem 5.1, line 549: every subgroup `H`
    (∀ H : AddSubgroup (Lat n d), ZeroPowOccursAt (n ^ d) 1 (n ^ d) (Nat.card H))

/-- **Claim inside the §5 convention, part (ii), positive half: the value
of `0^0` matters at `σ = 1`, `k = N`** (paper line 527; not a numbered
statement).

Paper (verbatim): "and `0^0:=1` (relevant only at `σ=1`, `k=N`)".

Second component of "relevant at `σ=1`, `k=N`": the value the convention
assigns is decisive — Theorem 5.1 and the counting step of its proof give
the true counts there exactly when `0^0` is given the value `1`.

Formal: for `n ≥ 2`, `d ≥ 1`, the one-letter alphabet `Fin 1`, its state
`a`, and every integer `z` (the value assigned to `0^0`):
(T) `|S^a_{n^d,N}| = kActiveRHSZ z n d 1 N ↔ z = 1`;
(P) for every subgroup `H`, `|Fix_N(H)| = convTermZ z N N |H| 1 ↔ z = 1`,
where `kActiveRHSZ z`/`convTermZ z` are the right-hand sides of Theorem 5.1
and of `fixKCountStatement` with `0^0 := z` (literally the frozen
expressions otherwise; `kActiveRHSZ_one`, `convTermZ_one`).

Delta: `σ = 1`, `k = N` substituted; `0^0 := z` is modelled by `powZ`
(every power with base `0` and exponent `0` evaluates to `z`, all others
are ordinary powers); `|Fix_N(H)|` is the left side of `fixKCountStatement`
at `k = N`; (C) not included (as in `zeroPowOccursStatement`); the
direction `z = 1 →` is Theorem 5.1 / `fixKCountStatement` at `σ = 1`,
`k = N`. A reader who takes "relevant" in the narrower sense "has to be
evaluated" can drop this Prop (`zeroPowOccursStatement` is that sense).
Review history: round 2 (exploit lens, optional item: "with `0^0:=0` the
RHS would be `0` instead of `|S^a_N| = 1`") — added in the stronger form
"correct iff `z = 1`".
PAPER ISSUE: none. -/
def zeroPowMattersStatement : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 1 ≤ d → ∀ (a : Fin 1) (z : ℤ),
    -- (T) Theorem 5.1 at `σ = 1`, `k = N`
    ((numKActive n d 1 a (n ^ d) : ℤ) = kActiveRHSZ z n d 1 (n ^ d) ↔ z = 1) ∧
    -- (P) the counting step of its proof at `σ = 1`, `k = N`, every subgroup `H`
    (∀ H : AddSubgroup (Lat n d),
      ((Nat.card {s : Config n d (Fin 1) //
          s ∈ fixedBy (Fin 1) H ∧ cellsInState s a = n ^ d} : ℤ)
        = convTermZ z (n ^ d) (n ^ d) (Nat.card H) 1 ↔ z = 1))

/-- **Claim inside the §5 convention, part (ii), whole claim** (paper line
527): "`0^0:=1` (relevant only at `σ=1`, `k=N`)" = the "only" half
(`zeroPowOnlyStatement`) ∧ the convention is invoked at `σ = 1`, `k = N`
(`zeroPowOccursStatement`) ∧ its value matters there
(`zeroPowMattersStatement`). -/
def zeroPowRelevanceStatement : Prop :=
  zeroPowOnlyStatement ∧ zeroPowOccursStatement ∧ zeroPowMattersStatement

/-- All mathematical claims inside the §5 convention (lines 523–527): the
no-fractional-exponent assertion, its presupposition, and the three parts of
the `0^0` claim. -/
def conventionClaimsStatement : Prop :=
  noFractionalExponentStatement ∧ fractionalExponentArisesStatement ∧ zeroPowRelevanceStatement

/-! ### Scope of the §5 convention (AUXILIARY; supports the PAPER ISSUE in
`noFractionalExponentStatement`) -/

/-- `F_d(n,σ)` of Theorem 6.1 (paper line 575,
`F_d(n,σ) = Σ_{r=1}^{d} (−1)^{r+1} n^{binom(r,2)} [d r]_n σ^{n^{d−r}}`) read
with the §5 convention in its LITERAL scope ("Here and below … a vanishing
binomial annihilates its whole summand"). The summand with index `r` is
annihilated (set to `0`) when its binomial `binom(r,2)` vanishes. Otherwise
it is the summand of the project's frozen `lowerEnvelope` (Statement.lean),
the `F_d` of the certified Theorem 6.1, literally
`(−1)^{r+1}·rdCoeff n r d·σ^{n^{d−r}}` with `rdCoeff n r d = n^{binom(r,2)}·[d r]_n`.

"`binom(r,2)` vanishes" is encoded as `r.choose 2 = 0`. This is the
convention's value: for `2 ∈ {0,…,r}` the convention leaves the ordinary
binomial, which is `≥ 1`, and for `2 ∉ {0,…,r}`, i.e. `r < 2`, it sets the
binomial to `0`. `Nat.choose` has the same value in both cases
(`choose_two_eq_zero_iff`). The only annihilated index in `1,…,d` is
`r = 1` (`lowerEnvelopeLit_eq`). NOT the paper's intended envelope: used
only to state the PAPER ISSUE. -/
def lowerEnvelopeLit (n d σ : ℕ) : ℤ :=
  ∑ r ∈ Finset.Icc 1 d,
    if r.choose 2 = 0 then 0
    else (-1 : ℤ) ^ (r + 1) * (rdCoeff n r d : ℤ) * (σ : ℤ) ^ (n ^ (d - r))

/-- Faithfulness of the guard of `lowerEnvelopeLit`: `binom(r,2)` vanishes
exactly when `2 ∉ {0,…,r}`, i.e. `r < 2` (the §5 convention's first clause). -/
theorem choose_two_eq_zero_iff (r : ℕ) : r.choose 2 = 0 ↔ r < 2 :=
  Nat.choose_eq_zero_iff

/-- The literal-scope envelope differs from the frozen `F_d`
(`lowerEnvelope`) exactly by the annihilated `r = 1` summand
`n^{binom(1,2)}[d 1]_n σ^{n^{d−1}} = [d 1]_n σ^{n^{d−1}}`. -/
theorem lowerEnvelopeLit_eq {n d σ : ℕ} (hd : 1 ≤ d) :
    lowerEnvelopeLit n d σ
      = lowerEnvelope n d σ - (gaussBinom n d 1 : ℤ) * (σ : ℤ) ^ (n ^ (d - 1)) := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 d := Finset.mem_Icc.mpr ⟨le_rfl, hd⟩
  unfold lowerEnvelopeLit lowerEnvelope
  rw [← Finset.add_sum_erase _ _ h1, ← Finset.add_sum_erase _ _ h1]
  have hrest : ∀ r ∈ (Finset.Icc 1 d).erase 1,
      (if r.choose 2 = 0 then (0 : ℤ)
        else (-1 : ℤ) ^ (r + 1) * (rdCoeff n r d : ℤ) * (σ : ℤ) ^ (n ^ (d - r)))
        = (-1 : ℤ) ^ (r + 1) * (rdCoeff n r d : ℤ) * (σ : ℤ) ^ (n ^ (d - r)) := by
    intro r hr
    have hr2 : 2 ≤ r := by
      rcases Finset.mem_erase.mp hr with ⟨hne, hmem⟩
      have := (Finset.mem_Icc.mp hmem).1
      omega
    rw [if_neg (by rw [choose_two_eq_zero_iff]; omega)]
  rw [Finset.sum_congr rfl hrest]
  simp [rdCoeff]

/-- **AUXILIARY (supports the PAPER ISSUE on the scope of the §5 convention,
recorded in `noFractionalExponentStatement`; not a paper claim).**

Paper (verbatim, lines 523–527): "Here and below, `binom(x,y):=0` whenever
`y` is not an integer in `{0,…,x}`; a vanishing binomial annihilates its
whole summand"; (Theorem 6.1, lines 571–579): "For all `n≥2`, `d≥1`, `σ≥2`:
`|S_{n^d}| ≥ F_d(n,σ) := Σ_{r=1}^{d}(−1)^{r+1} n^{binom(r,2)} [d r]_n
σ^{n^{d−r}}`, with equality if and only if `n` is prime."

Formal: with `F_d` read under the literal scope of the convention
(`lowerEnvelopeLit`), (a) at EVERY prime `n` (and every `d ≥ 1`, `σ ≥ 2`)
the envelope is strictly below `|S_{n^d}|`; (b) consequently Theorem 6.1 so
read, i.e. "`F_d^{lit} ≤ |S_{n^d}|` with equality iff `n` is prime" for all
`n ≥ 2`, `d ≥ 1`, `σ ≥ 2`, is FALSE. ((b) follows from (a) at
`(n,d,σ) = (2,1,2)`, where `F_1^{lit} = 0 < 2 = |S_2|`.)

Delta: `|S_{n^d}|` is the shared `numSS n d σ` (alphabet `Fin σ`), cast to
`ℤ`. The hypotheses `n` prime (so `n ≥ 2`), `d ≥ 1`, `σ ≥ 2` are those of
Theorem 6.1. The body of (b) is the certified `lowerBoundStatement` with
`lowerEnvelope` replaced by `lowerEnvelopeLit`, conjoined over all
parameters and negated. The intended `F_d` (`lowerEnvelope`) satisfies
Theorem 6.1: that is the certified `lowerBound_proved`.
Evidence: `s05/r3/bf_repair_r3.py` (definition-level brute force of `|S|`
for 14 triples, among them `(2,1,2), (3,2,2), (2,3,2), (2,2,3), (2,4,2)`:
`F_lit = 0, −6, −40, −6, −768` against `|S| = 2, 26, 72, 21, 3072`), and the
`#guard`s at the end of this file (`bfKActive` sums, i.e. a definition-level
`|S|`, inside Lean). -/
def conventionScopeLiteralStatement : Prop :=
  -- (a) at every prime `n` the literal-scope envelope is strictly below `|S|`
  (∀ n d σ : ℕ, n.Prime → 1 ≤ d → 2 ≤ σ → lowerEnvelopeLit n d σ < (numSS n d σ : ℤ)) ∧
  -- (b) Theorem 6.1 with the literal-scope envelope is false
  ¬ (∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 2 ≤ σ →
      lowerEnvelopeLit n d σ ≤ (numSS n d σ : ℤ) ∧
        (lowerEnvelopeLit n d σ = (numSS n d σ : ℤ) ↔ n.Prime))

/-- **Proof-internal claim of Theorem 5.1** (paper lines 544–550; not a
numbered statement, frozen because it is the paper's key counting step).

Paper (verbatim): "For a subgroup `H≤A` with `|H|=h`, a configuration in
`Fix(H)` is a free labeling of the `N/h` cosets; it has exactly `k` cells in
state `a` iff exactly `k/h` cosets carry the label `a` --- possible only when
`h∣k` --- and the remaining `(N−k)/h` cosets carry labels from `Σ∖{a}`.
Hence `|Fix_k(H)|=binom(N/h, k/h)(σ−1)^{(N−k)/h}`, which is `0` under the
stated convention unless `h∣k`."

Formal: for `n ≥ 2`, `d ≥ 1`, `σ ≥ 1`, `0 ≤ k ≤ N`, every state `a` and every
subgroup `H ≤ Z_n^d`, writing `h = |H|`:
`#{s ∈ Fix(H) : s has exactly k cells in state a}
   = if (h ∣ k ∧ k/h ≤ N/h) then binom(N/h, k/h)·(σ−1)^{(N−k)/h} else 0`.

Delta: alphabet `Fin σ`; `Fix(H)` is the project's `fixedBy (Fin σ) H`;
`|H|` is `Nat.card H`; `Fix_k(H)` (not named in the paper beyond this
sentence) is read as `{s ∈ Fix(H) : exactly k cells in state a}`; the
binomial convention is encoded by the same guard as `kActiveSummand` (the
right side is literally `convTerm (n^d) k (Nat.card H) σ`); the guard is
PROVED equivalent to the paper's rational condition "`k/h` is an integer
in `{0,…,N/h}`" (`guard_iff_subgroup`); the `ℕ`-quotients are exact:
`n^d / Nat.card H` by Lagrange (`card_addSubgroup_dvd_pow`, proved), and
`k / Nat.card H`, `(n^d − k) / Nat.card H` under the guard (`h ∣ k`,
`k ≤ N`); the quantifier ranges (`n ≥ 2`, `d ≥ 1`, `σ ≥ 1`, `k ≤ N`) are
those of Theorem 5.1, whose proof this sentence is part of.
PAPER ISSUE: none (checked by brute force, see the group-05 draft report). -/
def fixKCountStatement : Prop :=
  ∀ n d σ k : ℕ, 2 ≤ n → 1 ≤ d → 1 ≤ σ → k ≤ n ^ d →
    ∀ (a : Fin σ) (H : AddSubgroup (Lat n d)),
      (Nat.card {s : Config n d (Fin σ) // s ∈ fixedBy (Fin σ) H ∧ cellsInState s a = k} : ℤ)
        = if Nat.card H ∣ k ∧ k / Nat.card H ≤ n ^ d / Nat.card H then
            ((n ^ d / Nat.card H).choose (k / Nat.card H) : ℤ)
              * ((σ : ℤ) - 1) ^ ((n ^ d - k) / Nat.card H)
          else 0

/-- **Theorem 5.1** (`thm:kactive`, paper lines 530–541; conventions of the
§5 preamble, lines 522–528).

Paper (verbatim, preamble): "Fix a state `a∈Σ` and let `S^a_{n^d,k}` be the
set of shift-symmetric configurations with exactly `k` cells in state `a`.
Here and below, `binom(x,y):=0` whenever `y` is not an integer in
`{0,…,x}`; a vanishing binomial annihilates its whole summand (so the
accompanying factor with fractional exponent never occurs), and `0^0:=1`
(relevant only at `σ=1`, `k=N`)."

Paper (verbatim, theorem): "For all `n≥2`, `d≥1`, `σ≥1`, `0≤k≤N=n^d`, with
`h(v)=∏_i p_i^{v_i}` (here, to avoid a clash with the active-cell count `k`,
the rank vectors run over `v∈{0,…,d}^{ω(n)}`, one coordinate per distinct
prime factor):
`|S^a_{n^d,k}| = Σ_{v∈{0,…,d}^{ω(n)}, v≠0} (−1)^{1+|v|} ∏_{i=1}^{ω(n)} r_d(p_i,v_i)
   binom(N/h(v), k/h(v)) (σ−1)^{(N−k)/h(v)}`."

Formal: `∀ n d σ k, 2 ≤ n → 1 ≤ d → 1 ≤ σ → k ≤ n^d → ∀ a : Fin σ,
|S^a_{n^d,k}| = kActiveRHS n d σ k` (in `ℤ`).

Delta:
* alphabet `Σ = Fin σ`, `a : Fin σ` quantified after `σ` (the paper fixes
  `a` before the theorem; the claim holds for every `a`; the right-hand
  side does not depend on `a`, exactly as in the paper);
* `|S^a_{n^d,k}|` is `numKActive` (`Nat.card` of the subtype);
* rank vectors are functions `n.primeFactors → {0,…,d}` (coordinates
  labelled by the primes, see `rankVectors`); `v ≠ 0` is `erase 0`;
* `r_d(p,v)` is `rdCoeff p v d = p^{C(v,2)}·gaussBinom p d v`;
* the binomial convention and `0^0 = 1`: see `kActiveSummand`; `ℕ`-divisions
  are exact (`hVec_dvd_pow`, guard `h(v) ∣ k`, `k ≤ N`); the convention is
  applied to `binom(N/h(v), k/h(v))` only, never to the `binom(v_i, 2)`
  inside `r_d(p_i, v_i)` (restricted reading of the §5 convention's scope);
* equality is stated in `ℤ` (the right-hand side is a signed sum).
PAPER ISSUE: none in the theorem itself (formula confirmed against
definition-level brute force for 31 parameter triples incl. `σ = 1` and
multi-prime `n = 6, 10, 12, 15`, every `a`, every `k`; see the draft
report). The preamble convention it relies on has an ill-posed scope as
worded. That PAPER ISSUE is recorded in `noFractionalExponentStatement`. It
does not touch this statement under the intended reading, which is the one
encoded here. -/
def kActiveStatement : Prop :=
  ∀ n d σ k : ℕ, 2 ≤ n → 1 ≤ d → 1 ≤ σ → k ≤ n ^ d →
    ∀ a : Fin σ, (numKActive n d σ a k : ℤ) = kActiveRHS n d σ k

/-- **Consistency claim of §5** (paper lines 556–559).

Paper (verbatim): "The theorem was verified exactly against
definition-level brute force (`n=2`, `d∈{3,4}`, `σ≤3`, all `k`) and against
the independent subgroup-level evaluator (`n≤6` at `d=3`; `n≤12` at `d=2`;
all `k`), including the consistency check `Σ_k|S^a_{n^d,k}|=|S_{n^d}|`."

Formal (the mathematical identity asserted by the consistency check): for
`n ≥ 2`, `d ≥ 1`, `σ ≥ 1` and every state `a`,
`Σ_{k=0}^{N} |S^a_{n^d,k}| = |S_{n^d}|`.

Delta: the range of `k` is `{0,…,N}` (`Finset.range (N+1)`), the range of
Theorem 5.1 (for `k > N` the set `S^a_{n^d,k}` is empty anyway); the
parameter ranges are those of Theorem 5.1 (the paper does not restate
them); `|S_{n^d}|` is the shared `numSS n d σ` (alphabet `Fin σ`); the
identity is stated for ALL parameters in that range, not only for the
finitely many triples the computation covered (it is a general fact: the
`S^a_{n^d,k}`, `0 ≤ k ≤ N`, partition `S_{n^d}`). The report of which
computations were run is NON-MATHEMATICAL (see the draft report).
PAPER ISSUE: none. -/
def kActiveConsistencyStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 1 ≤ σ → ∀ a : Fin σ,
    ∑ k ∈ Finset.range (n ^ d + 1), numKActive n d σ a k = numSS n d σ

/-- **AUXILIARY (formula-level form of the same consistency check; not a
separate paper claim).** What the paper's consistency check computes when
`|S^a_{n^d,k}|` is replaced by the right-hand side of Theorem 5.1 and
`|S_{n^d}|` by that of Theorem 4.3: for `n ≥ 2`, `d ≥ 1`, `σ ≥ 1`,
`Σ_{k=0}^{N} kActiveRHS n d σ k = enumerationRHS n d σ` (the frozen
right-hand side of Theorem 4.3, divisor-indexed).

It is implied by `kActiveStatement` + `kActiveConsistencyStatement` +
the certified `enumeration_proved`, and directly by the binomial theorem
(`Σ_j binom(N/h, j)(σ−1)^{N/h−j} = σ^{N/h}`, with `0^0 = 1` at `σ = 1`).
Delta: as for Theorem 5.1; equality in `ℤ`.
PAPER ISSUE: none. -/
def kActiveRHSConsistencyStatement : Prop :=
  ∀ n d σ : ℕ, 2 ≤ n → 1 ≤ d → 1 ≤ σ →
    ∑ k ∈ Finset.range (n ^ d + 1), kActiveRHS n d σ k = enumerationRHS n d σ

/-! ## The remark "This convention is also implicitly required by
Eqs. (29)–(33) of [banda2019]" (§5 preamble, paper lines 527–528)

The 2019 equations (Banda–Caughman–Cenek–Teuscher, arXiv:1703.09030v2,
§IV, p. 8; transcribed from
`scratchpad/research/references/banda_1703.09030.pdf`) concern the
two-dimensional lattice `Z_n × Z_n` (our `d = 2`, `N = n²`). 2019 notation
(paragraph before its Eq. (17), verbatim): "given any v, w ∈ Z^k, we write
v ⊴ w whenever the coordinates satisfy v_i ≤ w_i for every i (1 ≤ i ≤ k).
We write v ◁ w if v ⊴ w and v ≠ w. We denote the sum of the coordinates by
|v| = Σ_{i=1}^k v_i, and for any m ∈ Z, we write m for the k-tuple whose
coordinates all equal m." Eqs. (25)–(27): `D^a_{n×n,k} = {s ∈ Σ^{n×n} | #_a s = k}`,
`S^a_{n×n,k} = S_{n×n} ∩ D^a_{n×n,k}`, `S^a_{n×n,k}(v) = S_{n×n}(v) ∩ D^a_{n×n,k}`,
where (Eq. (3)) `S_{n×n}(v) = {s ∈ Σ^{n×n} | ∀u ∈ Z_n×Z_n ∀w ∈ ⟨v⟩ : s_u = s_{u⊕w}}`
and (Eq. (11)) `S_{n×n} = ⋃_{0≠v∈Z_n×Z_n} S_{n×n}(v)`.

In Eqs. (30)–(33) the letter `d` denotes `gcd(k, n)` (NOT our dimension) and
`r_1, …, r_{ω(d)}` its distinct primes. Representation: an index vector is a
function `(Nat.gcd k n).primeFactors → ℕ` (coordinates labelled by the
primes `r_i` themselves; every summand is symmetric under relabelling). -/

/-- `0 ◁ v ⊴ 2` (outer index set of 2019 Eqs. (31)–(33)): `v_i ∈ {0,1,2}`
for every prime `r_i ∣ gcd(k, n)`, `v ≠ 0`. -/
def idxTwo2019 (n k : ℕ) : Finset ((Nat.gcd k n).primeFactors → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range 3).erase 0

/-- `0 ◁ u ⊴ r + 1` (index set of 2019 Eq. (30)), `r = (r_1,…,r_{ω(d)})`:
`0 ≤ u_i ≤ r_i + 1`, `u ≠ 0`. -/
def idxThirty2019 (n k : ℕ) : Finset ((Nat.gcd k n).primeFactors → ℕ) :=
  (Fintype.piFinset fun r : (Nat.gcd k n).primeFactors => Finset.range ((r : ℕ) + 2)).erase 0

/-- `h(u) = ∏_{i=1}^{ω(d)} r_i^{min(u_i, 2)}` (2019, after Eq. (30); the same
formula defines `h(v)` after Eqs. (31) and (32)). -/
def h2019 {g : ℕ} (u : g.primeFactors → ℕ) : ℕ :=
  ∏ r : g.primeFactors, (r : ℕ) ^ min (u r) 2

/-- `top(v)` (2019, after Eq. (31)): "`top(i) = v_i` if `v_i < 2`,
`r_i + 1` if `v_i = 2`" (only used for `v_i ∈ {0,1,2}`). -/
def top2019 {g : ℕ} (v : g.primeFactors → ℕ) : g.primeFactors → ℕ :=
  fun r => if v r < 2 then v r else (r : ℕ) + 1

/-- `{u : v ⊴ u ⊴ top(v)}` (inner index set of 2019 Eq. (31)). -/
def idxInner2019 {g : ℕ} (v : g.primeFactors → ℕ) : Finset (g.primeFactors → ℕ) :=
  Fintype.piFinset fun r => Finset.Icc (v r) (top2019 v r)

/-- `r(i)` of 2019 Eqs. (32)–(33): `coef2019 q v_i` is "`1` if `v_i = 0`,
`q + 1` if `v_i = 1`, `q` if `v_i = 2`". The 2019 text prints it with
`q = p_i` (a prime of `n`); the evidently intended (and correct) reading is
`q = r_i`, the prime of `gcd(k, n)` the coordinate belongs to — used in
`eq32RHS`/`eq33RHS`; the printed reading is `eq32PrintedRHS`/`eq33PrintedRHS`
and is false (PAPER ISSUE in `banda2019Eq32ValidStatement`). The value `0`
for `v > 2` is never used. -/
def coef2019 (r v : ℕ) : ℕ :=
  if v = 0 then 1 else if v = 1 then r + 1 else if v = 2 then r else 0

/-- Right-hand side of 2019 Eq. (30) read with the §5 convention:
`Σ_{0◁u⊴r+1} (−1)^{1+|u|} (∏_i binom(r_i+1, u_i)) ×
binom(n²/h(u), k/h(u)) (|Σ|−1)^{(n²−k)/h(u)}`, `|Σ| = σ`. -/
def eq30RHS (n k σ : ℕ) : ℤ :=
  ∑ u ∈ idxThirty2019 n k,
    (-1 : ℤ) ^ (1 + absVec u)
      * (∏ r : (Nat.gcd k n).primeFactors, (((r : ℕ) + 1).choose (u r) : ℤ))
      * convTerm (n ^ 2) k (h2019 u) σ

/-- Right-hand side of 2019 Eq. (31) read with the §5 convention:
`Σ_{0◁v⊴2} Σ_{v⊴u⊴top(v)} (−1)^{1+|u|} binom(n²/h(v), k/h(v))
(|Σ|−1)^{(n²−k)/h(v)} × ∏_i binom(r_i+1, u_i)`. -/
def eq31RHS (n k σ : ℕ) : ℤ :=
  ∑ v ∈ idxTwo2019 n k, ∑ u ∈ idxInner2019 v,
    (-1 : ℤ) ^ (1 + absVec u) * convTerm (n ^ 2) k (h2019 v) σ
      * ∏ r : (Nat.gcd k n).primeFactors, (((r : ℕ) + 1).choose (u r) : ℤ)

/-- Right-hand side of 2019 Eq. (32) read with the §5 convention:
`Σ_{0◁v⊴2} (−1)^{1+|v|} binom(n²/h(v), k/h(v)) (|Σ|−1)^{(n²−k)/h(v)}
∏_i r(i)`. -/
def eq32RHS (n k σ : ℕ) : ℤ :=
  ∑ v ∈ idxTwo2019 n k,
    (-1 : ℤ) ^ (1 + absVec v) * convTerm (n ^ 2) k (h2019 v) σ
      * ∏ r : (Nat.gcd k n).primeFactors, (coef2019 r (v r) : ℤ)

/-- Right-hand side of 2019 Eq. (33) (`|Σ| = 2`) read with the §5
convention: `Σ_{0◁v⊴2} (−1)^{1+|v|} binom(n²/h(v), k/h(v)) ∏_i r(i)`. -/
def eq33RHS (n k : ℕ) : ℤ :=
  ∑ v ∈ idxTwo2019 n k,
    (-1 : ℤ) ^ (1 + absVec v) * convBinom (n ^ 2) k (h2019 v)
      * ∏ r : (Nat.gcd k n).primeFactors, (coef2019 r (v r) : ℤ)

/-- Integrality of `n²/h(u)` in the 2019 formulas: `h(u) ∣ n²` (every
`r_i ∣ gcd(k,n) ∣ n` and `min(u_i,2) ≤ 2`). -/
theorem h2019_dvd_sq (n k : ℕ) (u : (Nat.gcd k n).primeFactors → ℕ) : h2019 u ∣ n ^ 2 := by
  calc h2019 u = ∏ r : (Nat.gcd k n).primeFactors, (r : ℕ) ^ min (u r) 2 := rfl
    _ ∣ ∏ r : (Nat.gcd k n).primeFactors, (r : ℕ) ^ 2 :=
        Finset.prod_dvd_prod_of_dvd _ _ fun r _ => pow_dvd_pow _ (min_le_right _ _)
    _ = (∏ r : (Nat.gcd k n).primeFactors, (r : ℕ)) ^ 2 := Finset.prod_pow _ _ _
    _ = (∏ r ∈ (Nat.gcd k n).primeFactors, r) ^ 2 := by
        rw [Finset.prod_coe_sort (Nat.gcd k n).primeFactors (fun p => p)]
    _ ∣ (Nat.gcd k n) ^ 2 := pow_dvd_pow_of_dvd (Nat.prod_primeFactors_dvd _) 2
    _ ∣ n ^ 2 := pow_dvd_pow_of_dvd (Nat.gcd_dvd_right k n) 2

/-- `h(u) > 0`. -/
theorem h2019_pos {g : ℕ} (u : g.primeFactors → ℕ) : 0 < h2019 u :=
  Finset.prod_pos fun p _ => pow_pos (Nat.prime_of_mem_primeFactors p.2).pos _

/-- Faithfulness of the convention guard inside `eq30RHS`–`eq33RHS`: it is
exactly the rational condition "`k/h(u)` is an integer in `{0,…,n²/h(u)}`". -/
theorem guard_iff_2019 (n k : ℕ) (u : (Nat.gcd k n).primeFactors → ℕ) :
    (h2019 u ∣ k ∧ k / h2019 u ≤ n ^ 2 / h2019 u) ↔ BinomNonvanishing (n ^ 2) k (h2019 u) :=
  guard_iff_of_dvd (h2019_pos u) (h2019_dvd_sq n k u)

/-- **Remark, lines 527–528, "required", Eq. (29).**

Paper (verbatim): "This convention is also implicitly required by
Eqs.~(29)--(33) of \cite{banda2019}."
2019 Eq. (29) (verbatim): "For any a ∈ Σ, any k ∈ ℕ, and v ∈ Z_n × Z_n such
that |⟨v⟩| divides k, |S^a_{n×n,k}(v)| = binom(n²/|⟨v⟩|, k/|⟨v⟩|)
(|Σ| − 1)^{(n²−k)/|⟨v⟩|}."

Reading of "required" (common to the five `…NeedsStatement`s): within the
equation's own stated range there is a summand in which the §5 convention
is actually invoked, so that without it the formula is undefined. Because
Eq. (29) assumes `|⟨v⟩| ∣ k`, its binomial index `k/|⟨v⟩|` is always an
integer; the convention is invoked only through `0^0 := 1`, at `|Σ| = 1`,
`k = n²` (and, since Eq. (29) is stated for every `k ∈ ℕ`, through the
annihilation of `0^{(n²−k)/|⟨v⟩|}` with negative exponent at `|Σ| = 1`,
`k > n²`).

Formal: there are `n ≥ 2`, `σ ≥ 1`, `k`, `v ∈ Z_n²` with `|⟨v⟩| ∣ k` such that
the binomial of Eq. (29) does not vanish and its power factor is `0^0`
(base `σ − 1 = 0`, exponent `(n²−k)/|⟨v⟩| = 0`).

Delta: `|Σ| = σ ≥ 1` (2019 puts no hypothesis on `Σ`; a state set is
nonempty, and `|Σ| = 1` is not excluded); `n ≥ 2` (our standing assumption;
2019 takes `n ∈ ℕ`); `⟨v⟩` is `AddSubgroup.zmultiples v`, `|⟨v⟩|` its
`Nat.card`; quotients and `σ − 1` in `ℚ`.
PAPER ISSUE (minor, wording): see `banda2019ConventionStatement` — for
Eq. (29) "required" holds only through the degenerate one-letter alphabet
(`banda2019Eq29StandardStatement`). -/
def banda2019Eq29NeedsStatement : Prop :=
  ∃ n σ k : ℕ, ∃ v : Lat n 2, 2 ≤ n ∧ 1 ≤ σ ∧ Nat.card (AddSubgroup.zmultiples v) ∣ k ∧
    BinomNonvanishing (n ^ 2) k (Nat.card (AddSubgroup.zmultiples v)) ∧
    (σ : ℚ) - 1 = 0 ∧
    (((n ^ 2 : ℕ) : ℚ) - (k : ℚ)) / (Nat.card (AddSubgroup.zmultiples v) : ℚ) = 0

/-- **Remark, lines 527–528, "required", Eq. (30).**

2019 Eq. (30) (verbatim): "Pick n, k ∈ ℕ with k ≤ n and let d = gcd(k, n).
Let n = ∏_{i=1}^{ω(n)} p_i^{α_i}, k = ∏_{i=1}^{ω(k)} q_i^{β_i}, and
d = ∏_{i=1}^{ω(d)} r_i^{γ_i} be the prime factorizations of n, k, d,
respectively. Then for any a ∈ Σ, |S^a_{n×n,k}| = Σ_{0◁u⊴r+1} (−1)^{1+|u|}
(∏_{i=1}^{ω(d)} binom(r_i+1, u_i)) × binom(n²/h(u), k/h(u))
(|Σ| − 1)^{(n²−k)/h(u)}, where r = (r_1, …, r_{ω(d)}) and
h(u) = ∏_{i=1}^{ω(d)} r_i^{min(u_i,2)}."

Formal: there are `n ≥ 2` and `k ≤ n` (hence `k ≤ n²`) and an index
`u ∈ {0 ◁ u ⊴ r+1}` such that `k/h(u)` is NOT an integer (so the summand
contains `binom(n²/h(u), k/h(u))` with a non-integer lower index) and
`(n²−k)/h(u)` is NOT an integer (its accompanying power has a fractional
exponent). (Witness: `n = k = 2`, `u = (2)`, `h = 4`, `k/h = (n²−k)/h = 1/2`.)

Delta: index set `idxThirty2019`, `h(u)` = `h2019` (with the literal
`min(u_i, 2)`); quotients in `ℚ`; the witness is required to satisfy the
2019 range as printed (`k ≤ n`), which implies the evidently intended
range `k ≤ n²` (see `banda2019Eq30ValidStatement`), so the claim holds
under either reading. -/
def banda2019Eq30NeedsStatement : Prop :=
  ∃ n k : ℕ, 2 ≤ n ∧ k ≤ n ∧ ∃ u ∈ idxThirty2019 n k,
    ¬ IsIntQ ((k : ℚ) / (h2019 u : ℚ)) ∧
    ¬ IsIntQ ((((n ^ 2 : ℕ) : ℚ) - (k : ℚ)) / (h2019 u : ℚ))

/-- **Remark, lines 527–528, "required", Eq. (31).**

2019 Eq. (31) (verbatim): "|S^a_{n×n,k}| = Σ_{0◁v⊴2, v⊴u⊴top(v)} (−1)^{1+|u|}
binom(n²/h(v), k/h(v)) (|Σ| − 1)^{(n²−k)/h(v)} × ∏_{i=1}^{ω(d)} binom(r_i+1, u_i),
where h(v) = ∏_{i=1}^{ω(d)} r_i^{min(v_i,2)} and top(v) ∈ Z^{ω(d)} has ith
coordinate top(i) = v_i if v_i < 2, r_i + 1 if v_i = 2."

Formal: there are `n ≥ 2`, `k ≤ n` and indices `v ∈ {0◁v⊴2}`,
`u ∈ {v⊴u⊴top(v)}` (so the summand exists) with `k/h(v)` and `(n²−k)/h(v)`
both non-integers. Delta: as for Eq. (30); the setting (`n`, `k`, `d`, `r_i`)
is that of Eq. (30). -/
def banda2019Eq31NeedsStatement : Prop :=
  ∃ n k : ℕ, 2 ≤ n ∧ k ≤ n ∧ ∃ v ∈ idxTwo2019 n k, ∃ _u ∈ idxInner2019 v,
    ¬ IsIntQ ((k : ℚ) / (h2019 v : ℚ)) ∧
    ¬ IsIntQ ((((n ^ 2 : ℕ) : ℚ) - (k : ℚ)) / (h2019 v : ℚ))

/-- **Remark, lines 527–528, "required", Eq. (32).**

2019 Eq. (32) (verbatim): "|S^a_{n×n,k}| = Σ_{0◁v⊴2} (−1)^{1+|v|}
binom(n²/h(v), k/h(v)) (|Σ| − 1)^{(n²−k)/h(v)} ∏_{i=1}^{ω(d)} r(i), where
h(v) = ∏_{i=1}^{ω(d)} r_i^{min(v_i,2)} and r(i) = 1 if v_i = 0, p_i + 1 if
v_i = 1, p_i if v_i = 2."

Formal: there are `n ≥ 2`, `k ≤ n` and `v ∈ {0◁v⊴2}` with `k/h(v)` and
`(n²−k)/h(v)` both non-integers. Delta: as for Eq. (30). -/
def banda2019Eq32NeedsStatement : Prop :=
  ∃ n k : ℕ, 2 ≤ n ∧ k ≤ n ∧ ∃ v ∈ idxTwo2019 n k,
    ¬ IsIntQ ((k : ℚ) / (h2019 v : ℚ)) ∧
    ¬ IsIntQ ((((n ^ 2 : ℕ) : ℚ) - (k : ℚ)) / (h2019 v : ℚ))

/-- **Remark, lines 527–528, "required", Eq. (33).**

2019 Eq. (33) (verbatim): "As a special case, it can be shown that the
number of binary symmetric configurations (|Σ| = 2) with k sites in state a
is |S^a_{n×n,k}| = Σ_{0◁v⊴2} (−1)^{1+|v|} binom(n²/h(v), k/h(v)) ∏_{i=1}^{ω(d)} r(i)."

Formal: there are `n ≥ 2`, `k ≤ n` and `v ∈ {0◁v⊴2}` with `k/h(v)` not an
integer (Eq. (33) has no power factor, so only the binomial part of the
convention is at stake). Delta: as for Eq. (30). -/
def banda2019Eq33NeedsStatement : Prop :=
  ∃ n k : ℕ, 2 ≤ n ∧ k ≤ n ∧ ∃ v ∈ idxTwo2019 n k,
    ¬ IsIntQ ((k : ℚ) / (h2019 v : ℚ))

/-- **Remark, lines 527–528, "required" — all five equations.** -/
def banda2019NeedsStatement : Prop :=
  banda2019Eq29NeedsStatement ∧ banda2019Eq30NeedsStatement ∧ banda2019Eq31NeedsStatement ∧
    banda2019Eq32NeedsStatement ∧ banda2019Eq33NeedsStatement

/-- **Remark, lines 527–528, presupposition, Eq. (29)**: read with the §5
convention, 2019 Eq. (29) is correct.

Formal: for `n ≥ 2`, `σ ≥ 1`, every `a`, every `k ∈ ℕ` and every
`v ∈ Z_n × Z_n` with `|⟨v⟩| ∣ k`:
`|S_{n×n}(v) ∩ D^a_{n×n,k}| = binom(n²/|⟨v⟩|, k/|⟨v⟩|)(σ−1)^{(n²−k)/|⟨v⟩|}`
under the convention (`convTerm`).

Delta: `S_{n×n}(v)` (2019 Eq. (3), "∀u ∀w ∈ ⟨v⟩ : s_u = s_{u⊕w}") is the
project's `fixedBy (Fin σ) (AddSubgroup.zmultiples v)` (`{s | ∀ w ∈ H,
shift w s = s}`, `shift w s u = s (u + w)`); `D^a_{n×n,k}` is
`cellsInState s a = k`; `|⟨v⟩| = Nat.card (zmultiples v)`; `k` ranges over
ALL of `ℕ`, as in 2019 (for `k > n²` the guard fails: both sides are `0`);
the right side is `convTerm`, whose guard is the rational condition
(`guard_iff_subgroup`) and whose quotients are exact (Lagrange); `n ≥ 2`,
`σ ≥ 1` as in `banda2019Eq29NeedsStatement`. This is the `d = 2`,
`H = ⟨v⟩` case of `fixKCountStatement`, extended from `k ≤ N` to every `k`. -/
def banda2019Eq29ValidStatement : Prop :=
  ∀ n σ k : ℕ, 2 ≤ n → 1 ≤ σ → ∀ (a : Fin σ) (v : Lat n 2),
    Nat.card (AddSubgroup.zmultiples v) ∣ k →
      (Nat.card {s : Config n 2 (Fin σ) //
          s ∈ fixedBy (Fin σ) (AddSubgroup.zmultiples v) ∧ cellsInState s a = k} : ℤ)
        = convTerm (n ^ 2) k (Nat.card (AddSubgroup.zmultiples v)) σ

/-- **Remark, lines 527–528, presupposition, Eq. (30)**: read with the §5
convention, 2019 Eq. (30) is correct: for `n ≥ 2`, `σ ≥ 1`, `0 ≤ k ≤ n²`,
every `a`: `|S^a_{n×n,k}| = eq30RHS n k σ`.

Delta: `|S^a_{n×n,k}| = |S_{n×n} ∩ D^a_{n×n,k}|` is `numKActive n 2 σ a k`
(2019's `S_{n×n} = ⋃_{v≠0} S_{n×n}(v)` is `IsShiftSymmetric`); `|Σ| = σ`,
alphabet `Fin σ`; equality in `ℤ`. Range of `k`: 2019 prints "k ≤ n", evidently
a typo for `k ≤ n²` (its Eq. (34) uses `|S^a_{n×n,k}|` for every
`0 ≤ k ≤ n²`); the intended range is frozen, which implies the printed one.
The factorization of `k` named in the 2019 preamble is not used by the
formula (only the primes of `d = gcd(k,n)` enter); `k = 0` is included
(2019's Eq. (34) sums from `k = 0`), with `d = gcd(0, n) = n`
(`Nat.gcd 0 n = n`). This concerns the 2019 paper, not the present one.
PAPER ISSUE (minor, typo in [banda2019]; it does not make the printed
equation false, only narrower than its use in Eq. (34)): "k ≤ n" should read
"k ≤ n²". -/
def banda2019Eq30ValidStatement : Prop :=
  ∀ n σ k : ℕ, 2 ≤ n → 1 ≤ σ → k ≤ n ^ 2 → ∀ a : Fin σ,
    (numKActive n 2 σ a k : ℤ) = eq30RHS n k σ

/-- **Remark, lines 527–528, presupposition, Eq. (31)**: read with the §5
convention, 2019 Eq. (31) is correct: for `n ≥ 2`, `σ ≥ 1`, `0 ≤ k ≤ n²`,
every `a`: `|S^a_{n×n,k}| = eq31RHS n k σ`. Delta: as for Eq. (30);
`top(v)` is `top2019`, the inner range `idxInner2019`. -/
def banda2019Eq31ValidStatement : Prop :=
  ∀ n σ k : ℕ, 2 ≤ n → 1 ≤ σ → k ≤ n ^ 2 → ∀ a : Fin σ,
    (numKActive n 2 σ a k : ℤ) = eq31RHS n k σ

/-- **Remark, lines 527–528, presupposition, Eq. (32)**: read with the §5
convention, 2019 Eq. (32) is correct: for `n ≥ 2`, `σ ≥ 1`, `0 ≤ k ≤ n²`,
every `a`: `|S^a_{n×n,k}| = eq32RHS n k σ`.

Delta: as for Eq. (30); `r(i)` is read with the primes `r_i` of
`d = gcd(k,n)` (`coef2019 r_i v_i`), the evidently intended reading — see the
PAPER ISSUE.

PAPER ISSUE (misprint in [banda2019], Eq. (32) as printed is FALSE; it
affects the presupposition (b) of our lines 527–528, see
`banda2019ConventionStatement`): the 2019 text defines `r(i) = 1, p_i + 1, p_i`
(for `v_i = 0, 1, 2`) with `p_i`, the primes of `n` (2019 preamble of
Eq. (30): `n = ∏_{i=1}^{ω(n)} p_i^{α_i}`), while the product runs over
`i = 1, …, ω(d)` and `h(v)` uses the primes `r_i` of `d`. As printed the formula
is well defined (`ω(d) ≤ ω(n)`, so `p_1, …, p_{ω(d)}` exist) but wrong: with
the primes in increasing order, `n = 6`, `k = 3`, `|Σ| = 2` gives `36`, while
`|S^a_{6×6,3}| = 48` (the 4 subgroups of order 3 each fix `binom(12,1) = 12`
configurations with 3 cells in state `a`, with no overlaps; definition-level
brute force agrees); for EVERY labelling of the primes of `n = 6` some
`k ≤ 6` fails (`banda2019Eq32PrintedFalseStatement`). Eq. (32) should read
`r(i) = 1, r_i + 1, r_i`; this intended reading is what is frozen here, and
it is correct (brute force; `#guard`s below). The printed reading coincides
with the intended one whenever every coordinate `r_i` is paired with
`p_i = r_i` (`eq32PrintedRHS_eq_of`), e.g. for prime-power `n`. This misprint
is not covered by the erratum draft `research/fix_note/banda2d_bounds_fix.tex`.
Review history: round 1 had justified the `r_i` reading by claiming the
printed formula is "not even well-indexed when ω(d) < ω(n)"; that claim was
false (round-2 exploit review) and is withdrawn. -/
def banda2019Eq32ValidStatement : Prop :=
  ∀ n σ k : ℕ, 2 ≤ n → 1 ≤ σ → k ≤ n ^ 2 → ∀ a : Fin σ,
    (numKActive n 2 σ a k : ℤ) = eq32RHS n k σ

/-- **Remark, lines 527–528, presupposition, Eq. (33)**: read with the §5
convention, 2019 Eq. (33) is correct: for `n ≥ 2`, `|Σ| = 2`, `0 ≤ k ≤ n²`,
every `a`: `|S^a_{n×n,k}| = eq33RHS n k`.

Delta: as for Eq. (32) (`r(i)` read with the primes `r_i` of `gcd(k,n)`);
alphabet `Fin 2`.

PAPER ISSUE (misprint in [banda2019], Eq. (33) as printed is FALSE): Eq. (33)
uses the same `r(i) = 1, p_i + 1, p_i` as Eq. (32). As printed it is wrong:
with the primes in increasing order, `n = 6`, `k = 3` gives `36`, while
`|S^a_{6×6,3}| = 48` (for every labelling of the primes of `n = 6` some
`k ≤ 6` fails: `banda2019Eq33PrintedFalseStatement`). It should read
`r(i) = 1, r_i + 1, r_i`; the intended reading is frozen. -/
def banda2019Eq33ValidStatement : Prop :=
  ∀ n k : ℕ, 2 ≤ n → k ≤ n ^ 2 → ∀ a : Fin 2,
    (numKActive n 2 2 a k : ℤ) = eq33RHS n k

/-- **Remark, lines 527–528, presupposition — all five equations**, with
Eqs. (32)–(33) in their evidently intended reading (`r(i)` built from the
primes `r_i` of `gcd(k,n)`).

PAPER ISSUE (inherited from the parts): Eqs. (32)–(33) of [banda2019] as
printed (`r(i)` with the primes `p_i` of `n`) are false (`n = 6`, `k = 3`,
`|Σ| = 2`: `36 ≠ 48`; see `banda2019Eq32ValidStatement`,
`banda2019Eq33ValidStatement`, `banda2019Eq32/33PrintedFalseStatement`).
Eqs. (29)–(31) are correct as printed (read with the §5 convention; the
range "k ≤ n" of Eq. (30) is a typo for "k ≤ n²", see
`banda2019Eq30ValidStatement`). -/
def banda2019ValidStatement : Prop :=
  banda2019Eq29ValidStatement ∧ banda2019Eq30ValidStatement ∧ banda2019Eq31ValidStatement ∧
    banda2019Eq32ValidStatement ∧ banda2019Eq33ValidStatement

/-- **AUXILIARY (supports the PAPER ISSUE below; not a paper claim).** For
`|Σ| ≥ 2`, Eq. (29) needs no part of the §5 convention: whenever
`|⟨v⟩| ∣ k`, both binomial arguments `n²/|⟨v⟩|` and `k/|⟨v⟩|` are natural
numbers (an ordinary binomial, `0` for `k > n²` by the standard
definition), the exponent `(n²−k)/|⟨v⟩|` is an integer and the base `σ − 1`
is nonzero (an ordinary integer power of a nonzero rational).
Delta: quotients and `σ − 1` in `ℚ`; `n ≥ 2`; every `k ∈ ℕ`, as in Eq. (29). -/
def banda2019Eq29StandardStatement : Prop :=
  ∀ n σ k : ℕ, 2 ≤ n → 2 ≤ σ → ∀ v : Lat n 2, Nat.card (AddSubgroup.zmultiples v) ∣ k →
    (∃ x j : ℕ, (x : ℚ) = ((n ^ 2 : ℕ) : ℚ) / (Nat.card (AddSubgroup.zmultiples v) : ℚ) ∧
        (j : ℚ) = (k : ℚ) / (Nat.card (AddSubgroup.zmultiples v) : ℚ)) ∧
      IsIntQ ((((n ^ 2 : ℕ) : ℚ) - (k : ℚ)) / (Nat.card (AddSubgroup.zmultiples v) : ℚ)) ∧
      (σ : ℚ) - 1 ≠ 0

/-! ### 2019 Eqs. (32)–(33) AS PRINTED (`r(i)` with `p_i`) — supports PAPER
ISSUE 2 of `banda2019ConventionStatement`. The 2019 text names the primes of
`n` as `p_1, …, p_{ω(n)}` and those of `d = gcd(k,n)` as `r_1, …, r_{ω(d)}`
without fixing an order; a labelling is modelled by a list. -/

/-- `L` lists the distinct primes of `m`, each exactly once, in some order
(a labelling `p_1, …, p_{ω(m)}` of the prime factorization of `m`). -/
def IsPrimeListing (m : ℕ) (L : List ℕ) : Prop :=
  L.Nodup ∧ ∀ p : ℕ, p ∈ L ↔ p ∈ m.primeFactors

/-- Right-hand side of 2019 Eq. (32) AS PRINTED, read with the §5
convention, for a labelling `P = [p_1, …, p_{ω(n)}]` of the primes of `n` and
a labelling `R = [r_1, …, r_{ω(d)}]` of the primes of `d = gcd(k,n)`: the
coordinate belonging to `r_i` (position `i` of `R`) contributes the printed
`r(i)`, built from `p_i` (position `i` of `P`), while `h(v)` uses `r_i`.
(For labellings, `i < ω(d) ≤ ω(n)`, so `List.getD … 0` never falls back.) -/
def eq32PrintedRHS (n k σ : ℕ) (P R : List ℕ) : ℤ :=
  ∑ v ∈ idxTwo2019 n k,
    (-1 : ℤ) ^ (1 + absVec v) * convTerm (n ^ 2) k (h2019 v) σ
      * ∏ r : (Nat.gcd k n).primeFactors, (coef2019 (P.getD (R.idxOf (r : ℕ)) 0) (v r) : ℤ)

/-- Right-hand side of 2019 Eq. (33) (`|Σ| = 2`) AS PRINTED, as in
`eq32PrintedRHS`. -/
def eq33PrintedRHS (n k : ℕ) (P R : List ℕ) : ℤ :=
  ∑ v ∈ idxTwo2019 n k,
    (-1 : ℤ) ^ (1 + absVec v) * convBinom (n ^ 2) k (h2019 v)
      * ∏ r : (Nat.gcd k n).primeFactors, (coef2019 (P.getD (R.idxOf (r : ℕ)) 0) (v r) : ℤ)

/-- The printed reading of Eq. (32) equals the frozen (intended) one when
every coordinate `r_i` is paired with `p_i = r_i` (a sufficient condition;
other labellings can agree by coincidence at single `k`, e.g. `k = 0`). -/
theorem eq32PrintedRHS_eq_of {n k σ : ℕ} {P R : List ℕ}
    (h : ∀ r : (Nat.gcd k n).primeFactors, P.getD (R.idxOf (r : ℕ)) 0 = r) :
    eq32PrintedRHS n k σ P R = eq32RHS n k σ := by
  unfold eq32PrintedRHS eq32RHS
  simp only [h]

/-- The same for Eq. (33). -/
theorem eq33PrintedRHS_eq_of {n k : ℕ} {P R : List ℕ}
    (h : ∀ r : (Nat.gcd k n).primeFactors, P.getD (R.idxOf (r : ℕ)) 0 = r) :
    eq33PrintedRHS n k P R = eq33RHS n k := by
  unfold eq33PrintedRHS eq33RHS
  simp only [h]

/-- **AUXILIARY (supports PAPER ISSUE 2 of `banda2019ConventionStatement`;
not a paper claim): 2019 Eq. (32) as printed is false**, whatever labelling
of the primes is chosen.

Formal: there are `n ≥ 2`, `σ ≥ 1` and a state `a` such that for EVERY
labelling `P` of the primes of `n` there is a `k` with `k ≤ n` (the 2019
range as printed, which implies `k ≤ n²`) such that for EVERY labelling `R`
of the primes of `gcd(k,n)`: `|S^a_{n×n,k}| ≠ eq32PrintedRHS n k σ P R`.
(Witness: `n = 6`, `σ = 2`; `k = 3` if `p_1 = 2` (printed `36`, true `48`),
`k = 2` if `p_1 = 3` (printed `72`, true `54`); there `ω(gcd) = 1`, so `R`
is forced.)

Delta: a formula stated for "the prime factorizations" of `n`, `k`, `d` has
to hold for every labelling of the primes; the Prop shows more — it fails
even when the labelling of `n` is fixed before `k` is chosen and the
labelling of `gcd(k,n)` is arbitrary. (A labelling chosen after `k` so as
to pair every `r_i` with `p_i = r_i` always reproduces the true count; that
is the intended `r_i` reading, `eq32PrintedRHS_eq_of`.) `|S^a_{n×n,k}|` is
`numKActive n 2 σ a k`; equality in `ℤ`. -/
def banda2019Eq32PrintedFalseStatement : Prop :=
  ∃ n σ : ℕ, 2 ≤ n ∧ 1 ≤ σ ∧ ∃ a : Fin σ, ∀ P : List ℕ, IsPrimeListing n P →
    ∃ k : ℕ, k ≤ n ∧ ∀ R : List ℕ, IsPrimeListing (Nat.gcd k n) R →
      (numKActive n 2 σ a k : ℤ) ≠ eq32PrintedRHS n k σ P R

/-- **AUXILIARY (supports PAPER ISSUE 2; not a paper claim): 2019 Eq. (33)
as printed is false**, in the same labelling-robust form as
`banda2019Eq32PrintedFalseStatement`, with `|Σ| = 2` (alphabet `Fin 2`).
(Witness: `n = 6`; `k = 3` if `p_1 = 2` (printed `36`, true `48`), `k = 2` if
`p_1 = 3` (printed `72`, true `54`).) -/
def banda2019Eq33PrintedFalseStatement : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ ∃ a : Fin 2, ∀ P : List ℕ, IsPrimeListing n P →
    ∃ k : ℕ, k ≤ n ∧ ∀ R : List ℕ, IsPrimeListing (Nat.gcd k n) R →
      (numKActive n 2 2 a k : ℤ) ≠ eq33PrintedRHS n k P R

/-- **Remark "This convention is also implicitly required by Eqs. (29)–(33)
of [banda2019]"** (§5 preamble, paper lines 527–528), whole sentence.

Paper (verbatim): "This convention is also implicitly required by
Eqs.~(29)--(33) of \cite{banda2019}."

Reading: (a) "required" — in each of Eqs. (29)–(33) the convention is
actually invoked within the equation's stated range, so the formula is
undefined without it (`banda2019NeedsStatement`): for Eqs. (30)–(33) a
binomial `binom(n²/h, k/h)` with non-integer `k/h` occurs (and, in (30)–(32),
a power with fractional exponent); for Eq. (29) only `0^0` at `|Σ| = 1`;
(b) "implicitly required" presupposes that, read with the convention, the
formulas are correct (`banda2019ValidStatement`, with Eqs. (32)–(33) in their
evidently intended reading — see PAPER ISSUE 2). Both are frozen; a reader
who takes only (a) as the content of the sentence can ignore (b).

Delta: `d = 2` (the 2019 paper is two-dimensional); see the docstrings of
the parts for all representation choices (index sets, `h`, `top`, `r(i)`,
`|⟨v⟩|`, alphabet `Fin σ`, quotients in `ℚ`).

PAPER ISSUE 1 (minor, wording; confirmed by `bf_repair_r1.py`): Eq. (29) of
[banda2019] carries the hypothesis "`|⟨v⟩|` divides `k`", so its binomial
index is always an integer and it never needs the non-integer-index part
of the convention; it needs the convention only for `0^0 := 1` (and for the
annihilation of `0^{(n²−k)/|⟨v⟩|}`, `k > n²`), i.e. only for the one-letter
alphabet `|Σ| = 1`; for `|Σ| ≥ 2` it is meaningful with the standard
binomial (`banda2019Eq29StandardStatement`). The sentence is true as
written (`banda2019Eq29NeedsStatement` holds via `|Σ| = 1`) but
overstated for Eq. (29).

PAPER ISSUE 2 (the cited equations; confirmed by `bf_repair_r2.py` and the
`#guard`s below): reading (b) presupposes that Eqs. (29)–(33), read with the
convention, are correct. Eqs. (32)–(33) of [banda2019] are FALSE as printed:
their `r(i) = 1, p_i + 1, p_i` uses the primes `p_i` of `n` instead of the
primes `r_i` of `gcd(k,n)` (`n = 6`, `k = 3`, `|Σ| = 2`: `36 ≠ 48 =
|S^a_{6×6,3}|`, primes in increasing order; for every labelling of the primes
of `6` some `k ≤ 6` fails: `banda2019Eq32PrintedFalseStatement`,
`banda2019Eq33PrintedFalseStatement`). With `r_i` in place of `p_i` they are
correct (`banda2019Eq32ValidStatement`, `banda2019Eq33ValidStatement`, which
freeze that reading). The misprint is not covered by the erratum draft
`research/fix_note/banda2d_bounds_fix.tex`.

Suggested wording (both issues): "This convention is also implicitly
required by Eqs. (30)–(33) of [banda2019] (in (32)–(33) read `r(i)` with the
primes `r_i` of `gcd(k,n)` in place of `p_i`), whose summands include
binomials with non-integer lower index (Eq. (29) needs only `0^0 := 1`, at
`|Σ| = 1`)."
Review history: round 1 (numeric lens) — the draft had labelled this
sentence NON-MATHEMATICAL; it is now frozen. Round 2 (exploit lens) — PAPER
ISSUE 2 added (Eqs. (32)–(33) misprint). -/
def banda2019ConventionStatement : Prop :=
  banda2019NeedsStatement ∧ banda2019ValidStatement

/-- **Corollary 7.2, displayed formula** (`cor:dens`, paper lines 693–702).

Paper (verbatim): "Let `σ≥2`. Under the density-uniform distribution
(first draw `k∈{0,…,N}` uniformly, then a configuration with exactly `k`
cells in state `a` uniformly),
`P^dens_{n^d} = (1/(N+1)) Σ_{k=0}^{N} |S^a_{n^d,k}| / (binom(N,k)(σ−1)^{N−k})`,
with `|S^a_{n^d,k}|` given by Theorem 5.1."

Formal: for `n ≥ 2`, `d ≥ 1`, `σ ≥ 2` and every state `a`,
`probDens n d σ a = (1/(N+1)) · Σ_{k=0}^{N} |S^a_{n^d,k}| / (binom(N,k)·(σ−1)^{N−k})`
in `ℝ`, where `probDens` is the probability of `S_{n^d}` under the
two-stage `PMF` `densPMF` (uniform `k ∈ Fin (N+1)`, then uniform on
`C^a_k = {s : exactly k cells in state a}`, composed by `PMF.bind`).

Delta:
* the distribution is modelled literally as the mathlib `PMF`
  `densPMF` (see its docstring); `P^dens` is the outer measure of
  `{s | IsShiftSymmetric s}`, converted by `ENNReal.toReal` (faithful, the
  value is `≤ 1`);
* `n ≥ 2`, `d ≥ 1` come from the paper's standing assumptions (Definition
  "Lattice and configurations", line 201); `σ ≥ 2` is the corollary's
  hypothesis and is also what makes the distribution well defined
  (`configsWithK_nonempty`);
* the dependence on `a` (implicit in the paper's notation `P^dens_{n^d}`)
  is explicit; the claim is made for every `a`;
* real division: every denominator `binom(N,k)(σ−1)^{N−k}` is a positive
  integer for `σ ≥ 2`, `0 ≤ k ≤ N`, so the `x/0 = 0` trap cannot fire;
  `N − k` is `ℕ`-subtraction with `k ≤ N` (exact); `σ − 1` is in `ℝ`;
* the `NeZero n` instance needed for the finite configuration space is
  built from `2 ≤ n` inside the statement.
PAPER ISSUE (minor, wording): `P^dens_{n^d}` is never defined in words;
by analogy with Corollary 7.1 (`P^unif`) and the section title it is the
probability that the drawn configuration is shift-symmetric — formalized
so. Suggested wording: "…, the probability `P^dens_{n^d}` that the drawn
configuration lies in `S_{n^d}` is …". Mathematically the formula is
correct (exact check by enumerating the two-stage distribution, see the
draft report). -/
def densityStatement : Prop :=
  ∀ n d σ : ℕ, ∀ hn : 2 ≤ n, 1 ≤ d → ∀ (hσ : 2 ≤ σ) (a : Fin σ),
    haveI : NeZero n := ⟨by omega⟩
    probDens n d σ hσ a
      = (1 / ((n ^ d : ℕ) + 1 : ℝ))
          * ∑ k ∈ Finset.range (n ^ d + 1),
              (numKActive n d σ a k : ℝ)
                / (((n ^ d).choose k : ℝ) * ((σ : ℝ) - 1) ^ (n ^ d - k))

/-- **Corollary 7.2, closed form** ("with `|S^a_{n^d,k}|` given by
Theorem 5.1", paper line 701): for `n ≥ 2`, `d ≥ 1`, `σ ≥ 2` and every
state `a`,
`probDens n d σ a = (1/(N+1)) · Σ_{k=0}^{N} kActiveRHS(n,d,σ,k) / (binom(N,k)·(σ−1)^{N−k})`.

Delta: as for `densityStatement`; `kActiveRHS` is the right-hand side of
Theorem 5.1 (cast `ℤ → ℝ`). It is `densityStatement` with Theorem 5.1
substituted.
PAPER ISSUE: as for `densityStatement` (wording only). -/
def densityClosedStatement : Prop :=
  ∀ n d σ : ℕ, ∀ hn : 2 ≤ n, 1 ≤ d → ∀ (hσ : 2 ≤ σ) (a : Fin σ),
    haveI : NeZero n := ⟨by omega⟩
    probDens n d σ hσ a
      = (1 / ((n ^ d : ℕ) + 1 : ℝ))
          * ∑ k ∈ Finset.range (n ^ d + 1),
              (kActiveRHS n d σ k : ℝ)
                / (((n ^ d).choose k : ℝ) * ((σ : ℝ) - 1) ^ (n ^ d - k))

/-- **Corollary 7.2** (`cor:dens`, lines 693–702), whole statement: the
displayed formula and its closed form via Theorem 5.1. -/
def corDensStatement : Prop :=
  densityStatement ∧ densityClosedStatement

/-! ## Sanity checks (display/elaboration-time only; prove nothing about
the frozen Props). Expected values from the Python brute force
`scratchpad/research/formal_ext/s05/bf_kactive.py` (definition level). -/

/-- Computable brute-force mirror of `numKActive` for `#guard` checks only:
`IsShiftSymmetric` unfolded to its definition `∃ v ≠ 0, shift v s = s`,
cell count as a `Finset.card`. -/
def bfKActive (n d σ : ℕ) [NeZero n] (a : Fin σ) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun s : Config n d (Fin σ) =>
    (∃ v : Lat n d, v ≠ 0 ∧ shift v s = s) ∧
      (Finset.univ.filter fun u => s u = a).card = k).card

-- Theorem 5.1, RHS vs brute force, every k in 0..N (and every a where cheap).
#guard (List.range 5).map (kActiveRHS 2 2 2) == [1, 0, 6, 0, 1]
#guard (List.range 5).map (bfKActive 2 2 2 0) == [1, 0, 6, 0, 1]
#guard (List.range 5).map (bfKActive 2 2 2 1) == [1, 0, 6, 0, 1]
#guard (List.range 5).map (kActiveRHS 2 2 3) == [8, 0, 12, 0, 1]
#guard (List.range 5).map (bfKActive 2 2 3 0) == [8, 0, 12, 0, 1]
#guard (List.range 5).map (bfKActive 2 2 3 2) == [8, 0, 12, 0, 1]
#guard (List.range 5).map (kActiveRHS 2 2 1) == [0, 0, 0, 0, 1]
#guard (List.range 5).map (bfKActive 2 2 1 0) == [0, 0, 0, 0, 1]
#guard (List.range 7).map (kActiveRHS 6 1 2) == [1, 0, 3, 2, 3, 0, 1]
#guard (List.range 7).map (bfKActive 6 1 2 0) == [1, 0, 3, 2, 3, 0, 1]
#guard (List.range 10).map (kActiveRHS 3 2 2) == [1, 0, 0, 12, 0, 0, 12, 0, 0, 1]
#guard (List.range 9).map (kActiveRHS 2 3 2) == [1, 0, 28, 0, 14, 0, 28, 0, 1]
#guard (List.range 17).map (kActiveRHS 4 2 2)
  == [1, 0, 24, 0, 76, 0, 168, 0, 198, 0, 168, 0, 76, 0, 24, 0, 1]
-- Consistency at formula level (AUXILIARY Prop) and against Theorem 4.3 values.
#guard (Finset.range 5).sum (kActiveRHS 2 2 2) == enumerationRHS 2 2 2
#guard (Finset.range 9).sum (kActiveRHS 2 3 2) == 72
#guard (Finset.range 10).sum (kActiveRHS 3 2 2) == 26
#guard (Finset.range 37).sum (kActiveRHS 6 2 2) == 801064
#guard (Finset.range 7).sum (kActiveRHS 6 1 3) == enumerationRHS 6 1 3
#guard (Finset.range 5).sum (kActiveRHS 2 2 1) == enumerationRHS 2 2 1

/-- Rational mirror of the closed form of Corollary 7.2 (sanity only). -/
def probDensClosedQ (n d σ : ℕ) : ℚ :=
  (1 / ((n ^ d : ℕ) + 1 : ℚ)) * ∑ k ∈ Finset.range (n ^ d + 1),
    (kActiveRHS n d σ k : ℚ) / (((n ^ d).choose k : ℚ) * ((σ : ℚ) - 1) ^ (n ^ d - k))

-- P^dens from the explicitly enumerated two-stage distribution (Python):
-- (2,1,2) → 2/3, (2,2,2) → 3/5, (2,2,3) → 2/5, (3,2,2) → 8/35.
#guard probDensClosedQ 2 1 2 == 2 / 3
#guard probDensClosedQ 2 2 2 == 3 / 5
#guard probDensClosedQ 2 2 3 == 2 / 5
#guard probDensClosedQ 3 2 2 == 8 / 35

-- `gaussBinom` (q-Pascal) agrees with the paper's product formula
-- `[d r]_p = ∏_{i<r} (p^{d−i} − 1)/(p^{i+1} − 1)` (cross-multiplied, in ℕ).
#guard (List.range 5).all fun d => (List.range (d + 1)).all fun r =>
  [2, 3, 5, 7].all fun p =>
    gaussBinom p d r * ((List.range r).map fun i => p ^ (i + 1) - 1).prod
      == ((List.range r).map fun i => p ^ (d - i) - 1).prod

-- 2019 Eqs. (30)–(33) read with the convention, against INDEPENDENT Python
-- values (`s05/bf_repair_r1.py`: definition-level brute force for n = 3,
-- union-of-Fix(C) enumeration for n = 5, 6).
#guard (List.range 26).map (fun k => eq32RHS 5 k 2)
  == [1, 0, 0, 0, 0, 30, 0, 0, 0, 0, 60, 0, 0, 0, 0, 60, 0, 0, 0, 0, 30, 0, 0, 0, 0, 1]
#guard (List.range 10).map (fun k => eq30RHS 3 k 3) == [26, 0, 0, 48, 0, 0, 24, 0, 0, 1]
#guard (List.range 13).map (fun k => eq31RHS 6 k 2)
  == [1, 0, 54, 48, 441, 0, 2640, 0, 9108, 868, 25704, 0, 57348]
#guard (List.range 9).map (fun k => eq30RHS 6 k 3)
  == [801064, 0, 7077888, 98304, 30076416, 0, 80484096, 0, 150395904]
#guard (Finset.range 37).sum (fun k => eq32RHS 6 k 2) == 801064
-- … and against the Theorem 5.1 right-hand side at d = 2, every k ≤ n², σ ∈ {1,2,3}.
#guard [2, 3, 4, 6].all fun n => (List.range (n ^ 2 + 1)).all fun k => [1, 2, 3].all fun σ =>
  eq30RHS n k σ == kActiveRHS n 2 σ k && eq31RHS n k σ == kActiveRHS n 2 σ k &&
    eq32RHS n k σ == kActiveRHS n 2 σ k
#guard [2, 3, 4, 5, 6].all fun n => (List.range (n ^ 2 + 1)).all fun k =>
  eq33RHS n k == kActiveRHS n 2 2 k
-- The necessity witness n = k = 2: gcd = 2, the index (2) lies in the ranges of
-- Eqs. (30)–(33) (and the inner range of (31) is nonempty), h = 4 ∤ 2
-- (k/h = (n²−k)/h = 1/2).
#guard (Nat.gcd 2 2).primeFactors == {2}
#guard decide ((fun _ => 2 : (Nat.gcd 2 2).primeFactors → ℕ) ∈ idxThirty2019 2 2)
#guard decide ((fun _ => 2 : (Nat.gcd 2 2).primeFactors → ℕ) ∈ idxTwo2019 2 2)
#guard (idxInner2019 (fun _ => 2 : (Nat.gcd 2 2).primeFactors → ℕ)).card == 2
#guard h2019 (fun _ => 2 : (Nat.gcd 2 2).primeFactors → ℕ) == 4
#guard !(decide ((4 : ℕ) ∣ 2))

/-- Sanity only: the lattice `Z_n²` as an explicit list (for `#guard`s). -/
def latList2 (n : ℕ) : List (Lat n 2) :=
  (List.range n).flatMap fun i => (List.range n).map fun j => ![(i : ZMod n), (j : ZMod n)]

/-- Sanity only: `|⟨v⟩|`, computed as the number of distinct multiples
`m • v`, `0 ≤ m < n` (in `Z_n²` these are all of `⟨v⟩`). -/
def bfCyc (n : ℕ) [NeZero n] (v : Lat n 2) : ℕ :=
  ((List.range n).map fun m => (m : ℕ) • v).dedup.length

/-- Sanity only: computable mirror of the left side of 2019 Eq. (29),
`|S_{n×n}(v) ∩ D^a_{n×n,k}|` (fixed by every multiple `m • v`, `m < n`;
exactly `k` cells in state `a`). -/
def bfFixK (n σ : ℕ) [NeZero n] (v : Lat n 2) (a : Fin σ) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun s : Config n 2 (Fin σ) =>
    (∀ m : Fin n, shift ((m : ℕ) • v) s = s) ∧ (Finset.univ.filter fun u => s u = a).card = k).card

-- 2019 Eq. (29) read with the convention, every v ∈ Z_n², every k with
-- |⟨v⟩| ∣ k up to n² + 2|⟨v⟩| (so k > n² is exercised), n ∈ {2, 3}.
#guard (latList2 2).length == 4 && (latList2 3).dedup.length == 9
#guard bfCyc 2 (0 : Lat 2 2) == 1 && bfCyc 2 (fun _ => 1) == 2 && bfCyc 3 (fun _ => 1) == 3
#guard (latList2 2).all fun v => (List.range (4 + 2 * bfCyc 2 v + 1)).all fun k =>
  !(decide (bfCyc 2 v ∣ k)) ||
    (((bfFixK 2 2 v 0 k : ℤ) == convTerm 4 k (bfCyc 2 v) 2) &&
     ((bfFixK 2 3 v 1 k : ℤ) == convTerm 4 k (bfCyc 2 v) 3) &&
     ((bfFixK 2 1 v 0 k : ℤ) == convTerm 4 k (bfCyc 2 v) 1))
#guard (latList2 3).all fun v => (List.range (9 + 2 * bfCyc 3 v + 1)).all fun k =>
  !(decide (bfCyc 3 v ∣ k)) || ((bfFixK 3 2 v 0 k : ℤ) == convTerm 9 k (bfCyc 3 v) 2)

/-- Sanity only: 2019 Eq. (32) read WITHOUT the convention (floor division,
no guard). It disagrees with the true count, so the convention is doing
real work in `banda2019Eq32ValidStatement`. -/
def eq32NaiveRHS (n k σ : ℕ) : ℤ :=
  ∑ v ∈ idxTwo2019 n k,
    (-1 : ℤ) ^ (1 + absVec v) * (((n ^ 2 / h2019 v).choose (k / h2019 v) : ℤ)
      * ((σ : ℤ) - 1) ^ ((n ^ 2 - k) / h2019 v))
      * ∏ r : (Nat.gcd k n).primeFactors, (coef2019 r (v r) : ℤ)
-- n = k = 2, σ = 2: naive reading 4, convention 6 = |S^a_{2×2,2}| (brute force).
#guard eq32NaiveRHS 2 2 2 == 4 && eq32RHS 2 2 2 == 6 && bfKActive 2 2 2 0 2 == 6

/-! ### Round-2 sanity checks -/

-- `0^0`, positive half: at σ = 1, k = N every rank-vector term passes the convention
-- guard (non-annihilated) and its exponent `(N − k)/h(v)` is 0 (base σ − 1 = 0) …
#guard [(2, 1), (2, 2), (3, 2), (6, 1), (6, 2), (12, 2), (30, 1), (2, 4)].all fun (n, d) =>
  decide (∀ v ∈ (rankVectors n d).erase 0,
    (hVec v ∣ n ^ d ∧ n ^ d / hVec v ≤ n ^ d / hVec v) ∧ (n ^ d - n ^ d) / hVec v = 0)
-- … with `0^0 := z` the Theorem 5.1 RHS equals `z`, while the true count is 1, so only
-- `z = 1` is correct (and `kActiveRHSZ 1 = kActiveRHS`) …
#guard [(2, 1), (2, 2), (3, 2), (6, 1), (6, 2), (12, 2), (30, 1), (2, 4)].all fun (n, d) =>
  ([-1, 0, 1, 2] : List ℤ).all fun z => kActiveRHSZ z n d 1 (n ^ d) == z
#guard bfKActive 2 2 1 0 4 == 1 && bfKActive 3 1 1 0 3 == 1 && bfKActive 2 3 1 0 8 == 1
#guard [1, 2, 4].all fun h => ([-1, 0, 1, 2] : List ℤ).all fun z => convTermZ z 4 4 h 1 == z
-- … and away from (σ, k) = (1, N) the value of `0^0` is immaterial (the "only" half).
#guard [(2, 2), (3, 2), (6, 1), (4, 2), (2, 3)].all fun (n, d) =>
  (List.range (n ^ d + 1)).all fun k => [1, 2, 3].all fun σ =>
    (σ == 1 && k == n ^ d) ||
      (kActiveRHSZ 0 n d σ k == kActiveRHS n d σ k && kActiveRHSZ 7 n d σ k == kActiveRHS n d σ k)

-- Fractional-exponent presupposition, witness n = d = 2, k = 2, v = (2), h = 4:
-- k/h and (N − k)/h are both 1/2 (4 ∤ 2, 4 ∤ 4 − 2).
#guard decide ((fun _ => 2 : (2 : ℕ).primeFactors → ℕ) ∈ (rankVectors 2 2).erase 0)
#guard hVec (fun _ => 2 : (2 : ℕ).primeFactors → ℕ) == 4
#guard !(decide ((4 : ℕ) ∣ 2)) && !(decide ((4 : ℕ) ∣ 2 ^ 2 - 2))

/-- Sanity only: computable mirror of `numKActive n d 2 a k` for the binary
alphabet: a configuration over `Fin 2` with exactly `k` cells in state `a`
is the same as the `k`-set `t` of its `a`-cells (every other cell carries
the other state), and `shift v s = s` iff `t` is invariant under
`u ↦ u + v`. Enumerates only the `binom(N,k)` such configurations, so it
reaches `Z_6²` at small `k`. -/
def bfKActive2 (n d : ℕ) [NeZero n] (k : ℕ) : ℕ :=
  (((Finset.univ : Finset (Lat n d)).powersetCard k).filter fun t =>
    ∃ v : Lat n d, v ≠ 0 ∧ ∀ u : Lat n d, (u + v ∈ t ↔ u ∈ t)).card

-- The mirror agrees with the full brute force `bfKActive` where both are cheap …
#guard (List.range 5).all fun k => bfKActive2 2 2 k == bfKActive 2 2 2 0 k
#guard (List.range 10).all fun k => bfKActive2 3 2 k == bfKActive 3 2 2 1 k
#guard (List.range 7).all fun k => bfKActive2 6 1 k == bfKActive 6 1 2 0 k
-- … and gives the true counts on Z_6², σ = 2, k = 2, 3 (definition level): 54 and 48.
#guard bfKActive2 6 2 2 == 54 && bfKActive2 6 2 3 == 48
-- 2019 Eq. (32)/(33) AS PRINTED (`p_i`) vs the intended reading (`r_i`) vs Theorem 5.1:
-- P = [2, 3] (increasing order), k = 3, R = [3]: printed 36, true 48;
-- P = [3, 2], k = 2, R = [2]: printed 72, true 54.
#guard eq32PrintedRHS 6 3 2 [2, 3] [3] == 36 && eq32RHS 6 3 2 == 48 && kActiveRHS 6 2 2 3 == 48
#guard eq32PrintedRHS 6 2 2 [3, 2] [2] == 72 && eq32RHS 6 2 2 == 54 && kActiveRHS 6 2 2 2 == 54
#guard eq33PrintedRHS 6 3 [2, 3] [3] == 36 && eq33PrintedRHS 6 2 [3, 2] [2] == 72
#guard eq33RHS 6 3 == 48 && eq33RHS 6 2 == 54
-- The labelling that pairs r_1 with p_1 = r_1 reproduces the intended reading:
#guard eq32PrintedRHS 6 3 2 [3, 2] [3] == 48 && eq32PrintedRHS 6 2 2 [2, 3] [2] == 54
-- Witness labellings are labellings (ω(gcd) = 1 at k = 2, 3, so R is forced):
#guard (Nat.gcd 3 6).primeFactors == {3} && (Nat.gcd 2 6).primeFactors == {2}
#guard (6 : ℕ).primeFactors == {2, 3}
-- The labelling-robust form of the AUXILIARY Props, with the Theorem 5.1 RHS as the true
-- count (validated against brute force above and in round 1): for n ∈ {6, 10, 12, 15},
-- EVERY labelling P of the primes of n has a k ≤ n at which the printed reading is wrong
-- for EVERY labelling R of the primes of gcd(k, n).
#guard [6, 10, 12, 15].all fun n => n.primeFactorsList.dedup.permutations.all fun P =>
  (List.range (n + 1)).any fun k => (Nat.gcd k n).primeFactorsList.dedup.permutations.all fun R =>
    eq32PrintedRHS n k 2 P R != kActiveRHS n 2 2 k && eq33PrintedRHS n k P R != kActiveRHS n 2 2 k
-- For prime-power n the printed and the intended readings coincide (P = R = [p] whenever
-- gcd(k, n) > 1; for gcd = 1 the index set is empty).
#guard [2, 3, 4, 5, 8, 9].all fun n => (List.range (n ^ 2 + 1)).all fun k =>
  eq32PrintedRHS n k 2 n.primeFactorsList.dedup (Nat.gcd k n).primeFactorsList.dedup
    == eq32RHS n k 2

/-! ### Round-3 sanity checks: scope of the §5 convention
(`conventionScopeLiteralStatement`; Python mirror `s05/r3/bf_repair_r3.py`) -/

-- Literal-scope envelope vs the frozen `F_d` (`lowerEnvelope`) at
-- (n,d,σ) = (2,1,2), (3,1,2), (5,1,2), (2,2,2), (3,2,2), (2,3,2), (2,2,3).
#guard [(2, 1, 2), (3, 1, 2), (5, 1, 2), (2, 2, 2), (3, 2, 2), (2, 3, 2), (2, 2, 3)].map
    (fun (n, d, σ) => lowerEnvelopeLit n d σ) == [0, 0, 0, -4, -6, -40, -6]
#guard [(2, 1, 2), (3, 1, 2), (5, 1, 2), (2, 2, 2), (3, 2, 2), (2, 3, 2), (2, 2, 3)].map
    (fun (n, d, σ) => lowerEnvelope n d σ) == [2, 2, 2, 8, 26, 72, 21]
-- Definition-level `|S_{n^d}|` inside Lean (Σ_k of the brute-force `bfKActive`): it equals
-- `lowerEnvelope` (Theorem 6.1 at prime n) and is strictly above `lowerEnvelopeLit`.
#guard let S : ℤ := ((Finset.range 3).sum (bfKActive 2 1 2 0) : ℕ)
  S == 2 && S == lowerEnvelope 2 1 2 && decide (lowerEnvelopeLit 2 1 2 < S)
#guard let S : ℤ := ((Finset.range 4).sum (bfKActive 3 1 2 0) : ℕ)
  S == 2 && S == lowerEnvelope 3 1 2 && decide (lowerEnvelopeLit 3 1 2 < S)
#guard let S : ℤ := ((Finset.range 5).sum (bfKActive 2 2 2 0) : ℕ)
  S == 8 && S == lowerEnvelope 2 2 2 && decide (lowerEnvelopeLit 2 2 2 < S)
#guard let S : ℤ := ((Finset.range 10).sum (bfKActive 3 2 2 0) : ℕ)
  S == 26 && S == lowerEnvelope 3 2 2 && decide (lowerEnvelopeLit 3 2 2 < S)
#guard let S : ℤ := ((Finset.range 9).sum (bfKActive 2 3 2 0) : ℕ)
  S == 72 && S == lowerEnvelope 2 3 2 && decide (lowerEnvelopeLit 2 3 2 < S)
#guard let S : ℤ := ((Finset.range 5).sum (bfKActive 2 2 3 0) : ℕ)
  S == 21 && S == lowerEnvelope 2 2 3 && decide (lowerEnvelopeLit 2 2 3 < S)
-- … at more primes against the certified formula (`enumerationRHS` = |S|, Theorem 4.3).
#guard [2, 3, 5, 7].all fun n => [1, 2, 3].all fun d => [2, 3].all fun σ =>
  enumerationRHS n d σ == lowerEnvelope n d σ && decide (lowerEnvelopeLit n d σ < enumerationRHS n d σ)
-- d = 2 ("exactly Lemma E.21"): `F_2 = (n+1)σ^n − nσ`, while the literal scope gives `−nσ`.
#guard (List.range 19).all fun m => [2, 3, 4].all fun σ =>
  lowerEnvelope (m + 2) 2 σ == ((m + 2 + 1 : ℤ)) * (σ : ℤ) ^ (m + 2) - (m + 2 : ℤ) * σ &&
    lowerEnvelopeLit (m + 2) 2 σ == -((m + 2 : ℤ) * σ)
-- The guard: `binom(r,2)` vanishes exactly at r ∈ {0, 1}.
#guard (List.range 20).all fun r => (r.choose 2 == 0) == decide (r < 2)
-- Non-vacuity of `conventionScopeLiteralStatement` (a): its hypotheses hold at (2,1,2).
example : Nat.Prime 2 ∧ 1 ≤ 1 ∧ 2 ≤ 2 := ⟨Nat.prime_two, le_rfl, le_rfl⟩

/-- Non-degeneracy of the frozen definition `numKActive` (proved, not a
paper statement): for `n ≥ 2`, `d ≥ 1`, exactly one shift-symmetric
configuration has all `N` cells in state `a` — the constant one. (A
kernel `decide` on a concrete torus is not available: reduction of
`Finset.filter` over the function type `Config` gets stuck; the concrete
values are covered by the `#guard`s on `bfKActive` above.) -/
theorem numKActive_top {n d σ : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (a : Fin σ) :
    numKActive n d σ a (n ^ d) = 1 := by
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < n) := ⟨by omega⟩
  classical
  have hcard : ∀ s : Config n d (Fin σ), cellsInState s a = n ^ d ↔ s = fun _ => a := by
    intro s
    unfold cellsInState
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← card_lat n d]
    constructor
    · intro h
      have hu := Finset.eq_univ_of_card _ h
      funext u
      have : u ∈ Finset.univ.filter (fun u => s u = a) := by
        rw [hu]; exact Finset.mem_univ u
      simpa using this
    · rintro rfl
      simp
  rw [numKActive, Nat.card_eq_one_iff_exists]
  refine ⟨⟨fun _ => a, ⟨Pi.single ⟨0, by omega⟩ 1, ?_, rfl⟩, (hcard _).mpr rfl⟩, ?_⟩
  · intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  · rintro ⟨s, -, hs⟩
    exact Subtype.ext ((hcard s).mp hs)

/-- Non-vacuity: the hypotheses of every frozen Prop are satisfiable. -/
example : (2 ≤ 2 ∧ 1 ≤ 1 ∧ 1 ≤ 1 ∧ 0 ≤ 2 ^ 1) ∧ (2 ≤ 2 ∧ 1 ≤ 1 ∧ 2 ≤ 2) := by decide

/-- Non-vacuity of the subgroup clauses (P) and of `banda2019Eq29ValidStatement`:
the hypothesis `|⟨v⟩| ∣ k` holds e.g. at `k = 0` for every `v`, and at
`v = 0` (`⟨0⟩ = ⊥`, order 1) for every `k`. -/
example : Nat.card (AddSubgroup.zmultiples (0 : Lat 2 2)) ∣ 3 := by
  rw [AddSubgroup.zmultiples_zero_eq_bot, AddSubgroup.card_bot]
  exact one_dvd 3

end ShiftSym.P05
