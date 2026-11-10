import Shiftsym.Paper.S09_CrossoverLaws

namespace ShiftSym.P09

/-- **Proposition 10.2, the window with the explicit constant 20, criteria
form** (`prop:inversion`, v5 lines 997–1000).

Paper (verbatim): "so the two-dimensional ``composite advantage'' inverts
within an explicitly bounded window around $d_c(p)$, a dimension that grows
\emph{linearly} in the prime: (i) applies to every integer $d\ge1$ with
$d\le d_c(p)-20$, and (ii) to every integer $d\ge d_c(p)+20$."
(with the standing "Let $p\ge3$ be prime, $\sigma\ge2$", line 981).

Formal: for every prime `p ≥ 3`, every `σ ≥ 2` and every `d ≥ 1`: if
`d ≤ d_c(p) − 20` then the hypothesis of (i) holds,
`log_σ(2 log₂(p) p^{d−1}) < φ(d)`; if `d ≥ d_c(p) + 20` then the hypothesis
of (ii) holds, `φ(d) < −log_σ(2 log₂(p+1) (p+1)^{d−1})`.

Delta: "(i) applies" = the hypothesis of (i) holds, as in
`inversionExplicitWindowStatement`, whose body this is with `C := 20`; `d_c(p)`
= `dc p`, `φ(d)` = `phi p (d : ℝ)`, and the two logarithmic thresholds are
literally those of `inversionCompositeStatement` / `inversionPrimeStatement`
(`p^{d−1}` with `ℕ`-subtraction, exact as `d ≥ 1`); `d` is a natural number,
cast to `ℝ` for the comparison with `d_c(p) ± 20`. The paper states `d ≥ 1`
for (i); for (ii) the shared antecedent `1 ≤ d` excludes nothing, since
`d ≥ d_c(p) + 20 > 20` (`d_c(p) > 0` for `p ≥ 3`).
PAPER ISSUE: none. -/
def inversionExplicitWindow20Statement : Prop :=
  ∀ p σ d : ℕ, p.Prime → 3 ≤ p → 2 ≤ σ → 1 ≤ d →
    ((d : ℝ) ≤ dc p - 20 →
        Real.logb (σ : ℝ) (2 * Real.logb 2 (p : ℝ) * (p : ℝ) ^ (d - 1)) < phi p (d : ℝ)) ∧
      (dc p + 20 ≤ (d : ℝ) →
        phi p (d : ℝ) <
          -Real.logb (σ : ℝ) (2 * Real.logb 2 ((p : ℝ) + 1) * ((p : ℝ) + 1) ^ (d - 1)))

/-- **Proposition 10.2, the inversion window with the explicit constant 20,
probability form** (`prop:inversion`, v5 lines 997–1000).

Paper (verbatim): as for `inversionExplicitWindow20Statement`; this is the
"inverts within an explicitly bounded window around $d_c(p)$" part, with the
bound the sentence makes explicit.

Formal: for every prime `p ≥ 3`, every `σ ≥ 2` and every `d ≥ 1`:
`d ≤ d_c(p) − 20` implies the composite advantage
`P^unif_{p^d} < P^unif_{(p+1)^d}`, and `d ≥ d_c(p) + 20` implies the prime
advantage `P^unif_{(p+1)^d} < P^unif_{p^d}`; the sign change of
`P^unif_{(p+1)^d} − P^unif_{p^d}` lies in `(d_c(p) − 20, d_c(p) + 20)`.

Delta: the body of `inversionWindowStatement` with `C := 20` (composite
advantage below the window, prime advantage above it, as the names are
attached to (i) and (ii) on lines 985–989); `P^unif_{m^d}` = `probUnif m d σ`
(real). PAPER ISSUE: none. -/
def inversionWindow20Statement : Prop :=
  ∀ p σ d : ℕ, p.Prime → 3 ≤ p → 2 ≤ σ → 1 ≤ d →
    ((d : ℝ) ≤ dc p - 20 → probUnif p d σ < probUnif (p + 1) d σ) ∧
      (dc p + 20 ≤ (d : ℝ) → probUnif (p + 1) d σ < probUnif p d σ)

/-- **Proposition 10.2** (`prop:inversion`, v5 lines 980–1001), the whole
statement as stated in v5: the frozen group-09 whole statement
`inversionLawStatement` ((i), (ii), the sign pattern and unique zero of `φ`,
`d_c(p) = p ln 2 + O(1)`, and the window with `∃ C`) together with the window
with the explicit constant 20 in both forms. (The `∃ C` conjuncts are implied
by the explicit ones and are kept so that the reviewed statement is contained
unchanged.) -/
def inversionLaw20Statement : Prop :=
  inversionLawStatement ∧ inversionExplicitWindow20Statement ∧ inversionWindow20Statement


open Lean Meta Elab Term in
/-- structural check: new Prop == headBeta(body of ∃C statement applied to (20:ℝ)) -/
def chk (old new : Name) : TermElabM Unit := do
  let env ← getEnv
  let some c1 := env.find? old | throwError "no {old}"
  let some c2 := env.find? new | throwError "no {new}"
  let twenty ← instantiateMVars (← elabTerm (← `((20 : ℝ))) none)
  match c1.value!.getAppFnArgs with
  | (``Exists, #[_, f]) =>
      let inst := (mkApp f twenty).headBeta
      logInfo m!"{new}: syntactically equal to body[C:=20]? {inst == c2.value!}; defeq? {← isDefEq inst c2.value!}"
  | _ => throwError "not an Exists"

#eval chk ``inversionExplicitWindowStatement ``inversionExplicitWindow20Statement
#eval chk ``inversionWindowStatement ``inversionWindow20Statement

-- the whole: is `inversionLaw20Statement` literally the 3-fold conjunction
#print inversionLaw20Statement

-- implications both ways: 20-forms imply the ∃C forms
example (h : inversionExplicitWindow20Statement) : inversionExplicitWindowStatement := ⟨20, h⟩
example (h : inversionWindow20Statement) : inversionWindowStatement := ⟨20, h⟩

-- elaboration details: exponent type and negation scope
set_option pp.explicit true in
#check fun (p σ d : ℕ) => -Real.logb (σ : ℝ) (2 * Real.logb 2 ((p : ℝ) + 1) * ((p : ℝ) + 1) ^ (d - 1))
end ShiftSym.P09
