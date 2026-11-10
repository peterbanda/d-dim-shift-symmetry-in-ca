# Independent judgment: Lemma A.2 and Corollary 8.2 (2026-10-27)

The correspondence audit of commit `977f823` left two of its 24 items open. Lemma A.2
(`lem:coef`) was never judged. The verdict on Corollary 8.2 (`cor:insolv`) is stale,
because it was given against a local build that was never committed. this note judges both items independently of the auditor's marks and of the
mapping notes. Each mapping of `data/corr/lem_coef.json` and `data/corr/cor_insolv.json`
was checked against the paper source (v6, `shift_symmetry_d_dimensions.tex`) and the
frozen Lean statements. Lean probes are in `Probes.lean`, with output in `probes.log`
(HEAD `977f823`, exit 0, axioms only `propext`, `Classical.choice`, `Quot.sound`).

These verdicts are not entered in `logs/events.jsonl`, which is the auditor's own record.

| Item | Mappings | Verdict |
| --- | --- | --- |
| Lemma A.2 (`lem:coef`, paper lines 1364–1370) | 15 / 15 hold | 👍 **holds** |
| Corollary 8.2 (`cor:insolv`, paper lines 790–804) | 22 / 23 hold, `pattern` fails | 👎 **one uncertified clause** |

## Lemma A.2: holds

Paper: "Let $`q\ge2`$ be real, with $`[d,j]_q`$ and $`r_d(q,j)=q^{\binom j2}[d,j]_q`$ defined
by the product formula. Then $`[d,j]_q\le 4q^{j(d-j)}`$, $`[d,1]_q\le 2q^{d-1}`$, and
$`\sum_{j=2}^{d}r_d(q,j)\le 4(d-1)q^{D}`$." Here $`D:=d(d-1)/2`$ (line 1333) and the product
formula is line 268.

| Mapping | Judgment |
| --- | --- |
| `whole` | ✓ `lemA2Statement` is the conjunction of the three parts. |
| `hyp.q` | ✓ `q : ℝ`, `2 ≤ q` in all three parts. |
| `hyp.d` | ✓ `1 ≤ d` is the standing hypothesis of Definition 2.1. Part (3) needs it: at d = 0 it is false (probe). Part (1) adds `j ≤ d`. For j > d the product formula is 0, so nothing of the paper is lost. The probe `lemA2Part1_all_j` proves part (1) for every j, with the printed exponents read as integers. |
| `def.gp` | ✓ `gaussProd q d r = ∏_{i<r} (q^{d−i} − 1)/(q^{i+1} − 1)` is line 268 with p replaced by q. The ℕ-subtraction d − i is exact for i < r ≤ d. Spot values: [3 1]₂ = 7, [4 2]₂ = 35 (probe). |
| `def.rd` | ✓ `rdReal q d j = q^C(j,2) · gaussProd q d j`. r₃(2,2) = 14 (probe). |
| `def.pf` | ✓ The real product formula is used because the q-Pascal `gaussBinom` is ℕ-valued. For real q ≥ 2 every denominator is ≥ 1. |
| `i1`, `i1.lhs`, `i1.rhs` | ✓ The inequality is in ℝ. The exponent j(d−j) is an exact natural number under j ≤ d. |
| `i2`, `i2.rhs` | ✓ d − 1 is exact under d ≥ 1. |
| `i3`, `i3.lhs`, `i3.rhs` | ✓ `Σ_{j ∈ Icc 2 d}` is empty for d = 1, giving 0 ≤ 0. 4(d−1) is real. q^D uses `DD d`. |
| `def.D` | ✓ `DD d = d(d−1)/2` with ℕ-division, exact since d(d−1) is even. DD 4 = 6 (probe). |

`lemA2_proved` has exactly the frozen type (probe `#check`; AuditPaper 345/345).

## Corollary 8.2: one clause of the corollary is not certified

Eight frozen Props are conjoined in `insolvStatement`. All eight are faithful. 22 of the
23 mappings hold:

| Mapping | Judgment |
| --- | --- |
| `gen`, `gen.task`, `gen.req`, `gen.unsolv` | ✓ The paper does not define "task", so a task is admissible inputs plus acceptable outputs per input. "Requiring an output outside S from an input inside S" means some admissible x ∈ S has every acceptable output outside S. "Solvable" means reaching an acceptable output at some step. This is the weakest notion of solving, so `¬ Solves` is the strongest form of unsolvability. Non-vacuous with nonempty acceptable-output sets: leader election on ℤ₂ satisfies `RequiresLeavingS` (probe). |
| `gen.ca`, `defCA` | ✓ Frozen both for every equivariant map and for the literal offset CA `caMap` of Definition 2.3. |
| `hypN`, `hypStd` | ✓ σ ≥ 2, N > 1 (`1 < n^d`), n ≥ 2 and d ≥ 1 appear as stated. |
| `const`, `const.ex`, `const.all` | ✓ S is nonempty and every constant lies in S. |
| `traj` | ✓ Under equivariant Φ, s ∈ S implies Φ^[k] s ∈ S for every k. |
| `leader`, `leader.asym`, `leader.uniq`, `leader.never` | ✓ "Unique distinguished cell" means some state occupies exactly one cell. That is a superset of the classical one-leader targets, so the asymmetry claim is stronger. Leader election (all inputs admissible) is unsolvable for every leader state. |
| `restrict`, `restrict.hyp`, `restrict.X` | ✓ The closing sentence is frozen in contrapositive form: an equivariant solver of leader election on X has X ∩ S = ∅. This is stronger than the literal "restrict the inputs" and is the paper's own example. |
| `algs`, `cite2d` | ✓ These are references to cited work and are not mathematical. |
| `whole` | ✓ `insolvStatement` conjoins the eight parts. |
| **`pattern`** | **✗** See below. |

**The failing mapping.** Paper v5 (commit `b9df6bc`) narrowed the sentence about pattern
recognition and image translation, as the independent review of 2026-10-16 requested
(finding 2). It now says the corollary covers "every pattern-recognition or
image-processing task whose required output breaks a symmetry of some admissible
input". The mapping data files this clause as `paper-only`: "Informal task names, not
frozen". However, the qualifier is a precise mathematical claim. Read literally, it says:
on some admissible input x, no acceptable output y keeps all the symmetries of x, that
is, Stab(x) ⊄ Stab(y). Any such task is then unsolvable by every translation-equivariant
map. Two findings:

1. The claim is **true**. It follows in a few lines from Theorem 8.1 in stabilizer form
   (frozen `irrevStabStatement`), iterated along the trajectory. The probe
   `insolv_breaksSymmetry` proves it, with axioms `propext` and `Quot.sound` only.
2. It is **strictly more** than the frozen `insolvGeneralStatement`, whose hypothesis
   `RequiresLeavingS` demands an asymmetric output. Probe `stripeTask` gives a
   counterexample on ℤ₄. The task asks the constant input 0000 to become the period-2
   pattern 0101. That breaks a symmetry of the input, so the clause makes the task
   unsolvable. But 0101 is itself shift-symmetric, so `RequiresLeavingS` fails and no
   frozen statement covers this case.

No frozen statement certifies the clause. Under the tool's own kinds it is a `weaker`
mapping, not `paper-only`. It also contradicts §11's claim that the mathematical content
of every corollary is formally verified. The frozen file's docstring still discusses the
v3.1 wording ("image translation"). Frozen files are never edited, so it predates the
v5 sentence.

**Applied 2026-10-27 (Run 027, paper v7).**
- New supplement `Paper/S07_Dynamics_SymmetryBreaking.lean` with `RequiresSymmetryBreaking`,
  `insolvSymBreakStatement` and `insolvFullStatement`. That is 2 statements, so the count goes
  345 → 347, not 346.
- Three fidelity reviews passed (`research/experiments/symbreak_fidelity/`). Reviewer A
  found that the corollary's "This covers" is imprecise wording, and v7 rewords the sentence.
- The proofs are in `Paper/Proofs/P07_Dynamics_SymmetryBreaking.lean`.
- `pattern` now maps to `insolvSymBreakStatement` as a `generalization`, with new mappings
  `pattern.hyp`, `pattern.why` and `full`.

The plan as first proposed follows.

**Remedy (as proposed).** Follow the pattern of the window-20 supplement:
- Freeze a supplement statement in a new file, for example
  `Paper/S07_Dynamics_SymmetryBreaking.lean`, with `insolvBreaksSymmetryStatement` (the
  `BreaksSymmetry` hypothesis of `Probes.lean`).
- Prove it in `Paper/Proofs/`, run fidelity reviews, and add its fingerprint.
- Remap `pattern` to it.
- Update the §11 count, 345 → 346, which is a paper text change.

The alternative is to reclassify `pattern` as `weaker` and qualify §11. That route is
weaker and makes no sense, since the proof is already written.
