/-
Paper §9 "Detection" (`shift_symmetry_d_dimensions.tex`, lines 797–877):
frozen statements, group 08 (Phase H, 2026-10-15).

Contents
* the §9 algorithm, modelled literally as a Lean function with explicit
  cell-read counting (`orbitWalk`, `compareTail`, `walkOrbit`,
  `subgroupTestAux`/`subgroupTest`, `detect`), parameterised by the reading
  of "abort the subgroup at the first failing orbit" (`stopEarly`);
* the admissible inputs of the algorithm (`IsTraversalOrder`, `IsSchedule`)
  and the uniform expectation `expectUnif`;
* the frozen `Prop`s for: the correctness sentence (Lemma 3.4, L816–818,
  and correctness of the algorithm), Theorem 9.1 (`thm:detect-worst`),
  Proposition 9.2 (`prop:detect-avg`), the computational sentence L858–860,
  and Remark 9.3 (`rem:polylog`), including the corrected form of its false
  sentence about randomly chosen `n` (PAPER ISSUE there);
* non-vacuity examples and `#eval` sanity checks on small instances.

No statement is proved here (only the cheap sanity examples at the end).

Paper prose fixing the model (L799–803, verbatim):
  "The detector generalizes \cite[Sec.~V]{banda2019}. Assume the prime
   factorization of $n$ is given (otherwise add one factorization of an
   integer of $\log_2 n$ bits), and count cell-read operations; $d$ is part
   of the input."
The algorithm (L805–814, verbatim):
  "\textbf{Algorithm.} For each prime $p\mid n$ and each of the
   $\gaussbinom d1_p$ order-$p$ cyclic subgroups $C=\langle\ww\rangle$
   (enumerated via one representative line each,
   Lemma~\ref{lem:torsion}): traverse the cells in a fixed order; for each
   yet-unvisited cell, walk its $C$-orbit ($p$ cells) checking equality;
   abort the subgroup at the first failing orbit. Report ``symmetric'' at
   the first subgroup all of whose orbits pass; report ``asymmetric'' if all
   subgroups fail."
The cost model (L820–823, verbatim):
  "Throughout this section we charge one read per visited cell: the first
   cell of an orbit walk (the \emph{anchor}) is read once and its value
   cached, and each subsequent cell of the orbit is read once and compared
   to the cached value."

Global representation choices (Delta, apply to every statement below):
* lattice `Lat n d = Fin d → ZMod n`, alphabet `Σ = Fin σ` (paper Def. 2.1:
  any finite alphabet with `σ = |Σ|`); `N` is written `n ^ d`.
* "the prime factorization of n is given" and the enumeration of the order-`p`
  subgroups "via one representative line each" are modelled by an input list
  `sched : List (ℕ × Lat n d)` of pairs `(p, w)` (`IsSchedule`): every entry
  has `p` prime, `p ∣ n`, `addOrderOf w = p`; every order-`p` cyclic subgroup
  (`p ∣ n` prime) is `⟨w⟩` for exactly one entry. The statements quantify over
  ALL such lists, i.e. over every enumeration order of the subgroups (primes
  may even be interleaved — this contains the paper's "for each prime, for each
  subgroup" nesting as a special case) and over every choice of generator `w`
  of each subgroup (every generator of an order-`p` subgroup is `(n/p)·y` for a
  representative `y` of the corresponding line, so this is exactly the choice
  of "representative line" vector).
* "traverse the cells in a fixed order": a traversal order PER SCHEDULE ENTRY,
  `ord : ℕ × Lat n d → List (Lat n d)`, where every `ord e` with `e ∈ sched`
  enumerates every cell exactly once (`IsTraversalOrder`). The order is fixed in
  advance (it does not depend on the configuration). Statements quantify over
  all such families; the reading "one order shared by all subgroups" is the
  special case `ord = fun _ => o`. Since the entries of a schedule are pairwise
  distinct, a function of the entry is as general as a function of the
  position in the schedule.
  PAPER ISSUE (ambiguity, minor; repair round 1, exploit review): in L806–809
  "traverse the cells in a fixed order" sits inside the per-subgroup loop, so it
  is not determined whether one order is shared by all subgroups or each
  subgroup has its own fixed order (the 2019 source says "an arbitrary but fixed
  order"). The two readings give different algorithms (for `n = 2`, `d = 2` the
  per-subgroup orders `(oA, oB, oA)` produce a read-count profile over the 16
  configurations that no single shared order produces; reviewer scratch
  `G08_exploit2.lean`). Every statement below is quantified over per-entry
  orders and therefore covers both readings; the paper could say "traverse the
  cells in a fixed order (which may depend on the subgroup)".
* "walk its C-orbit (p cells)": the cells `u + 0•w, u + 1•w, …, u + (p-1)•w`
  in this order (`orbitWalk`); the anchor is the first cell `u + 0•w = u`.
* "yet-unvisited": a cell is visited once it lies on an orbit already walked
  (and passed) in the CURRENT subgroup's traversal; the bookkeeping costs no
  read. A failing orbit aborts the subgroup, so its visited status is moot.
* Reads: exactly the paper's charge — 1 read for the anchor, 1 read for each
  further cell that is compared. The paper does not say whether a failing
  orbit walk stops at the first mismatch. `stopEarly = true`: stop at the
  first mismatch; `stopEarly = false`: the conservative reading, every walked
  orbit costs its full `p` reads. EVERY algorithmic statement below is
  quantified over both readings (`∀ stopEarly : Bool`), with one exception:
  `remPolylogFactorConservativeStatement` (the "exact factor `n^{d-1}`" reading
  of Remark 9.3), which is true only for the conservative reading and is stated
  for it alone (PAPER ISSUE there).
* The output Boolean `true` means "symmetric", `false` "asymmetric".
* Standing assumptions `n ≥ 2`, `d ≥ 1`, `σ ≥ 2` (Def. 2.1) are explicit
  antecedents of every statement (also where a statement would hold without
  them).
-/
import Shiftsym.Paper.Common

namespace ShiftSym.P08

open ShiftSym

/-! ## The algorithm of §9 with explicit read counting -/

section Algorithm

variable {n d : ℕ} {A : Type*} [DecidableEq A]

/-- The `C`-orbit of the cell `u` for `C = ⟨w⟩` of order `p`, as the list of
its cells in walk order `u + 0•w, u + 1•w, …, u + (p-1)•w` (paper L810:
"walk its $C$-orbit ($p$ cells)"). The head of the list is the anchor. -/
def orbitWalk (p : ℕ) (w u : Lat n d) : List (Lat n d) :=
  (List.range p).map fun k => u + k • w

/-- Reading and comparing the cells of an orbit walk after the anchor, whose
value `a` is cached (paper L822–823: "each subsequent cell of the orbit is read
once and compared to the cached value"). Returns `(all equal to a?, reads)`.
Each listed cell that is reached costs exactly one read. With
`stopEarly = true` the walk stops at the first mismatch; with
`stopEarly = false` the remaining cells are still read (conservative reading). -/
def compareTail (stopEarly : Bool) (s : Config n d A) (a : A) :
    List (Lat n d) → Bool × ℕ
  | [] => (true, 0)
  | x :: xs =>
      if s x = a then
        let r := compareTail stopEarly s a xs
        (r.1, r.2 + 1)
      else if stopEarly then (false, 1)
      else
        let r := compareTail stopEarly s a xs
        (false, r.2 + 1)

/-- One orbit walk (paper L820–823): the anchor (first cell) is read once and its
value cached (one read), then the remaining cells are compared with it.
Returns `(orbit passed?, reads)`. -/
def walkOrbit (stopEarly : Bool) (s : Config n d A) : List (Lat n d) → Bool × ℕ
  | [] => (true, 0)
  | a :: rest =>
      let r := compareTail stopEarly s (s a) rest
      (r.1, r.2 + 1)

/-- The traversal for one subgroup `C = ⟨w⟩` of order `p` (paper L809–811):
go through the remaining cells of the order; skip visited cells (no read);
for a yet-unvisited cell `u` walk its orbit; if it passes, mark the orbit's
cells visited and continue; at the first failing orbit abort.
Arguments: remaining order, visited cells. Returns
`(all orbits passed?, number of orbits visited, cells read)`; the failing orbit,
if any, counts as visited. -/
def subgroupTestAux (stopEarly : Bool) (s : Config n d A) (p : ℕ) (w : Lat n d) :
    List (Lat n d) → List (Lat n d) → Bool × ℕ × ℕ
  | [], _ => (true, 0, 0)
  | u :: us, visited =>
      if u ∈ visited then subgroupTestAux stopEarly s p w us visited
      else
        let cells := orbitWalk p w u
        let r := walkOrbit stopEarly s cells
        if r.1 then
          let t := subgroupTestAux stopEarly s p w us (visited ++ cells)
          (t.1, t.2.1 + 1, t.2.2 + r.2)
        else (false, 1, r.2)

/-- The test of one order-`p` subgroup `⟨w⟩` along the traversal order `ord`,
started with no cell visited. Returns `(passed?, orbits visited, reads)`. -/
def subgroupTest (stopEarly : Bool) (s : Config n d A) (ord : List (Lat n d))
    (p : ℕ) (w : Lat n d) : Bool × ℕ × ℕ :=
  subgroupTestAux stopEarly s p w ord []

/-- The full §9 detector (paper L805–814): process the subgroups of the
schedule in order; for the entry `e = (p, w)` traverse the cells in the fixed
order `ord e`; report "symmetric" (`true`) at the first subgroup all of whose
orbits pass, "asymmetric" (`false`) if all subgroups fail. Returns
`(verdict, total cells read)`; the reads of all processed subgroups are added.
(`ord` assigns a traversal order to each schedule entry; a single shared order
`o` is `fun _ => o` — see the file header.) -/
def detect (stopEarly : Bool) (s : Config n d A) (ord : ℕ × Lat n d → List (Lat n d)) :
    List (ℕ × Lat n d) → Bool × ℕ
  | [] => (false, 0)
  | e :: rest =>
      let t := subgroupTest stopEarly s (ord e) e.1 e.2
      if t.1 then (true, t.2.2)
      else
        let r := detect stopEarly s ord rest
        (r.1, t.2.2 + r.2)

end Algorithm

/-! ## Admissible inputs, the set 𝓛, the uniform expectation -/

section Inputs

variable {n d : ℕ}

/-- "traverse the cells in a fixed order" (L809): a list containing every cell
of `Lat n d` exactly once. (In the statements, every schedule entry `e` gets
such an order `ord e`.) -/
def IsTraversalOrder (ord : List (Lat n d)) : Prop :=
  ord.Nodup ∧ ∀ u : Lat n d, u ∈ ord

/-- Membership in `𝓛 = ⋃_{p ∣ n} 𝓛_p` of Lemma 3.4 (L320–321, verbatim: "Let
$\mathcal L_p$ be the set of cyclic subgroups of order $p$ of $\A$ and
$\mathcal L=\bigcup_{p\mid n}\mathcal L_p$"), `p` ranging over primes:
`C` is cyclic of order `p` for a prime `p ∣ n`. -/
def IsPrimeOrderCyclic (C : AddSubgroup (Lat n d)) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ IsAddCyclic C ∧ Nat.card C = p

/-- A schedule of subgroups for the algorithm (L806–809): a list of pairs
`(p, w)`, each with `p` prime, `p ∣ n`, `w` of order `p` (so `⟨w⟩` is one of the
order-`p` cyclic subgroups, given by its representative `w`), listing every
order-`p` cyclic subgroup (`p ∣ n` prime) exactly once:
no two entries generate the same subgroup, and every `C ∈ 𝓛` is generated by
some entry. The order of the list is arbitrary. -/
def IsSchedule (sched : List (ℕ × Lat n d)) : Prop :=
  (∀ e ∈ sched, e.1.Prime ∧ e.1 ∣ n ∧ addOrderOf e.2 = e.1) ∧
  (sched.map fun e => AddSubgroup.zmultiples e.2).Nodup ∧
  ∀ C : AddSubgroup (Lat n d), IsPrimeOrderCyclic C →
    ∃ e ∈ sched, AddSubgroup.zmultiples e.2 = C

/-- Expectation of a cost `f` for `s` uniform on `Σ^{n^d}` (`Σ = Fin σ`): the
average `(Σ_s f s) / |Σ^{𝒜}|` over all configurations. (The denominator is
`σ ^ (n ^ d)`, checked in the sanity section.) -/
noncomputable def expectUnif {σ : ℕ} [NeZero n] (f : Config n d (Fin σ) → ℕ) : ℝ :=
  (∑ s : Config n d (Fin σ), (f s : ℝ)) / (Fintype.card (Config n d (Fin σ)) : ℝ)

end Inputs

/-! ## Claims inside the algorithm's description (L805–814) -/

/-- **Algorithm description, implicit claim (a): the inputs exist.**
Paper L806–809 (verbatim): "For each prime $p\mid n$ and each of the
$\gaussbinom d1_p$ order-$p$ cyclic subgroups $C=\langle\ww\rangle$
(enumerated via one representative line each, Lemma~\ref{lem:torsion}):
traverse the cells in a fixed order".

Formal: for `n ≥ 2`, `d ≥ 1` a schedule (one generator per order-`p` cyclic
subgroup, all primes `p ∣ n`) and a traversal order exist — so the algorithm is
well defined and no statement below is vacuous.

Delta: see the file header. -/
def algorithmInputsExistStatement (n d : ℕ) : Prop :=
  2 ≤ n → 1 ≤ d →
    (∃ sched : List (ℕ × Lat n d), IsSchedule sched) ∧
      ∃ ord : List (Lat n d), IsTraversalOrder ord

/-- **Algorithm description, implicit claim (b): the number of subgroups.**
Paper L806–807 (verbatim): "each of the $\gaussbinom d1_p$ order-$p$ cyclic
subgroups"; Theorem 9.1's proof L833 (verbatim): "there are
$\mathrm{sopf}_d(n)$ subgroups."

Formal: every schedule has exactly `[d 1]_p` entries with prime `p`, for each
prime `p ∣ n`, and `sopf_d(n)` entries in total.

Delta: `[d 1]_p` is `gaussBinom p d 1` (q-Pascal recurrence, Statement.lean). -/
def scheduleCountStatement (n d : ℕ) : Prop :=
  2 ≤ n → 1 ≤ d → ∀ sched : List (ℕ × Lat n d), IsSchedule sched →
    (∀ p : ℕ, p.Prime → p ∣ n →
        (sched.filter fun e => decide (e.1 = p)).length = gaussBinom p d 1) ∧
      sched.length = sopfD n d

/-- **Algorithm description, whole** (claims (a) and (b)). -/
def algorithmSpecStatement (n d : ℕ) : Prop :=
  algorithmInputsExistStatement n d ∧ scheduleCountStatement n d

/-! ## Correctness (L816–818) -/

/-- **Correctness sentence, part 1 (= Lemma 3.4 as restated in §9).**
Paper L816–818 (verbatim): "Correctness is Lemma~\ref{lem:completeness}: a
configuration is shift-symmetric iff it is fixed by some order-$p$ cyclic
subgroup with $p\mid n$."

Delta: alphabet `Fin σ`; "shift-symmetric" is `IsShiftSymmetric` (a nonzero
translation fixes `s`, = `Stab(s) ≠ {0}`, Def. 2.2); "fixed by `C`" is
`s ∈ fixedBy (Fin σ) C`; "order-`p` cyclic subgroup with `p ∣ n`" is
`IsPrimeOrderCyclic` (`p` prime — the paper's `p` always denotes a prime). -/
def completenessIffStatement (n d σ : ℕ) : Prop :=
  2 ≤ n → 1 ≤ d → 2 ≤ σ → ∀ s : Config n d (Fin σ),
    (IsShiftSymmetric s ↔
      ∃ C : AddSubgroup (Lat n d), IsPrimeOrderCyclic C ∧ s ∈ fixedBy (Fin σ) C)

/-- **Correctness sentence, part 2: the algorithm is correct.**
Paper L816 ("Correctness is Lemma~\ref{lem:completeness}") together with the
algorithm's specification L811–813 (verbatim: "Report ``symmetric'' at the first
subgroup all of whose orbits pass; report ``asymmetric'' if all subgroups
fail."): for every schedule, every family of traversal orders (one fixed order
per subgroup, possibly all equal), both readings and every configuration, the
detector reports "symmetric" iff the configuration is shift-symmetric.

Delta: see the file header (schedule, per-entry order, reading, `true` =
"symmetric"). Repair round 1: `ord` generalised from one shared list to a
per-entry family (exploit review; covers both readings of "traverse the cells in
a fixed order", PAPER ISSUE in the file header). -/
def detectCorrectStatement (n d σ : ℕ) : Prop :=
  2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∀ sched : List (ℕ × Lat n d), IsSchedule sched →
    ∀ ord : ℕ × Lat n d → List (Lat n d), (∀ e ∈ sched, IsTraversalOrder (ord e)) →
    ∀ (stopEarly : Bool) (s : Config n d (Fin σ)),
      ((detect stopEarly s ord sched).1 = true ↔ IsShiftSymmetric s)

/-! ## Theorem 9.1 (`thm:detect-worst`, L825–828) -/

/-- **Theorem 9.1 (Worst case), the bound.**
Paper L825–828 (verbatim): "\begin{theorem}[Worst case]\label{thm:detect-worst}
The algorithm reads at most
$N\cdot\mathrm{sopf}_d(n)=O(\mathrm{sopf}_d(n)\cdot n^d)$ cells.
\end{theorem}"

Formal: for every configuration, every schedule (subgroup order and generator
choice), every family of traversal orders (one per subgroup, possibly all equal)
and both readings, the total number of cells read by `detect` is
`≤ n ^ d * sopfD n d`.

Delta: `N = n ^ d`; `sopf_d(n) = sopfD n d = Σ_{p ∈ n.primeFactors} [d 1]_p`
(Common.lean). The `O(sopf_d(n)·n^d)` clause is literally the same quantity
(`N = n^d`), so it adds nothing beyond the explicit bound and is not stated
separately. -/
def detectWorstStatement (n d σ : ℕ) : Prop :=
  2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∀ sched : List (ℕ × Lat n d), IsSchedule sched →
    ∀ ord : ℕ × Lat n d → List (Lat n d), (∀ e ∈ sched, IsTraversalOrder (ord e)) →
    ∀ (stopEarly : Bool) (s : Config n d (Fin σ)),
      (detect stopEarly s ord sched).2 ≤ n ^ d * sopfD n d

/-- **Theorem 9.1, whole statement**: "the algorithm" is the correct detector
(correctness sentence L816–818, both parts) and it reads at most `N · sopf_d(n)`
cells. -/
def thmDetectWorstStatement (n d σ : ℕ) : Prop :=
  completenessIffStatement n d σ ∧ detectCorrectStatement n d σ ∧
    detectWorstStatement n d σ

/-! ## Proposition 9.2 (`prop:detect-avg`, L836–847) -/

/-- **Proposition 9.2, part (i): exact expected number of orbits visited.**
Paper L838–840 (verbatim): "For $\ssb$ uniform on $\Sigma^{n^d}$ and any single
order-$p$ subgroup, the expected number of orbits visited is exactly
$\frac{1-Q^{m}}{1-Q}$ with $Q=\sigma^{1-p}$ and $m=N/p$;"

Formal: for every prime `p ∣ n`, every generator `w` of order `p` (i.e. every
order-`p` subgroup with every choice of generator), every traversal order and
both readings, the uniform average of the number of orbits visited by the test of
`⟨w⟩` alone equals `(1 - Q^m)/(1 - Q)`.

Delta: computed in `ℝ`; `Q = σ^(1-p)` is the integer power `(σ:ℝ) ^ ((1:ℤ) - p)`
(no truncation); `m = n ^ d / p` is ℕ-division, exact because `p ∣ n ∣ n^d`
(`d ≥ 1`); `1 - Q ≠ 0` because `σ ≥ 2`, `p ≥ 2` (no `x/0`); the expectation is
`expectUnif`; the cost is `(subgroupTest stopEarly s ord p w).2.1`; the number of
orbits visited does not depend on the reading.

PAPER ISSUE (ambiguity, minor): "the expected number of orbits visited" for "any
single order-$p$ subgroup" must mean the test of that subgroup run on its own (as
in the proof, L852–854: "the walk visits $i$ orbits iff the first $i-1$ pass"),
not the number of orbits of that subgroup visited inside the full algorithm
(there the subgroup is skipped whenever an earlier subgroup reports
"symmetric", and the expectation is different). Formalized as the stand-alone
test; the paper should say "the test of any single order-$p$ subgroup visits, in
expectation, exactly … orbits". -/
def detectAvgOrbitsStatement (n d σ : ℕ) [NeZero n] : Prop :=
  2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∀ p : ℕ, p.Prime → p ∣ n → ∀ w : Lat n d, addOrderOf w = p →
    ∀ ord : List (Lat n d), IsTraversalOrder ord → ∀ stopEarly : Bool,
      expectUnif (fun s : Config n d (Fin σ) => (subgroupTest stopEarly s ord p w).2.1)
        = (1 - ((σ : ℝ) ^ ((1 : ℤ) - (p : ℤ))) ^ (n ^ d / p))
            / (1 - (σ : ℝ) ^ ((1 : ℤ) - (p : ℤ)))

/-- **Proposition 9.2, part (ii): expected total reads, first bound.**
Paper L840–843 (verbatim): "consequently the expected total number of cells read
by the full algorithm is at most
\[ \sum_{p\mid n}\gaussbinom d1_p\;\frac{p}{1-\sigma^{1-p}} …" (the display
continues with parts (iii)–(iv))

Formal: for every schedule, family of traversal orders (one per subgroup) and
reading, the uniform average of the total reads of `detect` is at most
`Σ_{p ∈ n.primeFactors} [d 1]_p · p / (1 - σ^(1-p))`.

Delta: `ℝ`; `σ^(1-p)` as an integer power; `p ∣ n` ranges over
`n.primeFactors` (the primes dividing `n`, `n ≥ 2`); "the full algorithm" is
`detect` (it stops at the first subgroup that passes). -/
def detectAvgReadsStatement (n d σ : ℕ) [NeZero n] : Prop :=
  2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∀ sched : List (ℕ × Lat n d), IsSchedule sched →
    ∀ ord : ℕ × Lat n d → List (Lat n d), (∀ e ∈ sched, IsTraversalOrder (ord e)) →
    ∀ stopEarly : Bool,
      expectUnif (fun s : Config n d (Fin σ) => (detect stopEarly s ord sched).2)
        ≤ ∑ p ∈ n.primeFactors,
            (gaussBinom p d 1 : ℝ) * ((p : ℝ) / (1 - (σ : ℝ) ^ ((1 : ℤ) - (p : ℤ))))

/-- **Proposition 9.2, part (iii): the middle inequality.**
Paper L843–844 (verbatim): "\sum_{p\mid n}\gaussbinom d1_p\;\frac{p}{1-\sigma^{1-p}}
\;\le\; 2\sum_{p\mid n}p\,\gaussbinom d1_p"

Delta: `ℝ`; integer power for `σ^(1-p)`. -/
def detectAvgBoundLeStatement (n d σ : ℕ) : Prop :=
  2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∑ p ∈ n.primeFactors,
        (gaussBinom p d 1 : ℝ) * ((p : ℝ) / (1 - (σ : ℝ) ^ ((1 : ℤ) - (p : ℤ))))
      ≤ 2 * ∑ p ∈ n.primeFactors, (p : ℝ) * (gaussBinom p d 1 : ℝ)

/-- **Proposition 9.2, part (iv): the O-claim for the bound.**
Paper L844–845 (verbatim): "2\sum_{p\mid n}p\,\gaussbinom d1_p
\;=\;O\Bigl(\sum_{p\mid n}p^{\,d}\Bigr)."

Formal (explicit quantifiers, uniform in `n` and `d` — both are inputs, L803
"$d$ is part of the input"): there is one constant `C` with
`2 Σ_{p∣n} p [d 1]_p ≤ C · Σ_{p∣n} p^d` for all `n ≥ 2`, `d ≥ 1`.

Delta: the `=O(·)` is read as the one-sided bound (Landau "is in"); `ℝ`. -/
def detectAvgBigOStatement : Prop :=
  ∃ C : ℝ, ∀ n d : ℕ, 2 ≤ n → 1 ≤ d →
    2 * ∑ p ∈ n.primeFactors, (p : ℝ) * (gaussBinom p d 1 : ℝ)
      ≤ C * ∑ p ∈ n.primeFactors, (p : ℝ) ^ d

/-- **Proposition 9.2, part (v): the composed consequence.**
Paper L840–845 read end to end: "the expected total number of cells read by the
full algorithm is at most … $=O(\sum_{p\mid n}p^{\,d})$".

Formal: one constant `C` such that for all `n ≥ 2`, `d ≥ 1`, `σ ≥ 2`, every
schedule, family of traversal orders and reading, the expected total reads are
`≤ C · Σ_{p∣n} p^d` (uniform in `n`, `d`, `σ`).

Delta: as in parts (ii)–(iv); the `[NeZero n]` binder only supplies the
`Fintype` instance and is implied by `2 ≤ n`. -/
def detectAvgReadsBigOStatement : Prop :=
  ∃ C : ℝ, ∀ (n d σ : ℕ) [NeZero n], 2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∀ sched : List (ℕ × Lat n d), IsSchedule sched →
    ∀ ord : ℕ × Lat n d → List (Lat n d), (∀ e ∈ sched, IsTraversalOrder (ord e)) →
    ∀ stopEarly : Bool,
      expectUnif (fun s : Config n d (Fin σ) => (detect stopEarly s ord sched).2)
        ≤ C * ∑ p ∈ n.primeFactors, (p : ℝ) ^ d

/-- **Proposition 9.2, whole statement** (parts (i)–(v)). -/
def propDetectAvgStatement (n d σ : ℕ) [NeZero n] : Prop :=
  detectAvgOrbitsStatement n d σ ∧ detectAvgReadsStatement n d σ ∧
    detectAvgBoundLeStatement n d σ ∧ detectAvgBigOStatement ∧
    detectAvgReadsBigOStatement

/-- **Computational sentence after Proposition 9.2.**
Paper L858–860 (verbatim): "The per-generator expectation was confirmed to match
full-enumeration averages \emph{exactly} for
$(n,d,\sigma)\in\{(2,3,2),(2,3,3),(2,4,2)\}$ and, in two dimensions, for
$n\le4$."

Formal: the mathematical content — part (i) of Proposition 9.2 at these
instances (for every generator, traversal order and reading).

Delta: the 2-D instances are taken as `(n, σ) ∈ {(2,2), (3,2), (3,3), (4,2)}`,
exactly the instances of the repository's run log (Run 003,
`research/experiments/verify_banda2d.py` section [7]: "E.36 expectation model
exact on full enumerations n ≤ 4"); the 3-D/4-D triples are those of Run 006
(`verify_paper_claims.py` section [3]). The record of a computation itself is not a
mathematical statement; only its content is frozen.

PAPER ISSUE (ambiguity, minor): the alphabet size of the two-dimensional checks
is not stated in the paper; it should read "in two dimensions, for $n\le4$ with
$\sigma=2$ (and $\sigma=3$ at $n=3$)". (The general statement, part (i), covers
all `σ ≥ 2` anyway.) -/
def avgOrbitsCheckedStatement : Prop :=
  detectAvgOrbitsStatement 2 3 2 ∧ detectAvgOrbitsStatement 2 3 3 ∧
    detectAvgOrbitsStatement 2 4 2 ∧ detectAvgOrbitsStatement 2 2 2 ∧
    detectAvgOrbitsStatement 3 2 2 ∧ detectAvgOrbitsStatement 3 2 3 ∧
    detectAvgOrbitsStatement 4 2 2

/-! ## Remark 9.3 (`rem:polylog`, L862–871)

Paper L862–871 (verbatim): "\begin{remark}[On ``polylogarithmic'' average
cases]\label{rem:polylog} $\sum_{p\mid n}p^d$ is \emph{not} polylogarithmic in
$N$ in general: for prime $n$ it equals $n^d=N$. The polylogarithmic figures
quoted in \cite[Sec.~V--VI]{banda2019} for $d=2$ hold, as that paper states, for
\emph{randomly chosen} $n$ (whose prime factors are typically small), not in the
worst case over $n$; the same conditioning is required in every dimension. Note
also that for prime $n$ the average case $O(N)$ still improves the worst case
$O(N\cdot n^{d-1})$ by a factor $n^{d-1}$. \end{remark}"

Map of the frozen parts: (i) prime case of `Σ p^d`; (ii)(a) not polylogarithmic
in the worst case over `n`, every `d`; (ii)(b) randomly chosen `n` — the paper's
sentence is FALSE, the corrected statement is frozen; (ii)(c) smooth `n` (the
true part of the parenthetical), every `d`; (iii)(a) average case `O(N)` for
prime `n`; (iii)(b) worst case `O(N·n^{d-1})` for prime `n`; (iii)(b') that
worst case is attained up to a constant; (iii)(c) the improvement factor for
the actual costs, both readings; (iii)(c') the exact factor, conservative
reading; (iii)(c'') the ratio of the two explicit bounds (round-0 reading, kept).
-/

/-- **Remark 9.3, part (i): the prime case of the average-case bound.**
Paper L863–864 (verbatim): "for prime $n$ it equals $n^d=N$."
(`it` = `$\sum_{p\mid n}p^d$`.)

Delta: ℕ arithmetic, `p ∣ n` ranges over `n.primeFactors`. -/
def remPolylogPrimeSumStatement (n d : ℕ) : Prop :=
  n.Prime → 1 ≤ d → ∑ p ∈ n.primeFactors, p ^ d = n ^ d

/-- **Remark 9.3, part (ii)(a): not polylogarithmic in the worst case over `n`.**
Paper L863 (verbatim): "$\sum_{p\mid n}p^d$ is \emph{not} polylogarithmic in $N$
in general"; L866–867 (verbatim): "not in the worst case over $n$; the same
conditioning is required in every dimension".

Formal: for every dimension `d ≥ 1` there are no constants `C`, `k`, `M` with
`Σ_{p∣n} p^d ≤ C · (log N)^k` for all `n ≥ M` (`N = n^d`) — i.e. in every
dimension the bound is not polylogarithmic in the worst case over `n`.

Delta: natural logarithm (the base only changes `C`); `ℝ`; "polylogarithmic in
`N`" = `O((log N)^k)` for some `k`, as `n → ∞` with `d` fixed. For the
"conditioning" (random `n`) see parts (ii)(b) and (ii)(c). -/
def remPolylogNotPolylogStatement : Prop :=
  ∀ d : ℕ, 1 ≤ d → ¬ ∃ (C : ℝ) (k M : ℕ), ∀ n : ℕ, M ≤ n →
    (∑ p ∈ n.primeFactors, (p : ℝ) ^ d) ≤ C * (Real.log ((n : ℝ) ^ d)) ^ k

/-- **Remark 9.3, part (ii)(b): randomly chosen `n` — CORRECTED (the paper's
sentence is false).**
Paper L864–867 (verbatim): "The polylogarithmic figures quoted in
\cite[Sec.~V--VI]{banda2019} for $d=2$ hold, as that paper states, for
\emph{randomly chosen} $n$ (whose prime factors are typically small), not in the
worst case over $n$; the same conditioning is required in every dimension."

PAPER ISSUE (false; repair round 1, raised by both fidelity reviews; round 0 had
filed the sentence as NON-MATHEMATICAL, which was wrong). The figures are the
2019 paper's "for randomly chosen $n$ the expected time complexities drop to just
$O(\log(n)n^2)$ and $O(\log^2(n))$" (2019, Sec. V, and Thm. E.36), based there on
"sopf(n) … is of a logarithmic nature in ``most of the cases''". Both figures
rest on `sopf(n) = Σ_{p∣n} p` (`d = 1`) and `sopf₂(n) = Σ_{p∣n} p²` (`d = 2`)
being polylogarithmic for a random `n`, which is false under every standard
meaning of "randomly chosen `n`":
* almost all `n`: for every `d ≥ 1`, `C`, `k` the set of `n` with
  `Σ_{p∣n} p^d ≤ C (log N)^k` has natural density `0` (such `n` have all prime
  factors `≤ (C (log N)^k)^{1/d}`, i.e. they are `(log n)^{O(1)}`-smooth, and
  `Ψ(X, (log X)^a) = X^{1 - 1/a + o(1)}` for `a > 1`, `X^{o(1)}` for `a ≤ 1`,
  in all cases `o(X)`, de Bruijn) — this Prop;
* expectation: `E_{n ≤ X} sopf(n) ~ π² X / (12 ln X)` (Alladi–Erdős 1977); the
  density statement implies that the mean of `Σ_{p∣n} p^d` over `n ≤ X` is not
  `O((log X)^k)` for any `k`;
* the parenthetical is false: the largest prime factor of `n` exceeds `√n` for a
  proportion `→ ln 2 ≈ 0.69` of `n ≤ X` (Dickman), and on average it is about
  `n^{0.62}` (Golomb–Dickman constant `0.6243`).
Computation (independent, `scratchpad/research/formal_ext/s08/bf_detection_r1.py`
part (E), `X = 2·10^6`): `P⁺(n) > √n` for 73.1% of `n ≤ X`; median
`ln P⁺(n)/ln n = 0.631` on `[10^6, 2·10^6]`; mean `sopf(n) = 123234` versus
`(ln X)² = 211`; the fraction of `n ∈ [2, X]` with `Σ_{p∣n} p² ≤ (ln n²)²` is
0.061, 0.022, 0.0076, 0.0053 for `X = 10^4, 10^5, 10^6, 2·10^6`. The attribution
"as that paper states" is accurate (the 2019 paper does state it), but this paper
asserts in its own voice that the figures "hold". (The summary table, L1130–1131,
"polylog only for smooth/typical $n$", repeats the error in the word "typical";
that line is outside this group's range.)
What the paper should say: "The polylogarithmic figures quoted in
\cite[Sec.~V--VI]{banda2019} for $d=2$ are stated there for randomly chosen $n$,
but they hold only for $n$ all of whose prime factors are polylogarithmically
small (a set of density zero): for a proportion $\ln 2$ of all $n$ the largest
prime factor exceeds $\sqrt n$, so in every dimension $\sum_{p\mid n}p^d$ is not
polylogarithmic in $N$ for almost all $n$."

PAPER ISSUE (ambiguity, "the same conditioning is required in every
dimension"): correct for the bound expression `Σ_{p∣n} p^d` in every `d` (parts
(ii)(a)–(c)). Read as a claim about the algorithm's ACTUAL expected cost it
depends on the reading of a failing walk: with early stop the expected reads are
at most `Σ_C (1 + Σ_{j<p-1} σ^{-j})/(1 - σ^{1-p}) ≤ 6·sopf_d(n)`, and
`sopf_1(n) = ω(n) ≤ log₂ n`, so at `d = 1` the actual average cost is
polylogarithmic for EVERY `n`, with no conditioning (exact: `E[reads] = 3.000`
for `n = 13`, `σ = 2`, versus `n` under the conservative reading;
`bf_detection_r1.py` part (D), also literal review `g08_literal_d1_earlystop.out`).
The sentence is therefore formalized for the bound expression `Σ_{p∣n} p^d` —
the subject of the remark's first sentence — the only reading under which it is
correct for both readings of the algorithm.

Formal (the corrected content): for every `d ≥ 1`, every `C : ℝ` and `k : ℕ`,
the proportion of `n ∈ [2, X]` with `Σ_{p∣n} p^d ≤ C · (log n^d)^k` tends to `0`
as `X → ∞` (explicit `ε`–`X₀` form). The `d = 1` instance refutes
"`sopf(n) = O(log n)` for random `n`" (behind the 2019 worst-case figure
`O(log(n) n²)`), the `d = 2` instance refutes the 2019 average-case figure
`O(sopf₂(n) + sopf(n)) = O(log² n)`; since `p·[d 1]_p ≥ p^d`, it also applies to
the bounds `Σ [d 1]_p p/(1 - σ^{1-p})` and `2 Σ p [d 1]_p` of Proposition 9.2.

Delta: "randomly chosen `n`" = uniform on `[2, X]`, `X → ∞` (natural density;
the standing assumption `n ≥ 2`; including `n = 1` changes nothing); natural
logarithm; `ℝ`; the filter predicate is decided classically (the cardinality
does not depend on the decidability instance). -/
def remPolylogRandomNStatement : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ (C : ℝ) (k : ℕ), ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    ((((Finset.Icc 2 X).filter fun n : ℕ =>
        (∑ p ∈ n.primeFactors, (p : ℝ) ^ d) ≤ C * (Real.log ((n : ℝ) ^ d)) ^ k).card : ℝ)
      ≤ ε * (X : ℝ))

/-- **Remark 9.3, part (ii)(c): smooth `n` (the true part of L864–867).**
Paper L866 (verbatim): "(whose prime factors are typically small)" and L867
(verbatim) "the same conditioning is required in every dimension". The
parenthetical names the mechanism behind the polylogarithmic figures: when all
prime factors of `n` are polylogarithmically small, `Σ_{p∣n} p^d` is
polylogarithmic in `N` — in every dimension. (Its word "typically" is false;
see part (ii)(b).)

Formal: for every `d ≥ 1` and every exponent `c`, there are `C`, `k` such that
every `n ≥ 2` all of whose prime factors are `≤ (log n)^c` satisfies
`Σ_{p∣n} p^d ≤ C · (log N)^k` (`N = n^d`). (E.g. `C = 1/ln 2`, `k = cd + 1`,
from `ω(n) ≤ log₂ n`; checked numerically for `n ≤ 10^5`, `c, d ≤ 3`,
`bf_detection_r1.py` part (F).)

Delta: natural logarithm; `c ∈ ℕ` (a real exponent is dominated by a natural one
once `log n ≥ 1`, i.e. `n ≥ 3`); `ℝ`. -/
def remPolylogSmoothStatement : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ c : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ n : ℕ, 2 ≤ n →
    (∀ p ∈ n.primeFactors, (p : ℝ) ≤ Real.log (n : ℝ) ^ c) →
      (∑ p ∈ n.primeFactors, (p : ℝ) ^ d) ≤ C * (Real.log ((n : ℝ) ^ d)) ^ k

/-- **Remark 9.3, part (iii)(a): for prime `n` the average case is `O(N)`.**
Paper L868–869 (verbatim): "for prime $n$ the average case $O(N)$".

Formal: one constant `C` such that for every prime `n`, `d ≥ 1`, `σ ≥ 2`, every
schedule, family of traversal orders and reading, the expected total reads are
`≤ C · n^d`.

Delta: as in Proposition 9.2 (v); uniform in `n`, `d`, `σ`. -/
def remPolylogAvgPrimeStatement : Prop :=
  ∃ C : ℝ, ∀ (n d σ : ℕ) [NeZero n], n.Prime → 1 ≤ d → 2 ≤ σ →
    ∀ sched : List (ℕ × Lat n d), IsSchedule sched →
    ∀ ord : ℕ × Lat n d → List (Lat n d), (∀ e ∈ sched, IsTraversalOrder (ord e)) →
    ∀ stopEarly : Bool,
      expectUnif (fun s : Config n d (Fin σ) => (detect stopEarly s ord sched).2)
        ≤ C * (n : ℝ) ^ d

/-- **Remark 9.3, part (iii)(b): for prime `n` the worst case is `O(N·n^{d-1})`.**
Paper L869 (verbatim): "the worst case $O(N\cdot n^{d-1})$".

Formal: one constant `C` such that for every prime `n`, `d ≥ 1`, `σ ≥ 2`, every
schedule, family of traversal orders, reading and configuration, the reads are
`≤ C · n^d · n^(d-1)`.

Delta: `d - 1` is ℕ-subtraction, exact since `d ≥ 1`; `ℝ`. -/
def remPolylogWorstPrimeStatement : Prop :=
  ∃ C : ℝ, ∀ n d σ : ℕ, n.Prime → 1 ≤ d → 2 ≤ σ →
    ∀ sched : List (ℕ × Lat n d), IsSchedule sched →
    ∀ ord : ℕ × Lat n d → List (Lat n d), (∀ e ∈ sched, IsTraversalOrder (ord e)) →
    ∀ (stopEarly : Bool) (s : Config n d (Fin σ)),
      ((detect stopEarly s ord sched).2 : ℝ) ≤ C * ((n : ℝ) ^ d * (n : ℝ) ^ (d - 1))

/-- **Remark 9.3, part (iii)(b'): for prime `n` the worst case `N·n^{d-1}` is
attained (up to a constant).**
Paper L868–870 (verbatim): "Note also that for prime $n$ the average case
$O(N)$ still improves the worst case $O(N\cdot n^{d-1})$ by a factor
$n^{d-1}$." An improvement over "the worst case" by a factor `n^{d-1}` is a
claim about the algorithm's actual worst-case cost; it presupposes that the
worst case is of order `N·n^{d-1}` and not smaller (repair round 1, exploit
review: round 0 had frozen only an algorithm-free comparison of the two bounds,
now part (iii)(c'')).

Formal: there is `c > 0` such that for every prime `n`, `d ≥ 1`, `σ ≥ 2`, every
schedule, every family of traversal orders and both readings, some
configuration costs at least `c · n^d · n^(d-1)` reads.
(True with `c = 1/4`: for `d ≥ 2` average over the single-defect configurations —
every subgroup fails exactly at the defect's orbit, so the average reads are
`≥ [d 1]_n·((N - n)/2 + 1) ≥ N n^{d-1}/4`; for `d = 1` the constant configuration
costs `N` reads. Brute force, `bf_detection_r1.py` part (B): over random schedules
and per-subgroup orders, `max reads/(N n^{d-1}) ≥ 0.736` on every instance, both
readings, 0 failures of the bound `1/4`.)

Delta: `ℝ`; `d - 1` exact since `d ≥ 1`; `σ ≥ 2` supplies two symbols. -/
def remPolylogWorstLowerStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n d σ : ℕ, n.Prime → 1 ≤ d → 2 ≤ σ →
    ∀ sched : List (ℕ × Lat n d), IsSchedule sched →
    ∀ ord : ℕ × Lat n d → List (Lat n d), (∀ e ∈ sched, IsTraversalOrder (ord e)) →
    ∀ stopEarly : Bool, ∃ s : Config n d (Fin σ),
      c * ((n : ℝ) ^ d * (n : ℝ) ^ (d - 1)) ≤ ((detect stopEarly s ord sched).2 : ℝ)

/-- **Remark 9.3, part (iii)(c): the improvement factor `n^{d-1}` for the actual
costs (both readings).**
Paper L868–870 (verbatim): "Note also that for prime $n$ the average case
$O(N)$ still improves the worst case $O(N\cdot n^{d-1})$ by a factor
$n^{d-1}$."

Formal: there is `c > 0` such that for every prime `n`, `d ≥ 1`, `σ ≥ 2`, every
schedule, family of traversal orders and both readings, some configuration's
reads are at least `c · n^(d-1)` times the expected reads (uniform input): the
worst case exceeds the average case by at least a factor of order `n^{d-1}`.
(Follows from parts (iii)(a) and (iii)(b'); e.g. `c = 1/16`.)

Delta: `ℝ`; `expectUnif`; `d - 1` exact; "by a factor `n^{d-1}`" is read up to a
constant, since both sides of the paper's comparison are `O`-classes.

PAPER ISSUE (imprecision; repair round 1): the sentence compares the actual
costs, and it is true in the "at least" sense for both readings (this Prop) but
in the exact sense (a factor of order exactly `n^{d-1}`) only for the
conservative reading (part (iii)(c')). With early stop the average case for
prime `n` is `O(n^{d-1})`, not order `N` (it is `≤ 6·sopf_d(n) ≤ 12 n^{d-1}`,
see part (ii)(b)), so the actual improvement is of order `n^d`. Exact evidence
(`bf_detection_r1.py` parts (B)–(D)): `d = 1`, `σ = 2`, early stop:
`E[reads] = 3.000` at `n = 13`, and `worst/(n^d·E)` stays between 0.33 and 0.40
for `n = 3, 5, 7, 11, 13` (so `worst/E` grows like `n^d`, not `n^{d-1} = 1`);
conservative reading: `worst/(n^{d-1}·E) ∈ [0.32, 1.00]` on all exhaustive
instances. The paper should say "by a factor of at least order $n^{d-1}$ (of
order exactly $n^{d-1}$ when a failing orbit is walked to its end, as in the
proofs of Theorem 9.1 and Proposition 9.2)". -/
def remPolylogFactorStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n d σ : ℕ) [NeZero n], n.Prime → 1 ≤ d → 2 ≤ σ →
    ∀ sched : List (ℕ × Lat n d), IsSchedule sched →
    ∀ ord : ℕ × Lat n d → List (Lat n d), (∀ e ∈ sched, IsTraversalOrder (ord e)) →
    ∀ stopEarly : Bool, ∃ s : Config n d (Fin σ),
      c * (n : ℝ) ^ (d - 1) *
          expectUnif (fun s' : Config n d (Fin σ) => (detect stopEarly s' ord sched).2)
        ≤ ((detect stopEarly s ord sched).2 : ℝ)

/-- **Remark 9.3, part (iii)(c'): the exact factor `n^{d-1}`, conservative
reading.**
Paper L868–870 (verbatim): "… improves the worst case $O(N\cdot n^{d-1})$ by a
factor $n^{d-1}$." Read as "by a factor of order exactly `n^{d-1}`", this is the
upper half (the lower half is part (iii)(c) at `stopEarly = false`), for the
conservative reading `stopEarly = false` — the read model of the paper's own
proofs (L831: "an orbit walk of length $p$ performs $p$ reads"; L854: "Summing
$p\cdot(1-Q)^{-1}$ over all subgroups").

Formal: there is `C` such that for every prime `n`, `d ≥ 1`, `σ ≥ 2`, every
schedule and family of traversal orders, every configuration's reads (walking a
failing orbit to its end) are at most `C · n^(d-1)` times the expected reads.
(True with `C = 8`: reads `≤ N·[d 1]_n ≤ 2N n^{d-1}`; every asymmetric input
costs `≥ n·[d 1]_n ≥ N`, and asymmetric inputs have probability `≥ 1/4`.)

Delta: as in part (iii)(c).

PAPER ISSUE: false for the early-stop reading (the ratio is of order `n^d`
there; see part (iii)(c)); stated for the conservative reading only. -/
def remPolylogFactorConservativeStatement : Prop :=
  ∃ C : ℝ, ∀ (n d σ : ℕ) [NeZero n], n.Prime → 1 ≤ d → 2 ≤ σ →
    ∀ sched : List (ℕ × Lat n d), IsSchedule sched →
    ∀ ord : ℕ × Lat n d → List (Lat n d), (∀ e ∈ sched, IsTraversalOrder (ord e)) →
    ∀ s : Config n d (Fin σ),
      ((detect false s ord sched).2 : ℝ)
        ≤ C * (n : ℝ) ^ (d - 1) *
          expectUnif (fun s' : Config n d (Fin σ) => (detect false s' ord sched).2)

/-- **Remark 9.3, part (iii)(c''): the two explicit bounds differ by the factor
`n^{d-1}`.**
Paper L868–870 (verbatim): "Note also that for prime $n$ the average case
$O(N)$ still improves the worst case $O(N\cdot n^{d-1})$ by a factor
$n^{d-1}$." — read literally as a comparison of the two stated bounds.

Formal: for prime `n`, `d ≥ 1`, `σ ≥ 2`, the worst-case bound of Theorem 9.1,
`N · sopf_d(n)`, lies between `n^{d-1}/2` and `n^{d-1}` times the average-case
bound `B = Σ_{p∣n} [d 1]_p · p/(1 - σ^{1-p})` of Proposition 9.2:
`(n^{d-1}/2) · B ≤ N · sopf_d(n) ≤ n^{d-1} · B`.

Delta: `ℝ`; `d - 1` exact since `d ≥ 1`; integer power for `σ^(1-p)`. (This was
round 0's only formalization of the sentence; it says nothing about the actual
costs, which are parts (iii)(b'), (iii)(c), (iii)(c').) -/
def remPolylogBoundRatioStatement (n d σ : ℕ) : Prop :=
  n.Prime → 1 ≤ d → 2 ≤ σ →
    ((n : ℝ) ^ (d - 1) / 2) *
          (∑ p ∈ n.primeFactors,
            (gaussBinom p d 1 : ℝ) * ((p : ℝ) / (1 - (σ : ℝ) ^ ((1 : ℤ) - (p : ℤ)))))
        ≤ ((n ^ d * sopfD n d : ℕ) : ℝ) ∧
      ((n ^ d * sopfD n d : ℕ) : ℝ)
        ≤ (n : ℝ) ^ (d - 1) *
          (∑ p ∈ n.primeFactors,
            (gaussBinom p d 1 : ℝ) * ((p : ℝ) / (1 - (σ : ℝ) ^ ((1 : ℤ) - (p : ℤ)))))

/-- **Remark 9.3, whole mathematical content** (parts (i), (ii)(a)–(c),
(iii)(a), (iii)(b), (iii)(b'), (iii)(c), (iii)(c'), (iii)(c'')); part (ii)(b) is
the CORRECTED form of the false sentence L864–866 (PAPER ISSUE there).
NON-MATHEMATICAL: only the attribution "as that paper states" (L865), which is
accurate (2019, Sec. V: "for randomly chosen $n$ the expected time complexities
drop to just $O(\log(n)n^2)$ and $O(\log^2(n))$"). -/
def remPolylogStatement : Prop :=
  (∀ n d : ℕ, remPolylogPrimeSumStatement n d) ∧ remPolylogNotPolylogStatement ∧
    remPolylogRandomNStatement ∧ remPolylogSmoothStatement ∧
    remPolylogAvgPrimeStatement ∧ remPolylogWorstPrimeStatement ∧
    remPolylogWorstLowerStatement ∧ remPolylogFactorStatement ∧
    remPolylogFactorConservativeStatement ∧
    (∀ n d σ : ℕ, remPolylogBoundRatioStatement n d σ)

/-! ## NON-MATHEMATICAL sentences of §9 (not formalized)

* L799 "The detector generalizes \cite[Sec.~V]{banda2019}." — attribution.
* L799–803 "Assume the prime factorization of $n$ is given (otherwise add one
  factorization of an integer of $\log_2 n$ bits), and count cell-read operations;
  $d$ is part of the input." — cost-model convention; modelled by the `sched`
  input, the read counter, and uniformity in `d` of the O-statements; the cost of
  factoring is outside the model.
* L865 "as that paper states" — attribution (accurate). The rest of the sentence
  L864–867 is mathematical and FALSE as written: see
  `remPolylogRandomNStatement` (PAPER ISSUE, corrected statement frozen),
  `remPolylogSmoothStatement` and `remPolylogNotPolylogStatement`. (Round 0
  listed the whole sentence here; corrected in repair round 1.)
* L873–877 "Related decision problems … were recently analyzed by Anselmo,
  Cavallaro, Madonia, and Selmi \cite{anselmo2025}; detecting a nontrivial
  translation stabilizer, as here, is the tractable member of that family." —
  literature positioning; its mathematical core (a polynomial number of reads) is
  implied by `detectWorstStatement` since `sopf_d(n) ≤ N`.
-/

/-! ## Sanity checks (non-vacuity, small instances) -/

section Sanity

/-- The expectation's denominator is the paper's `|Σ^{n^d}| = σ^(n^d)`. -/
example (n d σ : ℕ) [NeZero n] : Fintype.card (Config n d (Fin σ)) = σ ^ (n ^ d) := by
  simp [Config, Lat, ZMod.card]

/-- Non-vacuity: a traversal order of `Lat 2 1`. -/
example : IsTraversalOrder ([![0], ![1]] : List (Lat 2 1)) := by
  refine ⟨by decide, ?_⟩
  decide

/-- Non-vacuity: a schedule for `n = 2`, `d = 1` (one subgroup, `[1 1]_2 = 1`). -/
example : IsSchedule ([(2, ![1])] : List (ℕ × Lat 2 1)) := by
  have h1 : (2 • (![1] : Lat 2 1)) = 0 := by decide
  have h0 : (![1] : Lat 2 1) ≠ 0 := by decide
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : addOrderOf (![1] : Lat 2 1) = 2 := addOrderOf_eq_prime h1 h0
  have hcard : Nat.card (Lat 2 1) = 2 := by
    simp [Lat, Nat.card_eq_fintype_card, ZMod.card]
  have htop : AddSubgroup.zmultiples (![1] : Lat 2 1) = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [Nat.card_zmultiples, hord, hcard])
  refine ⟨?_, by simp, ?_⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨Nat.prime_two, dvd_refl 2, hord⟩
  · rintro C ⟨p, hp, hpn, -, hC⟩
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpn
    refine ⟨(2, ![1]), List.mem_singleton.mpr rfl, ?_⟩
    rw [htop, eq_comm]
    exact AddSubgroup.eq_top_of_card_eq _ (by rw [hC, hp2, hcard])

/-- Non-vacuity of the arithmetic hypotheses of Proposition 9.2 (i). -/
example : (2 : ℕ).Prime ∧ 2 ∣ 6 ∧ addOrderOf (![3] : Lat 6 1) = 2 := by
  have h1 : (2 • (![3] : Lat 6 1)) = 0 := by decide
  have h0 : (![3] : Lat 6 1) ≠ 0 := by decide
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨Nat.prime_two, by decide, addOrderOf_eq_prime h1 h0⟩

/-! Computable test harness (only for the `#eval` checks below). -/

/-- All cells of `Lat n d`, as a list. -/
def allCells (n : ℕ) : (d : ℕ) → List (Lat n d)
  | 0 => [fun i => i.elim0]
  | d + 1 => (allCells n d).flatMap fun v =>
      (List.range n).map fun k => (Fin.cons (k : ZMod n) v : Lat n (d + 1))

/-- The `k`-th configuration over `Fin (σ+1)` (base-`(σ+1)` digits of `k` along
the list `cells`). -/
def cfgOfIndex {n d : ℕ} (cells : List (Lat n d)) (σ k : ℕ) : Config n d (Fin (σ + 1)) :=
  fun u => ⟨(k / (σ + 1) ^ cells.idxOf u) % (σ + 1), Nat.mod_lt _ (Nat.succ_pos σ)⟩

/-- Definition-level brute force for shift-symmetry. -/
def bruteSym {n d σ : ℕ} (s : Config n d (Fin σ)) : Bool :=
  (allCells n d).any fun v =>
    decide (v ≠ 0) && (allCells n d).all fun u => decide (s (u + v) = s u)

/-- A schedule built greedily: for each prime `p ∣ n`, every `w ≠ 0` with
`p • w = 0` not in an already chosen order-`p` subgroup. -/
def greedySchedule (n d : ℕ) : List (ℕ × Lat n d) :=
  (n.primeFactorsList.dedup).foldl (fun acc p =>
    (allCells n d).foldl (fun acc w =>
      if decide (w ≠ 0) && decide (p • w = 0) &&
          !(acc.any fun e => decide (e.1 = p) &&
              ((List.range p).map fun k => k • e.2).contains w)
      then acc ++ [(p, w)] else acc) acc) []

/-- Families of traversal orders used in the checks: the shared orders
`allCells` and its reverse, and two genuinely per-entry families (the order of
entry `(p, w)` is a rotation, resp. a reversed rotation, of `allCells` depending
on `w`). -/
def orderFamilies {n d : ℕ} (cells : List (Lat n d)) : List (ℕ × Lat n d → List (Lat n d)) :=
  [fun _ => cells, fun _ => cells.reverse, fun e => cells.rotate (cells.idxOf e.2),
    fun e => (cells.rotate (2 * cells.idxOf e.2 + 1)).reverse]

/-- Correctness and worst-case bound for all configurations (σ+1 symbols), for
the order families `orderFamilies` and both readings; also checks that the
greedy schedule has `sopf_d(n)` entries. -/
def checkCorrectWorst (n d σ : ℕ) : Bool :=
  let cells := allCells n d
  let sched := greedySchedule n d
  decide (sched.length = sopfD n d) &&
  (orderFamilies cells).all fun ord => [false, true].all fun st =>
    (List.range ((σ + 1) ^ cells.length)).all fun k =>
      let s := cfgOfIndex cells σ k
      let r := detect st s ord sched
      (r.1 == bruteSym s) && decide (r.2 ≤ n ^ d * sopfD n d)

/-- Proposition 9.2 (i) on all configurations, for every schedule entry, both
orders and both readings: `Σ_s orbits = σ^N · (1 - Q^m)/(1 - Q)` in `ℚ`. -/
def checkOrbits (n d σ : ℕ) : Bool :=
  let cells := allCells n d
  let M := (σ + 1) ^ cells.length
  [cells, cells.reverse].all fun ord => [false, true].all fun st =>
    (greedySchedule n d).all fun e =>
      let tot : ℕ := (List.range M).foldl
        (fun acc k => acc + (subgroupTest st (cfgOfIndex cells σ k) ord e.1 e.2).2.1) 0
      let Q : ℚ := 1 / ((σ + 1 : ℚ) ^ (e.1 - 1))
      (tot : ℚ) / M == (1 - Q ^ (n ^ d / e.1)) / (1 - Q)

/-- Proposition 9.2 (ii) on all configurations (all order families, both
readings). -/
def checkAvgReads (n d σ : ℕ) : Bool :=
  let cells := allCells n d
  let M := (σ + 1) ^ cells.length
  let B : ℚ := ∑ p ∈ n.primeFactors,
    (gaussBinom p d 1 : ℚ) * ((p : ℚ) / (1 - 1 / ((σ + 1 : ℚ) ^ (p - 1))))
  (orderFamilies cells).all fun ord => [false, true].all fun st =>
    let tot : ℕ := (List.range M).foldl
      (fun acc k => acc + (detect st (cfgOfIndex cells σ k) ord (greedySchedule n d)).2) 0
    decide ((tot : ℚ) / M ≤ B)

/-- Remark 9.3 (iii)(b'), (iii)(c), (iii)(c') on all configurations (prime `n`,
σ+1 symbols, all order families): `4·max ≥ N·n^(d-1)` (worst case attained with
`c = 1/4`), `16·max ≥ n^(d-1)·E` (factor, both readings, `c = 1/16`), and for the
conservative reading `max ≤ 8·n^(d-1)·E` (`C = 8`), with `E = tot / M`. -/
def checkFactor (n d σ : ℕ) : Bool :=
  let cells := allCells n d
  let M := (σ + 1) ^ cells.length
  let sched := greedySchedule n d
  (orderFamilies cells).all fun ord => [false, true].all fun st =>
    let rs := (List.range M).map fun k => (detect st (cfgOfIndex cells σ k) ord sched).2
    let tot := rs.sum
    let mx := rs.foldl max 0
    decide (n ^ d * n ^ (d - 1) ≤ 4 * mx) && decide (n ^ (d - 1) * tot ≤ 16 * mx * M) &&
      (st || decide (mx * M ≤ 8 * n ^ (d - 1) * tot))

/-- `scheduleCountStatement` on the greedy schedule: `[d 1]_p` entries per prime. -/
def checkCount (n d : ℕ) : Bool :=
  (n.primeFactorsList.dedup).all fun p =>
    ((greedySchedule n d).filter fun e => decide (e.1 = p)).length == gaussBinom p d 1

#eval [checkCount 2 3, checkCount 3 2, checkCount 6 2, checkCount 12 1, checkCount 5 2,
  checkCount 2 4]

-- expected: true (σ+1 symbols: the third argument is σ - 1)
#eval checkCorrectWorst 2 1 1
#eval checkCorrectWorst 2 2 1
#eval checkCorrectWorst 2 2 2
#eval checkCorrectWorst 3 2 1
#eval checkCorrectWorst 2 3 1
#eval checkCorrectWorst 6 1 1
#eval checkCorrectWorst 4 1 2
#eval checkOrbits 2 2 1
#eval checkOrbits 2 2 2
#eval checkOrbits 3 2 1
#eval checkOrbits 2 3 1
#eval checkOrbits 6 1 2
#eval checkAvgReads 2 2 1
#eval checkAvgReads 3 2 1
#eval checkAvgReads 2 3 1
#eval checkAvgReads 6 1 1
#eval checkFactor 2 1 1
#eval checkFactor 3 1 1
#eval checkFactor 5 1 1
#eval checkFactor 2 2 1
#eval checkFactor 2 2 2
#eval checkFactor 3 2 1
#eval checkFactor 2 3 1

-- Remark 9.3 / Proposition 9.2 arithmetic on a few values (kernel-checked)
example : ∑ p ∈ (7 : ℕ).primeFactors, p ^ 3 = 7 ^ 3 := by
  rw [Nat.Prime.primeFactors (by norm_num)]; simp
example : sopfD 6 2 = 7 := by
  have h : (6 : ℕ).primeFactors = {2, 3} := by
    unfold Nat.primeFactors; simp [Nat.primeFactorsList_ofNat]
  rw [sopfD, h]; decide
example : sopfD 2 3 = 7 := by
  rw [sopfD, Nat.Prime.primeFactors Nat.prime_two]; decide

/-- Non-vacuity of the smoothness hypothesis of `remPolylogSmoothStatement`
(`n = 8`, `c = 1`: the only prime factor `2` is `≤ log 8`). -/
example : ∀ p ∈ (8 : ℕ).primeFactors, (p : ℝ) ≤ Real.log (8 : ℕ) ^ 1 := by
  have h8 : (8 : ℕ).primeFactors = {2} := by
    unfold Nat.primeFactors; simp [Nat.primeFactorsList_ofNat]
  rw [h8]
  intro p hp
  rw [Finset.mem_singleton] at hp
  subst hp
  rw [pow_one, Real.le_log_iff_exp_le (by norm_num)]
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp ((2 : ℕ) : ℝ) = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  push_cast
  nlinarith

end Sanity

end ShiftSym.P08
