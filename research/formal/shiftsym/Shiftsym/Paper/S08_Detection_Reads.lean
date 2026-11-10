/-
Phase H, group 08 (Detection), SUPPLEMENT of 2026-11-06 — Remark 9.4 (Read complexity) and the
paragraph after it. FROZEN STATEMENTS, no proofs of them here (proofs:
`Shiftsym/Paper/Proofs/P08_Detection_Reads.lean`).

Paper: `shift_symmetry_d_dimensions.tex` (v10), Remark 9.4 `rem:reads`, lines 1141–1151:
  "With memory for all $N$ cells, $N$ reads suffice: read every cell once and test in memory.
   For $N\ge2$ and $\sigma\ge2$, $N$ reads are also necessary in the worst case: every correct
   deterministic algorithm, adaptive or not, makes at least $N$ reads on every constant
   configuration. Indeed, a constant configuration is shift-symmetric, while the configuration
   that differs from it in a single unread cell has trivial stabilizer and yields the same
   reads, hence the same answer. Writing $I_a$ for the indicator of the cells in state $a$, a
   translation $\ww$ lies in $\Stab(\ssb)$ if and only if
   $\sum_{a\in\Sigma}\sum_{\uu\in\A}I_a(\uu)\,I_a(\uu+\ww)=N$."
and the unnumbered paragraph after it (the Fourier route), whose claims are all listed below as not frozen.

Frozen here: `readOnceStatement` ("read every cell once and test in memory"),
`readAllStatement` ("N reads suffice"), `readLowerStatement` (every correct algorithm makes at
least N reads on every constant configuration),
`readWorstStatement` ("N reads are also necessary in the worst case"), `oneDefectStatement` (the
single-defect configuration has trivial stabilizer), `stabCorrStatement` (the indicator
identity).

Not frozen, with reasons. In the remark: "a constant configuration is shift-symmetric" is frozen
already as `ShiftSym.P07.insolvConstStatement` (Corollary 8.2; same hypotheses); "yields the
same reads, hence the same answer" is the proof step of `readLower` (`ReadTree.run_path_eq_of_agree`
in the proof module). In the paragraph after it: "obtained for all w at once by d-dimensional
fast Fourier transforms …, one per symbol that occurs …, in O(min(σ,N)·N log N) arithmetic
operations" — the operation counts are cited facts [cooleytukey1965, bluestein1970] (no cost
model in Lean); that each inner sum is a cyclic autocorrelation, that absent symbols contribute
0 and that at most min(σ, N) symbols occur are immediate from the definitions; "without rounding
error if a number-theoretic transform is used" — a cited property of the transform
[pollard1971], which needs the values to be integers in a range below the modulus, i.e.
the fact that the sums are integers in [0, N] (immediate: each counts the cells u with
s(u) = s(u + w)); the comparison with Theorem 9.1 and Proposition 9.2 ("improves … when
sopf_d(n) is large …; … the orbit walks are cheaper", with its regimes) — it compares arithmetic-operation counts that rest on
the cited transform counts, while Theorem 9.1 and Proposition 9.2 (frozen in
`S08_Detection.lean`) count cell reads. Section 11 of the paper lists such comparisons, resting on
cited operation counts, among the prose it does not formalize.

Provenance, stated plainly: five statements were first frozen on 2026-11-06 in the extension
layer (`Ext/SXA3_DetectionReads.lean`, from a draft of the remark), passed a fresh-context
fidelity review there and were proved there; they moved here with the namespace changed to
`ShiftSym.P08` when the remark entered the paper (v10), and the extension copy was deleted.
Fidelity reviews of this file (Run 036; rounds 1 and 2 by three reviewers: literal, exploit, numeric): round 1
found the count form of `readLowerStatement` weaker than the then text "reads every one of the N
cells" and an unfrozen bound; round 2 an unfrozen lexicographic clause (since removed from the
paper); round 3 (literal only; the statements were unchanged since round 2, where the exploit
and numeric reviewers passed): PASS. Afterwards (owner, 2026-11-06) the paper text was aligned with the statements
as first frozen: Remark 9.4 says "makes at least $N$ reads", and the bound clause was dropped from
the paragraph; the coverage conjunct and `stabCorrBoundStatement`, added after round 1 together with
their proofs, were removed again, so that every statement of this file was frozen before its proof
was written (five in the extension layer, `stabCorr` here). Re-review of this change (literal,
exploit): PASS, Run 036.

Representation choices (Deltas):
* A deterministic, adaptive cell-reading algorithm is a decision tree `ReadTree L A`: a leaf
  holds the answer; an inner node reads one cell and branches on its value. `run T s` is the
  answer on input `s`, `reads T s` the number of cells read on the way (a cell read twice
  counts twice, as in Section 9's read model), `path T s` the list of cells read. The model does not bound memory (a tree may
  branch on everything read so far); the paper's algorithm is one such tree.
* "Decides shift symmetry": `run T s = true ↔ IsShiftSymmetric s` for every `s`.
* "N reads are also necessary in the worst case" is frozen in both forms the remark states: the
  worst-case form as `readWorstStatement` (some input), and the stronger form after the colon as
  `readLowerStatement` (at least N reads on every constant configuration), which implies it.
  Hypotheses `n ≥ 2`, `d ≥ 1` (i.e. `N ≥ 2`) and `σ ≥ 2`.
* "Has trivial stabilizer" is `¬ IsShiftSymmetric`, i.e. `stab s = ⊥` by the definition of
  `IsShiftSymmetric` (no nonzero `v` with `shift v s = s`).
* `I_a(u)` is `if s u = a then 1 else 0`, the sums are over `Fin σ` and `Lat n d` in ℕ, and
  `N = n ^ d`; `[NeZero n]` makes the
  lattice a finite type (as for the frozen average-case statements of `S08_Detection.lean`).
  `Stab(s)` is the core `stab s`.
-/
import Shiftsym.Definitions

namespace ShiftSym.P08

open ShiftSym

/-- A deterministic adaptive algorithm that reads cells of a configuration `L → A`. -/
inductive ReadTree (L A : Type*) where
  | done : Bool → ReadTree L A
  | read : L → (A → ReadTree L A) → ReadTree L A

/-- The answer of the algorithm on input `s`. -/
def ReadTree.run {L A : Type*} : ReadTree L A → (L → A) → Bool
  | .done b, _ => b
  | .read u k, s => (k (s u)).run s

/-- The number of cells the algorithm reads on input `s`. -/
def ReadTree.reads {L A : Type*} : ReadTree L A → (L → A) → ℕ
  | .done _, _ => 0
  | .read u k, s => (k (s u)).reads s + 1

/-- The cells the algorithm reads on input `s`, in order. -/
def ReadTree.path {L A : Type*} : ReadTree L A → (L → A) → List L
  | .done _, _ => []
  | .read u k, s => u :: (k (s u)).path s

/-- The algorithm decides shift symmetry on `Z_n^d` over `σ` symbols. -/
def DecidesSymmetry {n d σ : ℕ} (T : ReadTree (Lat n d) (Fin σ)) : Prop :=
  ∀ s : Config n d (Fin σ), (T.run s = true ↔ IsShiftSymmetric s)

/-- "With memory for all N cells, N reads suffice". -/
def readAllStatement (n d σ : ℕ) : Prop :=
  1 ≤ n → ∃ T : ReadTree (Lat n d) (Fin σ), DecidesSymmetry T ∧ ∀ s, T.reads s ≤ n ^ d

/-- "read every cell once and test in memory": some correct algorithm reads, on every input,
each of the `N` cells exactly once. -/
def readOnceStatement (n d σ : ℕ) : Prop :=
  1 ≤ n → ∃ T : ReadTree (Lat n d) (Fin σ), DecidesSymmetry T ∧
    ∀ s, (T.path s).Nodup ∧ (T.path s).length = n ^ d ∧ T.reads s = n ^ d

/-- "For N ≥ 2 and σ ≥ 2, … every correct deterministic algorithm, adaptive or not, makes at least
N reads on every constant configuration." -/
def readLowerStatement (n d σ : ℕ) : Prop :=
  2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∀ T : ReadTree (Lat n d) (Fin σ), DecidesSymmetry T →
      ∀ a : Fin σ, n ^ d ≤ T.reads (fun _ => a)

/-- "For N ≥ 2 and σ ≥ 2, N reads are also necessary in the worst case". -/
def readWorstStatement (n d σ : ℕ) : Prop :=
  2 ≤ n → 1 ≤ d → 2 ≤ σ →
    ∀ T : ReadTree (Lat n d) (Fin σ), DecidesSymmetry T → ∃ s, n ^ d ≤ T.reads s

/-- "the configuration that differs from it in a single … cell has trivial stabilizer". -/
def oneDefectStatement (n d σ : ℕ) : Prop :=
  2 ≤ n → 1 ≤ d →
    ∀ (a b : Fin σ) (u : Lat n d), a ≠ b →
      ¬ IsShiftSymmetric (Function.update (fun _ : Lat n d => a) u b)

/-- "a translation `w` lies in `Stab(s)` if and only if
`Σ_{a∈Σ} Σ_{u∈A} I_a(u) I_a(u+w) = N`". -/
def stabCorrStatement (n d σ : ℕ) [NeZero n] : Prop :=
  ∀ (s : Config n d (Fin σ)) (w : Lat n d),
    w ∈ stab s ↔
      (∑ a : Fin σ, ∑ u : Lat n d,
        (if s u = a then 1 else 0) * (if s (u + w) = a then 1 else 0) : ℕ) = n ^ d

end ShiftSym.P08
