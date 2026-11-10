PASS

# C_reconstruction: independent reconstruction of the symmetry-breaking clause of Corollary 8.2

Reviewer: fresh-context agent, 2026-10-27.

Target: `insolvSymBreakStatement` in `Shiftsym/Paper/S07_Dynamics_SymmetryBreaking.lean`. Its sha256 `dbe24aa3…7288` matches `../frozen_at_review.sha256`.

Phase 1 came first: it was written and checksummed before the reviewer opened the Lean file (17:32 CET). Hashes before Phase 2:
- `phase1_statement.txt`: 47b98848…abb7 (unchanged since)
- `bruteforce_symbreak.py`: 89e84b3d…fc49

After Phase 2 the script gained one extra statistic (the nonempty-accept count) and a sanity check against reference values. `SHA256SUMS` records the final files.

(The reviewer's harness does not allow subagents to write report files. The parent session saved this text verbatim from the reviewer's hand-back, after re-verifying `SHA256SUMS`, the brute-force output and a clean re-run of `reconstruction_check.lean`.)

## Phase 1: reading from the paper alone

Sources: Definitions 2.1–2.3, Theorem 8.1, Corollary 8.2 (tex lines 790–804).

- **Task:** a set Adm of admissible inputs, plus a set Req(x) of acceptable outputs for each x ∈ Adm. This is a relation; a task given by a function is the special case |Req(x)| = 1.
- **Solves:** for every x ∈ Adm there is some k ≥ 0 with Φ^k(x) ∈ Req(x). This is the weakest notion of success; reaching the output at a fixed time, reaching it and staying, or reaching a fixed point all imply it.
- **"y breaks a symmetry of x":** some v ∈ Stab(x) is not in Stab(y), i.e. ¬(Stab x ⊆ Stab y).
- **The clause's hypothesis (reading R0):** ∃ x ∈ Adm such that every y ∈ Req(x) breaks a symmetry of x. The broken v may depend on y.
- **Unsolvable:** no translation-equivariant Φ solves T.

Alternative readings:
- **R1**, the corollary's literal first sentence (x ∈ S and Req(x) ∩ S = ∅): implies R0, but not conversely.
- **R2**, one v broken by every acceptable output: implies R0, and is strictly narrower when |Req(x)| ≥ 2.
- **R3**, "some acceptable output breaks a symmetry": false (take Req(x) = all configurations).
- **R4**, stronger notions of success: all implied by the ∃k version.

The most general true reading is R0 with ∃k success, and it is sharp. For each x, {Φ^k(x) : Φ equivariant, k ≥ 0} = {y : Stab x ⊆ Stab y}, because Φ(τ_v x) := τ_v y is well defined iff Stab x ⊆ Stab y. The brute force confirms this equality.

Statement written before Phase 2:
```
Solves Φ T := ∀ x ∈ T.adm, ∃ k, Φ^[k] x ∈ T.req x
RequiresSymBreak T := ∃ x ∈ T.adm, ∀ y ∈ T.req x, ¬ (stab x ≤ stab y)
∀ n d σ T, RequiresSymBreak T → ∀ Φ, Equivariant Φ → ¬ Solves Φ T   -- no side conditions needed
```

## Brute force

Setup: exact integers, σ = 2, seed 20261027, 9.6 s CPU.
- **Conventions:** (τ_v s)(u) = s(u+v). The equivariant maps are exactly Φ(s)(u) = φ(τ_u s).
- **"All N maps":** every equivariant map was enumerated and iterated until its trajectory repeats.
- **"One-step orbit-exhaustive":** exact over all 2^(2^m) maps, since Φ(x) depends only on φ restricted to the orbit of x.
- **Sanity anchors:** |S_{2^2}| = 8, |S_{3^2}| = 26, |S_{2^3}| = 72, all matching.

| torus | #configs | #equivariant maps checked | violations | #breaking pairs | #symmetric-but-breaking pairs |
|---|---|---|---|---|---|
| Z2 | 4 | all 16 (k ≤ 3) + orbit-exhaustive | 0 | 4 | 0 |
| Z3 | 8 | all 256 (k ≤ 6) + orbit-exhaustive | 0 | 12 | 0 |
| Z4 | 16 | all 65536 (k ≤ 12) + orbit-exhaustive | 0 | 52 | 4 |
| Z2×Z2 | 16 | all 65536 (k ≤ 5) + orbit-exhaustive | 0 | 100 | 36 |
| Z6 | 64 | orbit-exhaustive (all 2^64) + 25384 explicit maps iterated (k ≤ 49): every rule on every 1-, 2- or 3-offset set, plus 20000 random tables | 0 | 580 | 40 |
| Z5 (extra) | 32 | orbit-exhaustive | 0 | 60 | 0 |
| Z2^3 (extra) | 256 | orbit-exhaustive | 0 | 17476 | 4228 |
| Z3×Z3 (extra) | 512 | orbit-exhaustive | 0 | 13116 | 480 |
| Z2×Z4 (extra) | 256 | orbit-exhaustive | 0 | 9700 | 1060 |

- **Sharpness:** the reachable set equals {y : Stab x ⊆ Stab y} for every x on every torus.
- **The inclusion direction matters.** Stab(Φx) ⊆ Stab(x) fails for 8/16, 112/256, 51712/65536 and 63488/65536 maps on Z2, Z3, Z4 and Z2^2.
- **Every task on Z2.** All 17^4 = 83521 tasks were run against all 16 maps.
  - 40257 tasks satisfy R0 and 34680 satisfy R1; every R1 task satisfies R0.
  - No R0 task is solved by any equivariant map.
  - The 5577 tasks that satisfy R0 but not R1 all involve an empty accept set, so they are degenerate.
- **Where R1 misses cases.** Symmetric-but-breaking pairs, the cases a leaving-S formalization (R1) would miss, are absent exactly on Z2, Z3 and Z5, where N is prime. They appear whenever N is composite, including prime n with d = 2 (Z3×Z3: 480).
- **Hand recounts agree:** Z4 = 4, Z2^2 = 36, Z6 = 40.

## Phase 2: comparison with the frozen statement

The frozen `RequiresSymmetryBreaking T := ∃ x ∈ T.admissible, ∀ y ∈ T.accept x, ¬ stab x ≤ stab y` is R0 symbol for symbol. The same holds for `Task`, `Solves` (∃k), `shift v s u = s (u+v)`, `stab` and `Equivariant`.

`reconstruction_check.lean` was run with `lake env lean` under the requested flock: exit 0, no warnings, no `sorry`, and no `_proved` theorems written or read. It establishes:
1. The frozen Prop is `Iff.rfl` to the Phase 1 statement guarded by n ≥ 2, d ≥ 1, σ ≥ 2, N > 1; the unguarded Phase 1 statement implies the frozen one.
2. The docstring's Z4 task `⟨{0000}, fun _ => {0101}⟩` satisfies `RequiresSymmetryBreaking` and does NOT satisfy `RequiresLeavingS`.
3. `¬ stab c0 ≤ stab e0` (a sanity check of the inclusion direction).

Answers to the review questions:
- **Does the frozen statement imply the Phase 1 statement?** Yes, on the paper's domain. The guards are the paper's own. Outside them the claim is degenerate: N = 1 or σ = 1 gives Stab = ⊤, so the hypothesis forces accept = ∅.
- **Is the hypothesis at least as general as the Phase 1 reading?** It is identical to it. R1 and R2 are special cases. `Equivariant Φ` includes every offset CA (`caMap_equivariant`, Definitions.lean:78). By sharpness, no more general per-input hypothesis is true.
- **Is the inclusion direction right?** Yes. `stab x ≤ stab y` means "y keeps every symmetry of x", which is what Theorem 8.1 preserves (`stab s ≤ stab (Φ s)`). Stab does not depend on the sign convention of shifts, so only the direction of ≤ matters, and the brute force shows the reverse direction is not preserved.
- **Docstring Deltas:** accurate.
  - Line numbers (790–804, 795–799, 791–793) and the verbatim quote: correct.
  - The v3.1 → v5 history (`independent_review.md` finding 2, line 201): correct.
  - `Solves` as the weakest notion of success, the dependent-v reading as the most general one, task names generalized rather than formalized, `caMap` included, guards unused: all correct.
  - "Strictly extends `insolvGeneralStatement`": correct. RequiresLeavingS ⇒ RequiresSymmetryBreaking, and check (2) refutes the converse.

## Suggested fixes (none blocking)

1. The header cites Run 027, but `research/experiments/README.md` has no Run 027 entry yet (the last is Run 026). Log it before committing.
2. Optional: put the Z4 non-vacuity and strictness `example`s next to the frozen Prop. The docstring claims strictness, but nothing in the repository certifies it.
3. Optional Delta sentence: an admissible asymmetric x with `accept x = ∅` satisfies the hypothesis vacuously, as with `RequiresLeavingS`. This is harmless.
4. Optional paper prose (at most the "imprecise" class): the task class after "This covers…" lies outside the corollary's stated leaving-S hypothesis. It is covered by Theorem 8.1 in stabilizer form, and a wording such as "by Theorem 8.1 (Stab can only grow), this also covers…" would make that explicit. The reviewer agrees with "PAPER ISSUE: none".
5. Optional: an offset-CA companion statement like `insolvGeneralCAStatement`. It follows directly from `caMap_equivariant`.
