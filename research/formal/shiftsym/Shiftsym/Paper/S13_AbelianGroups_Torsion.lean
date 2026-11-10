/-
Phase H, group-13 supplement (2026-11-08): the setting sentence of Section 4.5 (`sec:abelian`) that
group 13 left unfrozen, "an $\FF_p$-vector space", together with "$d_p=\dim_{\FF_p}G[p]$". FROZEN
STATEMENTS ONLY; the proof is in `Shiftsym/Paper/Proofs/P13_AbelianGroups_Torsion.lean` as
`<X>_proved`, audited by `AuditPaper.lean` (group "13").

Why this file exists. `S13_AbelianGroups.lean` defines the p-rank `pRank G p` as the exponent of `p`
in `|G[p]|` (`pRankPowStatement`: `|G[p]| = p ^ pRank G p`) and lists "an $\FF_p$-vector space" as
not frozen ("standard structure, whose numerical content is certified by `pRankPowStatement`"). The
correspondence audit of paper v10 (2026-11-07, `research/formal/correspondence_audit/`) therefore had
one link of the kind "weaker" in Theorem 4.7, the only one in the audit. The owner decided on
2026-11-08 to freeze and prove the sentence rather than explain the exception. Frozen here before any
proof was attempted.

Paper source: `shift_symmetry_d_dimensions.tex` sha256
ce43fba2e76f32b3b8c3b99ec4cedcee32fad281dc3d72a0064e3da62f291655 (paper v10 with the affiliation
and viewer-link edits of 2026-11-07); line numbers are of this version.

Representation choices (Deltas):
* `G[p]` is `pTorsion G p`, the additive subgroup with carrier `{g | p • g = 0}` — the same set as the
  subtype `{g : G // p • g = 0}` in `pRank` and `pRankPowStatement`.
* $\FF_p$ is `ZMod p` (a field for prime `p`). "An $\FF_p$-vector space" is read as: `G[p]` carries a
  `Module (ZMod p)` structure whose scalar action is the natural one, `c • g = c.val • g` (`g` added
  to itself `c.val` times, `0 ≤ c.val < p`). The structure is asserted to exist. It is unique even
  without the action clause (mathlib's `ZMod.instSubsingletonModule`); the clause records which
  structure is meant. The statement uses the ring `ZMod p`; mathlib's field instance
  `ZMod.instField` (under `Fact p.Prime`) has the same ring structure, so `Module.finrank` is the
  dimension.
* `\dim_{\FF_p}` is `Module.finrank (ZMod p)` for that structure; the statement says it equals
  `pRank G p`, so the paper's definition `d_p = dim_{F_p} G[p]` and the formal definition of `pRank`
  agree.
* Stated for every prime `p` (for `p ∤ |G|`, `G[p] = 0` and both sides are `0`); `[Finite G]` as in
  group 13.

Fidelity review (2026-11-08, before the proof): three fresh-context reviewers (literal, exploit,
numeric): PASS, PASS, PASS. The numeric reviewer checked the statement on 930 groups (every product
of cyclic groups with N ≤ 200 and 25 larger ones; 2006 pairs (G, p) with p ∣ N), including the
paper's d_p = |{i : p ∣ n_i}|. Their cosmetic docstring items were applied before the proof; only
comments changed (Run 046).
-/
import Shiftsym.Paper.S13_AbelianGroups

namespace ShiftSym.P13

open ShiftSym

/-- §4.5, line 662: "$G[p]=\{g\in G: pg=0\}$", as an additive subgroup of `G` (carrier
`{g | p • g = 0}`). -/
def pTorsion (G : Type*) [AddCommGroup G] (p : ℕ) : AddSubgroup G where
  carrier := {g | p • g = 0}
  zero_mem' := nsmul_zero p
  add_mem' := fun {a b} (ha : p • a = 0) (hb : p • b = 0) =>
    show p • (a + b) = 0 by rw [nsmul_add, ha, hb, add_zero]
  neg_mem' := fun {a} (ha : p • a = 0) => show p • (-a) = 0 by rw [neg_nsmul, ha, neg_zero]

/-- §4.5, lines 662–663: "let $G[p]=\{g\in G: pg=0\}$, an $\FF_p$-vector space, and let
$d_p=\dim_{\FF_p}G[p]$ be the \emph{$p$-rank} of $G$."

Formal: for a prime `p`, `G[p]` carries a `ZMod p`-module structure (`ZMod p` = $\FF_p$, a field)
whose scalar action is the natural one, `c • g = c.val • g`, and its dimension over `ZMod p` is
`pRank G p` (the exponent of `p` in `|G[p]|`, the formal p-rank used in Theorem 4.7, Corollary 4.8,
Remark 4.9(i) and `rectRankStatement`).

Deltas: see the header (`ZMod p` for $\FF_p$; `pTorsion` for `G[p]`; the structure asserted to exist
with the natural action; `Module.finrank` for the dimension; every prime `p`; `[Finite G]` as in
group 13). -/
def pTorsionVectorSpaceStatement (G : Type*) [AddCommGroup G] [Finite G] (p : ℕ) : Prop :=
  p.Prime →
    ∃ _ : Module (ZMod p) (pTorsion G p),
      (∀ (c : ZMod p) (g : pTorsion G p), ((c • g : pTorsion G p) : G) = c.val • (g : G)) ∧
      Module.finrank (ZMod p) (pTorsion G p) = pRank G p

end ShiftSym.P13
