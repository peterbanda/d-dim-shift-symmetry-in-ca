/-
Paper group 13 (Section 4.5; moved from extension group A1) — assembly of the statements that combine the main theorem
(`P13_AbelianGroups_Count`: `abelianEnum_proved`, `kActive_proved`; `P13_AbelianGroups_Core`:
`pRankPow_proved`) with the rectangular and arithmetic part (`P13_AbelianGroups_Rect`:
`rectRank_proved`, `square_proved`, `bridge_proved`, `orbitCount_proved`, `freeOrbits_proved` and
the reduction lemmas). Frozen statements: `Shiftsym/Paper/S13_AbelianGroups.lean`.
-/
import Shiftsym.Paper.Proofs.P13_AbelianGroups_Count
import Shiftsym.Paper.Proofs.P13_AbelianGroups_Rect

namespace ShiftSym.P13

/-- Theorem A1, rectangular form (the paper's Open Problem (2)). -/
theorem rectEnum_proved (d : ℕ) (n : Fin d → ℕ) (σ : ℕ) : rectEnumStatement d n σ :=
  rectEnum_of_main (fun G _ _ σ => abelianEnum_proved G σ) d n σ

/-- Corollary (c): equal order and equal `p`-ranks give equal counts. -/
theorem onlyRanks_proved (G H : Type*) [AddCommGroup G] [Finite G] [AddCommGroup H] [Finite H]
    (σ : ℕ) : onlyRanksStatement G H σ :=
  onlyRanks_of_abelianEnum G H σ (abelianEnum_proved G σ) (abelianEnum_proved H σ)

/-- Corollary 4.8(i), the stated instance: `Z_2 × Z_24` and `Z_4 × Z_12` (both of order 48, with
`d_2 = 2`, `d_3 = 1`) both have `50388256` shift-symmetric configurations for `σ = 2`. -/
theorem cardTwoPrime_proved : cardTwoPrimeStatement :=
  cardTwoPrime_of_rectEnum (rectEnum_proved 2 ![2, 24] 2) (rectEnum_proved 2 ![4, 12] 2)

end ShiftSym.P13
