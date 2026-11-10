/-
Non-certified numeric sanity checks (`#eval` only — prints values at
build time; adds no axioms and proves nothing). Expected values from the
exactly-verified Python suite (research/experiments/):
  |S| at (n,d,σ=2): (2,2)→8, (3,2)→26, (5,2)→182, (2,3)→72, (3,3)→6398,
  (6,2)→801064.
-/
import Shiftsym.Statement

namespace ShiftSym

#eval enumerationRHS 2 2 2   -- expect 8
#eval enumerationRHS 3 2 2   -- expect 26
#eval enumerationRHS 5 2 2   -- expect 182
#eval enumerationRHS 2 3 2   -- expect 72
#eval enumerationRHS 3 3 2   -- expect 6398
#eval enumerationRHS 6 2 2   -- expect 801064
#eval lowerEnvelope 6 3 2    -- expect 2954937483568 (F_3(6,2))

end ShiftSym
