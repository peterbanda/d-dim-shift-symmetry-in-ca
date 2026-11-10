-- Counts only: independently checks the inventory quoted in paper section 11.
-- Kernel replay is performed separately for the main-paper import closure.
import Shiftsym
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  let mut modules := 0
  let mut theorems := 0
  let mut definitions := 0
  for i in [0:env.header.moduleNames.size] do
    unless env.header.moduleNames[i]!.toString.startsWith "Shiftsym" do continue
    modules := modules + 1
    for c in env.header.moduleData[i]!.constants do
      match c with
      | .thmInfo _ => theorems := theorems + 1
      | .defnInfo d => if d.safety == .safe then definitions := definitions + 1
      | _ => pure ()
  IO.println s!"ROOT INVENTORY (not replay): {modules} modules; {theorems} theorems; {definitions} safe definitions"
