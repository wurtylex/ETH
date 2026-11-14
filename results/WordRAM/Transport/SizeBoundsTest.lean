/-
Testable declarations for `RAMToTM.SizeBounds`: the label condition of a concrete program, the size
of a concrete initial table, and the turn-key bound on a concrete program.  Nothing here is a
`decide` of a computation problem; the `#eval`s just print small concrete tables.
-/

import RAMToTM.SizeBounds

namespace RAMToTM.SizeBounds

open Groundwork

/-- A concrete program satisfies the syntactic label condition of `progLabels`. -/
theorem progLabels_example :
    ∀ l ∈ progLabels [EndStatement.Instr.one 0, EndStatement.Instr.bltz 1 1,
      EndStatement.Instr.accept], l ≤ 3 := by
  intro l hl
  simp [progLabels, labels] at hl
  omega

example : ∀ l ∈ progLabels [EndStatement.Instr.accept, EndStatement.Instr.reject], l ≤ 2 := by
  intro l hl
  simp [progLabels, labels] at hl

/-- The turn-key bound, on a concrete program, a concrete input and every time step. -/
example : ∃ c, ∀ (ws : List ℤ) (v : Option Bool) (k : ℕ),
    size (((EthWordRam.tableStep [EndStatement.Instr.one 0, EndStatement.Instr.bltz 0 0]
          (widthOf 2 (recoveredVars [true, true, false])))^[k]
        (0, none, EthWordRam.initialTable [EndStatement.Instr.one 0, EndStatement.Instr.bltz 0 0]
          (widthOf 2 (recoveredVars [true, true, false])) ws)).2.2,
      ((EthWordRam.tableStep [EndStatement.Instr.one 0, EndStatement.Instr.bltz 0 0]
          (widthOf 2 (recoveredVars [true, true, false])))^[k]
        (0, none, EthWordRam.initialTable [EndStatement.Instr.one 0, EndStatement.Instr.bltz 0 0]
          (widthOf 2 (recoveredVars [true, true, false])) ws)).1,
      recoveredVars [true, true, false], v) ≤ c * ([true, true, false].length + 1) ^ c := by
  obtain ⟨c, hc⟩ := exists_tableStep_size_bound_ram
    [EndStatement.Instr.one 0, EndStatement.Instr.bltz 0 0] 2
  exact ⟨c, fun ws v k => hc [true, true, false] ws v k⟩

/-- The width and the table size of a small concrete instance. -/
example : widthOf 1 (recoveredVars [true, true, false]) = 2 := by
  simp [widthOf, recoveredVars]

example : EthWordRam.tableSize [EndStatement.Instr.one 0] (widthOf 1 (recoveredVars
    [true, true, false])) = 6 := by
  simp [widthOf, recoveredVars, EthWordRam.tableSize, EthWordRam.windowSize, EthWordRam.progCells,
    EthWordRam.cells]

-- the initial table of `loadWords 2 [3]` for the program `[one 0]`: five window cells
#eval EthWordRam.initialTable [EndStatement.Instr.one 0] 2 [3]
-- its size is bounded by `(6 + 1) * (2 + 2) = 28`
#eval (Groundwork.size (EthWordRam.initialTable [EndStatement.Instr.one 0] 2 [3]), (7 : ℕ) * 4)

end RAMToTM.SizeBounds
