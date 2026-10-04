/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.UnitPivotInduction
public import GeneralLinearGroups.LocalElementaryGeneration
public import GeneralLinearGroupsTests.LocalElementaryGenerationExamples

/-! The local-ring pivot property applied to a matrix with a nonunit leading entry. -/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.UnitPivotInductionClient

open Matrix.GeneralLinearGroup
open GeneralLinearGroupsTests.LocalElementaryGenerationExamples

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The local unit-pivot producer supplies the induction premise on a matrix
whose original leading entry is a nonunit. -/
theorem nonfieldMatrix_diagonalization :
    ∃ (left right : elementarySubgroup (Fin 2) ℤ_[2])
    (diagonal : Fin 2 → ℤ_[2]ˣ),
    (left : GL (Fin 2) ℤ_[2]) * nonfieldMatrix * (right : GL (Fin 2) ℤ_[2]) =
      diagonalUnit diagonal := by
  exact exists_elementary_diagonalization_of_unit_pivots
    (fun _ matrix => exists_elementary_unit_pivot_local matrix) nonfieldMatrix

end GeneralLinearGroupsTests.UnitPivotInductionClient
