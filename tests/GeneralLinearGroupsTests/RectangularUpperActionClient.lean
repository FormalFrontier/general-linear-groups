/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.RectangularUpperAction
public import Mathlib.LinearAlgebra.Matrix.Notation

/-! Ordered row operations on rectangular matrices and first/rest pivots. -/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.RectangularUpperActionClient

open Matrix.GeneralLinearGroup

abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ

/-- One noncentral matrix coefficient for the upper-block shear. -/
def leftCoeff : Coeff := !![0, 1; 0, 0]

/-- A second noncentral coefficient, with noncommuting products. -/
def rightCoeff : Coeff := !![0, 0; 1, 0]

/-- A one-entry rectangular upper block. -/
def shear : Matrix (Fin 1) (Fin 1) Coeff := fun _ _ => leftCoeff

/-- A nonsquare matrix whose lower row is the second coefficient. -/
def input : Matrix (Fin 1 ⊕ Fin 1) (Fin 3) Coeff :=
  fun row _ => match row with
    | Sum.inl _ => 0
    | Sum.inr _ => rightCoeff

/-- This nonsquare action multiplies its coefficient on the left. -/
theorem upper_row :
    (((rectangularUpperUnit shear : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) Coeff) *
      input) (Sum.inl 0) 0) = leftCoeff * rightCoeff := by
  rw [rectangularUpperUnit_mul_apply_inl]
  simp [shear, input]

example :
    (((rectangularUpperUnit shear : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) Coeff) *
      input) (Sum.inl 0) 0) ≠ rightCoeff * leftCoeff := by
  rw [upper_row]
  decide

example :
    (((rectangularUpperUnit shear : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) Coeff) *
      input) (Sum.inr 0) 2) = rightCoeff := by
  simpa [input] using rectangularUpperUnit_mul_apply_inr shear input 0 (2 : Fin 3)

private def firstColumn : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]
private def firstShear : Matrix (Fin 1) (Fin 1) ℤ := fun _ _ => 2

example :
    (((reindexEquiv ℤ (Matrix.firstRestEquiv 1).symm
      (rectangularUpperUnit firstShear) : GL (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) * firstColumn) 0 0 = -2 := by
  rw [reindexed_rectangularUpperUnit_mul_apply_zero]
  norm_num [firstColumn, firstShear, Fin.sum_univ_succ, Matrix.of_apply]

example (matrix : Matrix (Fin 1) (Fin 1) ℤ) :
    (((reindexEquiv ℤ (Matrix.firstRestEquiv 0).symm
      (rectangularUpperUnit (0 : Matrix (Fin 1) (Fin 0) ℤ)) : GL (Fin 1) ℤ) :
      Matrix (Fin 1) (Fin 1) ℤ) * matrix) 0 0 = matrix 0 0 := by
  rw [reindexed_rectangularUpperUnit_mul_apply_zero]
  simp

end GeneralLinearGroupsTests.RectangularUpperActionClient
