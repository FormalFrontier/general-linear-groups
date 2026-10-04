/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.StableDeterminant
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invertible matrices without a unit leading entry

A signed exchange has determinant one and zero leading entry. Over the
nonfield local ring of 2-adic integers, a determinant-one matrix can also
have a nonzero, nonunit leading entry.
-/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.LocalElementaryGenerationExamples

open Matrix.GeneralLinearGroup

/-- A determinant-one signed exchange, with zero in its leading entry. -/
def signedExchange (R : Type*) [Ring R] : GL (Fin 2) R where
  val := !![(0 : R), 1; -1, 0]
  inv := !![(0 : R), -1; 1, 0]
  val_inv := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply]
  inv_val := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply]

theorem signedExchange_det (R : Type*) [CommRing R] :
    Matrix.GeneralLinearGroup.det (signedExchange R) = 1 := by
  apply Units.ext
  simp [signedExchange, Matrix.det_fin_two, Matrix.of_apply]

example (R : Type*) [CommRing R] [IsLocalRing R] :
    ¬ IsUnit (((signedExchange R : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0) := by
  simp [signedExchange]

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The matrix `[[2,1],[-1,0]]` over the 2-adic integers. -/
noncomputable def nonfieldMatrix : GL (Fin 2) ℤ_[2] where
  val := !![(2 : ℤ_[2]), 1; -1, 0]
  inv := !![(0 : ℤ_[2]), -1; 1, 2]
  val_inv := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply]
  inv_val := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.of_apply]

theorem nonfieldMatrix_det : Matrix.GeneralLinearGroup.det nonfieldMatrix = 1 := by
  apply Units.ext
  simp [nonfieldMatrix, Matrix.det_fin_two, Matrix.of_apply]

example : (((nonfieldMatrix : GL (Fin 2) ℤ_[2]) :
    Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 0) ≠ 0 := by
  norm_num [nonfieldMatrix, Matrix.of_apply]

example : ¬ IsUnit (((nonfieldMatrix : GL (Fin 2) ℤ_[2]) :
    Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 0) := by
  simpa [nonfieldMatrix, Matrix.of_apply, nonunits] using
    (PadicInt.p_nonunit (p := 2))

end GeneralLinearGroupsTests.LocalElementaryGenerationExamples
