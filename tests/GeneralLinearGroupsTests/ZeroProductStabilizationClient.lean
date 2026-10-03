/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.ZeroProductStabilization
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Int.Units
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Zero-product rectangular-block clients

The integer example has `B * A = 0` but `A * B ≠ 0`. Empty blocks and the
zero ring are included; in contrast, one-by-one blocks `[1]`, `[1]` over
the integers do not satisfy the zero-product condition, and `1 + A * B = [2]`
is not invertible there.
-/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.ZeroProductStabilization

open Matrix.GeneralLinearGroup

private def integerColumn : Matrix (Fin 2) (Fin 1) ℤ :=
  fun row _ => if row = 0 then 1 else -1

private def integerRow : Matrix (Fin 1) (Fin 2) ℤ :=
  fun _ _ => 1

private theorem integerRow_mul_integerColumn : integerRow * integerColumn = 0 := by
  ext row col
  fin_cases row
  fin_cases col
  norm_num [integerRow, integerColumn, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem integerColumn_mul_integerRow_ne_zero :
    integerColumn * integerRow ≠ 0 := by
  intro h
  have h00 := congrArg
    (fun matrix : Matrix (Fin 2) (Fin 2) ℤ => matrix 0 0) h
  norm_num [integerColumn, integerRow, Matrix.mul_apply] at h00

example :
    (zeroProductUnit integerColumn integerRow integerRow_mul_integerColumn :
      Matrix (Fin 2) (Fin 2) ℤ) =
      !![(2 : ℤ), 1; -1, 0] := by
  ext row col
  fin_cases row <;> fin_cases col <;>
    norm_num [zeroProductUnit_val, integerColumn, integerRow, Matrix.mul_apply,
      Matrix.of_apply]

example :
    (((zeroProductUnit integerColumn integerRow integerRow_mul_integerColumn)⁻¹ :
      GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(0 : ℤ), -1; 1, 2] := by
  rw [zeroProductUnit_inv_val]
  ext row col
  fin_cases row <;> fin_cases col <;>
    norm_num [integerColumn, integerRow, Matrix.mul_apply,
      Matrix.of_apply]

example :
    stabilize (Y := Fin 1)
      (zeroProductUnit integerColumn integerRow integerRow_mul_integerColumn) ∈
        elementarySubgroup (Fin 2 ⊕ Fin 1) ℤ :=
  stabilize_zeroProductUnit_mem_elementarySubgroup _ _ integerRow_mul_integerColumn

example (A : Matrix (Fin 0) (Fin 1) ℤ) (B : Matrix (Fin 1) (Fin 0) ℤ) :
    zeroProductUnit A B (by ext row col; simp [Matrix.mul_apply]) = 1 := by
  apply Units.ext
  ext row col
  exact row.elim0

example (A : Matrix (Fin 1) (Fin 0) ℤ) (B : Matrix (Fin 0) (Fin 1) ℤ) :
    zeroProductUnit A B (by ext row col; exact row.elim0) = 1 := by
  apply Units.ext
  ext row col
  simp [zeroProductUnit_val]

example (A : Matrix (Fin 2) (Fin 1) (ZMod 1))
    (B : Matrix (Fin 1) (Fin 2) (ZMod 1)) :
    stabilize (Y := Fin 1) (zeroProductUnit A B (Subsingleton.elim _ _)) ∈
      elementarySubgroup (Fin 2 ⊕ Fin 1) (ZMod 1) :=
  stabilize_zeroProductUnit_mem_elementarySubgroup A B (Subsingleton.elim _ _)

private def oneByOne : Matrix (Fin 1) (Fin 1) ℤ :=
  Matrix.single 0 0 1

example : oneByOne * oneByOne ≠ 0 := by
  intro h
  have h00 := congrArg
    (fun matrix : Matrix (Fin 1) (Fin 1) ℤ => matrix 0 0) h
  norm_num [oneByOne, Matrix.mul_apply, Matrix.single] at h00

/-- Over the integers, the one-by-one product gives `[2]`, which is not invertible. -/
theorem oneByOne_one_add_mul_not_isUnit :
    ¬ IsUnit (1 + Matrix.single 0 0 (1 : ℤ) * Matrix.single 0 0 (1 : ℤ) :
      Matrix (Fin 1) (Fin 1) ℤ) := by
  change ¬ IsUnit (1 + oneByOne * oneByOne : Matrix (Fin 1) (Fin 1) ℤ)
  intro h
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp h
  norm_num [Matrix.det_fin_one, oneByOne, Matrix.mul_apply, Matrix.single] at hdet
  have hnat := Int.isUnit_iff_natAbs_eq.mp hdet
  norm_num at hnat

end GeneralLinearGroupsTests.ZeroProductStabilization
