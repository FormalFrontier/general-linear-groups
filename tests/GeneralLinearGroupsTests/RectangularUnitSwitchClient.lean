/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.RectangularUnitSwitch
public import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Rectangular unit-switch clients

One-by-one integer blocks give a nonzero reversed product and a nontrivial
switched unit, whose diagonal pair is elementary. Matrix coefficients detect
the order of inverse factors.
Both empty-block orientations and the zero ring remain valid.
-/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.RectangularUnitSwitch

open Matrix.GeneralLinearGroup

private def integerA : Matrix (Fin 1) (Fin 1) ℤ :=
  Matrix.single 0 0 1

private def integerB : Matrix (Fin 1) (Fin 1) ℤ :=
  Matrix.single 0 0 (-2)

private def integerG : GL (Fin 1) ℤ where
  val := !![(-1 : ℤ)]
  inv := !![(-1 : ℤ)]
  val_inv := by decide
  inv_val := by decide

private theorem integerG_val :
    (integerG : Matrix (Fin 1) (Fin 1) ℤ) = 1 + integerA * integerB := by
  decide

private theorem integerB_mul_integerA_ne_zero : integerB * integerA ≠ 0 := by
  decide

private theorem integer_switch_val :
    (rectangularUnitSwitch integerA integerB integerG integerG_val :
      Matrix (Fin 1) (Fin 1) ℤ) = !![(-1 : ℤ)] := by
  rw [rectangularUnitSwitch_val]
  decide

private theorem integer_switch_inv_val :
    (((rectangularUnitSwitch integerA integerB integerG integerG_val)⁻¹ :
      GL (Fin 1) ℤ) : Matrix (Fin 1) (Fin 1) ℤ) = !![(-1 : ℤ)] := by
  rw [rectangularUnitSwitch_inv_val]
  decide

/-- The integer example with `B * A ≠ 0` has the ordered four-shear factorization. -/
private theorem integer_factorization :
    diagonalPairUnit integerG
      ((rectangularUnitSwitch integerA integerB integerG integerG_val)⁻¹) =
      rectangularUpperUnit integerA * rectangularLowerUnit integerB *
        rectangularUpperUnit integerA * rectangularLowerUnit integerB := by
  rw [diagonalPairUnit_rectangularUnitSwitch_inv_eq]
  have hupper :
      -(((integerG⁻¹ : GL (Fin 1) ℤ) : Matrix (Fin 1) (Fin 1) ℤ) * integerA) =
        integerA := by decide
  have hlower : -(integerB * (integerG : Matrix (Fin 1) (Fin 1) ℤ)) =
      integerB := by decide
  rw [hupper, hlower]

/-- The diagonal pair of negative-one units on two integer rank-one blocks is elementary. -/
theorem diagonalPairUnit_neg_one_mem_elementarySubgroup :
    diagonalPairUnit (-1 : GL (Fin 1) ℤ) (-1 : GL (Fin 1) ℤ) ∈
      elementarySubgroup (Fin 1 ⊕ Fin 1) ℤ := by
  have hG : integerG = (-1 : GL (Fin 1) ℤ) := by
    apply Units.ext
    decide
  have hswitch :
      (rectangularUnitSwitch integerA integerB integerG integerG_val)⁻¹ =
        (-1 : GL (Fin 1) ℤ) := by
    apply Units.ext
    rw [integer_switch_inv_val]
    decide
  have hmem := diagonalPairUnit_rectangularUnitSwitch_inv_mem_elementarySubgroup
    integerA integerB integerG integerG_val
  rwa [hswitch, hG] at hmem

private abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ

private def coefficientA : Coeff := !![(0 : ℤ), 1; 0, 0]
private def coefficientB : Coeff := !![(0 : ℤ), 0; -2, 0]
private def coefficientP : Coeff := !![(-1 : ℤ), 0; 0, 1]
private def coefficientQ : Coeff := !![(1 : ℤ), 0; 0, -1]

private def noncommA : Matrix (Fin 1) (Fin 1) Coeff := fun _ _ => coefficientA
private def noncommB : Matrix (Fin 1) (Fin 1) Coeff := fun _ _ => coefficientB

private def noncommG : GL (Fin 1) Coeff where
  val := fun _ _ => coefficientP
  inv := fun _ _ => coefficientP
  val_inv := by decide
  inv_val := by decide

private theorem noncommG_val :
    (noncommG : Matrix (Fin 1) (Fin 1) Coeff) = 1 + noncommA * noncommB := by
  decide

private theorem noncomm_reversed_product_ne_zero : noncommB * noncommA ≠ 0 := by
  decide

private theorem noncomm_inverse_changes_upper :
    ((noncommG⁻¹ : GL (Fin 1) Coeff) : Matrix (Fin 1) (Fin 1) Coeff) *
      noncommA ≠ noncommA := by
  decide

private theorem noncomm_lower_order_matters :
    noncommB * (noncommG : Matrix (Fin 1) (Fin 1) Coeff) ≠
      (noncommG : Matrix (Fin 1) (Fin 1) Coeff) * noncommB := by
  decide

private theorem noncomm_switch_val :
    (rectangularUnitSwitch noncommA noncommB noncommG noncommG_val :
      Matrix (Fin 1) (Fin 1) Coeff) = fun _ _ => coefficientQ := by
  rw [rectangularUnitSwitch_val]
  ext row col innerRow innerCol
  fin_cases row
  fin_cases col
  fin_cases innerRow <;> fin_cases innerCol <;> decide

private theorem noncomm_switch_inv_val :
    (((rectangularUnitSwitch noncommA noncommB noncommG noncommG_val)⁻¹ :
      GL (Fin 1) Coeff) : Matrix (Fin 1) (Fin 1) Coeff) =
      fun _ _ => coefficientQ := by
  rw [rectangularUnitSwitch_inv_val]
  ext row col innerRow innerCol
  fin_cases row
  fin_cases col
  fin_cases innerRow <;> fin_cases innerCol <;> decide

private theorem noncomm_ordered_factorization :
    diagonalPairUnit noncommG
      ((rectangularUnitSwitch noncommA noncommB noncommG noncommG_val)⁻¹) =
      rectangularUpperUnit noncommA * rectangularLowerUnit noncommB *
        rectangularUpperUnit noncommA * rectangularLowerUnit noncommB := by
  rw [diagonalPairUnit_rectangularUnitSwitch_inv_eq]
  have hupper :
      -(((noncommG⁻¹ : GL (Fin 1) Coeff) : Matrix (Fin 1) (Fin 1) Coeff) *
        noncommA) = noncommA := by decide
  have hlower : -(noncommB * (noncommG : Matrix (Fin 1) (Fin 1) Coeff)) =
      noncommB := by decide
  rw [hupper, hlower]

example (A : Matrix (Fin 0) (Fin 1) ℤ) (B : Matrix (Fin 1) (Fin 0) ℤ) :
    rectangularUnitSwitch A B (1 : GL (Fin 0) ℤ)
      (by ext row col; exact row.elim0) = 1 := by
  apply Units.ext
  simp [rectangularUnitSwitch_val]

example (A : Matrix (Fin 1) (Fin 0) ℤ) (B : Matrix (Fin 0) (Fin 1) ℤ) :
    rectangularUnitSwitch A B (1 : GL (Fin 1) ℤ)
      (by
        have hB : B = 0 := Subsingleton.elim _ _
        rw [hB, Matrix.mul_zero, add_zero]
        simp) = 1 := by
  apply Units.ext
  exact Subsingleton.elim _ _

example (A : Matrix (Fin 1) (Fin 1) (ZMod 1))
    (B : Matrix (Fin 1) (Fin 1) (ZMod 1)) :
    rectangularUnitSwitch A B (1 : GL (Fin 1) (ZMod 1))
      (Subsingleton.elim _ _) = 1 := by
  apply Units.ext
  exact Subsingleton.elim _ _

private def zeroA : Matrix (Fin 2) (Fin 1) ℤ :=
  fun row _ => if row = 0 then 1 else -1

private def zeroB : Matrix (Fin 1) (Fin 2) ℤ := fun _ _ => 1

private theorem zeroB_mul_zeroA : zeroB * zeroA = 0 := by decide

private theorem zeroA_mul_zeroB_ne_zero : zeroA * zeroB ≠ 0 := by decide

private theorem zero_product_specialization :
    diagonalPairUnit (zeroProductUnit zeroA zeroB zeroB_mul_zeroA)
      ((rectangularUnitSwitch zeroA zeroB
        (zeroProductUnit zeroA zeroB zeroB_mul_zeroA)
        (zeroProductUnit_val zeroA zeroB zeroB_mul_zeroA))⁻¹) =
      stabilize (Y := Fin 1) (zeroProductUnit zeroA zeroB zeroB_mul_zeroA) := by
  rw [rectangularUnitSwitch_zeroProductUnit, inv_one, diagonalPairUnit_one_right]

end GeneralLinearGroupsTests.RectangularUnitSwitch
