/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.KroneckerUnits
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Finite clients for Kronecker products of matrix units

Permutation matrices over `Nat` distinguish coefficient order in a matrix semiring.
The generalized unit conclusion identifies the Kronecker matrix with a chosen scalar
unit on the product index; its stored inverse undoes the forward basis action, whereas
the Kronecker product of the input inverses does not.

Empty indices and the zero coefficient semiring give positive unit examples without
nonempty or nontriviality assumptions. Over commutative coefficients, the Units-data
bridge transfers the stored inverse and a nontrivial basis action from stock
`Matrix.GeneralLinearGroup.kronecker`.

## References

The constructions used here are formalized in Mathlib's
`Mathlib.LinearAlgebra.Matrix.Permutation`,
`Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`,
`Mathlib.LinearAlgebra.Matrix.Kronecker`, and
`Mathlib.Algebra.Group.Units.Hom`.
-/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.KroneckerUnits

open scoped Matrix

namespace PermutationCoefficients

/-- Natural-number matrices supplying noncommutative coefficients for the permutation examples. -/
abbrev Coefficient := Matrix (Fin 3) (Fin 3) Nat

private def swapZeroOne : Equiv.Perm (Fin 3) := Equiv.swap 0 1
private def swapOneTwo : Equiv.Perm (Fin 3) := Equiv.swap 1 2

-- The hom uses the inverse permutation, unlike the anti-multiplicative permMatrix.
private def firstUnit : Coefficientˣ :=
  (Matrix.permMatrixHom (n := Fin 3) (R := Nat)).toHomUnits swapZeroOne

private def secondUnit : Coefficientˣ :=
  (Matrix.permMatrixHom (n := Fin 3) (R := Nat)).toHomUnits swapOneTwo

private def forwardCoefficient : Coefficient := (firstUnit * secondUnit).val
private def reverseCoefficient : Coefficient := (secondUnit * firstUnit).val

private def firstOuterUnit : Matrix.GeneralLinearGroup (Fin 1) Coefficient :=
  Matrix.GeneralLinearGroup.scalar (Fin 1) firstUnit

private def secondOuterUnit : Matrix.GeneralLinearGroup (Fin 1) Coefficient :=
  Matrix.GeneralLinearGroup.scalar (Fin 1) secondUnit

private def productOuterUnit : Matrix.GeneralLinearGroup (Fin 1 × Fin 1) Coefficient :=
  Matrix.GeneralLinearGroup.scalar (Fin 1 × Fin 1) (firstUnit * secondUnit)

private theorem firstUnit_val :
    firstUnit.val = !![(0 : Nat), 1, 0; 1, 0, 0; 0, 0, 1] := by
  ext row col
  fin_cases row <;> fin_cases col <;> decide

private theorem secondUnit_val :
    secondUnit.val = !![(1 : Nat), 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext row col
  fin_cases row <;> fin_cases col <;> decide

private theorem firstUnit_inv : firstUnit.inv = firstUnit.val := by
  ext row col
  fin_cases row <;> fin_cases col <;> decide

private theorem secondUnit_inv : secondUnit.inv = secondUnit.val := by
  ext row col
  fin_cases row <;> fin_cases col <;> decide

private theorem forwardCoefficient_eq :
    forwardCoefficient = !![(0 : Nat), 0, 1; 1, 0, 0; 0, 1, 0] := by
  change firstUnit.val * secondUnit.val = _
  rw [firstUnit_val, secondUnit_val]
  decide

private theorem reverseCoefficient_eq :
    reverseCoefficient = !![(0 : Nat), 1, 0; 0, 0, 1; 1, 0, 0] := by
  change secondUnit.val * firstUnit.val = _
  rw [secondUnit_val, firstUnit_val]
  decide

private theorem coefficient_order :
    forwardCoefficient 0 1 = 0 ∧ reverseCoefficient 0 1 = 1 := by
  rw [forwardCoefficient_eq, reverseCoefficient_eq]
  decide

private theorem forward_square : forwardCoefficient ^ 2 = reverseCoefficient := by
  rw [pow_two, forwardCoefficient_eq, reverseCoefficient_eq]
  decide

private theorem forward_square_ne_one : forwardCoefficient ^ 2 ≠ 1 := by
  rw [forward_square, reverseCoefficient_eq]
  decide

private theorem productOuterUnit_val :
    productOuterUnit.val = Matrix.kronecker firstOuterUnit.val secondOuterUnit.val := by
  change Matrix.scalar (Fin 1 × Fin 1) (firstUnit.val * secondUnit.val) =
    Matrix.kronecker (Matrix.scalar (Fin 1) firstUnit.val)
      (Matrix.scalar (Fin 1) secondUnit.val)
  simpa only [Matrix.scalar_apply, Matrix.kronecker] using
    (Matrix.diagonal_kronecker_diagonal
      (fun _ : Fin 1 => firstUnit.val) (fun _ : Fin 1 => secondUnit.val)).symm

private theorem productOuterUnit_inv :
    productOuterUnit.inv = Matrix.scalar (Fin 1 × Fin 1) reverseCoefficient := by
  change Matrix.scalar (Fin 1 × Fin 1) (secondUnit.inv * firstUnit.inv) = _
  rw [firstUnit_inv, secondUnit_inv]
  rfl

private theorem productIsUnit :
    IsUnit (Matrix.kronecker firstOuterUnit.val secondOuterUnit.val) :=
  Matrix.isUnit_kronecker firstOuterUnit.isUnit secondOuterUnit.isUnit

private theorem product_unit_eq : productIsUnit.unit = productOuterUnit := by
  apply Units.ext
  rw [IsUnit.unit_spec]
  exact productOuterUnit_val.symm

private theorem product_val_entry :
    productIsUnit.unit.val (0, 0) (0, 0) = forwardCoefficient := by
  rw [product_unit_eq]
  change Matrix.scalar (Fin 1 × Fin 1) forwardCoefficient (0, 0) (0, 0) = _
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]

private theorem product_inv_entry :
    productIsUnit.unit.inv (0, 0) (0, 0) = reverseCoefficient := by
  rw [product_unit_eq, productOuterUnit_inv]
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]

/-- The chosen output has different value and inverse coefficient entries. -/
example :
    productIsUnit.unit.val (0, 0) (0, 0) 0 1 = 0 ∧
      productIsUnit.unit.inv (0, 0) (0, 0) 0 1 = 1 := by
  rw [product_val_entry, product_inv_entry]
  exact coefficient_order

/-- The reversed stored inverse undoes the mixed identity-factor product. -/
example :
    productIsUnit.unit.inv *
      (Matrix.kronecker firstOuterUnit.val (1 : Matrix (Fin 1) (Fin 1) Coefficient) *
        Matrix.kronecker (1 : Matrix (Fin 1) (Fin 1) Coefficient) secondOuterUnit.val) =
      1 := by
  rw [Matrix.kronecker_one_mul_one_kronecker]
  change (↑(productIsUnit.unit⁻¹) : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) Coefficient) *
    Matrix.kronecker firstOuterUnit.val secondOuterUnit.val = 1
  exact productIsUnit.val_inv_mul

private theorem forward_basis :
    forwardCoefficient *ᵥ Pi.single (1 : Fin 3) (1 : Nat) =
      Pi.single (2 : Fin 3) 1 := by
  rw [forwardCoefficient_eq]
  ext row
  fin_cases row <;> decide

private theorem reverse_basis :
    reverseCoefficient *ᵥ Pi.single (2 : Fin 3) (1 : Nat) =
      Pi.single (1 : Fin 3) 1 := by
  rw [reverseCoefficient_eq]
  ext row
  fin_cases row <;> decide

private theorem forward_basis_two :
    forwardCoefficient *ᵥ Pi.single (2 : Fin 3) (1 : Nat) =
      Pi.single (0 : Fin 3) 1 := by
  rw [forwardCoefficient_eq]
  ext row
  fin_cases row <;> decide

/-- Forward composition sends the first basis column to the second and the inverse returns it. -/
example :
    productIsUnit.unit.val (0, 0) (0, 0) *ᵥ Pi.single (1 : Fin 3) (1 : Nat) =
        Pi.single (2 : Fin 3) 1 ∧
      productIsUnit.unit.inv (0, 0) (0, 0) *ᵥ
        (productIsUnit.unit.val (0, 0) (0, 0) *ᵥ Pi.single (1 : Fin 3) (1 : Nat)) =
        Pi.single (1 : Fin 3) 1 := by
  rw [product_val_entry, product_inv_entry, forward_basis]
  exact ⟨rfl, reverse_basis⟩

private theorem inverse_kronecker_entry :
    Matrix.kronecker firstOuterUnit.inv secondOuterUnit.inv (0, 0) (0, 0) =
      forwardCoefficient := by
  change (Matrix.scalar (Fin 1) firstUnit.inv 0 0) *
    (Matrix.scalar (Fin 1) secondUnit.inv 0 0) = _
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  rw [firstUnit_inv, secondUnit_inv]
  rfl

/-- Tensoring the input inverses gives the wrong stored inverse over these coefficients. -/
example :
    Matrix.kronecker firstOuterUnit.inv secondOuterUnit.inv ≠ productIsUnit.unit.inv := by
  intro h
  have hentry := congrArg
    (fun A : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) Coefficient =>
      A (0, 0) (0, 0) 0 1) h
  rw [inverse_kronecker_entry, product_inv_entry,
    forwardCoefficient_eq, reverseCoefficient_eq] at hentry
  exact Nat.zero_ne_one hentry

/-- The wrong inverse sends the forward image to the zeroth basis column, not back to the first. -/
example :
    Matrix.kronecker firstOuterUnit.inv secondOuterUnit.inv (0, 0) (0, 0) *ᵥ
      (productIsUnit.unit.val (0, 0) (0, 0) *ᵥ Pi.single (1 : Fin 3) (1 : Nat)) =
        Pi.single (0 : Fin 3) 1 ∧
      forwardCoefficient ^ 2 ≠ (1 : Coefficient) := by
  rw [inverse_kronecker_entry, product_val_entry, forward_basis]
  exact ⟨forward_basis_two, forward_square_ne_one⟩

end PermutationCoefficients

namespace EmptyIndices

private def leftUnit : Matrix.GeneralLinearGroup (Fin 0) Nat := 1
private def rightUnit : Matrix.GeneralLinearGroup (Fin 1) Nat := 1
private def targetUnit : Matrix.GeneralLinearGroup (Fin 0 × Fin 1) Nat := 1

private theorem productIsUnit : IsUnit (Matrix.kronecker leftUnit.val rightUnit.val) :=
  Matrix.isUnit_kronecker leftUnit.isUnit rightUnit.isUnit

private theorem product_unit_eq : productIsUnit.unit = targetUnit := by
  apply Units.ext
  rw [IsUnit.unit_spec]
  ext row col
  exact row.1.elim0

/-- Both inputs are identity units; the empty output value and stored inverse are zero matrices. -/
example :
    productIsUnit.unit = targetUnit ∧
      productIsUnit.unit.val = (0 : Matrix (Fin 0 × Fin 1) (Fin 0 × Fin 1) Nat) ∧
      productIsUnit.unit.inv = (0 : Matrix (Fin 0 × Fin 1) (Fin 0 × Fin 1) Nat) := by
  rw [product_unit_eq]
  exact ⟨rfl, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The mixed product has a genuine inverse even though its product index is empty. -/
example :
    (Matrix.kronecker leftUnit.val (1 : Matrix (Fin 1) (Fin 1) Nat) *
        Matrix.kronecker (1 : Matrix (Fin 0) (Fin 0) Nat) rightUnit.val) *
      productIsUnit.unit.inv = 1 := by
  rw [Matrix.kronecker_one_mul_one_kronecker]
  change Matrix.kronecker leftUnit.val rightUnit.val *
    (↑(productIsUnit.unit⁻¹) : Matrix (Fin 0 × Fin 1) (Fin 0 × Fin 1) Nat) = 1
  exact productIsUnit.mul_val_inv

end EmptyIndices

namespace ZeroCoefficients

private abbrev Coefficient := ZMod 1

private def leftUnit : Matrix.GeneralLinearGroup (Fin 2) Coefficient := 1
private def rightUnit : Matrix.GeneralLinearGroup (Fin 3) Coefficient := 1
private def targetUnit : Matrix.GeneralLinearGroup (Fin 2 × Fin 3) Coefficient := 1

private theorem productIsUnit : IsUnit (Matrix.kronecker leftUnit.val rightUnit.val) :=
  Matrix.isUnit_kronecker leftUnit.isUnit rightUnit.isUnit

private theorem product_unit_eq : productIsUnit.unit = targetUnit := by
  apply Units.ext
  rw [IsUnit.unit_spec]
  ext row col
  exact Subsingleton.elim _ _

/-- These identity units on nonempty finite indices have zero value and inverse data. -/
example :
    leftUnit.val = 0 ∧ leftUnit.inv = 0 ∧ rightUnit.val = 0 ∧ rightUnit.inv = 0 := by
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The generalized output is the identity unit, with zero value and stored inverse. -/
example :
    productIsUnit.unit = targetUnit ∧ productIsUnit.unit.val = 0 ∧
      productIsUnit.unit.inv = 0 := by
  rw [product_unit_eq]
  exact ⟨rfl, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Both inverse laws have right-hand side zero, the identity matrix over `ZMod 1`. -/
example :
    productIsUnit.unit.val * productIsUnit.unit.inv = 0 ∧
      productIsUnit.unit.inv * productIsUnit.unit.val = 0 := by
  constructor
  · calc
      _ = 1 := productIsUnit.unit.val_inv
      _ = 0 := Subsingleton.elim _ _
  · calc
      _ = 1 := productIsUnit.unit.inv_val
      _ = 0 := Subsingleton.elim _ _

/-- The mixed identity factors are undone to the zero identity matrix. -/
example :
    productIsUnit.unit.inv *
      (Matrix.kronecker leftUnit.val (1 : Matrix (Fin 3) (Fin 3) Coefficient) *
        Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) Coefficient) rightUnit.val) =
      0 := by
  rw [Matrix.kronecker_one_mul_one_kronecker]
  change (↑(productIsUnit.unit⁻¹) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) Coefficient) *
    Matrix.kronecker leftUnit.val rightUnit.val = 0
  rw [productIsUnit.val_inv_mul]
  exact Subsingleton.elim _ _

end ZeroCoefficients

namespace CommutativeCoefficients

private def leftUnit : Matrix.GeneralLinearGroup (Fin 2) Nat :=
  (Matrix.permMatrixHom (n := Fin 2) (R := Nat)).toHomUnits (Equiv.swap 0 1)

private def rightUnit : Matrix.GeneralLinearGroup (Fin 3) Nat :=
  (Matrix.permMatrixHom (n := Fin 3) (R := Nat)).toHomUnits (Equiv.swap 1 2)

private theorem productIsUnit : IsUnit (Matrix.kronecker leftUnit.val rightUnit.val) :=
  Matrix.isUnit_kronecker leftUnit.isUnit rightUnit.isUnit

private theorem product_unit_eq :
    productIsUnit.unit = Matrix.GeneralLinearGroup.kronecker leftUnit rightUnit :=
  Matrix.GeneralLinearGroup.isUnit_kronecker_unit leftUnit rightUnit

/-- The Units-data bridge transfers the stock stored inverse, not just a proof of invertibility. -/
example :
    productIsUnit.unit.inv = Matrix.kronecker leftUnit.inv rightUnit.inv := by
  rw [product_unit_eq]
  rfl

/-- The chosen permutation product and its stored inverse both have nonzero off-diagonal entries. -/
example :
    productIsUnit.unit.val (1, 2) (0, 1) = 1 ∧
      productIsUnit.unit.inv (0, 1) (1, 2) = 1 := by
  rw [product_unit_eq]
  constructor <;> decide

private theorem product_basis :
    productIsUnit.unit.val *ᵥ Pi.single ((0 : Fin 2), (1 : Fin 3)) (1 : Nat) =
      Pi.single ((1 : Fin 2), (2 : Fin 3)) 1 := by
  rw [product_unit_eq]
  ext row
  rcases row with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> decide

private theorem inverse_basis :
    productIsUnit.unit.inv *ᵥ Pi.single ((1 : Fin 2), (2 : Fin 3)) (1 : Nat) =
      Pi.single ((0 : Fin 2), (1 : Fin 3)) 1 := by
  rw [product_unit_eq]
  ext row
  rcases row with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> decide

/-- The bridge identifies the nontrivial basis permutation and the inverse round trip. -/
example :
    productIsUnit.unit.val *ᵥ Pi.single ((0 : Fin 2), (1 : Fin 3)) (1 : Nat) =
        Pi.single ((1 : Fin 2), (2 : Fin 3)) 1 ∧
      productIsUnit.unit.inv *ᵥ
        (productIsUnit.unit.val *ᵥ Pi.single ((0 : Fin 2), (1 : Fin 3)) (1 : Nat)) =
        Pi.single ((0 : Fin 2), (1 : Fin 3)) 1 := by
  rw [product_basis]
  exact ⟨rfl, inverse_basis⟩

end CommutativeCoefficients

end GeneralLinearGroupsTests.KroneckerUnits
