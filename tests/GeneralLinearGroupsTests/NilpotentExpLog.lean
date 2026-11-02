/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.NonUnitalNilpotent
public import GeneralLinearGroups.PrincipalUnits.ExpLog
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Matrix and zero-algebra boundaries for finite exponential coordinates

The length-three Jordan block has a nonzero quadratic exponential term. Two
noncommuting square-zero matrix coordinates show why the addition formula needs
commutation. Two unipotent matrices of size two have a product with invertible,
non-nilpotent coordinate at one, so the unipotent subtype is not a subgroup.
The final statements retain the zero algebra, zero bound, and zero ideal.
-/

namespace Matrix

private def e3 (i j : Fin 3) : Matrix (Fin 3) (Fin 3) ℚ := single i j 1

private def x3 : Matrix (Fin 3) (Fin 3) ℚ := e3 0 1 + e3 1 2

/-- The length-three Jordan block has nonzero square in the top-right entry. -/
theorem jordanThree_sq : x3 ^ 2 = e3 0 2 := by
  simp [x3, e3, pow_two, add_mul, mul_add, single_mul_single_of_ne]

/-- The length-three Jordan block has cube zero. -/
theorem jordanThree_cube : x3 ^ 3 = 0 := by
  rw [pow_succ, jordanThree_sq]
  simp [x3, e3, mul_add, single_mul_single_of_ne]

private theorem e3_01_sq : e3 0 1 ^ 2 = 0 := by
  simp [e3, pow_two, single_mul_single_of_ne]

private theorem e3_12_sq : e3 1 2 ^ 2 = 0 := by
  simp [e3, pow_two, single_mul_single_of_ne]

/-- Its exponential has the required nonzero quadratic correction. -/
theorem exp_jordanThree :
    IsNilpotent.exp x3 =
      1 + x3 + (1 / 2 : ℚ) • e3 0 2 := by
  rw [IsNilpotent.exp_eq_sum jordanThree_cube]
  norm_num [Finset.sum_range_succ, jordanThree_sq]

/-- The nilpotent exponential is not the one-plus map in nilpotence order three. -/
theorem exp_jordanThree_ne_one_add :
    IsNilpotent.exp x3 ≠
      1 + x3 := by
  intro h
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ => M 0 2) h
  rw [exp_jordanThree] at h02
  norm_num [x3, e3, single] at h02

/-- Without commutation, the product of exponentials need not be the exponential of the sum. -/
theorem exp_single_mul_exp_single_ne_exp_add :
    (show IsNilpotent (e3 0 1) from ⟨2, e3_01_sq⟩).expUnit *
        (show IsNilpotent (e3 1 2) from ⟨2, e3_12_sq⟩).expUnit ≠
      (show IsNilpotent x3 from ⟨3, jordanThree_cube⟩).expUnit := by
  intro h
  have h02 := congrArg
    (fun u : (Matrix (Fin 3) (Fin 3) ℚ)ˣ => (u : Matrix (Fin 3) (Fin 3) ℚ) 0 2) h
  simp only [Units.val_mul, IsNilpotent.coe_expUnit] at h02
  rw [IsNilpotent.exp_eq_sum e3_01_sq, IsNilpotent.exp_eq_sum e3_12_sq,
    exp_jordanThree] at h02
  norm_num [Finset.sum_range_succ, mul_apply, Fin.sum_univ_succ, x3, e3, single] at h02

private def e2 (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℚ := single i j 1

private theorem e2_01_sq : e2 0 1 ^ 2 = 0 := by
  simp [e2, pow_two, single_mul_single_of_ne]

private theorem e2_10_sq : e2 1 0 ^ 2 = 0 := by
  simp [e2, pow_two, single_mul_single_of_ne]

private def upperTwo : (Matrix (Fin 2) (Fin 2) ℚ)ˣ :=
  IsNilpotent.oneAddUnitOfPowEqZero (e2 0 1) 2 e2_01_sq

private def lowerTwo : (Matrix (Fin 2) (Fin 2) ℚ)ˣ :=
  IsNilpotent.oneAddUnitOfPowEqZero (e2 1 0) 2 e2_10_sq

/-- The upper elementary unit has nilpotent coordinate at one. -/
theorem upperTwo_isNilpotent_sub_one :
    IsNilpotent ((upperTwo : Matrix (Fin 2) (Fin 2) ℚ) - 1) := by
  simpa only [upperTwo, IsNilpotent.oneAddUnitOfPowEqZero_val,
    add_sub_cancel_left] using (show IsNilpotent (e2 0 1) from ⟨2, e2_01_sq⟩)

/-- The lower elementary unit has nilpotent coordinate at one. -/
theorem lowerTwo_isNilpotent_sub_one :
    IsNilpotent ((lowerTwo : Matrix (Fin 2) (Fin 2) ℚ) - 1) := by
  simpa only [lowerTwo, IsNilpotent.oneAddUnitOfPowEqZero_val,
    add_sub_cancel_left] using (show IsNilpotent (e2 1 0) from ⟨2, e2_10_sq⟩)

/-- The product coordinate is the matrix with rows `(1,1)` and `(1,0)`. -/
theorem upperTwo_mul_lowerTwo_sub_one :
    ((upperTwo * lowerTwo : (Matrix (Fin 2) (Fin 2) ℚ)ˣ) :
      Matrix (Fin 2) (Fin 2) ℚ) - 1 = !![1, 1; 1, 0] := by
  simp only [Units.val_mul, upperTwo, lowerTwo, IsNilpotent.oneAddUnitOfPowEqZero_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e2, single, mul_apply, one_apply, Fin.sum_univ_succ]

/-- This product coordinate is invertible as a ring element. -/
theorem isUnit_upperTwo_mul_lowerTwo_sub_one :
    IsUnit ((((upperTwo * lowerTwo) : (Matrix (Fin 2) (Fin 2) ℚ)ˣ) :
      Matrix (Fin 2) (Fin 2) ℚ) - 1) := by
  rw [upperTwo_mul_lowerTwo_sub_one]
  refine ⟨⟨!![1, 1; 1, 0], !![0, 1; 1, -1], ?_, ?_⟩, rfl⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [mul_apply, Fin.sum_univ_succ]

/-- The product of these two unipotent units is not unipotent. -/
theorem not_isNilpotent_upperTwo_mul_lowerTwo_sub_one :
    ¬ IsNilpotent ((((upperTwo * lowerTwo) : (Matrix (Fin 2) (Fin 2) ℚ)ˣ) :
      Matrix (Fin 2) (Fin 2) ℚ) - 1) := by
  exact isUnit_upperTwo_mul_lowerTwo_sub_one.not_isNilpotent

end Matrix

section ZeroBound

universe u
variable {R : Type u} [Ring R] [Algebra ℚ R] [Subsingleton R]

/-- The exponential sum also admits the zero bound in the zero algebra. -/
theorem exp_zero_bound (x : {x : R // IsNilpotent x}) :
    (x.property.expUnit : R) =
      ∑ n ∈ Finset.range 0, (1 / (n.factorial : ℚ)) • x.val ^ n := by
  simpa only [IsNilpotent.coe_expUnit, one_div] using
    (IsNilpotent.exp_eq_sum (a := x.val) (k := 0) (Subsingleton.elim _ _))

/-- The logarithm sum also admits the zero bound in the zero algebra. -/
theorem log_zero_bound (u : {u : Rˣ // IsNilpotent ((u : R) - 1)}) :
    Units.log u = ∑ n ∈ Finset.Ico (1 : ℕ) 0,
      (((-1 : ℚ) ^ (n + 1)) / (n : ℚ)) • ((u.val : R) - 1) ^ n :=
  Units.log_eq_sum u 0 (Subsingleton.elim _ _)

end ZeroBound

section ZeroIdeal

universe u
variable {R : Type u} [Ring R] [Algebra ℚ R]

/-- The zero ideal has only the identity exponential principal unit, with no
nontriviality assumption. -/
theorem expLogEquiv_bot_apply (x : (⊥ : TwoSidedIdeal R).asIdeal) :
    (TwoSidedIdeal.isNil_bot (R := R)).expLogEquiv x = 1 := by
  have hx : x = 0 := by
    apply Subtype.ext
    simpa only [TwoSidedIdeal.bot_asIdeal, Ideal.mem_bot, Submodule.coe_zero] using x.property
  subst x
  exact Ideal.expLogEquivOfForallIsNilpotent_zero _ _

end ZeroIdeal
