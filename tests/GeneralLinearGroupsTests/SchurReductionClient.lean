/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.SchurReduction

/-! Ordered Schur reduction with unequal blocks, a nonunit corner and empty blocks. -/

set_option warningAsError true

@[expose] public section

open Matrix.GeneralLinearGroup

namespace GeneralLinearGroupsTests.SchurReduction

private abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ

private def upperCoefficient : Coeffˣ :=
  elementaryUnit (R := ℤ) (ι := Fin 2) 0 1 (by decide) 1

private def singletonBlock (unit : Coeffˣ) : GL (Fin 1) Coeff :=
  Units.map (Matrix.scalar (Fin 1) : Coeff →+* Matrix (Fin 1) (Fin 1) Coeff).toMonoidHom
    unit

private def pivot : GL (Fin 1) Coeff := singletonBlock upperCoefficient

private def upper : Matrix (Fin 1) (Fin 2) Coeff :=
  Matrix.of fun _ column => if column = 0 then Matrix.single 1 0 (1 : ℤ) else 0

private def lower : Matrix (Fin 2) (Fin 1) Coeff :=
  Matrix.of fun row _ => if row = 0 then 1 else 0

/-- The ordered cross-term makes the northwest coefficient of the southeast
block zero, although both off-diagonal blocks and the pivot are nontrivial. -/
private theorem southeast_entry :
    (((schurBlockUnit pivot upper lower (1 : GL (Fin 2) Coeff) :
      Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) Coeff)
        (Sum.inr 0) (Sum.inr 0) : Coeff) 0 0) = 0 := by
  rw [schurBlockUnit_val]
  decide

private theorem residual_entry :
    (((((schurBlockUnit pivot upper lower (1 : GL (Fin 2) Coeff) :
      Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) Coeff).toBlocks₂₂ -
        (schurBlockUnit pivot upper lower (1 : GL (Fin 2) Coeff) :
          Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) Coeff).toBlocks₂₁ *
          ((pivot⁻¹ : GL (Fin 1) Coeff) : Matrix (Fin 1) (Fin 1) Coeff) *
        (schurBlockUnit pivot upper lower (1 : GL (Fin 2) Coeff) :
          Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) Coeff).toBlocks₁₂)
      0 0 : Coeff) 0 0)) = 1 := by
  rw [schurBlockUnit_schur]
  decide

private theorem inverse_entry :
    ((((((schurBlockUnit pivot upper lower (1 : GL (Fin 2) Coeff))⁻¹ :
      GL (Fin 1 ⊕ Fin 2) Coeff) : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) Coeff)
        (Sum.inl 0) (Sum.inr 0) : Coeff) 0 0)) = 1 := by
  rw [schurBlockUnit_inv_val]
  decide

/-- Left multiplication by the inverse pivot differs from reversing the
coefficient order for the noncommuting off-diagonal entry. -/
private theorem coefficient_order_mismatch :
    (((((pivot⁻¹ : GL (Fin 1) Coeff) : Matrix (Fin 1) (Fin 1) Coeff) * upper)
      0 0 : Coeff) 0 0) ≠
      (((upper 0 0 : Coeff) * ((pivot⁻¹ : GL (Fin 1) Coeff) :
        Matrix (Fin 1) (Fin 1) Coeff) 0 0) 0 0) := by
  decide

/-- A nonidentity matrix-ring pivot and nonzero rectangular blocks exercise both
directions of the unit criterion without assuming the full block is a unit. -/
private theorem noncommutative_pivot_criterion :
    IsUnit (Matrix.fromBlocks (pivot : Matrix (Fin 1) (Fin 1) Coeff) upper lower
      (lower * ((pivot⁻¹ : GL (Fin 1) Coeff) : Matrix (Fin 1) (Fin 1) Coeff) * upper +
        (1 : Matrix (Fin 2) (Fin 2) Coeff))) ∧
    IsUnit ((lower * ((pivot⁻¹ : GL (Fin 1) Coeff) : Matrix (Fin 1) (Fin 1) Coeff) *
      upper + (1 : Matrix (Fin 2) (Fin 2) Coeff)) -
        lower * ⅟(pivot : Matrix (Fin 1) (Fin 1) Coeff) * upper) := by
  let : Invertible (pivot : Matrix (Fin 1) (Fin 1) Coeff) := pivot.invertible
  have hResidual : (lower * ((pivot⁻¹ : GL (Fin 1) Coeff) :
        Matrix (Fin 1) (Fin 1) Coeff) * upper + (1 : Matrix (Fin 2) (Fin 2) Coeff)) -
        lower * ⅟(pivot : Matrix (Fin 1) (Fin 1) Coeff) * upper =
      (1 : Matrix (Fin 2) (Fin 2) Coeff) := by
    rw [invOf_units]
    abel
  have hUnitResidual : IsUnit ((lower * ((pivot⁻¹ : GL (Fin 1) Coeff) :
        Matrix (Fin 1) (Fin 1) Coeff) * upper + (1 : Matrix (Fin 2) (Fin 2) Coeff)) -
        lower * ⅟(pivot : Matrix (Fin 1) (Fin 1) Coeff) * upper) := by
    rw [hResidual]
    exact isUnit_one
  have hCriterion := Matrix.isUnit_fromBlocks_iff_of_invertible₁₁_ring
    (A := (pivot : Matrix (Fin 1) (Fin 1) Coeff)) (B := upper) (C := lower)
    (D := lower * ((pivot⁻¹ : GL (Fin 1) Coeff) : Matrix (Fin 1) (Fin 1) Coeff) * upper +
      (1 : Matrix (Fin 2) (Fin 2) Coeff))
  have hBlock := hCriterion.mpr hUnitResidual
  exact ⟨hBlock, hCriterion.mp hBlock⟩

private def integralPivot : GL (Fin 1) ℤ :=
  Units.map (Matrix.scalar (Fin 1) : ℤ →+* Matrix (Fin 1) (Fin 1) ℤ).toMonoidHom
    (-1 : ℤˣ)

private def integralUpper : Matrix (Fin 1) (Fin 2) ℤ :=
  Matrix.of fun _ column => if column = 0 then 1 else 0

private def integralLower : Matrix (Fin 2) (Fin 1) ℤ :=
  Matrix.of fun row _ => if row = 0 then 1 else 0

/-- The image corollary applies to a supplied block unit with its block value
and ordered Schur residual explicitly identified. -/
private theorem supplied_integral_image :
    Matrix.GeneralLinearGroup.det
        (schurBlockUnit integralPivot integralUpper integralLower (1 : GL (Fin 2) ℤ)) =
      Matrix.GeneralLinearGroup.det (diagonalPairUnit integralPivot (1 : GL (Fin 2) ℤ)) := by
  let M := schurBlockUnit integralPivot integralUpper integralLower (1 : GL (Fin 2) ℤ)
  have hker : elementarySubgroup (Fin 1 ⊕ Fin 2) ℤ ≤
      (Matrix.GeneralLinearGroup.det (n := Fin 1 ⊕ Fin 2) (R := ℤ)).ker := by
    intro g hg
    exact Matrix.det_elementarySubgroup_eq_one ⟨g, hg⟩
  have hM : (M : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℤ) =
      Matrix.fromBlocks (integralPivot : Matrix (Fin 1) (Fin 1) ℤ)
        integralUpper integralLower
        (integralLower * ((integralPivot⁻¹ : GL (Fin 1) ℤ) : Matrix (Fin 1) (Fin 1) ℤ) *
          integralUpper + (1 : Matrix (Fin 2) (Fin 2) ℤ)) :=
    schurBlockUnit_val integralPivot integralUpper integralLower 1
  have hS : (1 : Matrix (Fin 2) (Fin 2) ℤ) =
      (integralLower * ((integralPivot⁻¹ : GL (Fin 1) ℤ) : Matrix (Fin 1) (Fin 1) ℤ) *
        integralUpper + (1 : Matrix (Fin 2) (Fin 2) ℤ)) -
        integralLower * ((integralPivot⁻¹ : GL (Fin 1) ℤ) : Matrix (Fin 1) (Fin 1) ℤ) *
          integralUpper := by
    abel
  exact map_unit_eq_diagonalPairUnit_of_fromBlocks
    (Matrix.GeneralLinearGroup.det (n := Fin 1 ⊕ Fin 2) (R := ℤ)) hker
    M integralPivot integralUpper integralLower
    (integralLower * ((integralPivot⁻¹ : GL (Fin 1) ℤ) : Matrix (Fin 1) (Fin 1) ℤ) *
      integralUpper + (1 : Matrix (Fin 2) (Fin 2) ℤ)) hM 1 hS

/-- A block unit can have a nonunit southeast corner and nontrivial
determinant image; this uses the elementary-kernel image theorem. -/
theorem integral_nonunit_corner_with_nontrivial_image :
    ∃ M : GL (Fin 1 ⊕ Fin 2) ℤ,
      Matrix.GeneralLinearGroup.det M = (-1 : ℤˣ) ∧
        ¬ IsUnit ((M : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℤ).toBlocks₂₂) := by
  let M := schurBlockUnit integralPivot integralUpper integralLower (1 : GL (Fin 2) ℤ)
  refine ⟨M, ?_, ?_⟩
  · have hker : elementarySubgroup (Fin 1 ⊕ Fin 2) ℤ ≤
        (Matrix.GeneralLinearGroup.det (n := Fin 1 ⊕ Fin 2) (R := ℤ)).ker := by
      intro g hg
      exact Matrix.det_elementarySubgroup_eq_one ⟨g, hg⟩
    have hdet := map_schurBlockUnit_eq_diagonalPairUnit
      (Matrix.GeneralLinearGroup.det (n := Fin 1 ⊕ Fin 2) (R := ℤ)) hker
      integralPivot integralUpper integralLower (1 : GL (Fin 2) ℤ)
    change Matrix.GeneralLinearGroup.det (schurBlockUnit integralPivot integralUpper
      integralLower (1 : GL (Fin 2) ℤ)) = (-1 : ℤˣ)
    rw [hdet]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, diagonalPairUnit_val]
    decide
  · intro h
    have hdet : IsUnit ((M : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℤ).toBlocks₂₂).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp h
    have hzero : ((M : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℤ).toBlocks₂₂).det = 0 := by
      rw [show (M : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℤ) = _ from
        schurBlockUnit_val integralPivot integralUpper integralLower 1]
      decide
    exact not_isUnit_zero (hzero ▸ hdet)

end GeneralLinearGroupsTests.SchurReduction

example (S : GL (Fin 1) ℤ) :
    schurBlockUnit (1 : GL (Fin 0) ℤ) (0 : Matrix (Fin 0) (Fin 1) ℤ)
      (0 : Matrix (Fin 1) (Fin 0) ℤ) S =
        reindexEquiv ℤ (Equiv.sumComm (Fin 1) (Fin 0)) (stabilize (Y := Fin 0) S) :=
  schurBlockUnit_empty_left S

example (A : GL (Fin 1) (ZMod 1)) :
    schurBlockUnit A (0 : Matrix (Fin 1) (Fin 0) (ZMod 1))
      (0 : Matrix (Fin 0) (Fin 1) (ZMod 1)) (1 : GL (Fin 0) (ZMod 1)) =
        stabilize A :=
  schurBlockUnit_empty_right A

example (D : Matrix (Fin 1) (Fin 1) ℤ) :
    IsUnit (Matrix.fromBlocks (1 : Matrix (Fin 0) (Fin 0) ℤ) 0 0 D) ↔ IsUnit D := by
  let : Invertible (1 : Matrix (Fin 0) (Fin 0) ℤ) := invertibleOne
  rw [Matrix.isUnit_fromBlocks_iff_of_invertible₁₁_ring]
  simp

example (A : GL (Fin 1) ℤ) :
    IsUnit (Matrix.fromBlocks (A : Matrix (Fin 1) (Fin 1) ℤ) 0 0
      (1 : Matrix (Fin 0) (Fin 0) ℤ)) ↔ IsUnit (1 : Matrix (Fin 0) (Fin 0) ℤ) := by
  let : Invertible (A : Matrix (Fin 1) (Fin 1) ℤ) := A.invertible
  rw [Matrix.isUnit_fromBlocks_iff_of_invertible₁₁_ring]
  simp

example (A : GL (Fin 1) (ZMod 1)) :
    IsUnit (Matrix.fromBlocks (A : Matrix (Fin 1) (Fin 1) (ZMod 1)) 0 0
      (1 : Matrix (Fin 0) (Fin 0) (ZMod 1))) ↔
        IsUnit (1 : Matrix (Fin 0) (Fin 0) (ZMod 1)) := by
  let : Invertible (A : Matrix (Fin 1) (Fin 1) (ZMod 1)) := A.invertible
  rw [Matrix.isUnit_fromBlocks_iff_of_invertible₁₁_ring]
  simp

example (A : GL (Fin 1) ℤ) (B : Matrix (Fin 1) (Fin 2) ℤ)
    (C : Matrix (Fin 2) (Fin 1) ℤ) (S : GL (Fin 2) ℤ) :
    (((schurBlockUnit A B C S)⁻¹ : GL (Fin 1 ⊕ Fin 2) ℤ) :
      Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℤ).toBlocks₂₂ =
        ((S⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) := by
  let : Invertible (A : Matrix (Fin 1) (Fin 1) ℤ) := A.invertible
  let D : Matrix (Fin 2) (Fin 2) ℤ :=
    C * ((A⁻¹ : GL (Fin 1) ℤ) : Matrix (Fin 1) (Fin 1) ℤ) * B +
      (S : Matrix (Fin 2) (Fin 2) ℤ)
  have hResidual : D - C * ⅟(A : Matrix (Fin 1) (Fin 1) ℤ) * B =
      (S : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [invOf_units]
    dsimp [D]
    abel
  let : Invertible (D - C * ⅟(A : Matrix (Fin 1) (Fin 1) ℤ) * B) :=
    S.invertible.copy _ hResidual
  let : Invertible (Matrix.fromBlocks (A : Matrix (Fin 1) (Fin 1) ℤ) B C D) :=
    Matrix.fromBlocks₁₁Invertible A B C D
  calc
    (((schurBlockUnit A B C S)⁻¹ : GL (Fin 1 ⊕ Fin 2) ℤ) :
      Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℤ).toBlocks₂₂ =
        (⅟(Matrix.fromBlocks (A : Matrix (Fin 1) (Fin 1) ℤ) B C D)).toBlocks₂₂ := by
          exact congrArg Matrix.toBlocks₂₂ (schurBlockUnit_inv_eq_invOf_fromBlocks₁₁ A B C S)
    _ = _ := by
      rw [Matrix.invOf_fromBlocks₁₁_eq A B C D, Matrix.toBlocks_fromBlocks₂₂]
      apply invOf_eq_right_inv
      rw [hResidual]
      exact Units.val_inv S
