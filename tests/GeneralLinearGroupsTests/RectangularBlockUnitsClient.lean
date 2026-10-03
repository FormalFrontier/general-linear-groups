/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups.RectangularBlockUnits

/-! Unequal-rank, noncommutative and empty-block clients for rectangular units. -/

set_option warningAsError true

@[expose] public section

open Matrix.GeneralLinearGroup

private abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ

private def upperCoefficient : Coeffˣ :=
  elementaryUnit (R := ℤ) (ι := Fin 2) 0 1 (by decide) 1

private def lowerCoefficient : Coeffˣ :=
  elementaryUnit (R := ℤ) (ι := Fin 2) 1 0 (by decide) 1

private def singletonBlock (g : Coeffˣ) : GL (Fin 1) Coeff :=
  Units.map (Matrix.scalar (Fin 1) : Coeff →+* Matrix (Fin 1) (Fin 1) Coeff).toMonoidHom g

private def leftBlock : GL (Fin 1) Coeff := singletonBlock upperCoefficient

private def rightBlock : GL (Fin 1 ⊕ Fin 1) Coeff :=
  diagonalPairUnit (singletonBlock lowerCoefficient) 1

private def offDiagonal : Matrix (Fin 1) (Fin 1 ⊕ Fin 1) Coeff :=
  Matrix.of fun _ column =>
    match column with
    | Sum.inl _ => Matrix.single 1 1 (1 : ℤ)
    | Sum.inr _ => 0

private theorem offDiagonal_nonzero : offDiagonal ≠ 0 := by decide

private theorem noncommuting_coefficients :
    ((upperCoefficient : Coeff) * (lowerCoefficient : Coeff)) 0 0 = 2 ∧
      ((lowerCoefficient : Coeff) * (upperCoefficient : Coeff)) 0 0 = 1 := by
  decide

/-- The first factorization places `B D⁻¹` on the left; its `1,0` coefficient
is nonzero because `E₂₂ (I-E₂₁) = E₂₂-E₂₁`, not `(I-E₂₁) E₂₂`. -/
private theorem right_inverse_order_detected :
    (((offDiagonal * ((rightBlock⁻¹ : GL (Fin 1 ⊕ Fin 1) Coeff) :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) Coeff))
      0 (Sum.inl 0) : Coeff) 1 0) = -1 := by
  decide

/-- The second factorization places `A⁻¹ B` on the right; its `0,1`
coefficient is nonzero because `(I-E₁₂) E₂₂ = E₂₂-E₁₂`. -/
private theorem left_inverse_order_detected :
    (((((leftBlock⁻¹ : GL (Fin 1) Coeff) : Matrix (Fin 1) (Fin 1) Coeff) *
      offDiagonal) 0 (Sum.inl 0) : Coeff) 0 1) = -1 := by
  decide

private theorem unequal_rank_factorizations :
    triangularUnit leftBlock offDiagonal rightBlock =
        rectangularUpperUnit (offDiagonal *
          ((rightBlock⁻¹ : GL (Fin 1 ⊕ Fin 1) Coeff) :
            Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) Coeff)) *
          diagonalPairUnit leftBlock rightBlock ∧
      triangularUnit leftBlock offDiagonal rightBlock =
        diagonalPairUnit leftBlock rightBlock *
          rectangularUpperUnit (((leftBlock⁻¹ : GL (Fin 1) Coeff) :
            Matrix (Fin 1) (Fin 1) Coeff) * offDiagonal) := by
  exact ⟨triangularUnit_eq_upper_mul_diagonal _ _ _,
    triangularUnit_eq_diagonal_mul_upper _ _ _⟩

/-- In the inverse, the `0,1` coefficient is `+1` after the NEGATIVE ordered
product `-A⁻¹ B D⁻¹`. This would differ if either inverse factor were reversed. -/
private theorem unequal_rank_inverse_order_detected :
    (((triangularUnit leftBlock offDiagonal rightBlock)⁻¹
      (Sum.inl 0) (Sum.inr (Sum.inl 0)) : Coeff) 0 1) = 1 ∧
    (((triangularUnit leftBlock offDiagonal rightBlock)⁻¹
      (Sum.inl 0) (Sum.inr (Sum.inl 0)) : Coeff) 1 0) = 1 := by
  decide

private theorem unequal_rank_elementary :
    rectangularUpperUnit offDiagonal ∈
      elementarySubgroup (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) Coeff :=
  rectangularUpperUnit_mem_elementarySubgroup offDiagonal

example (C : Matrix (Fin 0) (Fin 1) ℤ) :
    rectangularUpperUnit C ∈ elementarySubgroup (Fin 0 ⊕ Fin 1) ℤ :=
  rectangularUpperUnit_mem_elementarySubgroup C

example (C : Matrix (Fin 1) (Fin 0) ℤ) :
    rectangularUpperUnit C ∈ elementarySubgroup (Fin 1 ⊕ Fin 0) ℤ :=
  rectangularUpperUnit_mem_elementarySubgroup C

example : rectangularUpperUnit (0 : Matrix (Fin 0) (Fin 0) ℤ) = 1 := by
  simp

example : (rectangularUpperUnit (0 : Matrix (Fin 0) (Fin 1) ℤ))⁻¹ = 1 := by
  simp

example (C E : Matrix (Fin 1) (Fin 0) ℤ) :
    rectangularUpperUnit (C + E) = rectangularUpperUnit C * rectangularUpperUnit E :=
  rectangularUpperUnit_add C E

example (A : GL (Fin 1) ℤ) :
    diagonalPairUnit A (1 : GL (Fin 0) ℤ) = stabilize A := by
  simp

example (D : GL (Fin 1) ℤ) :
    diagonalPairUnit (1 : GL (Fin 0) ℤ) D =
      reindexEquiv ℤ (Equiv.sumComm (Fin 1) (Fin 0))
        (stabilize (Y := Fin 0) D) := by
  simp

example : diagonalPairUnit (1 : GL (Fin 0) ℤ) (1 : GL (Fin 0) ℤ) = 1 := by
  simp

example (C : Matrix (Fin 1) (Fin 1) ℤ) :
    rectangularUpperUnit C = upperUnit C := rectangularUpperUnit_eq_upperUnit C

example (g : GL (Fin 1) ℤ) :
    diagonalPairUnit g g⁻¹ = blockDiagonalUnit g := diagonalPairUnit_inv_pair g
