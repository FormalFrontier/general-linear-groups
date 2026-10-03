/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.ElementaryStabilization
public import GeneralLinearGroups.Reindex

/-!
# Rectangular upper block units

For independent finite index types, an upper block unit has an elementary
off-diagonal block. Explicit invertible diagonal blocks give an invertible
upper triangular matrix over any ring, including noncommutative rings.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR uG

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR}

section Semiring

variable [Semiring R]

/-- An independent pair of invertible diagonal blocks, assembled from the
existing stabilization and reindexing maps. -/
def diagonalPairUnit (A : GL X R) (D : GL Y R) : GL (X ⊕ Y) R :=
  stabilize (Y := Y) A *
    reindexEquiv R (Equiv.sumComm Y X) (stabilize (Y := X) D)

/-- Read back both diagonal blocks without requiring commutative coefficients. -/
@[simp]
theorem diagonalPairUnit_val (A : GL X R) (D : GL Y R) :
    (diagonalPairUnit A D : Matrix (X ⊕ Y) (X ⊕ Y) R) =
      Matrix.fromBlocks (A : Matrix X X R) 0 0 (D : Matrix Y Y R) := by
  have hswap :
      (reindexEquiv R (Equiv.sumComm Y X) (stabilize (Y := X) D) :
        Matrix (X ⊕ Y) (X ⊕ Y) R) = Matrix.fromBlocks 1 0 0 D := by
    ext row col
    rcases row with row | row <;> rcases col with col | col <;>
      simp [Matrix.one_apply]
  change Matrix.fromBlocks (A : Matrix X X R) 0 0 1 * _ = _
  rw [hswap, Matrix.fromBlocks_multiply]
  simp

/-- The inverse has the inverse of each diagonal block. -/
@[simp]
theorem diagonalPairUnit_inv (A : GL X R) (D : GL Y R) :
    (diagonalPairUnit A D)⁻¹ = diagonalPairUnit A⁻¹ D⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  simp [diagonalPairUnit_val, Matrix.fromBlocks_multiply]

/-- The first identity-block specialization is exactly stabilization. -/
@[simp]
theorem diagonalPairUnit_one_right (A : GL X R) :
    diagonalPairUnit A (1 : GL Y R) = stabilize (Y := Y) A := by
  simp [diagonalPairUnit]

/-- The second identity-block specialization is reindexed stabilization. -/
@[simp]
theorem diagonalPairUnit_one_left (D : GL Y R) :
    diagonalPairUnit (1 : GL X R) D =
      reindexEquiv R (Equiv.sumComm Y X) (stabilize (Y := X) D) := by
  simp [diagonalPairUnit]

end Semiring

section Ring

variable [Ring R]

/-- The rectangular upper unipotent matrix, with inverse upper block `-C`. -/
def rectangularUpperUnit (C : Matrix X Y R) : GL (X ⊕ Y) R where
  val := Matrix.fromBlocks 1 C 0 1
  inv := Matrix.fromBlocks 1 (-C) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

@[simp]
theorem rectangularUpperUnit_val (C : Matrix X Y R) :
    (rectangularUpperUnit C : Matrix (X ⊕ Y) (X ⊕ Y) R) =
      Matrix.fromBlocks 1 C 0 1 := rfl

@[simp]
theorem rectangularUpperUnit_inv (C : Matrix X Y R) :
    (rectangularUpperUnit C)⁻¹ = rectangularUpperUnit (-C) := by
  apply Units.ext
  rfl

@[simp]
theorem rectangularUpperUnit_zero :
    rectangularUpperUnit (0 : Matrix X Y R) = 1 := by
  apply Units.ext
  simp

/-- The upper block turns addition into ordered multiplication of units. -/
theorem rectangularUpperUnit_add (C E : Matrix X Y R) :
    rectangularUpperUnit (C + E) = rectangularUpperUnit C * rectangularUpperUnit E := by
  apply Units.ext
  simp [Matrix.fromBlocks_multiply, add_comm]

/-- One rectangular entry is the existing off-block elementary generator. -/
theorem rectangularUpperUnit_single (i : X) (j : Y) (c : R) :
    rectangularUpperUnit (Matrix.single i j c) =
      elementaryUnit (Sum.inl i) (Sum.inr j) (by simp) c := by
  apply Units.ext
  ext row col
  rcases row with row | row <;> rcases col with col | col <;>
    simp [rectangularUpperUnit, elementaryUnit, Matrix.single_apply, Matrix.one_apply]

/-- Rectangular upper unipotent matrices are elementary, even for empty blocks. -/
theorem rectangularUpperUnit_mem_elementarySubgroup (C : Matrix X Y R) :
    rectangularUpperUnit C ∈ elementarySubgroup (X ⊕ Y) R := by
  refine Matrix.induction_on' C ?_ ?_ ?_
  · rw [rectangularUpperUnit_zero]
    exact (elementarySubgroup (X ⊕ Y) R).one_mem
  · intro P Q hP hQ
    rw [rectangularUpperUnit_add]
    exact (elementarySubgroup (X ⊕ Y) R).mul_mem hP hQ
  · intro i j c
    rw [rectangularUpperUnit_single]
    exact elementaryUnit_mem _ _ _ _

/-- An upper triangular unit from *explicit* invertible diagonal blocks. -/
def triangularUnit (A : GL X R) (B : Matrix X Y R) (D : GL Y R) :
    GL (X ⊕ Y) R :=
  rectangularUpperUnit (B * ((D⁻¹ : GL Y R) : Matrix Y Y R)) * diagonalPairUnit A D

/-- The left ordered factorization is the definition of `triangularUnit`. -/
theorem triangularUnit_eq_upper_mul_diagonal (A : GL X R)
    (B : Matrix X Y R) (D : GL Y R) :
    triangularUnit A B D =
      rectangularUpperUnit (B * ((D⁻¹ : GL Y R) : Matrix Y Y R)) *
        diagonalPairUnit A D := rfl

@[simp]
theorem triangularUnit_val (A : GL X R) (B : Matrix X Y R) (D : GL Y R) :
    (triangularUnit A B D : Matrix (X ⊕ Y) (X ⊕ Y) R) =
      Matrix.fromBlocks (A : Matrix X X R) B 0 (D : Matrix Y Y R) := by
  simp only [triangularUnit, Units.val_mul, rectangularUpperUnit_val, diagonalPairUnit_val,
    Matrix.fromBlocks_multiply, one_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.zero_mul, Matrix.fromBlocks_inj, and_self, and_true, true_and]
  rw [Matrix.mul_assoc, ← Units.val_mul]
  simp

/-- The complementary right factorization retains coefficient order. -/
theorem triangularUnit_eq_diagonal_mul_upper (A : GL X R)
    (B : Matrix X Y R) (D : GL Y R) :
    triangularUnit A B D =
      diagonalPairUnit A D *
        rectangularUpperUnit (((A⁻¹ : GL X R) : Matrix X X R) * B) := by
  apply Units.ext
  simp only [triangularUnit_val, Units.val_mul, diagonalPairUnit_val,
    rectangularUpperUnit_val, Matrix.fromBlocks_multiply, mul_one, Matrix.mul_zero,
    add_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, Matrix.fromBlocks_inj,
    and_self, and_true, true_and]
  rw [← Matrix.mul_assoc, ← Units.val_mul]
  simp

/-- Ordered inverse blocks: the upper-right entry is `-A⁻¹ * B * D⁻¹`. -/
@[simp]
theorem triangularUnit_inv_val (A : GL X R) (B : Matrix X Y R) (D : GL Y R) :
    (((triangularUnit A B D)⁻¹ : GL (X ⊕ Y) R) : Matrix (X ⊕ Y) (X ⊕ Y) R) =
      Matrix.fromBlocks ((A⁻¹ : GL X R) : Matrix X X R)
        (-(((A⁻¹ : GL X R) : Matrix X X R) * B *
          ((D⁻¹ : GL Y R) : Matrix Y Y R))) 0
        ((D⁻¹ : GL Y R) : Matrix Y Y R) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [triangularUnit_val, Matrix.fromBlocks_multiply]
  simp only [Units.mul_inv, Matrix.mul_zero, add_zero, Matrix.mul_assoc,
    Matrix.mul_neg, Matrix.zero_mul, neg_zero, zero_add]
  rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]
  simp

/-- Any group homomorphism killing the elementary subgroup forgets the
off-diagonal block, without a normality or abelianness hypothesis. -/
theorem map_triangularUnit_eq_diagonalPairUnit {G : Type uG} [Group G]
    (f : GL (X ⊕ Y) R →* G)
    (hf : elementarySubgroup (X ⊕ Y) R ≤ f.ker)
    (A : GL X R) (B : Matrix X Y R) (D : GL Y R) :
    f (triangularUnit A B D) = f (diagonalPairUnit A D) := by
  rw [triangularUnit_eq_upper_mul_diagonal, map_mul]
  have hmem := hf (rectangularUpperUnit_mem_elementarySubgroup
    (B * ((D⁻¹ : GL Y R) : Matrix Y Y R)))
  simp only [MonoidHom.mem_ker] at hmem
  rw [hmem, one_mul]

/-- Equal-index upper blocks coincide with the published Whitehead unit. -/
theorem rectangularUpperUnit_eq_upperUnit (C : Matrix X X R) :
    rectangularUpperUnit C = upperUnit C := by
  apply Units.ext
  rfl

/-- The equal-index inverse pair is the existing Whitehead block diagonal. -/
theorem diagonalPairUnit_inv_pair (g : GL X R) :
    diagonalPairUnit g g⁻¹ = blockDiagonalUnit g := by
  apply Units.ext
  simp [diagonalPairUnit_val, blockDiagonalUnit]

end Ring

end Matrix.GeneralLinearGroup
