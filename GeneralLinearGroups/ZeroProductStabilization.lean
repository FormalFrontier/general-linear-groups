/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.UnitPivotDiagonalization
public import GeneralLinearGroups.NonUnitalNilpotent

/-!
# Elementary stabilization of zero-product blocks

When rectangular matrices `A` and `B` satisfy `B * A = 0`, the square matrix
`1 + A * B` is invertible. Its stabilization by an identity block is a
commutator of rectangular upper and lower units and hence elementary.
The index types may be empty, and the coefficient ring may be the zero ring.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] {R : Type uR} [Ring R]

/-- The unit `1 + A * B` for a pair of rectangular matrices with `B * A = 0`. -/
def zeroProductUnit (A : Matrix X Y R) (B : Matrix Y X R)
    (hBA : B * A = 0) : GL X R :=
  IsNilpotent.oneAddUnitOfPowEqZero (A * B) 2 (by
    rw [pow_two]
    calc
      (A * B) * (A * B) = A * (B * A) * B := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hBA, Matrix.mul_zero, Matrix.zero_mul])

/-- The underlying matrix of `zeroProductUnit` is `1 + A * B`. -/
@[simp]
theorem zeroProductUnit_val (A : Matrix X Y R) (B : Matrix Y X R)
    (hBA : B * A = 0) :
    (zeroProductUnit A B hBA : Matrix X X R) = 1 + A * B := rfl

/-- Its inverse has underlying matrix `1 - A * B`. -/
@[simp]
theorem zeroProductUnit_inv_val (A : Matrix X Y R) (B : Matrix Y X R)
    (hBA : B * A = 0) :
    (((zeroProductUnit A B hBA)⁻¹ : GL X R) : Matrix X X R) = 1 - A * B := by
  change (∑ i ∈ Finset.range 2, (-(A * B)) ^ i) = 1 - A * B
  simp [Finset.sum_range_succ, sub_eq_add_neg]

variable [DecidableEq Y]

/-- The stabilized zero-product unit is an ordered commutator of rectangular shears. -/
theorem stabilize_zeroProductUnit_eq (A : Matrix X Y R) (B : Matrix Y X R)
    (hBA : B * A = 0) :
    stabilize (Y := Y) (zeroProductUnit A B hBA) =
      rectangularUpperUnit A * rectangularLowerUnit B *
        (rectangularUpperUnit A)⁻¹ * (rectangularLowerUnit B)⁻¹ := by
  rw [rectangularUpperUnit_inv, rectangularLowerUnit_inv]
  apply Units.ext
  have hABA : (1 + A * B) * A = A := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hBA, Matrix.mul_zero, add_zero]
  simp only [Units.val_mul, rectangularUpperUnit_val, rectangularLowerUnit_val]
  change Matrix.fromBlocks (1 + A * B) 0 0 1 = _
  simp [Matrix.fromBlocks_multiply, hBA, hABA]

/-- Stabilizing `1 + A * B` gives an element of the existing elementary subgroup. -/
theorem stabilize_zeroProductUnit_mem_elementarySubgroup
    (A : Matrix X Y R) (B : Matrix Y X R) (hBA : B * A = 0) :
    stabilize (Y := Y) (zeroProductUnit A B hBA) ∈
      elementarySubgroup (X ⊕ Y) R := by
  rw [stabilize_zeroProductUnit_eq A B hBA]
  exact (elementarySubgroup (X ⊕ Y) R).mul_mem
    ((elementarySubgroup (X ⊕ Y) R).mul_mem
      ((elementarySubgroup (X ⊕ Y) R).mul_mem
        (rectangularUpperUnit_mem_elementarySubgroup A)
        (rectangularLowerUnit_mem_elementarySubgroup B))
      ((elementarySubgroup (X ⊕ Y) R).inv_mem
        (rectangularUpperUnit_mem_elementarySubgroup A)))
    ((elementarySubgroup (X ⊕ Y) R).inv_mem
      (rectangularLowerUnit_mem_elementarySubgroup B))

end Matrix.GeneralLinearGroup
