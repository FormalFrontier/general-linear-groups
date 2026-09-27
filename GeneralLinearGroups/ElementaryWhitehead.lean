/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.Elementary
public import GeneralLinearGroups.Whitehead

/-!
# Whitehead units in the elementary subgroup

The upper and lower block units are products of off-block elementary units;
the signed swap is a product of three such block units. The existing Whitehead
factorization then places `diag(g, g⁻¹)` in the elementary subgroup.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  {R : Type v} [Ring R]

/-- The upper block unit with zero off-diagonal block is the identity. -/
theorem upperUnit_zero :
    upperUnit (0 : Matrix ι ι R) = 1 := by
  apply Units.ext
  simp [upperUnit]

/-- The lower block unit with zero off-diagonal block is the identity. -/
theorem lowerUnit_zero :
    lowerUnit (0 : Matrix ι ι R) = 1 := by
  apply Units.ext
  simp [lowerUnit]

/-- Upper block units turn matrix addition into group multiplication. -/
theorem upperUnit_add (a b : Matrix ι ι R) :
    upperUnit (a + b) = upperUnit a * upperUnit b := by
  apply Units.ext
  simp [upperUnit, Matrix.fromBlocks_multiply, add_comm]

/-- Lower block units turn matrix addition into group multiplication. -/
theorem lowerUnit_add (a b : Matrix ι ι R) :
    lowerUnit (a + b) = lowerUnit a * lowerUnit b := by
  apply Units.ext
  simp [lowerUnit, Matrix.fromBlocks_multiply, add_comm]

/-- A single upper-block entry is an off-block elementary unit. -/
theorem upperUnit_single (i j : ι) (c : R) :
    upperUnit (Matrix.single i j c) =
      elementaryUnit (Sum.inl i) (Sum.inr j) (by simp) c := by
  apply Units.ext
  ext row col
  rcases row with row | row <;> rcases col with col | col <;>
    simp [upperUnit, elementaryUnit, Matrix.single_apply, Matrix.one_apply]

/-- A single lower-block entry is elementary with coefficient `-c`. -/
theorem lowerUnit_single (i j : ι) (c : R) :
    lowerUnit (Matrix.single i j c) =
      elementaryUnit (Sum.inr i) (Sum.inl j) (by simp) (-c) := by
  apply Units.ext
  ext row col
  rcases row with row | row <;> rcases col with col | col <;>
    simp [lowerUnit, elementaryUnit, Matrix.single_apply, Matrix.single_neg,
      Matrix.one_apply]

/-- Every upper unipotent block unit is elementary over any ring. -/
theorem upperUnit_mem_elementarySubgroup (a : Matrix ι ι R) :
    upperUnit a ∈ elementarySubgroup (ι ⊕ ι) R := by
  refine Matrix.induction_on' a ?_ ?_ ?_
  · rw [upperUnit_zero]
    exact (elementarySubgroup (ι ⊕ ι) R).one_mem
  · intro p q hp hq
    rw [upperUnit_add]
    exact (elementarySubgroup (ι ⊕ ι) R).mul_mem hp hq
  · intro i j c
    rw [upperUnit_single]
    exact elementaryUnit_mem _ _ _ _

/-- Every lower unipotent block unit (with lower-left block `-a`) is elementary. -/
theorem lowerUnit_mem_elementarySubgroup (a : Matrix ι ι R) :
    lowerUnit a ∈ elementarySubgroup (ι ⊕ ι) R := by
  refine Matrix.induction_on' a ?_ ?_ ?_
  · rw [lowerUnit_zero]
    exact (elementarySubgroup (ι ⊕ ι) R).one_mem
  · intro p q hp hq
    rw [lowerUnit_add]
    exact (elementarySubgroup (ι ⊕ ι) R).mul_mem hp hq
  · intro i j c
    rw [lowerUnit_single]
    exact elementaryUnit_mem _ _ _ _

private theorem swapUnit_eq_three :
    (swapUnit : GL (ι ⊕ ι) R) =
      upperUnit (-1 : Matrix ι ι R) *
        lowerUnit (-1 : Matrix ι ι R) *
          upperUnit (-1 : Matrix ι ι R) := by
  apply Units.ext
  simp [upperUnit, lowerUnit, swapUnit, Matrix.fromBlocks_multiply]

/-- The signed block swap `[0,-I;I,0]` is elementary. -/
theorem swapUnit_mem_elementarySubgroup :
    (swapUnit : GL (ι ⊕ ι) R) ∈ elementarySubgroup (ι ⊕ ι) R := by
  rw [swapUnit_eq_three]
  exact (elementarySubgroup (ι ⊕ ι) R).mul_mem
    ((elementarySubgroup (ι ⊕ ι) R).mul_mem
      (upperUnit_mem_elementarySubgroup (-1))
      (lowerUnit_mem_elementarySubgroup (-1)))
    (upperUnit_mem_elementarySubgroup (-1))

/-- The native Whitehead diagonal `diag(g,g⁻¹)` is elementary after doubling. -/
theorem blockDiagonalUnit_mem_elementarySubgroup (g : GL ι R) :
    blockDiagonalUnit g ∈ elementarySubgroup (ι ⊕ ι) R := by
  rw [blockDiagonalUnit_eq]
  exact (elementarySubgroup (ι ⊕ ι) R).mul_mem
    ((elementarySubgroup (ι ⊕ ι) R).mul_mem
      ((elementarySubgroup (ι ⊕ ι) R).mul_mem
        (upperUnit_mem_elementarySubgroup (g : Matrix ι ι R))
        (lowerUnit_mem_elementarySubgroup ((g⁻¹ : GL ι R) : Matrix ι ι R)))
      (upperUnit_mem_elementarySubgroup (g : Matrix ι ι R)))
    swapUnit_mem_elementarySubgroup

end Matrix.GeneralLinearGroup
