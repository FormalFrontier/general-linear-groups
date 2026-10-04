/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.UnitPivotDiagonalization

/-!
# Row action of the rectangular upper unit

The existing upper block unit acts by an ordered linear combination of lower
rows. Reindexing along the first/rest equivalence gives its first-column action.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {R : Type*} [Ring R] {n : ℕ}

/-- Reindex the existing upper block unit and read its first-column pivot. -/
theorem reindexed_rectangularUpperUnit_mul_apply_zero
    (C : Matrix (Fin 1) (Fin n) R)
    (matrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (((reindexEquiv R (Matrix.firstRestEquiv n).symm
        (rectangularUpperUnit C) : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) * matrix) 0 0 =
      matrix 0 0 + ∑ index : Fin n, C 0 index * matrix index.succ 0 := by
  have hreindex :
      (reindexEquiv R (Matrix.firstRestEquiv n).symm
        (rectangularUpperUnit C) : Matrix (Fin (n + 1)) (Fin (n + 1)) R).submatrix
          (Matrix.firstRestEquiv n).symm (Matrix.firstRestEquiv n).symm =
            (rectangularUpperUnit C : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) := by
    ext row column
    simp [Matrix.submatrix_apply]
  have hmul := Matrix.submatrix_mul_equiv
    (reindexEquiv R (Matrix.firstRestEquiv n).symm
      (rectangularUpperUnit C) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    matrix (Matrix.firstRestEquiv n).symm (Matrix.firstRestEquiv n).symm
    (id : Fin (n + 1) → Fin (n + 1))
  calc
    _ = (((reindexEquiv R (Matrix.firstRestEquiv n).symm
        (rectangularUpperUnit C) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *
          matrix).submatrix (Matrix.firstRestEquiv n).symm id) (Sum.inl 0) 0 := by
            simp only [Matrix.submatrix_apply, Matrix.firstRestEquiv_symm_inl, id_eq]
    _ = ((rectangularUpperUnit C : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) *
          matrix.submatrix (Matrix.firstRestEquiv n).symm id) (Sum.inl 0) 0 := by
            rw [← hmul, hreindex]
    _ = matrix 0 0 + ∑ index : Fin n, C 0 index * matrix index.succ 0 := by
      simpa only [Matrix.submatrix_apply, Matrix.firstRestEquiv_symm_inl,
        Matrix.firstRestEquiv_symm_inr, id_eq] using
        (rectangularUpperUnit_mul_apply_inl C
          (matrix.submatrix (Matrix.firstRestEquiv n).symm id) 0 (0 : Fin (n + 1)))

end Matrix.GeneralLinearGroup
