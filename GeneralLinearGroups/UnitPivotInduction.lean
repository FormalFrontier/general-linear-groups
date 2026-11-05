/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.ElementaryDiagonal
public import GeneralLinearGroups.RectangularUpperAction

/-!
# Diagonalization from elementary unit pivots

A unit pivot produced by an elementary left factor for every invertible matrix
at every successor rank reduces the diagonalization problem to the invertible
Schur residual. The premise is a property of the coefficient ring, not an
unconditional existence result for elementary pivot factors. Under the same
premise, product-one diagonals give the determinant-one characterization of
the elementary subgroup for arbitrary finite index types, including the empty
type. Local-ring and Euclidean-domain generation use this shared closure step.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {R : Type*} [CommRing R]

/-- If elementary left factors produce unit leading entries at every successor
rank, every invertible finite matrix admits a two-sided elementary reduction
to a diagonal of units, including in rank zero. -/
theorem exists_elementary_diagonalization_of_unit_pivots
    (pivot : ∀ (rank : ℕ) (matrix : GL (Fin (rank + 1)) R),
      ∃ factor : elementarySubgroup (Fin (rank + 1)) R,
        IsUnit (((((factor : GL (Fin (rank + 1)) R) * matrix) :
          GL (Fin (rank + 1)) R) : Matrix (Fin (rank + 1)) (Fin (rank + 1)) R) 0 0))
    {rank : ℕ} (matrix : GL (Fin rank) R) :
    ∃ (left right : elementarySubgroup (Fin rank) R) (diagonal : Fin rank → Rˣ),
      (left : GL (Fin rank) R) * matrix * (right : GL (Fin rank) R) =
        diagonalUnit diagonal := by
  induction rank with
  | zero =>
      refine ⟨1, 1, (fun index => index.elim0), ?_⟩
      apply Units.ext
      ext index
      exact index.elim0
  | succ rank ih =>
      obtain ⟨factor, hpivot⟩ := pivot rank matrix
      let corrected : GL (Fin (rank + 1)) R :=
        (factor : GL (Fin (rank + 1)) R) * matrix
      let M : Matrix (Fin (rank + 1)) (Fin (rank + 1)) R := corrected
      let T := Matrix.firstRestBlock M
      let A := T.toBlocks₁₁
      let B := T.toBlocks₁₂
      let C := T.toBlocks₂₁
      let D := T.toBlocks₂₂
      have hA : IsUnit A.det := by
        change IsUnit (Matrix.firstRestBlock M).toBlocks₁₁.det
        rw [Matrix.firstRestBlock_pivot]
        simpa [Matrix.leadingPrincipalMinor, Matrix.det_fin_one, M, corrected] using hpivot
      let inverseA : Invertible A := Matrix.invertibleOfIsUnitDet A hA
      let S := D - C * A⁻¹ * B
      have hM : IsUnit M := Units.isUnit corrected
      have hT : IsUnit T := by
        apply (Matrix.isUnit_iff_isUnit_det T).mpr
        have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
        simpa only [T, Matrix.firstRestBlock, Matrix.det_submatrix_equiv_self] using hMdet
      have hS : IsUnit S := by
        have hblock : IsUnit (Matrix.fromBlocks A B C D) := by
          simpa only [A, B, C, D, Matrix.fromBlocks_toBlocks] using hT
        simpa only [S, Matrix.invOf_eq_nonsing_inv] using
          (Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mp hblock)
      let residual : GL (Fin rank) R := hS.unit
      obtain ⟨left, right, diagonal, hdiagonal⟩ := ih residual
      have hSdiagonal :
          ((left : GL (Fin rank) R) : Matrix (Fin rank) (Fin rank) R) * S *
            ((right : GL (Fin rank) R) : Matrix (Fin rank) (Fin rank) R) =
              Matrix.diagonal (fun index => (diagonal index : R)) := by
        simpa only [Units.val_mul, diagonalUnit_val, residual, hS.unit_spec] using congrArg
          (fun unit : GL (Fin rank) R =>
            (unit : Matrix (Fin rank) (Fin rank) R)) hdiagonal
      obtain ⟨L, Q, entries, hfactor⟩ :=
        Matrix.exists_elementary_diagonalization_of_unit_pivot
          M hA left right diagonal hSdiagonal
      refine ⟨L * factor, Q, entries, ?_⟩
      apply Units.ext
      simpa only [Subgroup.coe_mul, Units.val_mul, corrected, M,
        Matrix.mul_assoc, diagonalUnit_val] using hfactor

/-- If elementary left factors produce unit leading entries at every successor
rank, the finite elementary subgroup is exactly the determinant-one subgroup,
including for empty index types. -/
theorem mem_elementarySubgroup_iff_det_eq_one_of_unit_pivots
    (pivot : ∀ (rank : ℕ) (matrix : GL (Fin (rank + 1)) R),
      ∃ factor : elementarySubgroup (Fin (rank + 1)) R,
        IsUnit (((((factor : GL (Fin (rank + 1)) R) * matrix) :
          GL (Fin (rank + 1)) R) : Matrix (Fin (rank + 1)) (Fin (rank + 1)) R) 0 0))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : GL ι R) :
    g ∈ elementarySubgroup ι R ↔ Matrix.GeneralLinearGroup.det g = 1 := by
  constructor
  · intro hg
    exact Matrix.det_elementarySubgroup_eq_one ⟨g, hg⟩
  · intro hdet
    let equiv : ι ≃ Fin (Fintype.card ι) := Fintype.equivOfCardEq (by simp)
    let reindexed : GL (Fin (Fintype.card ι)) R := reindexEquiv R equiv g
    have hdet' : Matrix.GeneralLinearGroup.det reindexed =
        Matrix.GeneralLinearGroup.det g := by
      apply Units.ext
      change (Matrix.reindex equiv equiv (g : Matrix ι ι R)).det =
        (g : Matrix ι ι R).det
      exact Matrix.det_reindex_self equiv _
    obtain ⟨left, right, diagonal, hfactor⟩ :=
      exists_elementary_diagonalization_of_unit_pivots pivot reindexed
    have hproduct : (∏ i, diagonal i) = 1 := by
      apply Units.ext
      have hmatrix := congrArg
        (fun x : GL (Fin (Fintype.card ι)) R =>
          (x : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) R)) hfactor
      have hfactorDet := Matrix.det_eq_prod_of_elementary_diagonalization
        (L := left) (Q := right)
        (M := (reindexed : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) R))
        (by simpa only [Units.val_mul, diagonalUnit_val] using hmatrix)
      change (Units.coeHom R) (∏ i, diagonal i) = 1
      rw [map_prod]
      exact hfactorDet.symm.trans (congrArg Units.val (hdet'.trans hdet))
    have hreindexed : reindexed ∈ elementarySubgroup (Fin (Fintype.card ι)) R := by
      apply ((elementarySubgroup (Fin (Fintype.card ι)) R).mul_mem_cancel_left
        left.property).mp
      apply ((elementarySubgroup (Fin (Fintype.card ι)) R).mul_mem_cancel_right
        right.property).mp
      rw [hfactor]
      exact diagonalUnit_mem_elementarySubgroup (Fintype.card ι) diagonal hproduct
    have hback := reindexEquiv_mem_elementarySubgroup equiv.symm hreindexed
    simpa only [reindexed, ← reindexEquiv_symm, MulEquiv.symm_apply_apply] using hback

end Matrix.GeneralLinearGroup
