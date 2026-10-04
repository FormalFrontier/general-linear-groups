/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.ElementaryDiagonal
public import Mathlib.Data.ZMod.Basic

/-! Elementary unit pivots and diagonalizations at the rank boundaries. -/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.UnitPivotPremiseClient

open Matrix.GeneralLinearGroup

/-- In rank one, the identity elementary factor already gives a unit pivot. -/
theorem rank_one_pivot (R : Type*) [CommRing R] (g : GL (Fin 1) R) :
    ∃ factor : elementarySubgroup (Fin 1) R,
      IsUnit (((((factor : GL (Fin 1) R) * g) : GL (Fin 1) R) :
        Matrix (Fin 1) (Fin 1) R) 0 0) := by
  refine ⟨1, ?_⟩
  have hdet : IsUnit ((g : Matrix (Fin 1) (Fin 1) R).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)
  simpa only [OneMemClass.coe_one, one_mul, Matrix.det_fin_one] using hdet

example (rank : ℕ) (g : GL (Fin (rank + 1)) (ZMod 1)) :
    ∃ factor : elementarySubgroup (Fin (rank + 1)) (ZMod 1),
      IsUnit (((((factor : GL (Fin (rank + 1)) (ZMod 1)) * g) :
        GL (Fin (rank + 1)) (ZMod 1)) :
          Matrix (Fin (rank + 1)) (Fin (rank + 1)) (ZMod 1)) 0 0) := by
  refine ⟨1, ?_⟩
  have h : ((g : Matrix (Fin (rank + 1)) (Fin (rank + 1)) (ZMod 1)) 0 0) = 1 :=
    Subsingleton.elim _ _
  simpa only [OneMemClass.coe_one, one_mul, h] using (isUnit_one : IsUnit (1 : ZMod 1))

example (R : Type*) [CommRing R] (g : GL (Fin 0) R) :
    ∃ (left right : elementarySubgroup (Fin 0) R) (diagonal : Fin 0 → Rˣ),
      (left : GL (Fin 0) R) * g * (right : GL (Fin 0) R) = diagonalUnit diagonal := by
  refine ⟨1, 1, (fun index => index.elim0), ?_⟩
  apply Units.ext
  ext index
  exact index.elim0

end GeneralLinearGroupsTests.UnitPivotPremiseClient
