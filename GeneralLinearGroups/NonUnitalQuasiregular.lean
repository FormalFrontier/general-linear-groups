/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.NonUnitalNilpotent
public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum

/-!
# Quasiregular matrices over nonunital rings

This file relates mathlib's nonunital `IsQuasiregular` predicate to the
canonical entrywise unitization of a finite square matrix.  It then identifies
quasiregularity with representability by `1 + x` in the augmentation-kernel
general linear group of the nonunital ring.

The index type may be empty, the coefficient ring may be trivial, and no
commutativity assumption is used.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {I : Type u} [NonUnitalRing I]
variable {n : Type v} [Fintype n] [DecidableEq n]

private def matrixFst (x : Matrix n n (Unitization ℤ I)) : Matrix n n ℤ :=
  (Unitization.fstHom (R := ℤ) (A := I)).toRingHom.mapMatrix x

private def matrixSnd (x : Matrix n n (Unitization ℤ I)) : Matrix n n I :=
  x.map (Unitization.sndHom ℤ ℤ I)

private theorem matrixFst_mul (x y : Matrix n n (Unitization ℤ I)) :
    matrixFst (x * y) = matrixFst x * matrixFst y := by
  simp [matrixFst]

private theorem matrixFst_one_add_unitizationMatrix (x : Matrix n n I) :
    matrixFst (1 + unitizationMatrix x) = 1 := by
  ext i j
  by_cases h : i = j <;>
    simp [matrixFst, unitizationMatrix, Matrix.one_apply, h]

omit [Fintype n] in
private theorem matrixSnd_one :
    matrixSnd (1 : Matrix n n (Unitization ℤ I)) = 0 := by
  ext i j
  by_cases h : i = j <;> simp [matrixSnd, h]

omit [Fintype n] in
private theorem matrixSnd_one_add_unitizationMatrix (x : Matrix n n I) :
    matrixSnd (1 + unitizationMatrix x) = x := by
  ext i j
  by_cases h : i = j <;> simp [matrixSnd, unitizationMatrix, h]

private theorem matrixSnd_mul_of_fst_eq_one
    (x y : Matrix n n (Unitization ℤ I))
    (hx : matrixFst x = 1) (hy : matrixFst y = 1) :
    matrixSnd (x * y) = matrixSnd x + matrixSnd y + matrixSnd x * matrixSnd y := by
  ext i j
  have hx' (k l : n) : (x k l).fst = (1 : Matrix n n ℤ) k l := by
    simpa [matrixFst] using congrFun (congrFun hx k) l
  have hy' (k l : n) : (y k l).fst = (1 : Matrix n n ℤ) k l := by
    simpa [matrixFst] using congrFun (congrFun hy k) l
  simp [matrixSnd, Matrix.mul_apply, Unitization.snd_mul, hx', hy',
    Matrix.one_apply, Finset.sum_add_distrib, add_comm, add_assoc]

private theorem matrix_ext
    {x y : Matrix n n (Unitization ℤ I)}
    (hfst : matrixFst x = matrixFst y)
    (hsnd : matrixSnd x = matrixSnd y) : x = y := by
  ext i j
  · simpa [matrixFst] using congrFun (congrFun hfst i) j
  · simpa [matrixSnd] using congrFun (congrFun hsnd i) j

/-- The entrywise unitization of a finite square matrix gives a unit after
adding one exactly when the original matrix is quasiregular. -/
theorem isUnit_one_add_unitizationMatrix_iff_isQuasiregular
    (x : Matrix n n I) :
    IsUnit (1 + unitizationMatrix x : Matrix n n (Unitization ℤ I)) ↔
      IsQuasiregular x := by
  rw [isQuasiregular_iff]
  constructor
  · intro hx
    rw [isUnit_iff_exists] at hx
    obtain ⟨z, hxz, hzx⟩ := hx
    have hzfst : matrixFst z = 1 := by
      have h := congrArg matrixFst hxz
      rw [matrixFst_mul, matrixFst_one_add_unitizationMatrix] at h
      simpa [matrixFst] using h
    let y : Matrix n n I := matrixSnd z
    refine ⟨y, ?_, ?_⟩
    · have h := congrArg matrixSnd hxz
      rw [matrixSnd_mul_of_fst_eq_one _ _
        (matrixFst_one_add_unitizationMatrix x) hzfst, matrixSnd_one] at h
      simpa [matrixSnd_one_add_unitizationMatrix, y, add_comm x y] using h
    · have h := congrArg matrixSnd hzx
      rw [matrixSnd_mul_of_fst_eq_one _ _ hzfst
        (matrixFst_one_add_unitizationMatrix x), matrixSnd_one] at h
      simpa [matrixSnd_one_add_unitizationMatrix, y, add_comm x y] using h
  · rintro ⟨y, hyx, hxy⟩
    rw [isUnit_iff_exists]
    refine ⟨1 + unitizationMatrix y, ?_, ?_⟩
    · apply matrix_ext
      · rw [matrixFst_mul, matrixFst_one_add_unitizationMatrix,
          matrixFst_one_add_unitizationMatrix]
        simp [matrixFst]
      · rw [matrixSnd_mul_of_fst_eq_one _ _
          (matrixFst_one_add_unitizationMatrix x)
          (matrixFst_one_add_unitizationMatrix y),
          matrixSnd_one_add_unitizationMatrix,
          matrixSnd_one_add_unitizationMatrix, matrixSnd_one]
        simpa only [add_comm x y] using hyx
    · apply matrix_ext
      · rw [matrixFst_mul, matrixFst_one_add_unitizationMatrix,
          matrixFst_one_add_unitizationMatrix]
        simp [matrixFst]
      · rw [matrixSnd_mul_of_fst_eq_one _ _
          (matrixFst_one_add_unitizationMatrix y)
          (matrixFst_one_add_unitizationMatrix x),
          matrixSnd_one_add_unitizationMatrix,
          matrixSnd_one_add_unitizationMatrix, matrixSnd_one]
        simpa only [add_comm x y] using hxy

/-- A matrix is quasiregular exactly when `1 + x` represents an element of
the augmentation-kernel general linear group of its nonunital coefficient
ring. -/
theorem exists_nonUnitalGeneralLinearGroup_iff_isQuasiregular
    (x : Matrix n n I) :
    (∃ u : nonUnitalGeneralLinearGroup (n := n) (I := I),
        (u.1 : Matrix n n (Unitization ℤ I)) = 1 + unitizationMatrix x) ↔
      IsQuasiregular x := by
  rw [← isUnit_one_add_unitizationMatrix_iff_isQuasiregular]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u.1, hu⟩
  · intro hx
    refine ⟨⟨hx.unit, ?_⟩, hx.unit_spec⟩
    change nonUnitalAugmentation hx.unit = 1
    apply Units.ext
    change matrixFst (hx.unit : Matrix n n (Unitization ℤ I)) = 1
    rw [hx.unit_spec, matrixFst_one_add_unitizationMatrix]

end Matrix.GeneralLinearGroup
