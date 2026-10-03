/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.DualNumberKernelAdjoint
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

/-! Ordinary-import clients for native GL/SL adjoint compatibility, including degenerate ranks. -/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.DualNumberKernelAdjoint

open Matrix.DualNumberKernels

/-- Inner conjugation on the reduction kernel has the expected formula in rank zero. -/
theorem empty_glKerEquiv_conj (h : Matrix.GeneralLinearGroup (Fin 0) (DualNumber ℤ))
    (X : Multiplicative (Matrix (Fin 0) (Fin 0) ℤ)) :
    MulAut.conjNormal h (glKerEquiv X) =
      glKerEquiv (Multiplicative.ofAdd
        (((glReduce ℤ (Fin 0) h : Matrix.GeneralLinearGroup (Fin 0) ℤ) :
          Matrix (Fin 0) (Fin 0) ℤ) * Multiplicative.toAdd X *
          (((glReduce ℤ (Fin 0) h)⁻¹ : Matrix.GeneralLinearGroup (Fin 0) ℤ) :
            Matrix (Fin 0) (Fin 0) ℤ))) :=
  glKerEquiv_conj h X

example (t : Matrix.SpecialLinearGroup (Fin 0) (DualNumber ℤ))
    (k : (slReduce ℤ (Fin 0)).ker) :
    slReadback (MulAut.conjNormal t k) =
      slAdjoint (Matrix.SpecialLinearGroup.toGL (slReduce ℤ (Fin 0) t)) (slReadback k) :=
  slReadback_conj t k

example (h : Matrix.GeneralLinearGroup (Fin 1) (DualNumber (ZMod 1)))
    (k : (glReduce (ZMod 1) (Fin 1)).ker) :
    glReadback (MulAut.conjNormal h k) =
      ((glReduce (ZMod 1) (Fin 1) h : Matrix.GeneralLinearGroup (Fin 1) (ZMod 1)) :
        Matrix (Fin 1) (Fin 1) (ZMod 1)) * glReadback k *
        (((glReduce (ZMod 1) (Fin 1) h)⁻¹ :
          Matrix.GeneralLinearGroup (Fin 1) (ZMod 1)) : Matrix (Fin 1) (Fin 1) (ZMod 1)) :=
  glReadback_conj h k

private def characteristicTwoIdentity : LieAlgebra.SpecialLinear.sl (Fin 2) (ZMod 2) :=
  ⟨1, by
    change (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)).trace = 0
    rw [Matrix.trace_one]
    decide⟩

example (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) :
    slAdjoint g characteristicTwoIdentity = characteristicTwoIdentity := by
  apply Subtype.ext
  rw [slAdjoint_val]
  change (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) * 1 *
    ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1
  rw [mul_one]
  exact g.mul_inv

example (t : Matrix.SpecialLinearGroup (Fin 2) (DualNumber (ZMod 2)))
    (k : (slReduce (ZMod 2) (Fin 2)).ker) :
    slToGL (MulAut.conjNormal t k) =
      MulAut.conjNormal (Matrix.SpecialLinearGroup.toGL t) (slToGL k) :=
  slToGL_conj t k

private def shear : Matrix.GeneralLinearGroup (Fin 2) ℤ :=
  Matrix.GeneralLinearGroup.upperRightHom 1

private def elementary10 : LieAlgebra.SpecialLinear.sl (Fin 2) ℤ :=
  LieAlgebra.SpecialLinear.single (1 : Fin 2) 0 (by decide) 1

private theorem shear_orientation :
    ((slAdjoint shear elementary10).1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by
  rw [slAdjoint_val]
  norm_num [shear, elementary10, Matrix.GeneralLinearGroup.upperRightHom_apply,
    Matrix.GeneralLinearGroup.upperRightHom, Matrix.mul_apply, Matrix.vecMul,
    Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two,
    Matrix.single_apply]

private def infinitesimal : Matrix.GeneralLinearGroup (Fin 2) (DualNumber ℤ) :=
  liftGL (Matrix.single (0 : Fin 2) 1 (1 : ℤ))

private theorem infinitesimal_ne_one : infinitesimal ≠ 1 := by
  intro h
  have hz := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (DualNumber ℤ) =>
    ((g : Matrix (Fin 2) (Fin 2) (DualNumber ℤ)) 0 1).snd) h
  norm_num [infinitesimal, liftGL, liftMatrix, Matrix.single_apply, Matrix.one_apply] at hz

private def variableShear : Matrix.GeneralLinearGroup (Fin 2) (DualNumber ℤ) :=
  Matrix.GeneralLinearGroup.map (algebraMap ℤ (DualNumber ℤ)) shear * infinitesimal

private theorem variableShear_nonconstant :
    variableShear ≠ Matrix.GeneralLinearGroup.map (algebraMap ℤ (DualNumber ℤ)) shear := by
  intro h
  apply infinitesimal_ne_one
  apply mul_left_cancel (a := Matrix.GeneralLinearGroup.map (algebraMap ℤ (DualNumber ℤ)) shear)
  simpa only [variableShear, mul_one] using h

private theorem variableShear_reduce : glReduce ℤ (Fin 2) variableShear = shear := by
  have hreduce : glReduce ℤ (Fin 2) infinitesimal = 1 :=
    (glKerEquiv (Multiplicative.ofAdd
      (Matrix.single (0 : Fin 2) 1 (1 : ℤ)))).property
  change glReduce ℤ (Fin 2)
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ (DualNumber ℤ)) shear * infinitesimal) = shear
  rw [map_mul, hreduce, mul_one]
  apply Units.ext
  rfl

example : (glReadback (MulAut.conjNormal variableShear
      (glKerEquiv (Multiplicative.ofAdd elementary10.1)))) 0 0 = 1 := by
  rw [glReadback_conj, variableShear_reduce, glKerEquiv_readback]
  exact shear_orientation

example (k : (glReduce ℤ (Fin 2)).ker) :
    glReadback (MulAut.conjNormal infinitesimal k) = glReadback k := by
  have hreduce : glReduce ℤ (Fin 2) infinitesimal = 1 :=
    (glKerEquiv (Multiplicative.ofAdd
      (Matrix.single (0 : Fin 2) 1 (1 : ℤ)))).property
  rw [glReadback_conj, hreduce]
  simp

example (k : (glReduce ℤ (Fin 2)).ker) :
    glKerMap (Int.castRingHom (ZMod 2)) (MulAut.conjNormal infinitesimal k) =
      MulAut.conjNormal
        (Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom (Int.castRingHom (ZMod 2)))
          infinitesimal)
        (glKerMap (Int.castRingHom (ZMod 2)) k) :=
  glKerMap_conj _ infinitesimal k

end GeneralLinearGroupsTests.DualNumberKernelAdjoint
