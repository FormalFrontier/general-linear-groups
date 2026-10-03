/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.DualNumberKernels
public import Mathlib.Data.ZMod.Basic

/-!
# Clients of the native finite GL/SL dual-number reduction kernels

These examples include empty and singleton ranks, the zero ring, positive characteristic,
nonzero trace-zero matrices, coefficient change, and the distinct ordinary group and Lie brackets.
-/

public section

open Matrix.DualNumberKernels

namespace GeneralLinearGroupsTests.DualNumberKernels

example : (glReduce ℤ (Fin 0)).ker ≃* Multiplicative (Matrix (Fin 0) (Fin 0) ℤ) :=
  (glKerEquiv (R := ℤ) (n := Fin 0)).symm

example : (slReduce ℤ (Fin 0)).ker ≃*
    Multiplicative (LieAlgebra.SpecialLinear.sl (Fin 0) ℤ) :=
  (slKerEquiv (R := ℤ) (n := Fin 0)).symm

example : (glReduce (ZMod 1) (Fin 1)).ker ≃*
    Multiplicative (Matrix (Fin 1) (Fin 1) (ZMod 1)) :=
  (glKerEquiv (R := ZMod 1) (n := Fin 1)).symm

example : (slReduce (ZMod 1) (Fin 0)).ker ≃*
    Multiplicative (LieAlgebra.SpecialLinear.sl (Fin 0) (ZMod 1)) :=
  (slKerEquiv (R := ZMod 1) (n := Fin 0)).symm

example : unitsKerEquiv (Multiplicative.ofAdd (1 : ℤ)) ≠ 1 := by
  intro h
  have hz := congrArg (fun r : (unitsReduce ℤ).ker => (r.1 : DualNumber ℤ).snd) h
  norm_num at hz

example (r : ℤ) :
    detKer (glKerEquiv (Multiplicative.ofAdd (Matrix.single (0 : Fin 1) 0 r))) =
      unitsKerEquiv (Multiplicative.ofAdd r) := by
  simpa [Matrix.trace_single_eq_same] using
    (detKer_glKerEquiv (R := ℤ) (n := Fin 1)
      (Multiplicative.ofAdd (Matrix.single (0 : Fin 1) 0 r)))

def elementary01 : LieAlgebra.SpecialLinear.sl (Fin 2) ℤ :=
  LieAlgebra.SpecialLinear.single (0 : Fin 2) 1 (by decide) 1

def elementary10 : LieAlgebra.SpecialLinear.sl (Fin 2) ℤ :=
  LieAlgebra.SpecialLinear.single (1 : Fin 2) 0 (by decide) 1

theorem elementary01_kernel_ne_one :
    slKerEquiv (Multiplicative.ofAdd elementary01) ≠ 1 := by
  intro h
  have hz := congrArg (fun g : (slReduce ℤ (Fin 2)).ker =>
    (slReadback g).1 (0 : Fin 2) 1) h
  norm_num [elementary01, LieAlgebra.SpecialLinear.val_single, Matrix.single_apply] at hz

example : slKerEquiv (Multiplicative.ofAdd elementary01) *
      slKerEquiv (Multiplicative.ofAdd elementary10) =
      slKerEquiv (Multiplicative.ofAdd elementary10) *
        slKerEquiv (Multiplicative.ofAdd elementary01) :=
  slKernel_mul_comm _ _

theorem elementary_bracket_nonzero :
    (⁅elementary01, elementary10⁆ : LieAlgebra.SpecialLinear.sl (Fin 2) ℤ).1
      (0 : Fin 2) 0 ≠ 0 := by
  rw [LieAlgebra.SpecialLinear.sl_bracket]
  norm_num [elementary01, elementary10, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.single_apply]

def characteristicTwoIdentity : LieAlgebra.SpecialLinear.sl (Fin 2) (ZMod 2) :=
  ⟨1, by
    change (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)).trace = 0
    rw [Matrix.trace_one]
    simpa using (ZMod.natCast_self 2)⟩

theorem characteristicTwoIdentity_kernel_ne_one :
    slKerEquiv (Multiplicative.ofAdd characteristicTwoIdentity) ≠ 1 := by
  intro h
  have hz := congrArg (fun g : (slReduce (ZMod 2) (Fin 2)).ker =>
    (slReadback g).1 (0 : Fin 2) 0) h
  norm_num [characteristicTwoIdentity] at hz

example (X : Matrix (Fin 2) (Fin 2) ℤ) :
    glKerMap (Int.castRingHom (ZMod 2)) (glKerEquiv (Multiplicative.ofAdd X)) =
      glKerEquiv (Multiplicative.ofAdd (X.map (Int.castRingHom (ZMod 2)))) :=
  glKerMap_glKerEquiv _ _

example (X : LieAlgebra.SpecialLinear.sl (Fin 2) ℤ) :
    slKerMap (Int.castRingHom (ZMod 2)) (slKerEquiv (Multiplicative.ofAdd X)) =
      slKerEquiv (Multiplicative.ofAdd (slMap (Int.castRingHom (ZMod 2)) X)) :=
  slKerMap_slKerEquiv _ _

example (r : ℤ) :
    unitsKerMap (Int.castRingHom (ZMod 2)) (unitsKerEquiv (Multiplicative.ofAdd r)) =
      unitsKerEquiv (Multiplicative.ofAdd ((Int.castRingHom (ZMod 2)) r)) :=
  unitsKerMap_unitsKerEquiv _ _

example (g : (glReduce ℤ (Fin 2)).ker) :
    detKer (glKerMap (Int.castRingHom (ZMod 2)) g) =
      unitsKerMap (Int.castRingHom (ZMod 2)) (detKer g) :=
  detKer_natural _ _

end GeneralLinearGroupsTests.DualNumberKernels
