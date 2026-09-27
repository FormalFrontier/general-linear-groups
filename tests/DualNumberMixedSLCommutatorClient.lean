/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.DualNumberMixedSLCommutator
public import Mathlib.Data.ZMod.Basic

/-!
# Public-import clients of the native special-linear mixed commutator

The zero-dimensional, zero-ring and characteristic-two clients exercise actual native
special-linear factors and the outer special-linear kernel. Integer elementary matrices
also test the nonzero, ordered mixed coefficient.
-/

public section
set_option warningAsError true

open Matrix.DualNumberKernels Matrix.DualNumberMixedSLCommutator

namespace GeneralLinearGroupsTests.DualNumberMixedSLCommutator

universe u v

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

example (X Y : LieAlgebra.SpecialLinear.sl n R) :
    Matrix.SpecialLinearGroup.toGL (epsilonLiftSL X) =
        Matrix.DualNumberMixedCommutator.epsilonLiftGL X.1 ∧
    Matrix.SpecialLinearGroup.toGL (etaLiftSL Y) =
        Matrix.DualNumberMixedCommutator.etaLiftGL Y.1 ∧
    slReduce (DualNumber R) n (epsilonLiftSL X) = liftSL X ∧
    slReduce (DualNumber R) n (etaLiftSL Y) = 1 :=
  ⟨epsilonLiftSL_toGL X, etaLiftSL_toGL Y,
    epsilonLiftSL_reduce X, etaLiftSL_reduce Y⟩

example (X Y : LieAlgebra.SpecialLinear.sl n R) :
    epsilonLiftSL X * etaLiftSL Y * (epsilonLiftSL X)⁻¹ * (etaLiftSL Y)⁻¹ =
        liftSL (innerPureSL ⁅X, Y⁆) ∧
    (mixedSLKernel X Y).1 =
        epsilonLiftSL X * etaLiftSL Y * (epsilonLiftSL X)⁻¹ * (etaLiftSL Y)⁻¹ ∧
    slReadback (mixedSLKernel X Y) = innerPureSL ⁅X, Y⁆ :=
  ⟨epsilon_eta_SL_commutator X Y, mixedSLKernel_val X Y,
    mixedSLKernel_readback X Y⟩

example (X Y : LieAlgebra.SpecialLinear.sl (Fin 0) ℤ) :
    slReduce (DualNumber ℤ) (Fin 0) (epsilonLiftSL X) = liftSL X ∧
    slReduce (DualNumber ℤ) (Fin 0) (etaLiftSL Y) = 1 ∧
    (mixedSLKernel X Y).1 =
      epsilonLiftSL X * etaLiftSL Y * (epsilonLiftSL X)⁻¹ * (etaLiftSL Y)⁻¹ ∧
    slReadback (mixedSLKernel X Y) = innerPureSL ⁅X, Y⁆ :=
  ⟨epsilonLiftSL_reduce X, etaLiftSL_reduce Y,
    mixedSLKernel_val X Y, mixedSLKernel_readback X Y⟩

example (X Y : LieAlgebra.SpecialLinear.sl (Fin 1) ℤ) :
    slReduce (DualNumber ℤ) (Fin 1) (epsilonLiftSL X) = liftSL X ∧
    slReduce (DualNumber ℤ) (Fin 1) (etaLiftSL Y) = 1 ∧
    slReadback (mixedSLKernel X Y) = innerPureSL ⁅X, Y⁆ ∧
    (((mixedSLKernel X Y).1 : Matrix (Fin 1) (Fin 1)
      (DualNumber (DualNumber ℤ))) 0 0).snd.snd = (⁅X, Y⁆).1 0 0 :=
  ⟨epsilonLiftSL_reduce X, etaLiftSL_reduce Y,
    mixedSLKernel_readback X Y, mixedSLKernel_snd_snd X Y 0 0⟩

example (X Y : LieAlgebra.SpecialLinear.sl (Fin 1) (ZMod 1)) :
    slReduce (DualNumber (ZMod 1)) (Fin 1) (epsilonLiftSL X) = liftSL X ∧
    slReduce (DualNumber (ZMod 1)) (Fin 1) (etaLiftSL Y) = 1 ∧
    (mixedSLKernel X Y).1 =
      epsilonLiftSL X * etaLiftSL Y * (epsilonLiftSL X)⁻¹ * (etaLiftSL Y)⁻¹ ∧
    slReadback (mixedSLKernel X Y) = innerPureSL ⁅X, Y⁆ :=
  ⟨epsilonLiftSL_reduce X, etaLiftSL_reduce Y,
    mixedSLKernel_val X Y, mixedSLKernel_readback X Y⟩

example (X Y : LieAlgebra.SpecialLinear.sl (Fin 2) (ZMod 2)) :
    Matrix.SpecialLinearGroup.toGL (epsilonLiftSL X) =
        Matrix.DualNumberMixedCommutator.epsilonLiftGL X.1 ∧
    Matrix.SpecialLinearGroup.toGL (etaLiftSL Y) =
        Matrix.DualNumberMixedCommutator.etaLiftGL Y.1 ∧
    slReduce (DualNumber (ZMod 2)) (Fin 2) (epsilonLiftSL X) = liftSL X ∧
    slReduce (DualNumber (ZMod 2)) (Fin 2) (etaLiftSL Y) = 1 ∧
    (mixedSLKernel X Y).1 =
      epsilonLiftSL X * etaLiftSL Y * (epsilonLiftSL X)⁻¹ * (etaLiftSL Y)⁻¹ ∧
    slReadback (mixedSLKernel X Y) = innerPureSL ⁅X, Y⁆ :=
  ⟨epsilonLiftSL_toGL X, etaLiftSL_toGL Y,
    epsilonLiftSL_reduce X, etaLiftSL_reduce Y,
    mixedSLKernel_val X Y, mixedSLKernel_readback X Y⟩

def integer01 : LieAlgebra.SpecialLinear.sl (Fin 2) ℤ :=
  LieAlgebra.SpecialLinear.single 0 1 (by decide) 1

def integer10 : LieAlgebra.SpecialLinear.sl (Fin 2) ℤ :=
  LieAlgebra.SpecialLinear.single 1 0 (by decide) 1

example :
    (mixedSLKernel integer01 integer10).1 =
      epsilonLiftSL integer01 * etaLiftSL integer10 * (epsilonLiftSL integer01)⁻¹ *
        (etaLiftSL integer10)⁻¹ ∧
    slReadback (mixedSLKernel integer01 integer10) =
      innerPureSL ⁅integer01, integer10⁆ :=
  ⟨mixedSLKernel_val _ _, mixedSLKernel_readback _ _⟩

example :
    (((mixedSLKernel integer01 integer10).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber ℤ))) 0 0).snd.snd = 1 := by
  rw [mixedSLKernel_snd_snd, LieAlgebra.SpecialLinear.sl_bracket]
  norm_num [integer01, integer10, LieAlgebra.SpecialLinear.val_single,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

example :
    (((mixedSLKernel integer01 integer10).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber ℤ))) 1 1).snd.snd = -1 := by
  rw [mixedSLKernel_snd_snd, LieAlgebra.SpecialLinear.sl_bracket]
  norm_num [integer01, integer10, LieAlgebra.SpecialLinear.val_single,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

example :
    (((mixedSLKernel integer10 integer01).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber ℤ))) 0 0).snd.snd = -1 := by
  rw [mixedSLKernel_snd_snd, LieAlgebra.SpecialLinear.sl_bracket]
  norm_num [integer01, integer10, LieAlgebra.SpecialLinear.val_single,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

example :
    (((mixedSLKernel integer10 integer01).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber ℤ))) 1 1).snd.snd = 1 := by
  rw [mixedSLKernel_snd_snd, LieAlgebra.SpecialLinear.sl_bracket]
  norm_num [integer01, integer10, LieAlgebra.SpecialLinear.val_single,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

example :
    (((mixedSLKernel integer01 integer10).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber ℤ))) 0 1).snd.snd = 0 := by
  rw [mixedSLKernel_snd_snd, LieAlgebra.SpecialLinear.sl_bracket]
  norm_num [integer01, integer10, LieAlgebra.SpecialLinear.val_single,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

example :
    (((mixedSLKernel integer01 integer10).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber ℤ))) 1 0).snd.snd = 0 := by
  rw [mixedSLKernel_snd_snd, LieAlgebra.SpecialLinear.sl_bracket]
  norm_num [integer01, integer10, LieAlgebra.SpecialLinear.val_single,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

example :
    (((mixedSLKernel integer10 integer01).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber ℤ))) 0 1).snd.snd = 0 := by
  rw [mixedSLKernel_snd_snd, LieAlgebra.SpecialLinear.sl_bracket]
  norm_num [integer01, integer10, LieAlgebra.SpecialLinear.val_single,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

example :
    (((mixedSLKernel integer10 integer01).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber ℤ))) 1 0).snd.snd = 0 := by
  rw [mixedSLKernel_snd_snd, LieAlgebra.SpecialLinear.sl_bracket]
  norm_num [integer01, integer10, LieAlgebra.SpecialLinear.val_single,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

def binary01 : LieAlgebra.SpecialLinear.sl (Fin 2) (ZMod 2) :=
  LieAlgebra.SpecialLinear.single 0 1 (by decide) 1

def binary10 : LieAlgebra.SpecialLinear.sl (Fin 2) (ZMod 2) :=
  LieAlgebra.SpecialLinear.single 1 0 (by decide) 1

example :
    (((mixedSLKernel binary01 binary10).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber (ZMod 2)))) 0 0).snd.snd ≠ 0 := by
  rw [mixedSLKernel_snd_snd, LieAlgebra.SpecialLinear.sl_bracket]
  norm_num [binary01, binary10, LieAlgebra.SpecialLinear.val_single,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

end GeneralLinearGroupsTests.DualNumberMixedSLCommutator
