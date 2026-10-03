/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.DualNumberMixedCommutator
public import Mathlib.Data.ZMod.Basic

/-!
# Public-import clients of the native mixed dual-number GL commutator

These examples use only the producer's public import and existing mathlib matrix units.
-/

public section
set_option warningAsError true

open Matrix.DualNumberKernels Matrix.DualNumberMixedCommutator

namespace GeneralLinearGroupsTests.DualNumberMixedCommutator

universe u v

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

example (X Y : Matrix n n R) :
    epsilonLiftGL X * etaLiftGL Y * (epsilonLiftGL X)⁻¹ * (etaLiftGL Y)⁻¹ =
      liftGL (innerPure (⁅X, Y⁆ : Matrix n n R)) :=
  epsilon_eta_commutator X Y

example (X Y : Matrix n n R) :
    glReadback (mixedKernel X Y) = innerPure (⁅X, Y⁆ : Matrix n n R) :=
  mixedKernel_readback X Y

example (X Y : Matrix (Fin 0) (Fin 0) ℤ) :
    epsilonLiftGL X * etaLiftGL Y * (epsilonLiftGL X)⁻¹ * (etaLiftGL Y)⁻¹ =
      liftGL (innerPure (⁅X, Y⁆ : Matrix (Fin 0) (Fin 0) ℤ)) ∧
    glReadback (mixedKernel X Y) = innerPure (⁅X, Y⁆ : Matrix (Fin 0) (Fin 0) ℤ) :=
  ⟨epsilon_eta_commutator X Y, mixedKernel_readback X Y⟩

example (X Y : Matrix (Fin 1) (Fin 1) ℤ) :
    epsilonLiftGL X * etaLiftGL Y * (epsilonLiftGL X)⁻¹ * (etaLiftGL Y)⁻¹ =
      liftGL (innerPure (⁅X, Y⁆ : Matrix (Fin 1) (Fin 1) ℤ)) ∧
    glReadback (mixedKernel X Y) = innerPure (⁅X, Y⁆ : Matrix (Fin 1) (Fin 1) ℤ) :=
  ⟨epsilon_eta_commutator X Y, mixedKernel_readback X Y⟩

example (X Y : Matrix (Fin 1) (Fin 1) (ZMod 1)) :
    epsilonLiftGL X * etaLiftGL Y * (epsilonLiftGL X)⁻¹ * (etaLiftGL Y)⁻¹ =
      liftGL (innerPure (⁅X, Y⁆ : Matrix (Fin 1) (Fin 1) (ZMod 1))) ∧
    glReadback (mixedKernel X Y) =
      innerPure (⁅X, Y⁆ : Matrix (Fin 1) (Fin 1) (ZMod 1)) :=
  ⟨epsilon_eta_commutator X Y, mixedKernel_readback X Y⟩

example (X Y : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    epsilonLiftGL X * etaLiftGL Y * (epsilonLiftGL X)⁻¹ * (etaLiftGL Y)⁻¹ =
      liftGL (innerPure (⁅X, Y⁆ : Matrix (Fin 2) (Fin 2) (ZMod 2))) ∧
    glReadback (mixedKernel X Y) =
      innerPure (⁅X, Y⁆ : Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
  ⟨epsilon_eta_commutator X Y, mixedKernel_readback X Y⟩

def integer01 : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 0 1 1
def integer10 : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 1 0 1

example :
    epsilonLiftGL integer01 * etaLiftGL integer10 * (epsilonLiftGL integer01)⁻¹ *
      (etaLiftGL integer10)⁻¹ =
      liftGL (innerPure (⁅integer01, integer10⁆ : Matrix (Fin 2) (Fin 2) ℤ)) ∧
    glReadback (mixedKernel integer01 integer10) =
      innerPure (⁅integer01, integer10⁆ : Matrix (Fin 2) (Fin 2) ℤ) :=
  ⟨epsilon_eta_commutator _ _, mixedKernel_readback _ _⟩

example :
    (((mixedKernel integer01 integer10).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber ℤ))) 0 0).snd.snd = 1 := by
  rw [mixedKernel_snd_snd, LieRing.of_associative_ring_bracket]
  norm_num [integer01, integer10, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.single_apply]

example :
    (((mixedKernel integer01 integer10).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber ℤ))) 1 1).snd.snd = -1 := by
  rw [mixedKernel_snd_snd, LieRing.of_associative_ring_bracket]
  norm_num [integer01, integer10, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.single_apply]

example :
    (((mixedKernel integer10 integer01).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber ℤ))) 0 0).snd.snd = -1 := by
  rw [mixedKernel_snd_snd, LieRing.of_associative_ring_bracket]
  norm_num [integer01, integer10, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.single_apply]

def binary01 : Matrix (Fin 2) (Fin 2) (ZMod 2) := Matrix.single 0 1 1
def binary10 : Matrix (Fin 2) (Fin 2) (ZMod 2) := Matrix.single 1 0 1

example :
    (((mixedKernel binary01 binary10).1 :
      Matrix (Fin 2) (Fin 2) (DualNumber (DualNumber (ZMod 2)))) 0 0).snd.snd ≠ 0 := by
  rw [mixedKernel_snd_snd, LieRing.of_associative_ring_bracket]
  norm_num [binary01, binary10, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.single_apply]

end GeneralLinearGroupsTests.DualNumberMixedCommutator
