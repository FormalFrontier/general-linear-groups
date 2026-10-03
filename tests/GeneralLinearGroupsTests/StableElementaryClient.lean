/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.StableElementary
public import Mathlib.Data.ZMod.Basic

/-! Elementary generators, noncommutative coefficients, and an integer quotient witness. -/

set_option warningAsError true

@[expose] public section

open Matrix.GeneralLinearGroup

private abbrev NoncommutativeCoefficients := Matrix (Fin 2) (Fin 2) ℤ
private def reduceTwo : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
private def matrixCoefficient : NoncommutativeCoefficients :=
  Matrix.single 0 1 (1 : ℤ)
private def reverseMatrixCoefficient : NoncommutativeCoefficients :=
  Matrix.single 1 0 (1 : ℤ)

private theorem matrixCoefficients_do_not_commute :
    matrixCoefficient * reverseMatrixCoefficient ≠
      reverseMatrixCoefficient * matrixCoefficient := by
  intro h
  have hentry := congrArg (fun a : NoncommutativeCoefficients => a 0 0) h
  norm_num [matrixCoefficient, reverseMatrixCoefficient,
    Matrix.mul_apply, Matrix.single] at hentry

private theorem stage_elementary_ne_one {R : Type*} [Ring R] (a : R) (ha : a ≠ 0) :
    StableGL.stage R 2 (elementaryUnit 0 1 (by decide) a) ≠ 1 := by
  intro h
  have hfinite : (elementaryUnit 0 1 (by decide) a : GL (Fin 2) R) = 1 := by
    apply StableGL.stage_injective R 2
    simpa using h
  have hentry := congrArg (fun e : GL (Fin 2) R => e 0 1) hfinite
  have hzero : a = 0 := by
    simpa [elementaryUnit_val, Matrix.single_apply, Matrix.one_apply] using hentry
  exact ha hzero

example : elementarySubgroup (Fin 0) ℤ = ⊥ :=
  elementarySubgroup_eq_bot_of_subsingleton

example : elementarySubgroup (Fin 1) (ZMod 1) = ⊥ :=
  elementarySubgroup_eq_bot_of_subsingleton

theorem integer_elementary_ne_one :
    StableGL.stage ℤ 2 (elementaryUnit 0 1 (by decide) (1 : ℤ)) ≠ 1 := by
  exact stage_elementary_ne_one 1 (by norm_num)

private noncomputable def integerElementary : stableElementarySubgroup ℤ :=
  ⟨StableGL.stage ℤ 2 (elementaryUnit 0 1 (by decide) (1 : ℤ)),
    elementaryUnit_mem_stableElementarySubgroup ℤ 2 0 1 (by decide) 1⟩

example : integerElementary ≠ 1 ∧
    integerElementary ∈ _root_.commutator (stableElementarySubgroup ℤ) := by
  refine ⟨?_, Group.IsPerfect.mem_commutator⟩
  intro h
  exact integer_elementary_ne_one (congrArg Subtype.val h)

example : StableGL.stage ℤ 2 (elementaryUnit 0 1 (by decide) (1 : ℤ)) ∈
    stableElementarySubgroup ℤ :=
  elementaryUnit_mem_stableElementarySubgroup ℤ 2 0 1 (by decide) 1

example (a : NoncommutativeCoefficients) :
    StableGL.stage NoncommutativeCoefficients 2 (elementaryUnit 0 1 (by decide) a) ∈
      _root_.commutator (StableGL NoncommutativeCoefficients) := by
  rw [← stableElementarySubgroup_eq_commutator]
  exact elementaryUnit_mem_stableElementarySubgroup NoncommutativeCoefficients
    2 0 1 (by decide) a

private theorem matrixCoefficient_ne_zero : matrixCoefficient ≠ 0 := by
  intro h
  have hentry := congrArg (fun a : NoncommutativeCoefficients => a 0 1) h
  norm_num [matrixCoefficient, Matrix.single_apply] at hentry

example : matrixCoefficient ≠ 0 ∧
    matrixCoefficient * reverseMatrixCoefficient ≠
      reverseMatrixCoefficient * matrixCoefficient :=
  ⟨matrixCoefficient_ne_zero, matrixCoefficients_do_not_commute⟩

private noncomputable def matrixElementary : stableElementarySubgroup NoncommutativeCoefficients :=
  ⟨StableGL.stage NoncommutativeCoefficients 2
      (elementaryUnit 0 1 (by decide) matrixCoefficient),
    elementaryUnit_mem_stableElementarySubgroup NoncommutativeCoefficients
      2 0 1 (by decide) matrixCoefficient⟩

example : matrixElementary ≠ 1 ∧
    matrixElementary ∈
      _root_.commutator (stableElementarySubgroup NoncommutativeCoefficients) := by
  refine ⟨?_, Group.IsPerfect.mem_commutator⟩
  intro h
  exact (stage_elementary_ne_one matrixCoefficient matrixCoefficient_ne_zero)
    (congrArg Subtype.val h)

example (e : stableElementarySubgroup (ZMod 1)) :
    e ∈ _root_.commutator (stableElementarySubgroup (ZMod 1)) :=
  Group.IsPerfect.mem_commutator

example : stableElementaryAbelianizationEquiv (ZMod 1)
      (QuotientGroup.mk' (stableElementarySubgroup (ZMod 1))
        (1 : StableGL (ZMod 1))) = 1 := by
  simp

example : StableGL.stage NoncommutativeCoefficients 2
      (elementaryUnit 0 1 (by decide) matrixCoefficient) ≠ 1 ∧
    StableGL.stage NoncommutativeCoefficients 2
      (elementaryUnit 0 1 (by decide) matrixCoefficient) ∈
        _root_.commutator (StableGL NoncommutativeCoefficients) := by
  refine ⟨stage_elementary_ne_one matrixCoefficient matrixCoefficient_ne_zero, ?_⟩
  rw [← stableElementarySubgroup_eq_commutator]
  exact elementaryUnit_mem_stableElementarySubgroup NoncommutativeCoefficients
    2 0 1 (by decide) matrixCoefficient

example (g h : StableGL (ZMod 1) ⧸ stableElementarySubgroup (ZMod 1)) :
    g * h = h * g := stableElementary_quotient_mul_comm (ZMod 1) g h

example (e : stableElementarySubgroup ℤ) :
    ((StableGL.mapElementary reduceTwo e : stableElementarySubgroup (ZMod 2)) :
      StableGL (ZMod 2)) = StableGL.map reduceTwo e := by
  simp

example (e : stableElementarySubgroup ℤ) :
    StableGL.mapElementary ((RingHom.id (ZMod 2)).comp reduceTwo) e =
      StableGL.mapElementary (RingHom.id (ZMod 2))
        (StableGL.mapElementary reduceTwo e) := by
  rw [StableGL.mapElementary_comp]
  rfl

example : reduceTwo (1 : ℤ) ≠ 0 := by
  norm_num [reduceTwo]

example : StableGL.map reduceTwo
      (StableGL.stage ℤ 2 (elementaryUnit 0 1 (by decide) (1 : ℤ))) =
      StableGL.stage (ZMod 2) 2 (elementaryUnit 0 1 (by decide) (1 : ZMod 2)) ∧
    StableGL.map reduceTwo
      (StableGL.stage ℤ 2 (elementaryUnit 0 1 (by decide) (1 : ℤ))) ≠ 1 := by
  have hmapped : StableGL.map reduceTwo
      (StableGL.stage ℤ 2 (elementaryUnit 0 1 (by decide) (1 : ℤ))) =
        StableGL.stage (ZMod 2) 2 (elementaryUnit 0 1 (by decide) (1 : ZMod 2)) := by
    simp only [StableGL.map_stage, mapRingHom_elementaryUnit]
    rfl
  refine ⟨hmapped, ?_⟩
  rw [hmapped]
  exact stage_elementary_ne_one 1 (by norm_num)
