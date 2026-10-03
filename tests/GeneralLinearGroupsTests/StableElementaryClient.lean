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

private def finiteDet (n : ℕ) : GL (Fin n) ℤ →* ℤˣ :=
  Matrix.GeneralLinearGroup.det

private theorem finiteDet_stabilize (n m : ℕ) (h : n ≤ m) (g : GL (Fin n) ℤ) :
    finiteDet m (finStabilize ℤ h g) = finiteDet n g := by
  apply Units.ext
  change Matrix.det ((finStabilize ℤ h g : GL (Fin m) ℤ) :
    Matrix (Fin m) (Fin m) ℤ) =
      Matrix.det (g : Matrix (Fin n) (Fin n) ℤ)
  change Matrix.det (Matrix.reindex (finBlockEquiv h) (finBlockEquiv h)
    (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℤ) 0 0 1)) =
      Matrix.det (g : Matrix (Fin n) (Fin n) ℤ)
  simp

private def stableDet : StableGL ℤ →* ℤˣ :=
  StableGL.lift ℤ finiteDet finiteDet_stabilize

private theorem stableDet_elementary (g : StableGL ℤ)
    (hg : g ∈ stableElementarySubgroup ℤ) : stableDet g = 1 := by
  obtain ⟨n, e, rfl⟩ := (mem_stableElementarySubgroup_iff ℤ g).mp hg
  exact Matrix.det_elementarySubgroup_eq_one e

private noncomputable def quotientDet :
    (StableGL ℤ ⧸ stableElementarySubgroup ℤ) →* ℤˣ :=
  QuotientGroup.lift (stableElementarySubgroup ℤ) stableDet
    (by intro g hg; exact MonoidHom.mem_ker.mpr (stableDet_elementary g hg))

private def negOneRankOne : GL (Fin 1) ℤ :=
  Matrix.GeneralLinearGroup.scalar (Fin 1) (-1 : ℤˣ)

example :
    (QuotientGroup.mk' (stableElementarySubgroup ℤ)
      (StableGL.stage ℤ 1 negOneRankOne) :
        StableGL ℤ ⧸ stableElementarySubgroup ℤ) ≠ 1 := by
  intro heq
  have hdet := congrArg quotientDet heq
  have hneg : (-1 : ℤˣ) = 1 := by
    convert hdet using 1 <;>
      simp [quotientDet, stableDet, finiteDet, negOneRankOne,
        Matrix.GeneralLinearGroup.det_scalar]
  have hval := congrArg Units.val hneg
  norm_num at hval
