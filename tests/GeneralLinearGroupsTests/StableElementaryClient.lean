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
private def reduceThree : ℤ →+* ZMod 3 := Int.castRingHom (ZMod 3)
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

private def finiteDet (R : Type*) [CommRing R] (n : ℕ) : GL (Fin n) R →* Rˣ :=
  Matrix.GeneralLinearGroup.det

private theorem finiteDet_stabilize (R : Type*) [CommRing R]
    (n m : ℕ) (h : n ≤ m) (g : GL (Fin n) R) :
    finiteDet R m (finStabilize R h g) = finiteDet R n g := by
  apply Units.ext
  change Matrix.det ((finStabilize R h g : GL (Fin m) R) :
    Matrix (Fin m) (Fin m) R) =
      Matrix.det (g : Matrix (Fin n) (Fin n) R)
  change Matrix.det (Matrix.reindex (finBlockEquiv h) (finBlockEquiv h)
    (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) R) 0 0 1)) =
      Matrix.det (g : Matrix (Fin n) (Fin n) R)
  simp

private def stableDet (R : Type*) [CommRing R] : StableGL R →* Rˣ :=
  StableGL.lift R (finiteDet R) (finiteDet_stabilize R)

private theorem stableDet_elementary (R : Type*) [CommRing R] (g : StableGL R)
    (hg : g ∈ stableElementarySubgroup R) : stableDet R g = 1 := by
  obtain ⟨n, e, rfl⟩ := (mem_stableElementarySubgroup_iff R g).mp hg
  exact Matrix.det_elementarySubgroup_eq_one e

private noncomputable def quotientDet (R : Type*) [CommRing R] :
    (StableGL R ⧸ stableElementarySubgroup R) →* Rˣ :=
  QuotientGroup.lift (stableElementarySubgroup R) (stableDet R)
    (by intro g hg; exact MonoidHom.mem_ker.mpr (stableDet_elementary R g hg))

private theorem quotientDet_eq_abelianizationLift (R : Type*) [CommRing R] :
    quotientDet R =
      (Abelianization.lift (stableDet R)).comp
        (stableElementaryAbelianizationEquiv R).toMonoidHom := by
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro g
  change stableDet R g =
    Abelianization.lift (stableDet R)
      (stableElementaryAbelianizationEquiv R
        (QuotientGroup.mk' (stableElementarySubgroup R) g))
  rw [stableElementaryAbelianizationEquiv_mk, Abelianization.lift_apply_of]

private theorem stableDet_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : StableGL R) :
    stableDet S (StableGL.map f g) = Units.map f (stableDet R g) := by
  obtain ⟨n, x, rfl⟩ := StableGL.exists_stage R g
  rw [StableGL.map_stage]
  change finiteDet S n (mapRingHom f x) = Units.map f (finiteDet R n x)
  exact Matrix.GeneralLinearGroup.map_det f x

private def negOneRankOne : GL (Fin 1) ℤ :=
  Matrix.GeneralLinearGroup.scalar (Fin 1) (-1 : ℤˣ)

example :
    (QuotientGroup.mk' (stableElementarySubgroup ℤ)
      (StableGL.stage ℤ 1 negOneRankOne) :
        StableGL ℤ ⧸ stableElementarySubgroup ℤ) ≠ 1 := by
  intro heq
  have hdet := congrArg (quotientDet ℤ) heq
  have hneg : (-1 : ℤˣ) = 1 := by
    convert hdet using 1 <;>
      simp [quotientDet, stableDet, finiteDet, negOneRankOne,
        Matrix.GeneralLinearGroup.det_scalar]
  have hval := congrArg Units.val hneg
  norm_num at hval

private noncomputable def negOneQuotient : StableGL ℤ ⧸ stableElementarySubgroup ℤ :=
  QuotientGroup.mk' (stableElementarySubgroup ℤ)
    (StableGL.stage ℤ 1 negOneRankOne)

private noncomputable def mappedNegOneQuotient :
    StableGL (ZMod 3) ⧸ stableElementarySubgroup (ZMod 3) :=
  QuotientGroup.map (stableElementarySubgroup ℤ)
    (stableElementarySubgroup (ZMod 3)) (StableGL.map reduceThree)
    ((Subgroup.map_le_iff_le_comap).mp
      (StableGL.map_elementarySubgroup_le reduceThree)) negOneQuotient

private theorem quotientDet_mappedNegOne :
    quotientDet (ZMod 3) mappedNegOneQuotient = (-1 : (ZMod 3)ˣ) := by
  have hrepresentative : mappedNegOneQuotient =
      QuotientGroup.mk' (stableElementarySubgroup (ZMod 3))
        (StableGL.map reduceThree (StableGL.stage ℤ 1 negOneRankOne)) := by
    simp [mappedNegOneQuotient, negOneQuotient]
  rw [hrepresentative]
  change stableDet (ZMod 3)
    (StableGL.map reduceThree (StableGL.stage ℤ 1 negOneRankOne)) =
      (-1 : (ZMod 3)ˣ)
  rw [stableDet_map]
  simp [stableDet, finiteDet, negOneRankOne,
    Matrix.GeneralLinearGroup.det_scalar, reduceThree]

example : (Abelianization.lift (stableDet ℤ))
      (stableElementaryAbelianizationEquiv ℤ negOneQuotient) = (-1 : ℤˣ) := by
  have hquot : (Abelianization.lift (stableDet ℤ))
      (stableElementaryAbelianizationEquiv ℤ negOneQuotient) =
        quotientDet ℤ negOneQuotient := by
    rw [quotientDet_eq_abelianizationLift ℤ]
    rfl
  rw [hquot]
  simp [negOneQuotient, quotientDet, stableDet, finiteDet, negOneRankOne,
    Matrix.GeneralLinearGroup.det_scalar]

example : stableElementaryAbelianizationEquiv (ZMod 3) mappedNegOneQuotient =
      Abelianization.map (StableGL.map reduceThree)
        (stableElementaryAbelianizationEquiv ℤ negOneQuotient) ∧
    mappedNegOneQuotient ≠ 1 := by
  refine ⟨stableElementaryAbelianizationEquiv_map reduceThree negOneQuotient, ?_⟩
  intro heq
  have hdet := congrArg (quotientDet (ZMod 3)) heq
  rw [quotientDet_mappedNegOne, map_one] at hdet
  have hval := congrArg Units.val hdet
  have hne : (-1 : ZMod 3) ≠ 1 := by decide
  exact hne hval
