/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups
public import Mathlib.Data.ZMod.Basic

/-! Clients for finite relative Whitehead block units over proper ideals. -/

set_option warningAsError true

@[expose] public section

open Matrix.GeneralLinearGroup

private def reduceTwo : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)

private def evenIdeal : TwoSidedIdeal ℤ :=
  (⊥ : TwoSidedIdeal (ZMod 2)).comap reduceTwo

private theorem two_mem_evenIdeal : (2 : ℤ) ∈ evenIdeal := by
  change (2 : ZMod 2) = 0
  decide

private theorem evenIdeal_ne_top : evenIdeal ≠ ⊤ := by
  intro h
  have h1 : (1 : ℤ) ∈ evenIdeal := by rw [h]; simp
  simp [evenIdeal, reduceTwo, TwoSidedIdeal.mem_comap] at h1

private def minusOne : GL (Fin 1) ℤ :=
  ⟨-1, -1, by simp, by simp⟩

private theorem minusOne_mem_congruence :
    minusOne ∈ congruenceSubgroup (n := Fin 1) evenIdeal := by
  change mapRingHom (Ideal.Quotient.mk evenIdeal.asIdeal) minusOne = 1
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  change Ideal.Quotient.mk evenIdeal.asIdeal (-1 : ℤ) = 1
  have htwo : Ideal.Quotient.mk evenIdeal.asIdeal (2 : ℤ) = 0 :=
    quotient_mk_ideal_coe_eq_zero evenIdeal ⟨2, two_mem_evenIdeal⟩
  have hneg : (-1 : ℤ) = 1 - 2 := by norm_num
  rw [hneg, map_sub, map_one, htwo, sub_zero]

private theorem minusOne_not_elementary :
    minusOne ∉ elementarySubgroup (Fin 1) ℤ := by
  rw [elementarySubgroup_eq_bot_of_subsingleton]
  intro h
  have heq : minusOne = 1 := Subgroup.mem_bot.mp h
  have h00 := congrArg
    (fun x : GL (Fin 1) ℤ => (x : Matrix (Fin 1) (Fin 1) ℤ) 0 0) heq
  norm_num [minusOne, Matrix.one_apply] at h00

example : evenIdeal ≠ ⊤ := evenIdeal_ne_top

example : minusOne ∉ elementarySubgroup (Fin 1) ℤ := minusOne_not_elementary

example :
    (⟨blockDiagonalUnit minusOne,
      blockDiagonalUnit_mem_elementarySubgroup minusOne⟩ :
      elementarySubgroup ((Fin 1) ⊕ (Fin 1)) ℤ) ∈
        relativeElementarySubgroup evenIdeal :=
  blockDiagonalUnit_mem_relativeElementarySubgroup evenIdeal
    ⟨minusOne, minusOne_mem_congruence⟩

private abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ
private abbrev ReducedCoeff := Matrix (Fin 2) (Fin 2) (ZMod 2)

private def matrixEvenIdeal : TwoSidedIdeal Coeff :=
  (⊥ : TwoSidedIdeal ReducedCoeff).comap reduceTwo.mapMatrix

private theorem matrixEvenIdeal_ne_top : matrixEvenIdeal ≠ ⊤ := by
  intro h
  have h1 : (1 : Coeff) ∈ matrixEvenIdeal := by rw [h]; simp
  change reduceTwo.mapMatrix (1 : Coeff) = 0 at h1
  have h00 := congrArg (fun m : ReducedCoeff => m 0 0) h1
  norm_num at h00

private def firstCoeff : Coeff := Matrix.single 0 1 2
private def secondCoeff : Coeff := Matrix.single 1 0 1

private theorem firstCoeff_mem_matrixEvenIdeal : firstCoeff ∈ matrixEvenIdeal := by
  change reduceTwo.mapMatrix firstCoeff ∈ (⊥ : TwoSidedIdeal ReducedCoeff)
  have htwo : reduceTwo (2 : ℤ) = 0 := by decide
  simp [firstCoeff, htwo]

private theorem coefficients_do_not_commute :
    firstCoeff * secondCoeff ≠ secondCoeff * firstCoeff := by
  intro h
  have h00 := congrArg (fun m : Coeff => m 0 0) h
  norm_num [firstCoeff, secondCoeff, Matrix.mul_apply, Matrix.single] at h00

private def matrixGenerator : GL (Fin 2) Coeff :=
  elementaryUnit (ι := Fin 2) 0 1 (by decide) firstCoeff

private theorem matrixGenerator_mem_congruence :
    matrixGenerator ∈ congruenceSubgroup (n := Fin 2) matrixEvenIdeal := by
  have hrel :
      (⟨matrixGenerator, elementaryUnit_mem 0 1 (by decide) firstCoeff⟩ :
        elementarySubgroup (Fin 2) Coeff) ∈
          relativeElementarySubgroup matrixEvenIdeal :=
    elementaryUnit_mem_relativeElementarySubgroup matrixEvenIdeal
      0 1 (by decide) firstCoeff firstCoeff_mem_matrixEvenIdeal
  exact relativeElementarySubgroup_le_congruenceSubgroup matrixEvenIdeal hrel

private theorem matrixGenerator_ne_one : matrixGenerator ≠ 1 := by
  intro h
  have h01 := congrArg
    (fun x : GL (Fin 2) Coeff => (x : Matrix (Fin 2) (Fin 2) Coeff) 0 1) h
  have hcoeff := congrArg (fun x : Coeff => x 0 1) h01
  norm_num [matrixGenerator, elementaryUnit, firstCoeff, Matrix.single] at hcoeff

example : matrixEvenIdeal ≠ ⊤ := matrixEvenIdeal_ne_top

example : firstCoeff * secondCoeff ≠ secondCoeff * firstCoeff :=
  coefficients_do_not_commute

example : matrixGenerator ≠ 1 := matrixGenerator_ne_one

example :
    (⟨blockDiagonalUnit matrixGenerator,
      blockDiagonalUnit_mem_elementarySubgroup matrixGenerator⟩ :
      elementarySubgroup ((Fin 2) ⊕ (Fin 2)) Coeff) ∈
        relativeElementarySubgroup matrixEvenIdeal :=
  blockDiagonalUnit_mem_relativeElementarySubgroup matrixEvenIdeal
    ⟨matrixGenerator, matrixGenerator_mem_congruence⟩

example (a : Matrix (Fin 2) (Fin 2) Coeff)
    (ha : ∀ i j, a i j ∈ matrixEvenIdeal) :
    (⟨upperUnit a, upperUnit_mem_elementarySubgroup a⟩ :
      elementarySubgroup ((Fin 2) ⊕ (Fin 2)) Coeff) ∈
        relativeElementarySubgroup matrixEvenIdeal :=
  upperUnit_mem_relativeElementarySubgroup matrixEvenIdeal a ha

example (a : Matrix (Fin 2) (Fin 2) Coeff)
    (ha : ∀ i j, a i j ∈ matrixEvenIdeal) :
    (⟨lowerUnit a, lowerUnit_mem_elementarySubgroup a⟩ :
      elementarySubgroup ((Fin 2) ⊕ (Fin 2)) Coeff) ∈
        relativeElementarySubgroup matrixEvenIdeal :=
  lowerUnit_mem_relativeElementarySubgroup matrixEvenIdeal a ha

namespace GeneralLinearGroupsTests.RelativeWhitehead

/-- The doubled diagonal of an empty-index congruence unit is relatively elementary. -/
theorem empty_blockDiagonalUnit_relative
    (I : TwoSidedIdeal ℤ) (g : congruenceSubgroup (n := PEmpty) I) :
    (⟨blockDiagonalUnit g.1, blockDiagonalUnit_mem_elementarySubgroup g.1⟩ :
      elementarySubgroup (PEmpty ⊕ PEmpty) ℤ) ∈ relativeElementarySubgroup I :=
  blockDiagonalUnit_mem_relativeElementarySubgroup I g

end GeneralLinearGroupsTests.RelativeWhitehead

example (I : TwoSidedIdeal (ZMod 1))
    (g : congruenceSubgroup (n := Fin 1) I) :
    (⟨blockDiagonalUnit g.1, blockDiagonalUnit_mem_elementarySubgroup g.1⟩ :
      elementarySubgroup ((Fin 1) ⊕ (Fin 1)) (ZMod 1)) ∈
        relativeElementarySubgroup I :=
  blockDiagonalUnit_mem_relativeElementarySubgroup I g
