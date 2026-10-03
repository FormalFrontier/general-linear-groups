/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups
public import Mathlib.Data.ZMod.Basic

/-! Clients for proper-ideal reduction, compatible transport and noncommutative conjugation. -/

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

example :
    (⟨elementaryUnit (ι := Fin 2) 0 1 (by decide) (2 : ℤ),
      elementaryUnit_mem 0 1 (by decide) (2 : ℤ)⟩ :
      elementarySubgroup (Fin 2) ℤ) ∈
      relativeElementarySubgroup (ι := Fin 2) evenIdeal :=
  elementaryUnit_mem_relativeElementarySubgroup evenIdeal 0 1 (by decide) 2
    two_mem_evenIdeal

example :
    mapElementarySubgroup (ι := Fin 2) reduceTwo
      (⟨elementaryUnit (ι := Fin 2) 0 1 (by decide) (2 : ℤ),
        elementaryUnit_mem 0 1 (by decide) (2 : ℤ)⟩ :
        elementarySubgroup (Fin 2) ℤ) = 1 := by
  rw [mapElementarySubgroup_elementaryUnit]
  apply Subtype.ext
  have htwo : reduceTwo (2 : ℤ) = 0 := by decide
  rw [htwo]
  simp

example :
    (relativeElementarySubgroup (ι := Fin 2) evenIdeal).map
      (mapElementarySubgroup reduceTwo) ≤
      relativeElementarySubgroup (ι := Fin 2) (⊥ : TwoSidedIdeal (ZMod 2)) :=
  mapElementarySubgroup_relativeElementarySubgroup_le reduceTwo evenIdeal ⊥ le_rfl

example :
    (relativeElementarySubgroup (ι := Fin 2) evenIdeal).map
      (mapElementarySubgroup reduceTwo) = ⊥ := by
  apply le_antisymm
  · simpa using (mapElementarySubgroup_relativeElementarySubgroup_le
      (ι := Fin 2) reduceTwo evenIdeal ⊥ le_rfl)
  · exact bot_le

private abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ
private abbrev ReducedCoeff := Matrix (Fin 2) (Fin 2) (ZMod 2)

private def matrixEvenIdeal : TwoSidedIdeal Coeff :=
  (⊥ : TwoSidedIdeal ReducedCoeff).comap reduceTwo.mapMatrix

private theorem matrixEvenIdeal_ne_top : matrixEvenIdeal ≠ ⊤ := by
  intro h
  have h1 : (1 : Coeff) ∈ matrixEvenIdeal := by rw [h]; simp
  change reduceTwo.mapMatrix (1 : Coeff) = 0 at h1
  have h00 := congrArg (fun m : ReducedCoeff ↦ m 0 0) h1
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
  have h00 := congrArg (fun m : Coeff ↦ m 0 0) h
  norm_num [firstCoeff, secondCoeff, Matrix.mul_apply, Matrix.single] at h00

private def relativeGenerator : elementarySubgroup (Fin 2) Coeff :=
  ⟨elementaryUnit (ι := Fin 2) 0 1 (by decide) firstCoeff,
    elementaryUnit_mem 0 1 (by decide) firstCoeff⟩

private def conjugator : elementarySubgroup (Fin 2) Coeff :=
  ⟨elementaryUnit (ι := Fin 2) 1 0 (by decide) secondCoeff,
    elementaryUnit_mem 1 0 (by decide) secondCoeff⟩

example :
    conjugator * relativeGenerator * conjugator⁻¹ ∈
      relativeElementarySubgroup (ι := Fin 2) matrixEvenIdeal := by
  exact (inferInstance : (relativeElementarySubgroup (ι := Fin 2) matrixEvenIdeal).Normal).conj_mem
    relativeGenerator (elementaryUnit_mem_relativeElementarySubgroup
      matrixEvenIdeal 0 1 (by decide) firstCoeff firstCoeff_mem_matrixEvenIdeal)
    conjugator

example : relativeElementarySubgroup (ι := PEmpty) evenIdeal = ⊥ := by
  apply le_antisymm _ bot_le
  intro x _
  exact Subgroup.mem_bot.mpr (Subsingleton.elim x 1)

namespace GeneralLinearGroupsTests.RelativeElementary

/-- In the zero ring, the relative elementary subgroup at the zero ideal is trivial. -/
theorem zero_ring_relativeElementarySubgroup_bot :
    relativeElementarySubgroup (ι := Fin 1) (⊥ : TwoSidedIdeal (ZMod 1)) = ⊥ :=
  relativeElementarySubgroup_bot

end GeneralLinearGroupsTests.RelativeElementary

example : mapElementarySubgroup (ι := Fin 2) (RingHom.id (ZMod 1)) =
    MonoidHom.id (elementarySubgroup (Fin 2) (ZMod 1)) :=
  mapElementarySubgroup_id

example (f : ℤ →+* ZMod 2) (g : ZMod 2 →+* ZMod 1) :
    mapElementarySubgroup (ι := Fin 2) (g.comp f) =
      (mapElementarySubgroup g).comp (mapElementarySubgroup f) :=
  mapElementarySubgroup_comp f g
