/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups
public import Mathlib.Data.ZMod.Basic

/-! Finite clients, including an ordered noncommuting example and degenerate index/ring types. -/

set_option warningAsError true

@[expose] public section

open Matrix.GeneralLinearGroup

private def reduceTwo : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)

private def evenIdeal : TwoSidedIdeal ℤ :=
  (⊥ : TwoSidedIdeal (ZMod 2)).comap reduceTwo

private theorem evenIdeal_ne_top : evenIdeal ≠ ⊤ := by
  intro h
  have h1 : (1 : ℤ) ∈ evenIdeal := by rw [h]; simp
  simp [evenIdeal, reduceTwo, TwoSidedIdeal.mem_comap] at h1

private theorem two_mem_evenIdeal : (2 : ℤ) ∈ evenIdeal := by
  change (2 : ZMod 2) = 0
  decide

private def arbitraryConjugator : GL (Fin 2) ℤ :=
  elementaryUnit 0 1 (by decide) 1

private def relativeUnit : elementarySubgroup (Fin 2) ℤ :=
  ⟨elementaryUnit 1 0 (by decide) 2, elementaryUnit_mem 1 0 (by decide) 2⟩

private theorem relativeUnit_mem :
    relativeUnit ∈ relativeElementarySubgroup evenIdeal :=
  elementaryUnit_mem_relativeElementarySubgroup evenIdeal 1 0 (by decide) 2
    two_mem_evenIdeal

private theorem arbitraryConjugator_not_congruence :
    arbitraryConjugator ∉ congruenceSubgroup (n := Fin 2) evenIdeal := by
  intro hg
  have h1 := congruenceSubgroup_entry_sub_mem evenIdeal
    (⟨arbitraryConjugator, hg⟩ : congruenceSubgroup (n := Fin 2) evenIdeal) 0 1
  have hnot : (1 : ℤ) ∉ evenIdeal := by
    intro hone
    change (1 : ZMod 2) = 0 at hone
    norm_num at hone
  apply hnot
  simpa [arbitraryConjugator, elementaryUnit, Matrix.one_apply] using h1

private def firstCongruenceUnit : congruenceSubgroup (n := Fin 2) evenIdeal :=
  ⟨elementaryUnit 0 1 (by decide) 2,
    relativeElementarySubgroup_le_congruenceSubgroup evenIdeal
      (elementaryUnit_mem_relativeElementarySubgroup evenIdeal 0 1 (by decide) 2
        two_mem_evenIdeal)⟩

private def secondCongruenceUnit : congruenceSubgroup (n := Fin 2) evenIdeal :=
  ⟨elementaryUnit 1 0 (by decide) 2,
    relativeElementarySubgroup_le_congruenceSubgroup evenIdeal relativeUnit_mem⟩

private theorem congruence_units_do_not_commute :
    firstCongruenceUnit * secondCongruenceUnit ≠
      secondCongruenceUnit * firstCongruenceUnit := by
  intro h
  have h00 := congrArg (fun g : congruenceSubgroup (n := Fin 2) evenIdeal =>
    (g.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  norm_num [firstCongruenceUnit, secondCongruenceUnit,
    elementaryUnit, Matrix.mul_apply, Matrix.single] at h00

private theorem ordered_commutator_ne_one :
    firstCongruenceUnit * secondCongruenceUnit * firstCongruenceUnit⁻¹ *
      secondCongruenceUnit⁻¹ ≠ 1 := by
  intro h
  have hcomm : firstCongruenceUnit * secondCongruenceUnit =
      secondCongruenceUnit * firstCongruenceUnit := by
    have := congrArg (fun g : congruenceSubgroup (n := Fin 2) evenIdeal =>
      g * secondCongruenceUnit * firstCongruenceUnit) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using this
  exact congruence_units_do_not_commute hcomm

private theorem stabilized_commutator_ne_one :
    stabilize (Y := Fin 2) (firstCongruenceUnit.1 * secondCongruenceUnit.1 *
      firstCongruenceUnit.1⁻¹ * secondCongruenceUnit.1⁻¹) ≠ 1 := by
  intro h
  have heq : firstCongruenceUnit.1 * secondCongruenceUnit.1 *
      firstCongruenceUnit.1⁻¹ * secondCongruenceUnit.1⁻¹ = (1 : GL (Fin 2) ℤ) := by
    apply stabilize_injective (Y := Fin 2)
    simpa using h
  apply ordered_commutator_ne_one
  exact Subtype.ext heq

example : evenIdeal ≠ ⊤ := evenIdeal_ne_top

example : arbitraryConjugator ∉ congruenceSubgroup (n := Fin 2) evenIdeal :=
  arbitraryConjugator_not_congruence

example : firstCongruenceUnit * secondCongruenceUnit ≠
    secondCongruenceUnit * firstCongruenceUnit := congruence_units_do_not_commute

example : firstCongruenceUnit * secondCongruenceUnit * firstCongruenceUnit⁻¹ *
    secondCongruenceUnit⁻¹ ≠ 1 := ordered_commutator_ne_one

example : stabilize (Y := Fin 2) (firstCongruenceUnit.1 * secondCongruenceUnit.1 *
    firstCongruenceUnit.1⁻¹ * secondCongruenceUnit.1⁻¹) ≠ 1 :=
  stabilized_commutator_ne_one

example : stabilize (Y := Fin 2)
    (arbitraryConjugator * (relativeUnit : GL (Fin 2) ℤ) * arbitraryConjugator⁻¹) ∈
      (relativeElementarySubgroup (ι := Fin 2 ⊕ Fin 2) evenIdeal).map
        (elementarySubgroup (Fin 2 ⊕ Fin 2) ℤ).subtype :=
  stabilize_conj_mem_relativeElementarySubgroup evenIdeal
    arbitraryConjugator relativeUnit relativeUnit_mem

example : stabilize (Y := Fin 2)
    (firstCongruenceUnit.1 * secondCongruenceUnit.1 * firstCongruenceUnit.1⁻¹ *
      secondCongruenceUnit.1⁻¹) ∈
      (relativeElementarySubgroup (ι := Fin 2 ⊕ Fin 2) evenIdeal).map
        (elementarySubgroup (Fin 2 ⊕ Fin 2) ℤ).subtype :=
  stabilize_commutator_mem_relativeElementarySubgroup evenIdeal
    firstCongruenceUnit secondCongruenceUnit

universe uX uR

example {X : Type uX} [Fintype X] [DecidableEq X]
    {R : Type uR} [Ring R] (g h : GL X R) :
    stabilize (Y := X) (g * h * g⁻¹ * h⁻¹) =
      blockDiagonalUnit g * blockDiagonalUnit h * blockDiagonalUnit ((h * g)⁻¹) :=
  stabilize_commutator_eq_blockDiagonalUnit_mul g h

example (g h : GL PEmpty ℤ) :
    stabilize (Y := PEmpty) (g * h * g⁻¹) =
      blockDiagonalUnit g * stabilize (Y := PEmpty) h * (blockDiagonalUnit g)⁻¹ :=
  stabilize_conj_eq_blockDiagonalUnit_conj g h

namespace GeneralLinearGroupsTests.RelativeWhiteheadConsequences

/-- Stabilized commutators on empty indices lie in the relative elementary subgroup. -/
theorem empty_stabilized_commutator_relative
    (g h : congruenceSubgroup (n := PEmpty.{1}) (⊥ : TwoSidedIdeal ℤ)) :
    stabilize (Y := PEmpty.{1}) (g.1 * h.1 * g.1⁻¹ * h.1⁻¹) ∈
      (relativeElementarySubgroup (ι := PEmpty.{1} ⊕ PEmpty.{1})
        (⊥ : TwoSidedIdeal ℤ)).map
        (elementarySubgroup (PEmpty.{1} ⊕ PEmpty.{1}) ℤ).subtype :=
  stabilize_commutator_mem_relativeElementarySubgroup ⊥ g h

end GeneralLinearGroupsTests.RelativeWhiteheadConsequences

example (g : GL (Fin 1) (ZMod 1))
    (h : elementarySubgroup (Fin 1) (ZMod 1))
    (hh : h ∈ relativeElementarySubgroup (⊥ : TwoSidedIdeal (ZMod 1))) :
    stabilize (Y := Fin 1) (g * (h : GL (Fin 1) (ZMod 1)) * g⁻¹) ∈
      (relativeElementarySubgroup (ι := Fin 1 ⊕ Fin 1)
        (⊥ : TwoSidedIdeal (ZMod 1))).map
        (elementarySubgroup (Fin 1 ⊕ Fin 1) (ZMod 1)).subtype :=
  stabilize_conj_mem_relativeElementarySubgroup ⊥ g h hh
