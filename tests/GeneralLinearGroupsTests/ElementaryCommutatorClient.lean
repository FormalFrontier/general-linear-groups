/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups
public import Mathlib.Data.ZMod.Basic

/-! Clients for disjoint positions, ordered commutators, and finite-rank perfectness. -/

set_option warningAsError true

@[expose] public section

open Matrix.GeneralLinearGroup
open scoped commutatorElement

private abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ

private def firstCoeff : Coeff := Matrix.single 0 1 1
private def secondCoeff : Coeff := Matrix.single 1 0 1

private theorem coefficients_do_not_commute :
    firstCoeff * secondCoeff ≠ secondCoeff * firstCoeff := by
  intro h
  have h00 := congrArg (fun m : Coeff ↦ m 0 0) h
  norm_num [firstCoeff, secondCoeff, Matrix.mul_apply, Matrix.single] at h00

example (a b : Coeff) :
    Commute (elementaryUnit (ι := Fin 3) 0 1 (by decide) a)
      (elementaryUnit 0 2 (by decide) b) :=
  elementaryUnit_commute_disjoint 0 1 0 2 (by decide) (by decide)
    (by decide) (by decide) a b

example (a b : Coeff) :
    ⁅elementaryUnit (ι := Fin 3) 0 1 (by decide) a,
      elementaryUnit (ι := Fin 3) 1 2 (by decide) b⁆ =
        elementaryUnit (ι := Fin 3) 0 2 (by decide) (a * b) :=
  elementaryUnit_commutator (ι := Fin 3) 0 1 2 (by decide) (by decide) (by decide) a b

example (a : Coeff) :
    elementaryUnit (ι := Fin 3) 0 2 (by decide) a =
      ⁅elementaryUnit (ι := Fin 3) 0 1 (by decide) a,
        elementaryUnit (ι := Fin 3) 1 2 (by decide) (1 : Coeff)⁆ :=
  elementaryUnit_eq_commutator (ι := Fin 3) 0 2 1 (by decide) (by decide) (by decide) a

example :
    ⁅elementaryUnit (ι := Fin 3) 0 1 (by decide) firstCoeff,
      elementaryUnit (ι := Fin 3) 1 2 (by decide) secondCoeff⁆ ≠
    ⁅elementaryUnit (ι := Fin 3) 0 1 (by decide) secondCoeff,
      elementaryUnit (ι := Fin 3) 1 2 (by decide) firstCoeff⁆ := by
  rw [elementaryUnit_commutator (ι := Fin 3) 0 1 2 (by decide) (by decide) (by decide),
    elementaryUnit_commutator (ι := Fin 3) 0 1 2 (by decide) (by decide) (by decide)]
  intro h
  have h02 := congrArg
    (fun g : GL (Fin 3) Coeff ↦ ((g : Matrix (Fin 3) (Fin 3) Coeff) 0 2)) h
  apply coefficients_do_not_commute
  simpa [Matrix.single_apply, Matrix.one_apply] using h02

example : Group.IsPerfect (elementarySubgroup (Fin 3) ℤ) :=
  elementarySubgroup_isPerfect_of_three_le_card (by decide)

example : Group.IsPerfect (elementarySubgroup (Fin 3) Coeff) :=
  elementarySubgroup_isPerfect_of_three_le_card (by decide)

namespace GeneralLinearGroupsTests.ElementaryCommutator

/-- The rank-three elementary subgroup over the zero ring is perfect. -/
theorem zero_ring_elementarySubgroup_isPerfect :
    Group.IsPerfect (elementarySubgroup (Fin 3) (ZMod 1)) :=
  elementarySubgroup_isPerfect_of_three_le_card (by decide)

end GeneralLinearGroupsTests.ElementaryCommutator

example (a b : ZMod 1) :
    ⁅elementaryUnit (ι := Fin 3) 0 1 (by decide) a,
      elementaryUnit (ι := Fin 3) 1 2 (by decide) b⁆ =
        elementaryUnit (ι := Fin 3) 0 2 (by decide) (a * b) :=
  elementaryUnit_commutator (ι := Fin 3) 0 1 2 (by decide) (by decide) (by decide) a b

example : elementarySubgroup PEmpty ℤ = ⊥ :=
  elementarySubgroup_eq_bot_of_subsingleton

example : elementarySubgroup (Fin 1) ℤ = ⊥ :=
  elementarySubgroup_eq_bot_of_subsingleton
