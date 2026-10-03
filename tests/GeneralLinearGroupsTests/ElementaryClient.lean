/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups
public import Mathlib.Data.ZMod.Basic

/-! Client checks for native elementary units over noncommutative and degenerate rings. -/

set_option warningAsError true

@[expose] public section

open Matrix.GeneralLinearGroup

private abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ

/-- The coefficient ring in the following GL examples is genuinely noncommutative. -/
private theorem coefficients_do_not_commute :
    (Matrix.single 0 1 (1 : ℤ) : Coeff) * Matrix.single 1 0 1 ≠
      (Matrix.single 1 0 (1 : ℤ) : Coeff) * Matrix.single 0 1 1 := by
  intro h
  have h00 := congrArg (fun m : Coeff ↦ m 0 0) h
  norm_num [Matrix.mul_apply, Matrix.single] at h00

example (c d : Coeff) :
    elementaryUnit (ι := Fin 2) 0 1 (by decide) c *
        elementaryUnit 0 1 (by decide) d =
      elementaryUnit 0 1 (by decide) (c + d) :=
  elementaryUnit_mul_same 0 1 (by decide) c d

example (c : Coeff) :
    elementaryUnit (ι := Fin 2) 0 1 (by decide) c ∈
      elementarySubgroup (Fin 2) Coeff :=
  elementaryUnit_mem 0 1 (by decide) c

example (c d : Coeff) :
    ([(elementaryUnit (ι := Fin 2) 0 1 (by decide) c),
      elementaryUnit 1 0 (by decide) d] : List (GL (Fin 2) Coeff)).prod ∈
      elementarySubgroup (Fin 2) Coeff := by
  apply elementary_list_prod_mem
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨0, 1, by decide, c, rfl⟩
  · exact ⟨1, 0, by decide, d, rfl⟩

example (a : Matrix (Fin 2) (Fin 2) Coeff) :
    upperUnit a ∈ elementarySubgroup ((Fin 2) ⊕ (Fin 2)) Coeff :=
  upperUnit_mem_elementarySubgroup a

example (a : Matrix (Fin 2) (Fin 2) Coeff) :
    lowerUnit a ∈ elementarySubgroup ((Fin 2) ⊕ (Fin 2)) Coeff :=
  lowerUnit_mem_elementarySubgroup a

example (g : GL (Fin 2) Coeff) :
    blockDiagonalUnit g ∈ elementarySubgroup ((Fin 2) ⊕ (Fin 2)) Coeff :=
  blockDiagonalUnit_mem_elementarySubgroup g

example :
    (swapUnit : GL ((Fin 2) ⊕ (Fin 2)) Coeff) ∈
      elementarySubgroup ((Fin 2) ⊕ (Fin 2)) Coeff :=
  swapUnit_mem_elementarySubgroup

example (c : ℤ) :
    elementaryUnit (ι := Fin 2) 0 1 (by decide) c =
      Matrix.GeneralLinearGroup.transvection 0 1 (by decide) c :=
  elementaryUnit_eq_transvection 0 1 (by decide) c

namespace GeneralLinearGroupsTests.Elementary

/-- On empty indices the elementary subgroup is trivial. -/
theorem empty_elementarySubgroup_bot : elementarySubgroup PEmpty ℤ = ⊥ :=
  elementarySubgroup_eq_bot_of_subsingleton

end GeneralLinearGroupsTests.Elementary

example : elementarySubgroup (Fin 1) ℤ = ⊥ :=
  elementarySubgroup_eq_bot_of_subsingleton

example (c : ZMod 1) :
    elementaryUnit (ι := Fin 2) 0 1 (by decide) c ∈
      elementarySubgroup (Fin 2) (ZMod 1) :=
  elementaryUnit_mem 0 1 (by decide) c

example (a : Matrix (Fin 1) (Fin 1) (ZMod 1)) :
    upperUnit a ∈ elementarySubgroup ((Fin 1) ⊕ (Fin 1)) (ZMod 1) :=
  upperUnit_mem_elementarySubgroup a
