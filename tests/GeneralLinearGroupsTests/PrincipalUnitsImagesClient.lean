/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups.PrincipalUnits.Images
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.NormNum

/-!
# Images of principal units over the 5-adic integers

For the inclusion `ℤ_[5] →+* ℚ_[5]`, the ideal `(5)` lies in the Jacobson
radical. The unit `6 = 1 + 5` is the image of a unit congruent to `1` modulo
`5`. Its construction and this image membership use only Mathlib's p-adic
unit criterion and subgroup image API. The image criterion then recovers
`6 - 1 = 5` as the image of an element of `(5)`.

For `ℤ →+* ℚ`, the unit `3` has `3 - 1 = 2` in the set image of `(2)`, but
it is not the image of an integer unit. This shows why invertibility in the
target does not replace the Jacobson lifting hypothesis.

Mathlib supplies the p-adic rings and inclusion, the ideal and norm criteria,
and the classification of integer units as `1` and `-1`.
-/

namespace Ideal

section Padic

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private noncomputable def inclusion : ℤ_[5] →+* ℚ_[5] := PadicInt.Coe.ringHom

private noncomputable def fiveIdeal : Ideal ℤ_[5] := Ideal.span {(5 : ℤ_[5])}

private theorem fiveIdeal_jacobson : fiveIdeal ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.jacobson_bot, IsLocalRing.ringJacobson_eq_maximalIdeal,
    PadicInt.maximalIdeal_eq_span_p]
  exact le_rfl

private theorem integralSix_isUnit : IsUnit (6 : ℤ_[5]) := by
  apply PadicInt.isUnit_iff.mpr
  exact (PadicInt.norm_natCast_eq_one_iff (p := 5) (n := 6)).mpr (by decide)

private noncomputable def integralSix : ℤ_[5]ˣ := integralSix_isUnit.unit

private theorem integralSix_value : (integralSix : ℤ_[5]) = 6 := IsUnit.unit_spec _

private noncomputable def six : ℚ_[5]ˣ := Units.mk0 6 (by norm_num)

private theorem six_value : (six : ℚ_[5]) = 6 := rfl

private theorem six_ne_one : six ≠ 1 := by
  intro h
  have hv := congrArg (fun x : ℚ_[5]ˣ => (x : ℚ_[5])) h
  norm_num [six_value] at hv

private theorem six_mem_image :
    six ∈ (MulAction.stabilizer ℤ_[5]ˣ
      (Submodule.Quotient.mk (1 : ℤ_[5]) : ℤ_[5] ⧸ fiveIdeal)).map
        (Units.map inclusion.toMonoidHom) := by
  apply Subgroup.mem_map.mpr
  refine ⟨integralSix, ?_, ?_⟩
  · rw [mem_stabilizer_quotient_one, integralSix_value]
    have hfive : (5 : ℤ_[5]) ∈ fiveIdeal := Ideal.mem_span_singleton_self _
    simpa only [show (6 : ℤ_[5]) - 1 = 5 by norm_num] using hfive
  · apply Units.ext
    change inclusion (integralSix : ℤ_[5]) = (6 : ℚ_[5])
    simpa only [map_ofNat] using congrArg inclusion integralSix_value

example : six ≠ 1 ∧ ∃ a : ℤ_[5], a ∈ fiveIdeal ∧ inclusion a = (5 : ℚ_[5]) := by
  refine ⟨six_ne_one, ?_⟩
  have h := (mem_map_stabilizer_quotient_one_iff inclusion fiveIdeal
    fiveIdeal_jacobson six).mp six_mem_image
  simpa only [six_value, show (6 : ℚ_[5]) - 1 = 5 by norm_num] using h

end Padic

section Integer

private def twoIdeal : Ideal ℤ := Ideal.span {(2 : ℤ)}

private noncomputable def three : ℚˣ := Units.mk0 3 (by norm_num)

private theorem three_scalar_preimage :
    ∃ a : ℤ, a ∈ twoIdeal ∧ Int.castRingHom ℚ a = (three : ℚ) - 1 := by
  refine ⟨2, Ideal.mem_span_singleton_self _, ?_⟩
  norm_num [three]

private theorem three_not_mem_image :
    three ∉ (MulAction.stabilizer ℤˣ
      (Submodule.Quotient.mk (1 : ℤ) : ℤ ⧸ twoIdeal)).map
        (Units.map (Int.castRingHom ℚ).toMonoidHom) := by
  intro h
  obtain ⟨v, _, hv⟩ := Subgroup.mem_map.mp h
  have hval := congrArg (fun x : ℚˣ => (x : ℚ)) hv
  rcases Int.units_eq_one_or v with rfl | rfl <;> norm_num [three] at hval

private theorem twoIdeal_not_le_jacobson : ¬ twoIdeal ≤ Ideal.jacobson ⊥ := by
  intro h
  have hthree : IsUnit (3 : ℤ) := Ideal.isUnit_of_sub_one_mem_jacobson_bot 3
    (h (by norm_num [twoIdeal, Ideal.mem_span_singleton]))
  norm_num [Int.isUnit_iff] at hthree

example : ¬ twoIdeal ≤ Ideal.jacobson ⊥ ∧
    (∃ a : ℤ, a ∈ twoIdeal ∧ Int.castRingHom ℚ a = (three : ℚ) - 1) ∧
    three ∉ (MulAction.stabilizer ℤˣ
      (Submodule.Quotient.mk (1 : ℤ) : ℤ ⧸ twoIdeal)).map
        (Units.map (Int.castRingHom ℚ).toMonoidHom) :=
  ⟨twoIdeal_not_le_jacobson, three_scalar_preimage, three_not_mem_image⟩

end Integer

end Ideal
