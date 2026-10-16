/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups.PrincipalUnits.Powers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.NormNum

/-!
# A principal-unit power layer over the 5-adic integers

The ideal `(5)` in `ℤ_[5]` is nonzero and lies in the Jacobson radical. Its
coefficient quotient is nontrivial, as detected by reduction to `ZMod 5`.
The original unit `6 = 1 + 5` has nontrivial first-layer class. With generator
`10 = 2 * 5`, its forward coefficient is `3` modulo `5`. In contrast, the
inverse parameter `1` for generator `10` gives the unit `11 = 1 + 10`, whose
coefficient for generator `5` is `2`. Thus the two change-of-generator factors
are distinguished numerically.

The ideal hypotheses, coefficient nontriviality, original-unit values and
nontrivial unit class below use only the ideal, p-adic and principal-unit APIs.
-/

namespace Ideal

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private noncomputable def fiveIdeal : Ideal ℤ_[5] := Ideal.span {(5 : ℤ_[5])}

private theorem fiveIdeal_ne_bot : fiveIdeal ≠ ⊥ := by
  rw [fiveIdeal, ne_eq, Ideal.span_singleton_eq_bot]
  norm_num

private theorem fiveIdeal_jacobson : fiveIdeal ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.jacobson_bot, IsLocalRing.ringJacobson_eq_maximalIdeal,
    PadicInt.maximalIdeal_eq_span_p]
  exact le_rfl

private theorem fiveIdeal_le_ker : fiveIdeal ≤ RingHom.ker PadicInt.toZMod := by
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
  exact le_rfl

private noncomputable def fiveReduction : (ℤ_[5] ⧸ fiveIdeal) →+* ZMod 5 :=
  Ideal.Quotient.lift fiveIdeal PadicInt.toZMod
    (fun _ hx => RingHom.mem_ker.mp (fiveIdeal_le_ker hx))

private theorem fiveReduction_mk (a : ℤ_[5]) :
    fiveReduction (Ideal.Quotient.mk fiveIdeal a) = PadicInt.toZMod a := rfl

private theorem coefficient_nontrivial : Nontrivial (ℤ_[5] ⧸ fiveIdeal) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have h' := congrArg fiveReduction h
  simp at h'

private theorem coefficient_three_ne_two :
    (3 : ℤ_[5] ⧸ fiveIdeal) ≠ 2 := by
  intro h
  have h' : (3 : ZMod 5) = 2 := by
    simpa only [map_ofNat] using congrArg fiveReduction h
  exact (by decide : (3 : ZMod 5) ≠ 2) h'

private theorem two_isUnit : IsUnit (2 : ℤ_[5]) := by
  apply PadicInt.isUnit_iff.mpr
  exact (PadicInt.norm_natCast_eq_one_iff (p := 5) (n := 2)).mpr (by decide)

private noncomputable def two : ℤ_[5]ˣ := two_isUnit.unit

private theorem two_value : (two : ℤ_[5]) = 2 := IsUnit.unit_spec _

private theorem ten_generator : fiveIdeal = Ideal.span {(10 : ℤ_[5])} := by
  rw [show (10 : ℤ_[5]) = (two : ℤ_[5]) * 5 by rw [two_value]; norm_num,
    Ideal.span_singleton_mul_left_unit two.isUnit]
  rfl

private theorem inverse_two_mod_five : PadicInt.toZMod (↑(two⁻¹) : ℤ_[5]) = 3 := by
  change (↑((Units.map PadicInt.toZMod.toMonoidHom two)⁻¹) : ZMod 5) = 3
  apply Units.inv_eq_of_mul_eq_one_right
  change PadicInt.toZMod (two : ℤ_[5]) * 3 = 1
  simpa only [two_value, map_ofNat] using (show (2 : ZMod 5) * 3 = 1 by decide)

private theorem layer_square_le :
    (fiveIdeal ^ 1) ^ 2 ≤ fiveIdeal ^ (1 + 1) := by simp

private theorem layer_jacobson : fiveIdeal ^ 1 ≤ Ring.jacobson ℤ_[5] := by
  simpa only [pow_one, Ideal.jacobson_bot] using fiveIdeal_jacobson

private noncomputable def fiveMultiple (a : ℤ_[5]) : (fiveIdeal ^ 1 : Ideal ℤ_[5]) :=
  ⟨a * 5 ^ 1, by
    simpa only [pow_one] using
      Ideal.mul_mem_left fiveIdeal a (Ideal.mem_span_singleton_self (5 : ℤ_[5]))⟩

private noncomputable def liftCoefficient (a : ℤ_[5]) :
    MulAction.stabilizer ℤ_[5]ˣ
      (Submodule.Quotient.mk (1 : ℤ_[5]) : ℤ_[5] ⧸ (fiveIdeal ^ 1 : Ideal ℤ_[5])) :=
  (fiveIdeal ^ 1).principalUnitsMk layer_jacobson (fiveMultiple a)

private theorem liftCoefficient_value (a : ℤ_[5]) :
    ((liftCoefficient a).1 : ℤ_[5]) = 1 + a * 5 := by
  simp [liftCoefficient, fiveMultiple]

private theorem six_value : ((liftCoefficient 1).1 : ℤ_[5]) = 6 := by
  rw [liftCoefficient_value]
  norm_num

private theorem five_not_mem_square : (5 : ℤ_[5]) ∉ fiveIdeal ^ 2 := by
  rw [fiveIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro h
  have hz : (5 ^ 2 : ℤ) ∣ 5 :=
    (PadicInt.pow_p_dvd_int_iff (p := 5) 2 5).mp h
  norm_num at hz

private theorem six_class_ne_one :
    (QuotientGroup.mk (liftCoefficient 1) :
      MulAction.stabilizer ℤ_[5]ˣ
        (Submodule.Quotient.mk (1 : ℤ_[5]) : ℤ_[5] ⧸ (fiveIdeal ^ 1 : Ideal ℤ_[5])) ⧸
        ((fiveIdeal ^ 1).principalUnitsToQuotient (fiveIdeal ^ (1 + 1))
          layer_square_le).ker) ≠ 1 := by
  intro h
  have hm := ((fiveIdeal ^ 1).principalUnits_quotient_mk_eq_mk_iff
    (fiveIdeal ^ (1 + 1)) layer_square_le (liftCoefficient 1) 1).mp
      (h.trans (QuotientGroup.mk_one _).symm)
  apply five_not_mem_square
  simpa only [six_value, Subgroup.coe_one, Units.val_one,
    show (6 : ℤ_[5]) - 1 = 5 by norm_num] using hm

private noncomputable def fiveEquiv :=
  fiveIdeal.principalUnitsPowQuotientEquiv fiveIdeal_ne_bot fiveIdeal_jacobson
    5 rfl 1 (by decide)

private noncomputable def tenEquiv :=
  fiveIdeal.principalUnitsPowQuotientEquiv fiveIdeal_ne_bot fiveIdeal_jacobson
    10 ten_generator 1 (by decide)

private theorem five_six_coordinate :
    fiveEquiv (QuotientGroup.mk (liftCoefficient 1)) =
      Multiplicative.ofAdd (Ideal.Quotient.mk fiveIdeal 1) := by
  simpa only [fiveEquiv, liftCoefficient, fiveMultiple] using
    fiveIdeal.principalUnitsPowQuotientEquiv_mk fiveIdeal_ne_bot fiveIdeal_jacobson
      5 rfl 1 (by decide) 1

private theorem ten_six_coordinate :
    fiveReduction (Multiplicative.toAdd
      (tenEquiv (QuotientGroup.mk (liftCoefficient 1)))) = 3 := by
  have h := fiveIdeal.principalUnitsPowQuotientEquiv_unit_mul fiveIdeal_ne_bot
    fiveIdeal_jacobson 5 rfl 1 (by decide) two (QuotientGroup.mk (liftCoefficient 1))
  have h' : Multiplicative.toAdd (tenEquiv (QuotientGroup.mk (liftCoefficient 1))) =
      Ideal.Quotient.mk fiveIdeal (↑(two⁻¹) : ℤ_[5]) *
        Multiplicative.toAdd (fiveEquiv (QuotientGroup.mk (liftCoefficient 1))) := by
    simpa only [fiveEquiv, tenEquiv, pow_one, Units.coe_map_inv,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, two_value,
      show (2 : ℤ_[5]) * 5 = 10 by norm_num] using h
  rw [h', five_six_coordinate]
  simpa only [toAdd_ofAdd, map_mul, fiveReduction_mk, map_one, mul_one]
    using inverse_two_mod_five

private noncomputable def tenMultiple : (fiveIdeal ^ 1 : Ideal ℤ_[5]) :=
  ⟨1 * 10 ^ 1, Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow
    (ten_generator.ge (Ideal.mem_span_singleton_self (10 : ℤ_[5]))) 1)⟩

private noncomputable def tenLift :
    MulAction.stabilizer ℤ_[5]ˣ
      (Submodule.Quotient.mk (1 : ℤ_[5]) : ℤ_[5] ⧸ (fiveIdeal ^ 1 : Ideal ℤ_[5])) :=
  (fiveIdeal ^ 1).principalUnitsMk layer_jacobson tenMultiple

private theorem tenLift_value : (tenLift.1 : ℤ_[5]) = 11 := by
  simp only [tenLift, principalUnitsMk_coe, tenMultiple]
  norm_num

private theorem tenLift_eq : tenLift = liftCoefficient 2 := by
  apply Subtype.ext
  apply Units.ext
  rw [tenLift_value, liftCoefficient_value]
  norm_num

private theorem ten_inverse_one :
    tenEquiv.symm (Multiplicative.ofAdd (Ideal.Quotient.mk fiveIdeal 1)) =
      QuotientGroup.mk tenLift := by
  simpa only [tenEquiv, tenLift, tenMultiple] using
    fiveIdeal.principalUnitsPowQuotientEquiv_symm_mk fiveIdeal_ne_bot fiveIdeal_jacobson
      10 ten_generator 1 (by decide) 1

private theorem five_tenLift_coordinate :
    fiveEquiv (QuotientGroup.mk tenLift) =
      Multiplicative.ofAdd (Ideal.Quotient.mk fiveIdeal 2) := by
  have h := fiveIdeal.principalUnitsPowQuotientEquiv_symm_unit_mul fiveIdeal_ne_bot
    fiveIdeal_jacobson 5 rfl 1 (by decide) two (Ideal.Quotient.mk fiveIdeal 1)
  have h' : tenEquiv.symm (Multiplicative.ofAdd (Ideal.Quotient.mk fiveIdeal 1)) =
      fiveEquiv.symm (Multiplicative.ofAdd (Ideal.Quotient.mk fiveIdeal 2)) := by
    simpa only [fiveEquiv, tenEquiv, pow_one, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, two_value,
      show (2 : ℤ_[5]) * 5 = 10 by norm_num, map_one, mul_one] using h
  rw [ten_inverse_one] at h'
  calc
    fiveEquiv (QuotientGroup.mk tenLift) =
        fiveEquiv (fiveEquiv.symm (Multiplicative.ofAdd
          (Ideal.Quotient.mk fiveIdeal 2))) := congrArg fiveEquiv h'
    _ = Multiplicative.ofAdd (Ideal.Quotient.mk fiveIdeal 2) :=
      fiveEquiv.apply_symm_apply _

end Ideal
