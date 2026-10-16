/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups

/-!
# Square-zero unit-kernel clients

For dual numbers over any field, the infinitesimal is a nonzero element of the
projection kernel. The square-zero equivalence constructs a nonidentity unit
from it, and its inverse has infinitesimal coefficient `-1`. The comparison with
the dual-number construction detects every nonzero coefficient. For the identity
homomorphism on any ring, every unit-kernel coordinate is zero.
-/

-- Client witnesses are private: this module adds no public mathematical API.
set_option linter.privateModule false

@[expose] public section

universe u v

namespace DualNumber

private theorem eps_kernel_ne_zero (K : Type u) [Field K] :
    (⟨eps, by rfl⟩ : RingHom.ker (fstRingHom K)) ≠ 0 := by
  intro h
  have hs := congrArg
    (fun x : RingHom.ker (fstRingHom K) => (x : DualNumber K).snd) h
  exact one_ne_zero hs

private theorem eps_unit_ne_one (K : Type u) [Field K] :
    (RingHom.unitsKerEquivOfSquareZero (fstRingHom K)
      (fstRingHom_ker_sq K)).symm
        (Multiplicative.ofAdd (⟨eps, by rfl⟩ : RingHom.ker (fstRingHom K))) ≠ 1 := by
  intro h
  have hs := congrArg
    (fun u : (Units.map (fstRingHom K).toMonoidHom).ker =>
      (u.1 : DualNumber K).snd) h
  rw [RingHom.unitsKerEquivOfSquareZero_symm_apply_coe, toAdd_ofAdd] at hs
  simp at hs

private theorem eps_unit_inverse_snd (K : Type u) [Field K] :
    (Units.val (((RingHom.unitsKerEquivOfSquareZero (fstRingHom K)
      (fstRingHom_ker_sq K)).symm
        (Multiplicative.ofAdd (⟨eps, by rfl⟩ : RingHom.ker (fstRingHom K)))).1⁻¹)).snd =
      -1 := by
  rw [RingHom.unitsKerEquivOfSquareZero_symm_apply_inv_coe, toAdd_ofAdd]
  simp

private theorem unitsKerEquiv_coordinate_ne_one (K : Type u) [Field K] (r : K) (hr : r ≠ 0) :
    RingHom.unitsKerEquivOfSquareZero (fstRingHom K)
        (fstRingHom_ker_sq K)
        (Matrix.DualNumberKernels.unitsKerEquiv (Multiplicative.ofAdd r)) ≠ 1 := by
  intro h
  rw [Matrix.DualNumberKernels.unitsKerEquiv_eq_unitsKerEquivOfSquareZero_symm,
    MulEquiv.apply_symm_apply] at h
  have hs := congrArg
    (fun x : Multiplicative (RingHom.ker (fstRingHom K)) =>
      ((Multiplicative.toAdd x : RingHom.ker (fstRingHom K)) : DualNumber K).snd) h
  simp only [toAdd_ofAdd, toAdd_one, ZeroMemClass.coe_zero,
    TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero] at hs
  exact hr hs

end DualNumber

private theorem identity_unit_kernel_coordinate_eq_one (R : Type v) [Ring R]
    (u : (Units.map (RingHom.id R).toMonoidHom).ker) :
    RingHom.unitsKerEquivOfSquareZero (RingHom.id R)
        (by
          rw [(RingHom.injective_iff_ker_eq_bot (RingHom.id R)).mp Function.injective_id]
          exact Ideal.bot_pow (by decide)) u = 1 := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [RingHom.unitsKerEquivOfSquareZero_apply_coe]
  have hu := congrArg (fun x : Rˣ => (x : R)) u.property
  change (u.1 : R) = 1 at hu
  simpa only [toAdd_one, ZeroMemClass.coe_zero] using sub_eq_zero.mpr hu
