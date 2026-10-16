/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.SquareZeroUnits
public import GeneralLinearGroups.DualNumberKernels
public import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# Comparing dual-number and square-zero unit coordinates

The scalar-unit equivalence for dual numbers agrees with the general square-zero
kernel construction. The comparison uses the canonical inclusion of the second
coordinate, `TrivSqZeroExt.inr`, into the kernel of the first projection. Thus no
additional choice of additive coordinates or new kernel equivalence is needed.

The dual-number equivalence in `GeneralLinearGroups.DualNumberKernels` inherits
its algebraic laws from the general construction while retaining its explicit
lift and readback. Square-zero of the projection kernel is Mathlib's
`TrivSqZeroExt.kerIdeal_sq`, exposed as `DualNumber.fstRingHom_ker_sq`.
-/

@[expose] public section

universe u

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R]

/-- The dual-number scalar-unit construction agrees with the inverse of the
general square-zero unit-kernel equivalence on the canonical second-coordinate
inclusion. This identifies the two constructions pointwise on every coefficient. -/
theorem unitsKerEquiv_eq_unitsKerEquivOfSquareZero_symm (r : Multiplicative R) :
    unitsKerEquiv r =
      (RingHom.unitsKerEquivOfSquareZero (DualNumber.fstRingHom R)
        (DualNumber.fstRingHom_ker_sq R)).symm
          (Multiplicative.ofAdd
            (⟨TrivSqZeroExt.inr (Multiplicative.toAdd r), by rfl⟩ :
              RingHom.ker (DualNumber.fstRingHom R))) := by
  apply Subtype.ext
  apply Units.ext
  rw [RingHom.unitsKerEquivOfSquareZero_symm_apply_coe]
  change (⟨1, Multiplicative.toAdd r⟩ : DualNumber R) =
    1 + TrivSqZeroExt.inr (Multiplicative.toAdd r)
  apply TrivSqZeroExt.ext
  · change (1 : R) = 1 + 0
    exact (add_zero 1).symm
  · change Multiplicative.toAdd r = (0 : R) + Multiplicative.toAdd r
    exact (zero_add _).symm

end Matrix.DualNumberKernels
