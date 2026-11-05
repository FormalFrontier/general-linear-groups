/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Topology.Algebra.Module.Basic

public import GeneralLinearGroups.SquareZeroUnits
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Square-zero principal-unit kernels

For a ring homomorphism with square-zero kernel, the principal-unit kernel is
multiplicatively homeomorphic to the additive kernel. Only the topology of the
additive group of the domain is needed: continuity in the reverse direction uses
the two coordinates of the units topology, given by `1 + x` and `1 - x`.
-/

@[expose] public section

universe u v

namespace RingHom

variable {A : Type u} {B : Type v} [Ring A] [Semiring B]
  [TopologicalSpace A] [IsTopologicalAddGroup A]

/-- The units kernel of a homomorphism with square-zero kernel is
multiplicatively homeomorphic to its additive kernel. -/
def unitsKerHomeomorphOfSquareZero (f : A →+* B) (h : (RingHom.ker f) ^ 2 = ⊥) :
    (Units.map f.toMonoidHom).ker ≃ₜ* Multiplicative (RingHom.ker f) where
  toMulEquiv := f.unitsKerEquivOfSquareZero h
  continuous_toFun := by
    change Continuous (fun u => (f.unitsKerEquivOfSquareZero h u).toAdd)
    apply continuous_induced_rng.2
    have hv : Continuous (fun u : (Units.map f.toMonoidHom).ker =>
        ((u : Aˣ) : A)) :=
      Units.continuous_val.comp continuous_subtype_val
    simpa only [Function.comp_def, Pi.sub_def, unitsKerEquivOfSquareZero_apply_coe] using
      hv.sub continuous_const
  continuous_invFun := by
    change Continuous (fun x => (f.unitsKerEquivOfSquareZero h).symm x)
    apply continuous_induced_rng.2
    apply Units.continuous_iff.2
    have hx : Continuous (fun x : Multiplicative (RingHom.ker f) => (x.toAdd : A)) :=
      continuous_subtype_val
    constructor
    · simpa only [Function.comp_def, Pi.add_def, unitsKerEquivOfSquareZero_symm_apply_coe] using
        continuous_const.add hx
    · simpa only [Function.comp_def, Pi.sub_def, unitsKerEquivOfSquareZero_symm_apply_inv_coe] using
        (continuous_const :
          Continuous (fun _ : Multiplicative (RingHom.ker f) => (1 : A))).sub hx

variable (f : A →+* B) (h : (RingHom.ker f) ^ 2 = ⊥)

/-- The underlying multiplicative equivalence is the square-zero kernel equivalence. -/
theorem unitsKerHomeomorphOfSquareZero_toMulEquiv :
    (f.unitsKerHomeomorphOfSquareZero h).toMulEquiv =
      f.unitsKerEquivOfSquareZero h := rfl

/-- The inverse homeomorphism has the inverse square-zero kernel equivalence. -/
@[simp] theorem unitsKerHomeomorphOfSquareZero_symm_toMulEquiv :
    (f.unitsKerHomeomorphOfSquareZero h).symm.toMulEquiv =
      (f.unitsKerEquivOfSquareZero h).symm := rfl

/-- The additive coordinate of a principal unit is its value minus one. -/
theorem unitsKerHomeomorphOfSquareZero_apply_coe
    (u : (Units.map f.toMonoidHom).ker) :
    ((f.unitsKerHomeomorphOfSquareZero h u).toAdd : A) = ((u : Aˣ) : A) - 1 := by
  exact f.unitsKerEquivOfSquareZero_apply_coe h u

/-- The unit associated to an additive kernel element has value `1 + x`. -/
theorem unitsKerHomeomorphOfSquareZero_symm_apply_coe
    (x : Multiplicative (RingHom.ker f)) :
    (((f.unitsKerHomeomorphOfSquareZero h).symm x : Aˣ) : A) = 1 + (x.toAdd : A) := by
  exact f.unitsKerEquivOfSquareZero_symm_apply_coe h x

/-- The inverse of the unit associated to an additive kernel element has value `1 - x`. -/
theorem unitsKerHomeomorphOfSquareZero_symm_apply_inv_coe
    (x : Multiplicative (RingHom.ker f)) :
    ((((f.unitsKerHomeomorphOfSquareZero h).symm x : Aˣ)⁻¹ : Aˣ) : A) =
      1 - (x.toAdd : A) := by
  exact f.unitsKerEquivOfSquareZero_symm_apply_inv_coe h x

/-- The square-zero units kernel is a topological group for its original subgroup topology,
even without continuity of multiplication in the ambient ring. -/
theorem isTopologicalGroup_unitsKer_of_squareZero (h : (RingHom.ker f) ^ 2 = ⊥) :
    IsTopologicalGroup ((Units.map f.toMonoidHom).ker) := by
  let e := f.unitsKerHomeomorphOfSquareZero h
  have hs : Continuous (fun x : Multiplicative (RingHom.ker f) => e.symm x) :=
    e.symm.continuous
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · have hm : Continuous (fun p : (Units.map f.toMonoidHom).ker ×
        (Units.map f.toMonoidHom).ker => e p.1 * e p.2) :=
      (e.continuous.comp continuous_fst).mul (e.continuous.comp continuous_snd)
    simpa only [Function.comp_def, map_mul, e.symm_apply_apply] using hs.comp hm
  · have hi : Continuous (fun u : (Units.map f.toMonoidHom).ker => (e u)⁻¹) :=
      e.continuous.inv
    simpa only [Function.comp_def, map_inv, e.symm_apply_apply] using hs.comp hi

end RingHom
