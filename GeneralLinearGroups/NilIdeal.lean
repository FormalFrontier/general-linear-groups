/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.QuasiregularIdeal
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Nil two-sided ideals

This file defines a nil two-sided ideal by the standard pointwise condition:
every element is nilpotent, with no uniform exponent required for the ideal.
It relates this condition to quasi-regularity and the Jacobson radical over an
arbitrary, possibly noncommutative ring.
-/

set_option warningAsError true

@[expose] public section

namespace TwoSidedIdeal

universe u

variable {R : Type u} [Ring R]

/-- A two-sided ideal is nil if each of its elements is nilpotent. The
nilpotence exponent may depend on the element. -/
def IsNil (I : TwoSidedIdeal R) : Prop :=
  ∀ x : R, x ∈ I → IsNilpotent x

/-- The pointwise nil property passes to smaller two-sided ideals. -/
theorem IsNil.mono {I J : TwoSidedIdeal R} (hI : I.IsNil) (hJI : J ≤ I) :
    J.IsNil := by
  intro x hxJ
  exact hI x (hJI hxJ)

/-- The zero two-sided ideal is nil. -/
@[simp] theorem isNil_bot : (⊥ : TwoSidedIdeal R).IsNil := by
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  subst x
  exact IsNilpotent.zero

/-- Every nil two-sided ideal is quasi-regular. -/
theorem IsNil.isQuasiregular {I : TwoSidedIdeal R} (hI : I.IsNil) :
    I.IsQuasiregular := by
  rw [I.isQuasiregular_iff_forall_isUnit_one_add]
  intro x hxI
  exact (hI x hxI).isUnit_one_add

/-- Every nil two-sided ideal is contained in the Jacobson radical. -/
theorem IsNil.le_ringJacobson {I : TwoSidedIdeal R} (hI : I.IsNil) :
    I ≤ (Ring.jacobson R).toTwoSided :=
  hI.isQuasiregular.le_ringJacobson

end TwoSidedIdeal
