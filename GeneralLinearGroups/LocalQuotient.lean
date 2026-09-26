/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Quotients by two-sided ideals with unit complements

This file connects a source-independent condition on a proper two-sided ideal
to mathlib's left-ideal quotient API. If every element outside the ideal is a
unit, then its associated left ideal is maximal, even for a noncommutative
ring. The standard quotient construction therefore gives a division ring.
-/

set_option warningAsError true

@[expose] public section

namespace TwoSidedIdeal

universe u

variable {R : Type u} [Ring R]

/-- A proper two-sided ideal whose complement consists of units is maximal
after being viewed as a left ideal. -/
theorem isMaximal_asIdeal_of_isUnit_compl (I : TwoSidedIdeal R)
    (hI : I ≠ ⊤) (hunit : ∀ x : R, x ∉ I → IsUnit x) :
    I.asIdeal.IsMaximal := by
  refine Ideal.isMaximal_iff.mpr ⟨?_, ?_⟩
  · intro hOne
    apply hI
    exact (TwoSidedIdeal.one_mem_iff I).mp (TwoSidedIdeal.mem_asIdeal.mp hOne)
  · intro J x _ hxI hxJ
    have hxI' : x ∉ I := by
      simpa only [TwoSidedIdeal.mem_asIdeal] using hxI
    have hJ : J = ⊤ := J.eq_top_of_isUnit_mem hxJ (hunit x hxI')
    simp [hJ]

/-- The standard division-ring structure on the quotient by a proper
two-sided ideal whose complement consists of units.

This is an abbreviation rather than an instance so that applications can
control which noncomputable quotient structure they install. -/
protected noncomputable abbrev quotientDivisionRing (I : TwoSidedIdeal R)
    (hI : I ≠ ⊤) (hunit : ∀ x : R, x ∉ I → IsUnit x) :
    DivisionRing (R ⧸ I.asIdeal) := by
  letI : I.asIdeal.IsMaximal := I.isMaximal_asIdeal_of_isUnit_compl hI hunit
  exact Ideal.Quotient.divisionRing I.asIdeal

end TwoSidedIdeal
