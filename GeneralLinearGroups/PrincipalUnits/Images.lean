/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.PrincipalUnits

/-!
# Images of principal-unit subgroups

Let `f : R →+* S` be a homomorphism between arbitrary rings and let `I` be
a left ideal of `R` contained in its Jacobson radical. The image under
`Units.map f.toMonoidHom` of the units congruent to `1` modulo `I` consists
exactly of those `u : Sˣ` for which `(u : S) - 1` is the image of an element
of `I`. The homomorphism need not be injective, and neither ring needs to be
commutative.

The condition concerns the set image of the elements of `I`, not the ideal
extension `Ideal.map f I`. The Jacobson hypothesis lifts `1 + a` to a unit
of `R`; it cannot be replaced by invertibility of its image in `S`.
The subgroup carrier is the stabilizer of `[1]` in the quotient left module
`R ⧸ I` from `GeneralLinearGroups.PrincipalUnits`, and its image uses Mathlib's
`Subgroup.map`. No new unit subgroup or map on units is introduced.

## References

Mathlib supplies `Units.map`, `Subgroup.map` and
`Ideal.isUnit_of_sub_one_mem_jacobson_bot`. The congruence membership and
Jacobson lifts are provided by `GeneralLinearGroups.PrincipalUnits`.
-/

@[expose] public section

universe u v

namespace Ideal

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- A unit belongs to the image of the principal-unit stabilizer precisely
when its value minus `1` is the image of an element of the ideal. The
Jacobson hypothesis ensures that the preimage `1 + a` is a unit in `R`.
No injectivity of the ring homomorphism is required. -/
theorem mem_map_stabilizer_quotient_one_iff (f : R →+* S) (I : Ideal R)
    (hJac : I ≤ Ideal.jacobson ⊥) (u : Sˣ) :
    u ∈ (MulAction.stabilizer Rˣ
      (Submodule.Quotient.mk (1 : R) : R ⧸ I)).map (Units.map f.toMonoidHom) ↔
      ∃ a : R, a ∈ I ∧ f a = (u : S) - 1 := by
  constructor
  · intro hu
    obtain ⟨v, hv, hfv⟩ := Subgroup.mem_map.mp hu
    refine ⟨(v : R) - 1, (I.mem_stabilizer_quotient_one v).mp hv, ?_⟩
    have hval : f (v : R) = (u : S) := congrArg Units.val hfv
    rw [map_sub, map_one, hval]
  · rintro ⟨a, ha, hfa⟩
    have hI : I ≤ Ring.jacobson R := by
      simpa only [Ideal.jacobson_bot] using hJac
    refine Subgroup.mem_map.mpr
      ⟨(I.principalUnitsMk hI ⟨a, ha⟩).1, (I.principalUnitsMk hI ⟨a, ha⟩).property, ?_⟩
    apply Units.ext
    change f ((I.principalUnitsMk hI ⟨a, ha⟩).1 : R) = (u : S)
    rw [I.principalUnitsMk_coe hI ⟨a, ha⟩, map_add, map_one, hfa, add_sub_cancel]

end Ideal
