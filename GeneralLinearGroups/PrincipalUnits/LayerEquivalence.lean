/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.PrincipalUnits.Naturality
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Jacobson equivalences for positive principal-unit layers

If a left ideal `I` of a ring `R` lies in `Ring.jacobson R`, the symbol on
each positive principal-unit layer is an integer-linear equivalence with the
successive ideal layer. The forward map is the symbol from
`GeneralLinearGroups.PrincipalUnits.Commutator`, on the same kernel quotient
and with the same operations. The inverse is characterized by the class of
the original-ring Jacobson lift with value `1 + x`.

The theorem statements describe this inverse on representatives and its
compatibility with ring maps. Inverse compatibility assumes the Jacobson
condition on both source and target ideals. No commutativity, two-sidedness,
nontriviality or finiteness condition is imposed, and degrees are positive.
The surjectivity statements also cover left ideals whose elements are all
nilpotent, and left ideals with a uniform vanishing power, including exponents
zero and one. For arbitrary left ideals the symbol remains injective but need
not be surjective.

## References

The noncommutative Jacobson lifts and coordinate quotient equivalence are
from `GeneralLinearGroups.PrincipalUnits`. Mathlib supplies the linear
equivalence associated to a bijective linear map and its inverse laws.
-/

@[expose] public section

universe u v

namespace Ideal

variable {R : Type u} [Ring R]

private theorem principalUnitsPowLayerSymbol_surjective (I : Ideal R)
    (hJac : I ≤ Ring.jacobson R) (n : ℕ+) :
    Function.Surjective (I.principalUnitsPowLayerSymbol n) := by
  have hpow : I ^ (n : ℕ) ≤ Ring.jacobson R :=
    (Ideal.pow_le_self (Nat.ne_of_gt n.pos)).trans hJac
  have hsq : (I ^ (n : ℕ)) ^ 2 ≤ I ^ ((n : ℕ) + 1) := by
    rw [Submodule.pow_succ, Submodule.pow_one, ← Submodule.pow_add _ n.ne_zero]
    exact Ideal.pow_le_pow_right (by have := n.pos; omega)
  intro y
  obtain ⟨u, hu⟩ := (I ^ (n : ℕ)).principalUnitsToQuotient_surjective
    (I ^ ((n : ℕ) + 1)) hsq hpow (Multiplicative.ofAdd y)
  refine ⟨Additive.ofMul (QuotientGroup.mk u), ?_⟩
  exact congrArg Multiplicative.toAdd hu

/-- Under the Jacobson condition, the symbol identifies the additive
principal-unit layer with the successive ideal layer, linearly over `ℤ`.
The forward map is `Ideal.principalUnitsPowLayerSymbol`. -/
noncomputable def principalUnitsPowLayerEquiv (I : Ideal R)
    (hJac : I ≤ Ring.jacobson R) (n : ℕ+) :
    I.principalUnitsPowAdditiveLayer n ≃ₗ[ℤ] I.powLayer n :=
  LinearEquiv.ofBijective (I.principalUnitsPowLayerSymbol n)
    ⟨I.principalUnitsPowLayerSymbol_injective n,
      by exact principalUnitsPowLayerSymbol_surjective I hJac n⟩

/-- The linear map underlying the Jacobson equivalence is the symbol. -/
@[simp]
theorem principalUnitsPowLayerEquiv_toLinearMap (I : Ideal R)
    (hJac : I ≤ Ring.jacobson R) (n : ℕ+) :
    (I.principalUnitsPowLayerEquiv hJac n).toLinearMap =
      I.principalUnitsPowLayerSymbol n :=
  rfl

/-- The Jacobson equivalence evaluates by taking the symbol. -/
@[simp]
theorem principalUnitsPowLayerEquiv_apply (I : Ideal R)
    (hJac : I ≤ Ring.jacobson R) (n : ℕ+) (x : I.principalUnitsPowAdditiveLayer n) :
    I.principalUnitsPowLayerEquiv hJac n x = I.principalUnitsPowLayerSymbol n x :=
  rfl

/-- The inverse equivalence sends a coordinate class to the class of the
original-ring Jacobson lift with value `1 + x`. -/
@[simp]
theorem principalUnitsPowLayerEquiv_symm_mk (I : Ideal R)
    (hJac : I ≤ Ring.jacobson R) (n : ℕ+) (x : (I ^ (n : ℕ) : Ideal R)) :
    (I.principalUnitsPowLayerEquiv hJac n).symm (Submodule.Quotient.mk x) =
      Additive.ofMul (QuotientGroup.mk
        ((I ^ (n : ℕ)).principalUnitsMk
          ((Ideal.pow_le_self (Nat.ne_of_gt n.pos)).trans hJac) x)) := by
  apply (I.principalUnitsPowLayerEquiv hJac n).injective
  rw [LinearEquiv.apply_symm_apply, principalUnitsPowLayerEquiv_apply,
    principalUnitsPowLayerSymbol_mk]
  simp only [principalUnitsMk_coe, add_sub_cancel_left]

/-- The symbol on a positive principal-unit layer is surjective when every
element of the left ideal is nilpotent. No uniform exponent or two-sidedness
condition is needed. -/
theorem principalUnitsPowLayerSymbol_surjective_of_forall_isNilpotent (I : Ideal R)
    (hNil : ∀ x : R, x ∈ I → IsNilpotent x) (n : ℕ+) :
    Function.Surjective (I.principalUnitsPowLayerSymbol n) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (Submodule.comap (I ^ (n : ℕ)).subtype (I ^ ((n : ℕ) + 1))) y
  have hxNil : IsNilpotent (x : R) :=
    hNil x (Ideal.pow_le_self (Nat.ne_of_gt n.pos) x.property)
  obtain ⟨u, hu⟩ := hxNil.isUnit_one_add
  have huMem : u ∈ MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (n : ℕ) : Ideal R)) := by
    rw [MulAction.mem_stabilizer_iff, units_smul_quotient_one_eq_one, hu]
    simpa only [add_sub_cancel_left] using x.property
  refine ⟨Additive.ofMul (QuotientGroup.mk ⟨u, huMem⟩), ?_⟩
  rw [principalUnitsPowLayerSymbol_mk]
  simp only [hu, add_sub_cancel_left]

/-- A vanishing power of a left ideal makes the symbol on every positive
principal-unit layer surjective. The exponent may be zero or one; no
nontriviality or two-sidedness condition is needed. -/
theorem principalUnitsPowLayerSymbol_surjective_of_pow_eq_bot (I : Ideal R)
    (N : ℕ) (hNil : I ^ N = ⊥) (n : ℕ+) :
    Function.Surjective (I.principalUnitsPowLayerSymbol n) := by
  refine I.principalUnitsPowLayerSymbol_surjective_of_forall_isNilpotent ?_ n
  intro x hx
  refine ⟨N, ?_⟩
  simpa only [hNil, Ideal.mem_bot] using (Ideal.pow_mem_pow hx N)

section Naturality

variable {S : Type v} [Ring S]
variable {F : Type*} [FunLike F R S] [RingHomClass F R S]

/-- The inverse Jacobson equivalences commute with the forward layer maps.
Both ideals satisfy the Jacobson condition; the ring map only needs to carry
`I` into `J`. -/
theorem principalUnitsPowLayerEquiv_symm_map (I : Ideal R) (J : Ideal S) (f : F)
    (h : I ≤ J.comap f) (hI : I ≤ Ring.jacobson R) (hJ : J ≤ Ring.jacobson S)
    (n : ℕ+) (x : I.powLayer n) :
    I.principalUnitsPowLayerMap J f h n ((I.principalUnitsPowLayerEquiv hI n).symm x) =
      (J.principalUnitsPowLayerEquiv hJ n).symm (I.powLayerMap J f h n x) := by
  apply (J.principalUnitsPowLayerEquiv hJ n).injective
  rw [LinearEquiv.apply_symm_apply, principalUnitsPowLayerEquiv_apply,
    principalUnitsPowLayerSymbol_map, ← principalUnitsPowLayerEquiv_apply I hI n,
    LinearEquiv.apply_symm_apply]

end Naturality

end Ideal
