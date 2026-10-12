/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.Tactic.NormNum

/-!
# Scalar unit-reflection boundaries

Identity maps and maps from a subsingleton ring to a subsingleton semiring
satisfy the surjectivity and quasi-regular-kernel premises without a
nontriviality assumption. The unital map from the integers to `ZMod 1` is
zero-valued, but its kernel is not quasi-regular. Reduction modulo two shows
that the kernel premise is needed,
while the embedding of the integers in the rationals shows that surjectivity
is needed. All these input properties are proved independently of unit
reflection.

The final example recovers the quotient-unit equivalence for a globally
nilpotent ideal in a commutative ring. Ideal powers first give pointwise
nilpotence of the canonical quotient kernel, hence quasi-regularity; the
local-homomorphism constructor and its unit-reflection API then give the iff.

## References

The quotient-unit equivalence is the characteristic statement of Mathlib's
`IsNilpotent.isUnit_quotient_mk_iff`. The examples reuse Mathlib's canonical
integer casts, kernels, ideal powers, and units API.
-/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.LocalHomBoundary

universe u v

example (R : Type u) [Ring R] :
    Function.Surjective (RingHom.id R) ∧
      (TwoSidedIdeal.ker (RingHom.id R)).IsQuasiregular := by
  refine ⟨fun x => ⟨x, rfl⟩, ?_⟩
  have hker : TwoSidedIdeal.ker (RingHom.id R) = ⊥ :=
    (TwoSidedIdeal.ker_eq_bot (RingHom.id R)).mpr (fun _ _ h => h)
  rw [hker]
  exact TwoSidedIdeal.isNil_bot.isQuasiregular

example (R : Type u) (S : Type v) [Ring R] [Semiring S]
    [Subsingleton R] [Subsingleton S] (f : R →+* S) :
    Function.Surjective f ∧ (TwoSidedIdeal.ker f).IsNil ∧
      (TwoSidedIdeal.ker f).IsQuasiregular := by
  have hnil : (TwoSidedIdeal.ker f).IsNil := by
    intro x _
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    exact IsNilpotent.zero
  exact ⟨fun y => ⟨0, Subsingleton.elim _ y⟩, hnil, hnil.isQuasiregular⟩

example :
    Function.Surjective (Int.castRingHom (ZMod 1)) ∧
      (∀ z : ℤ, Int.castRingHom (ZMod 1) z = 0) ∧
      TwoSidedIdeal.ker (Int.castRingHom (ZMod 1)) = ⊤ ∧
      ¬ (TwoSidedIdeal.ker (Int.castRingHom (ZMod 1))).IsQuasiregular := by
  refine ⟨ZMod.intCast_surjective, fun _ => Subsingleton.elim _ _, ?_, ?_⟩
  · ext z
    rw [TwoSidedIdeal.mem_ker (Int.castRingHom (ZMod 1))]
    exact iff_of_true (Subsingleton.elim _ _) (TwoSidedIdeal.mem_top ℤ)
  · intro hquasi
    have hmem : (-1 : ℤ) ∈ TwoSidedIdeal.ker (Int.castRingHom (ZMod 1)) :=
      (TwoSidedIdeal.mem_ker (Int.castRingHom (ZMod 1))).mpr (Subsingleton.elim _ _)
    have hunit :=
      (TwoSidedIdeal.isQuasiregular_iff_forall_isUnit_one_add _).mp hquasi (-1) hmem
    simp at hunit

example :
    Function.Surjective (Int.castRingHom (ZMod 2)) ∧
      IsUnit (Int.castRingHom (ZMod 2) 3) ∧
      ¬ IsUnit (3 : ℤ) ∧
      ¬ (TwoSidedIdeal.ker (Int.castRingHom (ZMod 2))).IsQuasiregular := by
  have hthree : ¬ IsUnit (3 : ℤ) := by norm_num [Int.isUnit_iff]
  refine ⟨ZMod.intCast_surjective, ?_, hthree, ?_⟩
  · have himage : Int.castRingHom (ZMod 2) (3 : ℤ) = 1 := by decide
    rw [himage]
    exact isUnit_one
  · intro hquasi
    have hmem : (2 : ℤ) ∈ TwoSidedIdeal.ker (Int.castRingHom (ZMod 2)) :=
      (TwoSidedIdeal.mem_ker (Int.castRingHom (ZMod 2))).mpr
        (by decide)
    have hunit :=
      (TwoSidedIdeal.isQuasiregular_iff_forall_isUnit_one_add _).mp hquasi 2 hmem
    apply hthree
    simpa only [show (1 + (2 : ℤ)) = 3 by norm_num] using hunit

example :
    Function.Injective (Int.castRingHom ℚ) ∧
      TwoSidedIdeal.ker (Int.castRingHom ℚ) = ⊥ ∧
      (TwoSidedIdeal.ker (Int.castRingHom ℚ)).IsQuasiregular ∧
      IsUnit (Int.castRingHom ℚ 2) ∧ ¬ IsUnit (2 : ℤ) ∧
      ¬ Function.Surjective (Int.castRingHom ℚ) := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hker : TwoSidedIdeal.ker (Int.castRingHom ℚ) = ⊥ :=
    (TwoSidedIdeal.ker_eq_bot (Int.castRingHom ℚ)).mpr hinj
  refine ⟨hinj, hker, ?_, ?_, ?_, ?_⟩
  · rw [hker]
    exact TwoSidedIdeal.isNil_bot.isQuasiregular
  · change IsUnit (2 : ℚ)
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  · norm_num [Int.isUnit_iff]
  · have : Fact (1 < 2) := ⟨by decide⟩
    intro hsurj
    obtain ⟨z, hz⟩ := hsurj (1 / 2 : ℚ)
    change (z : ℚ) = 1 / 2 at hz
    have hrat : ((2 * z : ℤ) : ℚ) = (1 : ℚ) := by
      rw [Int.cast_mul]
      change (2 : ℚ) * (z : ℚ) = 1
      rw [hz]
      norm_num
    have hint : (2 : ℤ) * z = 1 := Int.cast_injective hrat
    have hzmod : ((2 * z : ℤ) : ZMod 2) = (1 : ZMod 2) :=
      congrArg (fun a : ℤ => (a : ZMod 2)) hint
    have hzero : (0 : ZMod 2) = 1 := by
      simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_one,
        show (2 : ZMod 2) = 0 by decide, zero_mul] using hzmod
    exact zero_ne_one hzero

example {R : Type u} [CommRing R] (I : Ideal R) (hI : IsNilpotent I) (x : R) :
    IsUnit (Ideal.Quotient.mk I x) ↔ IsUnit x := by
  have hkerAsIdeal :
      (TwoSidedIdeal.ker (Ideal.Quotient.mk I)).asIdeal =
        RingHom.ker (Ideal.Quotient.mk I) := by
    rw [Ideal.mk_ker]
    ext a
    rw [TwoSidedIdeal.mem_asIdeal,
      TwoSidedIdeal.mem_ker (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
  have hkerNil : (TwoSidedIdeal.ker (Ideal.Quotient.mk I)).IsNil := by
    obtain ⟨n, hn⟩ := hI
    intro a ha
    have haI : a ∈ I := by
      have ha' := TwoSidedIdeal.mem_asIdeal.mpr ha
      rwa [hkerAsIdeal, Ideal.mk_ker] at ha'
    refine ⟨n, ?_⟩
    have hpow : I ^ n = (⊥ : Ideal R) := hn
    have hapow : a ^ n ∈ I ^ n := Ideal.pow_mem_pow haI n
    simpa only [hpow, Ideal.mem_bot] using hapow
  let _ : IsLocalHom (Ideal.Quotient.mk I) :=
    RingHom.isLocalHom_of_surjective_of_isQuasiregular_ker
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hkerNil.isQuasiregular
  exact isUnit_map_iff (Ideal.Quotient.mk I) x

end GeneralLinearGroupsTests.LocalHomBoundary
