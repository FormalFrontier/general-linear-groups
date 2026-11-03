/-
Copyright (c) 2026 Corbel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Corbel
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Principal units of a two-sided ideal

The principal units are exactly the kernel of the map on units induced by the
canonical quotient ring homomorphism. Ideal-preserving ring homomorphisms induce
maps of these subgroups by the stock domain and codomain restriction operations.

These definitions use Mathlib's existing two-sided ideals, ideal quotients,
units, subgroups, and bundled homomorphisms without replacing their structures.
The proofs below are new applications of those APIs; no stock implementation is
copied or replaced.
-/

@[expose] public section

universe u v w

namespace TwoSidedIdeal

variable {A : Type u} {B : Type v} {C : Type w}
variable [Ring A] [Ring B] [Ring C]

/-- The units congruent to one modulo a two-sided ideal, as the canonical kernel. -/
def principalUnits (I : TwoSidedIdeal A) : Subgroup Aˣ :=
  (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom).ker

/-- Membership in the principal-unit subgroup is the usual difference-from-one condition. -/
@[simp]
theorem mem_principalUnits (I : TwoSidedIdeal A) (v : Aˣ) :
    v ∈ I.principalUnits ↔ (v : A) - 1 ∈ I := by
  change Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom v = 1 ↔ _
  rw [← Units.val_inj]
  change Ideal.Quotient.mk I.asIdeal (v : A) = 1 ↔ _
  simpa only [mem_asIdeal] using
    (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := I.asIdeal) (v : A))

variable {I : TwoSidedIdeal A} {J : TwoSidedIdeal B} {L : TwoSidedIdeal C}

/-- Restrict the map on units along an ideal-preserving ring homomorphism. -/
def principalUnitsMap (f : A →+* B) (hIJ : ∀ a : A, a ∈ I → f a ∈ J) :
    I.principalUnits →* J.principalUnits :=
  ((Units.map f.toMonoidHom).domRestrict I.principalUnits).codRestrict
    J.principalUnits (by
      intro k
      apply (J.mem_principalUnits _).2
      change f ((k : Aˣ) : A) - 1 ∈ J
      have hk : ((k : Aˣ) : A) - 1 ∈ I :=
        (I.mem_principalUnits (k : Aˣ)).1 k.property
      simpa only [map_sub, map_one] using hIJ _ hk)

/-- Forgetting subgroup membership recovers the stock map on units. -/
@[simp]
theorem principalUnitsMap_apply_coe (f : A →+* B)
    (hIJ : ∀ a : A, a ∈ I → f a ∈ J) (k : I.principalUnits) :
    (principalUnitsMap f hIJ k : Bˣ) = Units.map f.toMonoidHom (k : Aˣ) :=
  rfl

/-- The underlying ring element is mapped by the original ring homomorphism. -/
@[simp]
theorem coe_principalUnitsMap_apply (f : A →+* B)
    (hIJ : ∀ a : A, a ∈ I → f a ∈ J) (k : I.principalUnits) :
    ((principalUnitsMap f hIJ k : Bˣ) : B) = f ((k : Aˣ) : A) :=
  rfl

/-- Principal units preserve the identity ring homomorphism. -/
@[simp]
theorem principalUnitsMap_id (I : TwoSidedIdeal A) :
    principalUnitsMap (I := I) (J := I) (RingHom.id A) (fun _ ha => ha) =
      MonoidHom.id I.principalUnits := by
  apply MonoidHom.ext
  intro k
  apply Subtype.ext
  apply Units.ext
  rfl

/-- Principal-unit maps compose with the original ring homomorphisms. -/
theorem principalUnitsMap_comp (f : A →+* B) (g : B →+* C)
    (hIJ : ∀ a : A, a ∈ I → f a ∈ J)
    (hJL : ∀ b : B, b ∈ J → g b ∈ L) :
    (principalUnitsMap g hJL).comp (principalUnitsMap f hIJ) =
      principalUnitsMap (g.comp f) (fun a ha => hJL (f a) (hIJ a ha)) := by
  apply MonoidHom.ext
  intro k
  apply Subtype.ext
  apply Units.ext
  rfl

end TwoSidedIdeal
