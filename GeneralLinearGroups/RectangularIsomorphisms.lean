/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Isomorphisms of rectangular complements

For morphisms `a : X ⟶ Y` and `b : Y ⟶ X` in a preadditive category,
`𝟙 X - a ≫ b` is an isomorphism if and only if `𝟙 Y - b ≫ a` is an isomorphism.
When the latter is an isomorphism, the canonical inverse of the former is
`𝟙 X + a ≫ inv (𝟙 Y - b ≫ a) ≫ b`.
The objects are arbitrary and the object and morphism universes are independent.

## References

* Jacobson's lemma, the standard unit identity relating `1 - ab` and `1 - ba`;
  these statements give its two-object preadditive form.
* Mathlib's `CategoryTheory.Preadditive.Basic` and `CategoryTheory.Iso` provide
  the preadditive and canonical-inverse interfaces. Its
  `Matrix.invOf_add_mul_mul` is a related finite-matrix inverse identity.
* `GeneralLinearGroups.RectangularUnitSwitch` gives the related plus-sign
  finite-matrix unit switch over arbitrary rings.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [cat : Category.{v} C] [Preadditive C] {X Y : C}

private theorem id_sub_comp_inverse_identities (a : X ⟶ Y) (b : Y ⟶ X)
    [IsIso (𝟙 Y - b ≫ a)] :
    (𝟙 X - a ≫ b) ≫ (𝟙 X + a ≫ inv (𝟙 Y - b ≫ a) ≫ b) = 𝟙 X ∧
      (𝟙 X + a ≫ inv (𝟙 Y - b ≫ a) ≫ b) ≫ (𝟙 X - a ≫ b) = 𝟙 X := by
  have ha : (𝟙 X - a ≫ b) ≫ a = a ≫ (𝟙 Y - b ≫ a) := by
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
      Category.comp_id, Category.assoc]
  have hb : b ≫ (𝟙 X - a ≫ b) = (𝟙 Y - b ≫ a) ≫ b := by
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
      Category.comp_id, Category.assoc]
  constructor
  · calc
      (𝟙 X - a ≫ b) ≫ (𝟙 X + a ≫ inv (𝟙 Y - b ≫ a) ≫ b) =
          (𝟙 X - a ≫ b) + ((𝟙 X - a ≫ b) ≫ a) ≫ inv (𝟙 Y - b ≫ a) ≫ b := by
        simp only [Preadditive.comp_add, Category.comp_id, Category.assoc]
      _ = (𝟙 X - a ≫ b) + a ≫ ((𝟙 Y - b ≫ a) ≫ inv (𝟙 Y - b ≫ a)) ≫ b := by
        rw [ha]
        simp only [Category.assoc]
      _ = (𝟙 X - a ≫ b) + a ≫ b := by
        rw [IsIso.hom_inv_id, Category.id_comp]
      _ = 𝟙 X := sub_add_cancel _ _
  · calc
      (𝟙 X + a ≫ inv (𝟙 Y - b ≫ a) ≫ b) ≫ (𝟙 X - a ≫ b) =
          (𝟙 X - a ≫ b) + a ≫ inv (𝟙 Y - b ≫ a) ≫ (b ≫ (𝟙 X - a ≫ b)) := by
        simp only [Preadditive.add_comp, Category.id_comp, Category.assoc]
      _ = (𝟙 X - a ≫ b) + a ≫ (inv (𝟙 Y - b ≫ a) ≫ (𝟙 Y - b ≫ a)) ≫ b := by
        rw [hb]
        simp only [Category.assoc]
      _ = (𝟙 X - a ≫ b) + a ≫ b := by
        rw [IsIso.inv_hom_id, Category.id_comp]
      _ = 𝟙 X := sub_add_cancel _ _

/-- The two-object preadditive form of Jacobson's lemma: the complements of
`a ≫ b` and `b ≫ a` are isomorphisms simultaneously. -/
theorem isIso_id_sub_comp_iff (a : X ⟶ Y) (b : Y ⟶ X) :
    IsIso (𝟙 X - a ≫ b) ↔ IsIso (𝟙 Y - b ≫ a) := by
  constructor
  · intro h
    let : IsIso (𝟙 X - a ≫ b) := h
    exact ⟨⟨𝟙 Y + b ≫ inv (𝟙 X - a ≫ b) ≫ a,
      id_sub_comp_inverse_identities b a⟩⟩
  · intro h
    let : IsIso (𝟙 Y - b ≫ a) := h
    exact ⟨⟨𝟙 X + a ≫ inv (𝟙 Y - b ≫ a) ≫ b,
      id_sub_comp_inverse_identities a b⟩⟩

/-- The canonical inverse formula in the two-object preadditive form of
Jacobson's lemma, assuming only that `𝟙 Y - b ≫ a` is an isomorphism. -/
theorem inv_id_sub_comp (a : X ⟶ Y) (b : Y ⟶ X) [h : IsIso (𝟙 Y - b ≫ a)] :
    @inv.{v, u} C cat X X (𝟙 X - a ≫ b) ((isIso_id_sub_comp_iff a b).mpr h) =
      𝟙 X + a ≫ (@inv.{v, u} C cat Y Y (𝟙 Y - b ≫ a) h) ≫ b := by
  let : IsIso (𝟙 X - a ≫ b) := (isIso_id_sub_comp_iff a b).mpr h
  exact IsIso.inv_eq_of_hom_inv_id (id_sub_comp_inverse_identities a b).1

end CategoryTheory
