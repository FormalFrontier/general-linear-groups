/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.RelativeElementary
public import Mathlib.Data.Matrix.Block

/-!
# Finite stabilization of general linear and elementary groups

For finite index types `X` and `Y`, `stabilize` embeds `GL X R` into
`GL (X ⊕ Y) R` by adjoining an identity block. For a ring, this restricts to
elementary groups and preserves their relative normal closures and the existing
congruence subgroup. No surjectivity or ambient normality is assumed.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR uS

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR}

section Semiring

variable [Semiring R]

/-- Extend an invertible matrix by an identity block, with no positivity
assumption on the sizes of either block. -/
def stabilize : GL X R →* GL (X ⊕ Y) R where
  toFun g := {
    val := Matrix.fromBlocks (g : Matrix X X R) 0 0 1
    inv := Matrix.fromBlocks ((g⁻¹ : GL X R) : Matrix X X R) 0 0 1
    val_inv := by simp [Matrix.fromBlocks_multiply]
    inv_val := by simp [Matrix.fromBlocks_multiply] }
  map_one' := by
    apply Units.ext
    exact Matrix.fromBlocks_one
  map_mul' g h := by
    apply Units.ext
    simp [Matrix.fromBlocks_multiply]

@[simp]
theorem stabilize_apply_inl_inl (g : GL X R) (i j : X) :
    stabilize (Y := Y) g (Sum.inl i) (Sum.inl j) = g i j := rfl

@[simp]
theorem stabilize_apply_inl_inr (g : GL X R) (i : X) (j : Y) :
    stabilize (Y := Y) g (Sum.inl i) (Sum.inr j) = 0 := rfl

@[simp]
theorem stabilize_apply_inr_inl (g : GL X R) (i : Y) (j : X) :
    stabilize (Y := Y) g (Sum.inr i) (Sum.inl j) = 0 := rfl

@[simp]
theorem stabilize_apply_inr_inr (g : GL X R) (i j : Y) :
    stabilize (Y := Y) g (Sum.inr i) (Sum.inr j) = (1 : Matrix Y Y R) i j := rfl

/-- The original matrix can be recovered from the upper-left block. -/
theorem stabilize_injective :
    Function.Injective (stabilize (X := X) (Y := Y) (R := R)) := by
  intro g h eq
  apply Units.ext
  ext i j
  exact congrArg (fun k : GL (X ⊕ Y) R => k (Sum.inl i) (Sum.inl j)) eq

end Semiring

section Coefficients

variable {S : Type uS} [Semiring R] [Semiring S]

/-- Stabilization commutes with entrywise mapping of coefficients. -/
theorem mapRingHom_stabilize (f : R →+* S) (g : GL X R) :
    mapRingHom f (stabilize (Y := Y) g) =
      stabilize (Y := Y) (mapRingHom f g) := by
  apply Units.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [mapRingHom_apply, Matrix.one_apply]

end Coefficients

section Ring

variable [Ring R]

/-- Stabilization sends an elementary generator exactly to the corresponding
generator on the first summand. -/
@[simp]
theorem stabilize_elementaryUnit (i j : X) (hij : i ≠ j) (a : R) :
    stabilize (Y := Y) (elementaryUnit i j hij a) =
      elementaryUnit (Sum.inl i) (Sum.inl j)
        (fun eq => hij (Sum.inl_injective eq)) a := by
  apply Units.ext
  ext k l
  rcases k with k | k <;> rcases l with l | l <;>
    simp [Matrix.one_apply, Matrix.single_apply, Matrix.add_apply]

/-- The image of the absolute elementary group under stabilization remains elementary. -/
theorem stabilize_elementarySubgroup_le :
    (elementarySubgroup X R).map (stabilize (Y := Y)) ≤
      elementarySubgroup (X ⊕ Y) R := by
  apply Subgroup.map_le_iff_le_comap.mpr
  change Subgroup.closure _ ≤ _
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, j, hij, a, rfl⟩
  change stabilize (Y := Y) (elementaryUnit i j hij a) ∈
    elementarySubgroup (X ⊕ Y) R
  rw [stabilize_elementaryUnit]
  exact elementaryUnit_mem (Sum.inl i) (Sum.inl j)
    (fun eq => hij (Sum.inl_injective eq)) a

/-- Stabilization restricted to the existing elementary subgroups. -/
def stabilizeElementarySubgroup :
    elementarySubgroup X R →* elementarySubgroup (X ⊕ Y) R where
  toFun g := ⟨stabilize (Y := Y) g.1,
    stabilize_elementarySubgroup_le (Subgroup.mem_map_of_mem (stabilize (Y := Y)) g.2)⟩
  map_one' := Subtype.ext (map_one (stabilize (X := X) (Y := Y) (R := R)))
  map_mul' _ _ := Subtype.ext (map_mul (stabilize (X := X) (Y := Y) (R := R)) _ _)

@[simp]
theorem stabilizeElementarySubgroup_coe (g : elementarySubgroup X R) :
    ((stabilizeElementarySubgroup (Y := Y) g : elementarySubgroup (X ⊕ Y) R) :
      GL (X ⊕ Y) R) = stabilize (Y := Y) g := rfl

@[simp]
theorem stabilizeElementarySubgroup_elementaryUnit (i j : X) (hij : i ≠ j) (a : R) :
    stabilizeElementarySubgroup (Y := Y)
      (⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a⟩ :
        elementarySubgroup X R) =
      (⟨elementaryUnit (Sum.inl i) (Sum.inl j)
          (fun eq => hij (Sum.inl_injective eq)) a,
        elementaryUnit_mem (Sum.inl i) (Sum.inl j)
          (fun eq => hij (Sum.inl_injective eq)) a⟩ :
        elementarySubgroup (X ⊕ Y) R) := by
  apply Subtype.ext
  exact stabilize_elementaryUnit (Y := Y) i j hij a

/-- Relative elementary normal closures are preserved by stabilization as an
image inclusion, without asserting surjectivity of the restricted map. -/
theorem stabilize_relativeElementarySubgroup_le (I : TwoSidedIdeal R) :
    (relativeElementarySubgroup (ι := X) I).map
      (stabilizeElementarySubgroup (Y := Y)) ≤
        relativeElementarySubgroup (ι := X ⊕ Y) I := by
  change (Subgroup.normalClosure (relativeElementaryGenerators (ι := X) I)).map
      (stabilizeElementarySubgroup (Y := Y)) ≤
      Subgroup.normalClosure (relativeElementaryGenerators (ι := X ⊕ Y) I)
  apply (Subgroup.map_normalClosure_le _ _).trans
  apply Subgroup.normalClosure_mono
  rintro x ⟨y, ⟨i, j, hij, a, ha, rfl⟩, rfl⟩
  exact ⟨Sum.inl i, Sum.inl j, (fun eq => hij (Sum.inl_injective eq)), a,
    ha, stabilizeElementarySubgroup_elementaryUnit (Y := Y) i j hij a⟩

/-- Stabilization preserves the existing quotient-reduction congruence kernel. -/
theorem stabilize_congruenceSubgroup_le (I : TwoSidedIdeal R) :
    (congruenceSubgroup (n := X) I).map (stabilize (Y := Y)) ≤
      congruenceSubgroup (n := X ⊕ Y) I := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  change mapRingHom (Ideal.Quotient.mk I.asIdeal) x = 1 at hx
  change mapRingHom (Ideal.Quotient.mk I.asIdeal) (stabilize (Y := Y) x) = 1
  rw [mapRingHom_stabilize, hx, map_one]

end Ring

end Matrix.GeneralLinearGroup
