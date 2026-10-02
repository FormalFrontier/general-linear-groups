/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.Elementary
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Instances.Matrix

/-!
# Paths of elementary matrices over topological rings

An off-diagonal elementary unit depends continuously on its coefficient, including
its inverse matrix. Paths of coefficients lift both to the ambient general linear
group and to its algebraic elementary subgroup. When the ring is path
connected, closure under multiplication and inverse makes this subgroup path
connected, without assuming that the ambient general linear group is so.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  {R : Type v} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]

/-- An elementary unit, including its inverse, varies continuously with its coefficient. -/
theorem continuous_elementaryUnit (i j : ι) (hij : i ≠ j) :
    Continuous (elementaryUnit (R := R) i j hij) := by
  have hsingle : Continuous (fun c : R => (Matrix.single i j c : Matrix ι ι R)) := by
    refine continuous_matrix fun row col => ?_
    by_cases h : i = row ∧ j = col
    · have hfun : (fun c : R => Matrix.single i j c row col) = id := by
        funext c
        simp [h]
      rw [hfun]
      exact continuous_id
    · have hfun : (fun c : R => Matrix.single i j c row col) =
          (fun _ : R => (0 : R)) := by
        funext c
        simp [h]
      rw [hfun]
      exact continuous_const
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun c : R => (1 + Matrix.single i j c : Matrix ι ι R))
    exact (continuous_const : Continuous (fun _ : R => (1 : Matrix ι ι R))).add hsingle
  · change Continuous (fun c : R => (1 + Matrix.single i j (-c) : Matrix ι ι R))
    exact (continuous_const : Continuous (fun _ : R => (1 : Matrix ι ι R))).add
      (hsingle.comp continuous_neg)

/-- The elementary generator is continuous as a map into the elementary subgroup. -/
theorem continuous_elementaryUnit_subtype (i j : ι) (hij : i ≠ j) :
    Continuous (fun c : R =>
      (⟨elementaryUnit i j hij c, elementaryUnit_mem i j hij c⟩ :
        elementarySubgroup ι R)) :=
  (continuous_elementaryUnit i j hij).subtype_mk _

/-- A coefficient path from zero to `c` gives a path from one to the elementary unit. -/
def elementaryUnitPath (i j : ι) (hij : i ≠ j) {c : R}
    (γ : Path (0 : R) c) : Path (1 : GL ι R) (elementaryUnit i j hij c) where
  toFun t := elementaryUnit i j hij (γ t)
  continuous_toFun := (continuous_elementaryUnit i j hij).comp γ.continuous
  source' := by simp
  target' := by simp

/-- The same coefficient path takes values in the algebraic elementary subgroup. -/
def elementaryUnitPathSubtype (i j : ι) (hij : i ≠ j) {c : R}
    (γ : Path (0 : R) c) :
    Path (1 : elementarySubgroup ι R)
      (⟨elementaryUnit i j hij c, elementaryUnit_mem i j hij c⟩ :
        elementarySubgroup ι R) where
  toFun t := ⟨elementaryUnit i j hij (γ t), elementaryUnit_mem i j hij (γ t)⟩
  continuous_toFun := (continuous_elementaryUnit_subtype i j hij).comp γ.continuous
  source' := by ext; simp
  target' := by ext; simp

/-- The algebraic elementary subgroup is path connected when the coefficient ring is. -/
theorem elementarySubgroup_pathConnectedSpace [PathConnectedSpace R] :
    PathConnectedSpace (elementarySubgroup ι R) := by
  let E := elementarySubgroup ι R
  have hgen : ∀ (g : GL ι R) (hg : g ∈ E), Joined (1 : E) ⟨g, hg⟩ := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, j, hij, c, rfl⟩ := hg
      exact ⟨elementaryUnitPathSubtype i j hij
        (PathConnectedSpace.joined (0 : R) c).somePath⟩
    | one => exact Joined.refl 1
    | mul x y hx hy hx' hy' =>
      change Joined (1 : E) (⟨x, hx⟩ * ⟨y, hy⟩)
      simpa only [one_mul] using hx'.mul hy'
    | inv x hx hx' =>
      change Joined (1 : E) (⟨x, hx⟩⁻¹)
      simpa only [inv_one] using hx'.inv
  refine ⟨⟨1⟩, ?_⟩
  intro x y
  simpa only [mul_one, one_mul] using (hgen x x.property).symm.mul (hgen y y.property)

/-- Every elementary-subgroup element is joined to one in the ambient general linear group. -/
theorem elementarySubgroup_joined_one [PathConnectedSpace R] (g : GL ι R)
    (hg : g ∈ elementarySubgroup ι R) : Joined (1 : GL ι R) g := by
  let := elementarySubgroup_pathConnectedSpace (ι := ι) (R := R)
  exact (PathConnectedSpace.joined (1 : elementarySubgroup ι R) ⟨g, hg⟩).map
    continuous_subtype_val

/-- Any two elementary-subgroup elements are joined in the ambient general linear group. -/
theorem elementarySubgroup_joined [PathConnectedSpace R] (g h : GL ι R)
    (hg : g ∈ elementarySubgroup ι R) (hh : h ∈ elementarySubgroup ι R) :
    Joined g h := by
  let := elementarySubgroup_pathConnectedSpace (ι := ι) (R := R)
  exact (PathConnectedSpace.joined (⟨g, hg⟩ : elementarySubgroup ι R)
    ⟨h, hh⟩).map continuous_subtype_val

end Matrix.GeneralLinearGroup
