/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.ElementaryDiagonal
public import GeneralLinearGroups.ElementaryPaths
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.Clopen

/-!
# Elementary neighborhoods in finite special linear groups

The elementary subgroup of the finite special linear group is the inverse image
of the existing general-linear elementary subgroup under `toGL`. When
`{r : R | IsUnit r}` is open, unit leading principal minors give an open
neighborhood of one inside it, making the subgroup open and closed.
Path-connected coefficients lift elementary paths to the special linear group
without this openness assumption. With both hypotheses, the elementary subgroup
is the path component of one.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.SpecialLinearGroup

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {n : ℕ}

/-- The existing general-linear elementary subgroup, pulled back along `toGL`. -/
def elementarySubgroup : Subgroup (SpecialLinearGroup (Fin n) R) :=
  (GeneralLinearGroup.elementarySubgroup (Fin n) R).comap
    (toGL : SpecialLinearGroup (Fin n) R →* GeneralLinearGroup (Fin n) R)

/-- The finite unit-leading-principal-minor locus is open when scalar units are open. -/
theorem isOpen_unitLeadingPrincipalMinors
    (hunits : IsOpen {r : R | IsUnit r}) :
    IsOpen {g : SpecialLinearGroup (Fin n) R |
      ∀ k : Fin (n + 1),
        IsUnit (Matrix.leadingPrincipalMinor (g : Matrix (Fin n) (Fin n) R)
          k.val (Nat.le_of_lt_succ k.isLt))} := by
  have hcont (k : Fin (n + 1)) : Continuous
      (fun g : SpecialLinearGroup (Fin n) R =>
        Matrix.leadingPrincipalMinor (g : Matrix (Fin n) (Fin n) R)
          k.val (Nat.le_of_lt_succ k.isLt)) := by
    exact (continuous_subtype_val.matrix_submatrix _ _).matrix_det
  simpa only [Set.ofPred_forall, Set.preimage_ofPred_eq] using
    (isOpen_iInter_of_finite (fun k : Fin (n + 1) => hunits.preimage (hcont k)))

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The identity has unit leading principal minors, including in dimensions zero and one. -/
theorem one_mem_unitLeadingPrincipalMinors :
    (1 : SpecialLinearGroup (Fin n) R) ∈
      {g : SpecialLinearGroup (Fin n) R |
        ∀ k : Fin (n + 1),
          IsUnit (Matrix.leadingPrincipalMinor (g : Matrix (Fin n) (Fin n) R)
            k.val (Nat.le_of_lt_succ k.isLt))} := by
  intro k
  have hinj : Function.Injective (Fin.castLE (Nat.le_of_lt_succ k.isLt) :
      Fin k.val → Fin n) := Fin.castLE_injective _
  simp [Matrix.leadingPrincipalMinor, Matrix.submatrix_one _ hinj]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Unit leading principal minors and determinant one force elementary membership. -/
theorem unitLeadingPrincipalMinors_subset_elementarySubgroup :
    {g : SpecialLinearGroup (Fin n) R |
      ∀ k : Fin (n + 1),
        IsUnit (Matrix.leadingPrincipalMinor (g : Matrix (Fin n) (Fin n) R)
          k.val (Nat.le_of_lt_succ k.isLt))} ⊆
      (elementarySubgroup (n := n) (R := R) : Set (SpecialLinearGroup (Fin n) R)) := by
  intro g hg
  change (toGL g : GeneralLinearGroup (Fin n) R) ∈
    GeneralLinearGroup.elementarySubgroup (Fin n) R
  apply GeneralLinearGroup.mem_elementarySubgroup_of_det_one_of_unit_leadingPrincipalMinors
    (toGL g)
  · exact g.property
  · intro k hk hkpos
    simpa only [coe_GL_coe_matrix] using hg ⟨k, Nat.lt_succ_of_le hk⟩

/-- Open scalar units make the elementary subgroup open in finite `SL`. -/
theorem isOpen_elementarySubgroup (hunits : IsOpen {r : R | IsUnit r}) :
    IsOpen (elementarySubgroup (n := n) (R := R) : Set (SpecialLinearGroup (Fin n) R)) := by
  apply (elementarySubgroup (n := n) (R := R)).isOpen_of_mem_nhds
  exact Filter.mem_of_superset
    ((isOpen_unitLeadingPrincipalMinors (n := n) hunits).mem_nhds
      (one_mem_unitLeadingPrincipalMinors (n := n) (R := R)))
    (unitLeadingPrincipalMinors_subset_elementarySubgroup (n := n) (R := R))

/-- With open scalar units, the elementary subgroup is closed; no separation axiom
is required. -/
theorem isClosed_elementarySubgroup (hunits : IsOpen {r : R | IsUnit r}) :
    IsClosed (elementarySubgroup (n := n) (R := R) : Set (SpecialLinearGroup (Fin n) R)) :=
  (elementarySubgroup (n := n) (R := R)).isClosed_of_isOpen
    (isOpen_elementarySubgroup (n := n) hunits)

/-- For path-connected coefficients, elementary subgroup paths lift to `SL`
without open scalar units. -/
theorem elementarySubgroup_joined_one [PathConnectedSpace R]
    (g : SpecialLinearGroup (Fin n) R)
    (hg : g ∈ elementarySubgroup (n := n) (R := R)) :
    Joined (1 : SpecialLinearGroup (Fin n) R) g := by
  let E := GeneralLinearGroup.elementarySubgroup (Fin n) R
  have hdet (x : E) : (((x : GeneralLinearGroup (Fin n) R) :
      Matrix (Fin n) (Fin n) R)).det = 1 := by
    exact congrArg Units.val (Matrix.det_elementarySubgroup_eq_one x)
  have hcont : Continuous (fun x : E =>
      (⟨((x : GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R),
        hdet x⟩ : SpecialLinearGroup (Fin n) R)) :=
    (Units.continuous_val.comp continuous_subtype_val).subtype_mk _
  let := GeneralLinearGroup.elementarySubgroup_pathConnectedSpace (ι := Fin n) (R := R)
  have hpath := (PathConnectedSpace.joined (1 : E) ⟨toGL g, hg⟩).map hcont
  exact hpath

/-- With open scalar units and path-connected coefficients, the elementary subgroup
is the path component of the identity in finite `SL`. -/
theorem elementarySubgroup_eq_pathComponentOne [PathConnectedSpace R]
    (hunits : IsOpen {r : R | IsUnit r}) :
    elementarySubgroup (n := n) (R := R) =
      Subgroup.pathComponentOne (SpecialLinearGroup (Fin n) R) := by
  apply le_antisymm
  · intro g hg
    exact elementarySubgroup_joined_one g hg
  · intro g hg
    have hclopen : IsClopen
        (elementarySubgroup (n := n) (R := R) : Set (SpecialLinearGroup (Fin n) R)) :=
      ⟨isClosed_elementarySubgroup (n := n) hunits,
        isOpen_elementarySubgroup (n := n) hunits⟩
    exact hclopen.connectedComponent_subset
      ((elementarySubgroup (n := n) (R := R)).one_mem)
      (pathComponent_subset_component (1 : SpecialLinearGroup (Fin n) R) hg)

end Matrix.SpecialLinearGroup
