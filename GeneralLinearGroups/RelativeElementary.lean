/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.Elementary
public import GeneralLinearGroups.CongruenceSubgroup

/-!
# Relative elementary subgroups

For a two-sided ideal `I` of an arbitrary ring, the relative elementary subgroup
is the normal closure **inside the elementary subgroup** of the elementary
units whose coefficients belong to `I`. Coefficient homomorphisms preserve
elementary subgroups and transport relative subgroups for compatible ideals.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uR uS uT

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
  {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- Entrywise coefficient mapping sends an elementary unit to an elementary unit. -/
@[simp]
theorem mapRingHom_elementaryUnit (f : R →+* S) (i j : ι) (hij : i ≠ j) (a : R) :
    mapRingHom f (elementaryUnit i j hij a) = elementaryUnit i j hij (f a) := by
  apply Units.ext
  change f.mapMatrix (1 + Matrix.single i j a : Matrix ι ι R) =
    1 + Matrix.single i j (f a)
  rw [map_add, map_one]
  exact congrArg (fun m : Matrix ι ι S => 1 + m) (Matrix.map_single i j a f)

/-- Entrywise coefficient mapping preserves the absolute elementary subgroup. -/
theorem mapRingHom_elementarySubgroup_le (f : R →+* S) :
    (elementarySubgroup ι R).map (mapRingHom f) ≤ elementarySubgroup ι S := by
  apply Subgroup.map_le_iff_le_comap.mpr
  change Subgroup.closure _ ≤ _
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, j, hij, a, rfl⟩
  change mapRingHom f (elementaryUnit i j hij a) ∈ elementarySubgroup ι S
  rw [mapRingHom_elementaryUnit]
  exact elementaryUnit_mem i j hij (f a)

/-- The native restricted map on elementary subgroups. -/
def mapElementarySubgroup (f : R →+* S) :
    elementarySubgroup ι R →* elementarySubgroup ι S where
  toFun g := ⟨mapRingHom f g.1,
    mapRingHom_elementarySubgroup_le f (Subgroup.mem_map_of_mem (mapRingHom f) g.2)⟩
  map_one' := Subtype.ext (map_one (mapRingHom f))
  map_mul' _ _ := Subtype.ext (map_mul (mapRingHom f) _ _)

@[simp]
theorem mapElementarySubgroup_coe (f : R →+* S) (g : elementarySubgroup ι R) :
    ((mapElementarySubgroup f g : elementarySubgroup ι S) : GL ι S) =
      mapRingHom f g := rfl

@[simp]
theorem mapElementarySubgroup_elementaryUnit (f : R →+* S)
    (i j : ι) (hij : i ≠ j) (a : R) :
    mapElementarySubgroup f
        (⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a⟩ :
          elementarySubgroup ι R) =
      (⟨elementaryUnit i j hij (f a), elementaryUnit_mem i j hij (f a)⟩ :
        elementarySubgroup ι S) := by
  apply Subtype.ext
  exact mapRingHom_elementaryUnit f i j hij a

@[simp]
theorem mapElementarySubgroup_id :
    mapElementarySubgroup (ι := ι) (RingHom.id R) =
      MonoidHom.id (elementarySubgroup ι R) := by
  ext g i j
  simp

@[simp]
theorem mapElementarySubgroup_comp {T : Type uT} [Ring T]
    (f : R →+* S) (g : S →+* T) :
    mapElementarySubgroup (ι := ι) (g.comp f) =
      (mapElementarySubgroup g).comp (mapElementarySubgroup f) := by
  ext x i j
  simp

/-- Elementary generators with coefficients in `I`, viewed as members of `E(R)`. -/
def relativeElementaryGenerators (I : TwoSidedIdeal R) :
    Set (elementarySubgroup ι R) :=
  {g | ∃ i j : ι, ∃ hij : i ≠ j, ∃ a : R, a ∈ I ∧
    g = (⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a⟩ :
      elementarySubgroup ι R)}

/-- The normal closure of the ideal-coefficient generators **inside** `E(R)`. -/
def relativeElementarySubgroup (I : TwoSidedIdeal R) :
    Subgroup (elementarySubgroup ι R) :=
  Subgroup.normalClosure (relativeElementaryGenerators (ι := ι) I)

/-- Every ideal-coefficient elementary unit belongs to the relative subgroup. -/
theorem elementaryUnit_mem_relativeElementarySubgroup (I : TwoSidedIdeal R)
    (i j : ι) (hij : i ≠ j) (a : R) (ha : a ∈ I) :
    (⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a⟩ :
      elementarySubgroup ι R) ∈ relativeElementarySubgroup (ι := ι) I :=
  Subgroup.subset_normalClosure ⟨i, j, hij, a, ha, rfl⟩

instance relativeElementarySubgroup_normal (I : TwoSidedIdeal R) :
    (relativeElementarySubgroup (ι := ι) I).Normal := by
  change (Subgroup.normalClosure (relativeElementaryGenerators (ι := ι) I)).Normal
  infer_instance

/-- Enlarging the ideal enlarges its relative elementary subgroup. -/
theorem relativeElementarySubgroup_mono {I J : TwoSidedIdeal R} (hIJ : I ≤ J) :
    relativeElementarySubgroup (ι := ι) I ≤ relativeElementarySubgroup J := by
  apply Subgroup.normalClosure_mono
  rintro x ⟨i, j, hij, a, ha, rfl⟩
  exact ⟨i, j, hij, a, hIJ ha, rfl⟩

/-- The zero ideal has trivial relative elementary subgroup, including in rank zero or one. -/
@[simp]
theorem relativeElementarySubgroup_bot :
    relativeElementarySubgroup (ι := ι) (⊥ : TwoSidedIdeal R) = ⊥ := by
  apply Subgroup.normalClosure_eq_bot_iff.mpr
  rintro x ⟨i, j, hij, a, ha, rfl⟩
  have ha0 : a = 0 := by simpa using ha
  subst a
  apply Subtype.ext
  simp

/-- Relative elementary elements reduce to the identity modulo their ideal. -/
theorem relativeElementarySubgroup_le_congruenceSubgroup (I : TwoSidedIdeal R) :
    relativeElementarySubgroup (ι := ι) I ≤
      (congruenceSubgroup (n := ι) I).subgroupOf (elementarySubgroup ι R) := by
  change Subgroup.normalClosure (relativeElementaryGenerators (ι := ι) I) ≤
    (MonoidHom.ker (mapRingHom (Ideal.Quotient.mk I.asIdeal) :
      GL ι R →* GL ι (R ⧸ I.asIdeal))).subgroupOf (elementarySubgroup ι R)
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨i, j, hij, a, ha, rfl⟩
  change elementaryUnit i j hij a ∈ congruenceSubgroup (n := ι) I
  change mapRingHom (Ideal.Quotient.mk I.asIdeal) (elementaryUnit i j hij a) = 1
  rw [mapRingHom_elementaryUnit]
  have ha0 : Ideal.Quotient.mk I.asIdeal a = 0 :=
    quotient_mk_ideal_coe_eq_zero I ⟨a, ha⟩
  rw [ha0]
  exact elementaryUnit_zero i j hij

/-- The image of the relative group in the ambient GL lies in the existing
congruence kernel. This is an image inclusion, not a claim of ambient normality. -/
theorem relativeElementarySubgroup_map_subtype_le_congruenceSubgroup
    (I : TwoSidedIdeal R) :
    (relativeElementarySubgroup (ι := ι) I).map
      (elementarySubgroup ι R).subtype ≤ congruenceSubgroup (n := ι) I := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  exact relativeElementarySubgroup_le_congruenceSubgroup I hx

/-- Compatible coefficient maps carry relative elementary groups into relative
elementary groups, without any surjectivity assumption. -/
theorem mapElementarySubgroup_relativeElementarySubgroup_le
    (f : R →+* S) (I : TwoSidedIdeal R) (J : TwoSidedIdeal S)
    (hIJ : I ≤ J.comap f) :
    (relativeElementarySubgroup (ι := ι) I).map (mapElementarySubgroup f) ≤
      relativeElementarySubgroup J := by
  change (Subgroup.normalClosure (relativeElementaryGenerators (ι := ι) I)).map
      (mapElementarySubgroup f) ≤
      Subgroup.normalClosure (relativeElementaryGenerators (ι := ι) J)
  apply (Subgroup.map_normalClosure_le _ _).trans
  apply Subgroup.normalClosure_mono
  rintro x ⟨y, ⟨i, j, hij, a, ha, rfl⟩, rfl⟩
  refine ⟨i, j, hij, f a, (TwoSidedIdeal.mem_comap f).mp (hIJ ha), ?_⟩
  exact mapElementarySubgroup_elementaryUnit f i j hij a

end Matrix.GeneralLinearGroup
