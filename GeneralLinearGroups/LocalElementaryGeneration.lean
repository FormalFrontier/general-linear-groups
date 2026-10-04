/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.ElementaryDiagonal
public import GeneralLinearGroups.UnitPivotInduction
public import GeneralLinearGroups.StableDeterminant
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Elementary matrices over commutative local rings

Invertible matrices over a commutative local ring admit elementary left and right
factors reducing them to a diagonal of units. Consequently, determinant one
characterizes the elementary subgroup in every finite rank. The stable elementary
subgroup is the kernel of the stable determinant, and the existing quotient
determinant identifies the elementary quotient with the coefficient units.

The factorization here concerns invertible matrices: the corresponding field
transvection factorization in Mathlib also applies to singular matrices.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v w

section LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

private theorem isUnit_add_of_not_isUnit_of_isUnit {a b : R}
    (ha : ¬ IsUnit a) (hb : IsUnit b) : IsUnit (a + b) := by
  by_contra hab
  have hneg : ¬ IsUnit (-a) := by simpa only [IsUnit.neg_iff] using ha
  have hsum : ¬ IsUnit ((a + b) + -a) := IsLocalRing.nonunits_add hab hneg
  exact hsum (by simpa [add_comm, add_left_comm, add_assoc] using hb)

private theorem exists_elementary_unit_pivot {n : ℕ} (g : GL (Fin (n + 1)) R) :
    ∃ e : elementarySubgroup (Fin (n + 1)) R,
      IsUnit ((((e : GL (Fin (n + 1)) R) * g : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0) := by
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) R := g
  have hsum : (∑ row : Fin (n + 1),
      (((g⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
        0 row) * M row 0) = 1 := by
    have h := congrArg
      (fun x : GL (Fin (n + 1)) R =>
        ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0)) (inv_mul_cancel g)
    simpa only [Units.val_mul, Units.val_one, Matrix.mul_apply,
      Matrix.one_apply_eq, M] using h
  have hcol : ∃ row : Fin (n + 1), IsUnit (M row 0) := by
    have hunit : IsUnit (∑ row ∈ (Finset.univ : Finset (Fin (n + 1))),
        (((g⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
          0 row) * M row 0) := by
      simpa only [hsum] using (isUnit_one : IsUnit (1 : R))
    obtain ⟨row, _, hproduct⟩ := IsLocalRing.exists_of_isUnit_sum hunit
    exact ⟨row, isUnit_of_mul_isUnit_right hproduct⟩
  by_cases hfirst : IsUnit (M 0 0)
  · exact ⟨1, by simpa only [OneMemClass.coe_one, one_mul] using hfirst⟩
  obtain ⟨row, hrow⟩ := hcol
  have hne : (0 : Fin (n + 1)) ≠ row := by
    intro h
    exact hfirst (by simpa [← h] using hrow)
  let e : elementarySubgroup (Fin (n + 1)) R :=
    ⟨elementaryUnit 0 row hne 1, elementaryUnit_mem 0 row hne 1⟩
  refine ⟨e, ?_⟩
  have hpivot :
      (((e : GL (Fin (n + 1)) R) * g : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0 = M 0 0 + M row 0 := by
    simp [e, M, Matrix.add_mul, Matrix.single_mul_apply_same]
  rw [hpivot]
  exact isUnit_add_of_not_isUnit_of_isUnit hfirst hrow

/-- Over a commutative local ring, an elementary left factor makes the
leading entry of every invertible successor-rank matrix a unit. -/
theorem exists_elementary_unit_pivot_local {n : ℕ} (g : GL (Fin (n + 1)) R) :
    ∃ e : elementarySubgroup (Fin (n + 1)) R,
      IsUnit ((((e : GL (Fin (n + 1)) R) * g : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0) :=
  exists_elementary_unit_pivot g

/-- Elementary factors reduce any invertible matrix over a commutative local ring
to an invertible diagonal, including in rank zero. -/
theorem exists_elementary_diagonalization_local {n : ℕ} (g : GL (Fin n) R) :
    ∃ (left right : elementarySubgroup (Fin n) R) (diagonal : Fin n → Rˣ),
      (left : GL (Fin n) R) * g * (right : GL (Fin n) R) = diagonalUnit diagonal := by
  exact exists_elementary_diagonalization_of_unit_pivots
    (fun _ matrix => exists_elementary_unit_pivot_local matrix) g

private theorem mem_elementarySubgroup_iff_det_eq_one_fin {n : ℕ}
    (g : GL (Fin n) R) :
    g ∈ elementarySubgroup (Fin n) R ↔ Matrix.GeneralLinearGroup.det g = 1 := by
  constructor
  · intro hg
    exact Matrix.det_elementarySubgroup_eq_one ⟨g, hg⟩
  · intro hdet
    obtain ⟨left, right, diagonal, hfactor⟩ := exists_elementary_diagonalization_local g
    have hmatrix := congrArg
      (fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) hfactor
    have hproduct : (∏ i, diagonal i) = 1 := by
      apply Units.ext
      have hfactorDet := Matrix.det_eq_prod_of_elementary_diagonalization
        (L := left) (Q := right) (M := (g : Matrix (Fin n) (Fin n) R))
        (by simpa only [Units.val_mul, diagonalUnit_val] using hmatrix)
      change (Units.coeHom R) (∏ i, diagonal i) = 1
      rw [map_prod]
      exact hfactorDet.symm.trans (congrArg Units.val hdet)
    have hdiagonal : diagonalUnit diagonal ∈ elementarySubgroup (Fin n) R :=
      diagonalUnit_mem_elementarySubgroup n diagonal hproduct
    have hg : g = (left : GL (Fin n) R)⁻¹ * diagonalUnit diagonal *
        (right : GL (Fin n) R)⁻¹ := by
      calc
        g = ((left : GL (Fin n) R)⁻¹ *
            ((left : GL (Fin n) R) * g * (right : GL (Fin n) R))) *
              (right : GL (Fin n) R)⁻¹ := by group
        _ = (left : GL (Fin n) R)⁻¹ * diagonalUnit diagonal *
            (right : GL (Fin n) R)⁻¹ := by rw [hfactor]
    rw [hg]
    exact (elementarySubgroup (Fin n) R).mul_mem
      ((elementarySubgroup (Fin n) R).mul_mem
        ((elementarySubgroup (Fin n) R).inv_mem left.property) hdiagonal)
      ((elementarySubgroup (Fin n) R).inv_mem right.property)

/-- Over a commutative local ring, the finite elementary subgroup is exactly
the determinant-one subgroup, for arbitrary finite decidable index types. -/
theorem mem_elementarySubgroup_iff_det_eq_one_local
    {ι : Type v} [Fintype ι] [DecidableEq ι] (g : GL ι R) :
    g ∈ elementarySubgroup ι R ↔ Matrix.GeneralLinearGroup.det g = 1 := by
  constructor
  · intro hg
    exact Matrix.det_elementarySubgroup_eq_one ⟨g, hg⟩
  · intro hdet
    let equiv : ι ≃ Fin (Fintype.card ι) := Fintype.equivOfCardEq (by simp)
    let reindexed : GL (Fin (Fintype.card ι)) R := reindexEquiv R equiv g
    have hdet' : Matrix.GeneralLinearGroup.det reindexed =
        Matrix.GeneralLinearGroup.det g := by
      apply Units.ext
      change (Matrix.reindex equiv equiv (g : Matrix ι ι R)).det =
        (g : Matrix ι ι R).det
      exact Matrix.det_reindex_self equiv _
    have hreindexed : reindexed ∈ elementarySubgroup (Fin (Fintype.card ι)) R :=
      (mem_elementarySubgroup_iff_det_eq_one_fin reindexed).2 (hdet'.trans hdet)
    have hback := reindexEquiv_mem_elementarySubgroup equiv.symm hreindexed
    simpa only [reindexed, ← reindexEquiv_symm, MulEquiv.symm_apply_apply] using hback

namespace StableGL

/-- The stable elementary subgroup is the kernel of the stable determinant
over a commutative local ring. -/
theorem elementary_eq_ker_det_local (R : Type u) [CommRing R] [IsLocalRing R] :
    stableElementarySubgroup R = (det R).ker := by
  apply le_antisymm (elementary_le_ker_det R)
  intro g hg
  obtain ⟨n, x, rfl⟩ := exists_stage R g
  have hx : Matrix.GeneralLinearGroup.det x = 1 := by
    simpa only [MonoidHom.mem_ker, det_stage] using hg
  exact elementary_stage_le R n
    (Subgroup.mem_map_of_mem _ (mem_elementarySubgroup_iff_det_eq_one_local x |>.2 hx))

/-- The existing quotient determinant has trivial kernel over a local ring. -/
theorem quotientDet_ker_eq_bot_local (R : Type u) [CommRing R] [IsLocalRing R] :
    (quotientDet R).ker = ⊥ := by
  apply eq_bot_iff.mpr
  intro quotient hquotient
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (stableElementarySubgroup R) quotient
  apply (QuotientGroup.eq_one_iff g).mpr
  rw [elementary_eq_ker_det_local R]
  apply MonoidHom.mem_ker.mpr
  exact MonoidHom.mem_ker.mp hquotient

/-- The existing quotient determinant, with inverse the existing rank-one section,
identifies stable elementary classes with coefficient units over a local ring. -/
noncomputable def quotientDetMulEquiv (R : Type u) [CommRing R] [IsLocalRing R] :
    (StableGL R ⧸ stableElementarySubgroup R) ≃* Rˣ where
  toFun := quotientDet R
  invFun := quotientRankOneUnits R
  left_inv := by
    intro quotient
    apply ((quotientDet R).ker_eq_bot_iff.mp (quotientDet_ker_eq_bot_local R))
    exact quotientDet_quotientRankOneUnits R (quotientDet R quotient)
  right_inv := quotientDet_quotientRankOneUnits R
  map_mul' := (quotientDet R).map_mul

/-- The equivalence evaluates as the existing quotient determinant. -/
@[simp]
theorem quotientDetMulEquiv_apply (R : Type u) [CommRing R] [IsLocalRing R]
    (quotient : StableGL R ⧸ stableElementarySubgroup R) :
    quotientDetMulEquiv R quotient = quotientDet R quotient := rfl

/-- Its inverse evaluates as the existing rank-one section. -/
@[simp]
theorem quotientDetMulEquiv_symm_apply (R : Type u) [CommRing R] [IsLocalRing R]
    (unit : Rˣ) :
    (quotientDetMulEquiv R).symm unit = quotientRankOneUnits R unit := rfl

/-- The equivalence commutes with changes of local-ring coefficients. -/
theorem quotientDetMulEquiv_map {S : Type w} [CommRing S] [IsLocalRing S]
    (f : R →+* S) (quotient : StableGL R ⧸ stableElementarySubgroup R) :
    quotientDetMulEquiv S
      (QuotientGroup.map (stableElementarySubgroup R)
        (stableElementarySubgroup S) (map f)
        ((Subgroup.map_le_iff_le_comap).mp (map_elementarySubgroup_le f)) quotient) =
      Units.map f (quotientDetMulEquiv R quotient) := by
  simpa only [quotientDetMulEquiv_apply] using quotientDet_map f quotient

/-- The inverse equivalence commutes with changes of local-ring coefficients. -/
theorem quotientDetMulEquiv_symm_map {S : Type w} [CommRing S] [IsLocalRing S]
    (f : R →+* S) (unit : Rˣ) :
    QuotientGroup.map (stableElementarySubgroup R)
        (stableElementarySubgroup S) (map f)
        ((Subgroup.map_le_iff_le_comap).mp (map_elementarySubgroup_le f))
        ((quotientDetMulEquiv R).symm unit) =
      (quotientDetMulEquiv S).symm (Units.map f unit) := by
  simpa only [quotientDetMulEquiv_symm_apply] using quotientRankOneUnits_map f unit

end StableGL

end LocalRing

section CommutativeRingComparison

variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The GL elementary factors of a transvection list have the same underlying
matrix product as Mathlib's transvection factors. -/
theorem elementaryUnit_list_val (factors : List (Matrix.TransvectionStruct ι R)) :
    (((factors.map (fun factor => elementaryUnit factor.i factor.j factor.hij factor.c)).prod :
      GL ι R) : Matrix ι ι R) =
      (factors.map Matrix.TransvectionStruct.toMatrix).prod := by
  induction factors with
  | nil => simp
  | cons factor factors ih =>
    simp only [List.map_cons, List.prod_cons, Units.val_mul, ih]
    rw [elementaryUnit_eq_transvection]
    rfl

end CommutativeRingComparison

section FieldComparison

variable {F : Type u} [Field F] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- For invertible field matrices, Mathlib's transvection-factor lists can be
read as GL elementary factors with an invertible diagonal. -/
theorem exists_elementary_transvection_diagonalization_field (g : GL ι F) :
    ∃ (left right : List (Matrix.TransvectionStruct ι F)) (diagonal : ι → Fˣ),
      (left.map (fun factor => elementaryUnit factor.i factor.j factor.hij factor.c)).prod *
        g * (right.map (fun factor => elementaryUnit factor.i factor.j factor.hij factor.c)).prod =
          diagonalUnit diagonal := by
  obtain ⟨left, right, values, hvalues⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal
      (g : Matrix ι ι F)
  have hunit : IsUnit (Matrix.diagonal values) := by
    rw [← hvalues]
    rw [← elementaryUnit_list_val left, ← elementaryUnit_list_val right]
    exact Units.isUnit
      ((left.map (fun factor => elementaryUnit factor.i factor.j factor.hij factor.c)).prod *
        g * (right.map (fun factor => elementaryUnit factor.i factor.j factor.hij factor.c)).prod)
  have hentries : ∀ i, IsUnit (values i) :=
    (Pi.isUnit_iff).mp (Matrix.isUnit_diagonal.mp hunit)
  let diagonal : ι → Fˣ := fun i => (hentries i).unit
  refine ⟨left, right, diagonal, ?_⟩
  apply Units.ext
  simp only [Units.val_mul, elementaryUnit_list_val, diagonalUnit_val]
  exact hvalues.trans (congrArg Matrix.diagonal (funext fun i =>
    (hentries i).unit_spec.symm))

end FieldComparison

end Matrix.GeneralLinearGroup
