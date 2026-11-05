/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.ElementaryPermutation
public import GeneralLinearGroups.LocalElementaryGeneration
public import Mathlib.Algebra.EuclideanDomain.Basic

/-!
# Elementary matrices over Euclidean domains

Elementary row operations over a Euclidean domain produce a unit leading entry
in an invertible matrix. The existing unit-pivot induction then reduces finite
matrices to unit diagonals. This gives the determinant classification of the
existing stable elementary quotient, with the existing rank-one section as inverse.

The reduction uses Mathlib's well-founded Euclidean relation, so no
natural-valued norm is required. A first-column Bézout identity from the inverse
matrix ensures that Euclidean row reduction ends at a unit. Signed swaps and
transvections remain in the original elementary subgroup throughout.

The finite and stable classifications reuse
`exists_elementary_diagonalization_of_unit_pivots`,
`diagonalUnit_mem_elementarySubgroup`, the stable elementary subgroup,
and the determinant and rank-one maps in `StableDeterminant`. The local-ring
comparison identifies the constructions on their overlap without changing either
map. Empty and singleton finite ranks are included.

## References

* Charles A. Weibel, *The K-book*, III.1.2.2 (field case), proves
  `E_n(F) = SL_n(F)` for fields in ranks at least one. The Euclidean-domain result
  here extends that field comparison using Mathlib's well-founded Euclidean relation and this
  library's unit-pivot diagonalization infrastructure.
* Mathlib's `EuclideanDomain` and elementary matrix APIs.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {R : Type u} [EuclideanDomain R]

private theorem first_column_common_divisor_dvd_one {n : ℕ}
    (g : GL (Fin (n + 1)) R) (a : R)
    (hdiv : ∀ i, a ∣ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i 0) :
    a ∣ 1 := by
  have hsum : (∑ i : Fin (n + 1),
      ((g⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 i *
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i 0) = 1 := by
    have h := congrArg
      (fun x : GL (Fin (n + 1)) R =>
        (x : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0) (inv_mul_cancel g)
    simpa only [Units.val_mul, Units.val_one, Matrix.mul_apply,
      Matrix.one_apply_eq] using h
  rw [← hsum]
  exact Finset.dvd_sum (fun i _ => (hdiv i).mul_left _)

private theorem exists_elementary_unit_pivot_of_ne_zero {n : ℕ}
    (g : GL (Fin (n + 1)) R)
    (hzero : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0 ≠ 0) :
    ∃ e : elementarySubgroup (Fin (n + 1)) R,
      IsUnit ((((e : GL (Fin (n + 1)) R) * g : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0) := by
  classical
  suffices ∀ a : R, ∀ g : GL (Fin (n + 1)) R,
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0 = a → a ≠ 0 →
      ∃ e : elementarySubgroup (Fin (n + 1)) R,
        IsUnit ((((e : GL (Fin (n + 1)) R) * g : GL (Fin (n + 1)) R) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0) from
    this _ g rfl hzero
  intro a
  refine (@EuclideanDomain.r_wellFounded R ‹EuclideanDomain R›).induction
    (C := fun a => ∀ g : GL (Fin (n + 1)) R,
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0 = a → a ≠ 0 →
      ∃ e : elementarySubgroup (Fin (n + 1)) R,
        IsUnit ((((e : GL (Fin (n + 1)) R) * g : GL (Fin (n + 1)) R) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0)) a ?_
  intro a ih g hentry ha
  by_cases hunit : IsUnit a
  · exact ⟨1, by simpa only [OneMemClass.coe_one, one_mul, hentry] using hunit⟩
  -- A nonunit cannot divide the whole unimodular column.
  have hrow : ∃ i, ¬ a ∣ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i 0 := by
    by_contra h
    exact hunit (isUnit_iff_dvd_one.mpr
      (first_column_common_divisor_dvd_one g a (not_exists_not.mp h)))
  obtain ⟨i, hi⟩ := hrow
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hi (hentry ▸ dvd_rfl)
  let b := (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i 0
  -- Subtract the Euclidean quotient, then move the remainder to the leading entry.
  let t : elementarySubgroup (Fin (n + 1)) R :=
    ⟨elementaryUnit i 0 hi0 (-(b / a)), elementaryUnit_mem i 0 hi0 (-(b / a))⟩
  let s : elementarySubgroup (Fin (n + 1)) R :=
    ⟨signedSwapUnit 0 i hi0.symm, signedSwapUnit_mem_elementarySubgroup 0 i hi0.symm⟩
  let g' : GL (Fin (n + 1)) R := (s : GL (Fin (n + 1)) R) *
    ((t : GL (Fin (n + 1)) R) * g)
  have hentry' : (g' : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0 = b % a := by
    change (((signedSwapUnit (R := R) 0 i hi0.symm :
      Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ
      fun j => (((t : GL (Fin (n + 1)) R) * g : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) j 0) 0) = b % a
    rw [signedSwapUnit_mulVec]
    simp only [ite_true]
    simp [t, Matrix.add_mul, hentry, b, EuclideanDomain.mod_eq_sub_mul_div,
      mul_comm, sub_eq_add_neg]
  have hrem : b % a ≠ 0 := by
    intro h
    exact hi (EuclideanDomain.mod_eq_zero.mp h)
  obtain ⟨e, he⟩ := ih (b % a) (EuclideanDomain.mod_lt b ha) g' hentry' hrem
  refine ⟨e * (s * t), ?_⟩
  simpa only [Subgroup.coe_mul, mul_assoc, g'] using he

/-- Elementary left multiplication makes the leading entry of an invertible
successor-rank matrix over a Euclidean domain a unit. -/
theorem exists_elementary_unit_pivot_euclidean {n : ℕ} (g : GL (Fin (n + 1)) R) :
    ∃ e : elementarySubgroup (Fin (n + 1)) R,
      IsUnit ((((e : GL (Fin (n + 1)) R) * g : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0) := by
  classical
  by_cases hzero : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0 = 0
  · have hrow : ∃ i, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i 0 ≠ 0 := by
      by_contra h
      have hdvd : (0 : R) ∣ 1 := first_column_common_divisor_dvd_one g 0 (by
        intro i
        simpa only [not_exists_not.mp h i] using dvd_zero (0 : R))
      exact one_ne_zero (zero_dvd_iff.mp hdvd)
    obtain ⟨i, hi⟩ := hrow
    have hi0 : (0 : Fin (n + 1)) ≠ i := by
      rintro rfl
      exact hi hzero
    let s : elementarySubgroup (Fin (n + 1)) R :=
      ⟨signedSwapUnit 0 i hi0, signedSwapUnit_mem_elementarySubgroup 0 i hi0⟩
    have hpivot : (((s : GL (Fin (n + 1)) R) * g : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 0 =
          (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i 0 := by
      change (((signedSwapUnit (R := R) 0 i hi0 :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ
        fun j => (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) j 0) 0) = _
      rw [signedSwapUnit_mulVec]
      simp only [ite_true]
    obtain ⟨e, he⟩ := exists_elementary_unit_pivot_of_ne_zero
      ((s : GL (Fin (n + 1)) R) * g) (hpivot ▸ hi)
    refine ⟨e * s, ?_⟩
    simpa only [Subgroup.coe_mul, mul_assoc] using he
  · exact exists_elementary_unit_pivot_of_ne_zero g hzero

/-- Over a Euclidean domain, a finite invertible matrix is elementary exactly
when its determinant is one, including for empty and singleton index types. -/
theorem mem_elementarySubgroup_iff_det_eq_one_euclidean
    {ι : Type v} [Fintype ι] [DecidableEq ι] (g : GL ι R) :
    g ∈ elementarySubgroup ι R ↔ Matrix.GeneralLinearGroup.det g = 1 := by
  exact mem_elementarySubgroup_iff_det_eq_one_of_unit_pivots
    (fun _ matrix => exists_elementary_unit_pivot_euclidean matrix) g

namespace StableGL

/-- The original stable elementary subgroup over a Euclidean domain is the
kernel of the original stable determinant. -/
theorem elementary_eq_ker_det_euclidean (R : Type u) [EuclideanDomain R] :
    stableElementarySubgroup R = (det R).ker := by
  apply le_antisymm (elementary_le_ker_det R)
  intro g hg
  obtain ⟨n, representative, rfl⟩ := exists_stage R g
  have hdet : Matrix.GeneralLinearGroup.det representative = 1 := by
    simpa only [MonoidHom.mem_ker, det_stage] using hg
  exact elementary_stage_le R n
    (Subgroup.mem_map_of_mem _
      ((mem_elementarySubgroup_iff_det_eq_one_euclidean representative).2 hdet))

/-- The determinant identifies the original stable elementary quotient over a
Euclidean domain with coefficient units. Its inverse is the original rank-one
section. -/
noncomputable def quotientDetMulEquivEuclidean (R : Type u) [EuclideanDomain R] :
    (StableGL R ⧸ stableElementarySubgroup R) ≃* Rˣ where
  toFun := quotientDet R
  invFun := quotientRankOneUnits R
  left_inv := by
    intro q
    have hinjective : Function.Injective (quotientDet R) :=
      (QuotientGroup.injective_lift_iff (stableElementarySubgroup R) (det R)
        (elementary_le_ker_det R)).2 (elementary_eq_ker_det_euclidean R)
    exact hinjective (quotientDet_quotientRankOneUnits R (quotientDet R q))
  right_inv := by
    exact quotientDet_quotientRankOneUnits R
  map_mul' := by
    exact (quotientDet R).map_mul

/-- The equivalence evaluates as the original quotient determinant. -/
@[simp]
theorem quotientDetMulEquivEuclidean_apply (R : Type u) [EuclideanDomain R]
    (q : StableGL R ⧸ stableElementarySubgroup R) :
    quotientDetMulEquivEuclidean R q = quotientDet R q := by
  rfl

/-- The inverse equivalence evaluates as the original rank-one section. -/
@[simp]
theorem quotientDetMulEquivEuclidean_symm_apply (R : Type u) [EuclideanDomain R]
    (a : Rˣ) :
    (quotientDetMulEquivEuclidean R).symm a = quotientRankOneUnits R a := by
  rfl

/-- The determinant equivalence commutes with arbitrary coefficient
homomorphisms between Euclidean domains, without an injectivity assumption. -/
theorem quotientDetMulEquivEuclidean_map {S : Type v} [EuclideanDomain S]
    (f : R →+* S) (q : StableGL R ⧸ stableElementarySubgroup R) :
    quotientDetMulEquivEuclidean S
      (QuotientGroup.map (stableElementarySubgroup R)
        (stableElementarySubgroup S) (map f)
        ((Subgroup.map_le_iff_le_comap).mp (map_elementarySubgroup_le f)) q) =
      Units.map f (quotientDetMulEquivEuclidean R q) := by
  simpa only [quotientDetMulEquivEuclidean_apply] using quotientDet_map f q

/-- The inverse determinant equivalence commutes with arbitrary coefficient
homomorphisms between Euclidean domains. -/
theorem quotientDetMulEquivEuclidean_symm_map {S : Type v} [EuclideanDomain S]
    (f : R →+* S) (a : Rˣ) :
    QuotientGroup.map (stableElementarySubgroup R)
        (stableElementarySubgroup S) (map f)
        ((Subgroup.map_le_iff_le_comap).mp (map_elementarySubgroup_le f))
        ((quotientDetMulEquivEuclidean R).symm a) =
      (quotientDetMulEquivEuclidean S).symm (Units.map f a) := by
  simpa only [quotientDetMulEquivEuclidean_symm_apply] using quotientRankOneUnits_map f a

/-- Every finite representative has the same stable elementary class as its
rank-one determinant representative, including in ranks zero and one. -/
theorem mk_stage_eq_quotientRankOneUnits_det_euclidean
    (R : Type u) [EuclideanDomain R] (n : ℕ) (g : GL (Fin n) R) :
    QuotientGroup.mk' (stableElementarySubgroup R) (stage R n g) =
      quotientRankOneUnits R (Matrix.GeneralLinearGroup.det g) := by
  apply (quotientDetMulEquivEuclidean R).injective
  simp only [quotientDetMulEquivEuclidean_apply, quotientDet_mk, det_stage,
    quotientDet_quotientRankOneUnits]

/-- On a Euclidean domain that is also a local ring, the determinant equivalence
agrees with the existing local-ring equivalence. -/
theorem quotientDetMulEquivEuclidean_eq_local (R : Type u)
    [EuclideanDomain R] [IsLocalRing R] :
    quotientDetMulEquivEuclidean R = quotientDetMulEquiv R := by
  apply MulEquiv.ext
  intro q
  rw [quotientDetMulEquivEuclidean_apply, quotientDetMulEquiv_apply]

end StableGL
end Matrix.GeneralLinearGroup
