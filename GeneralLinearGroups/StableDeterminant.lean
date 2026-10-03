/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.StableElementary

/-!
# The stable determinant and rank-one units

Rank-one units embed in stable general linear groups over semirings. Over a
commutative ring, the determinants of finite representatives define a map from
stable general linear groups to units. It factors through the stable elementary
quotient and through the abelianization. The rank-one maps give sections of
these determinant maps without asserting that the stable elementary subgroup
is the whole determinant kernel. Since the elementary quotient is abelian, it
splits as the product of the quotient determinant kernel and the unit group.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup
namespace StableGL

universe u v

/-- Include a unit in stable general linear groups at rank one. -/
noncomputable def rankOneUnits (R : Type u) [Semiring R] : Rˣ →* StableGL R :=
  (stage R 1).comp (Matrix.GeneralLinearGroup.scalar (Fin 1))

@[simp]
theorem rankOneUnits_apply (R : Type u) [Semiring R] (unit : Rˣ) :
    rankOneUnits R unit = stage R 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) unit) :=
  rfl

/-- Recover a unit from its rank-one stable image, also for noncommutative semirings. -/
theorem rankOneUnits_injective (R : Type u) [Semiring R] :
    Function.Injective (rankOneUnits R) := by
  intro first second equality
  apply Units.ext
  have hscalar : Matrix.scalar (Fin 1) (first : R) =
      Matrix.scalar (Fin 1) (second : R) := by
    simpa only [Matrix.GeneralLinearGroup.coe_scalar] using
      congrArg Units.val (stage_injective R 1 equality)
  exact Matrix.scalar_inj.mp hscalar

/-- Rank-one inclusion is compatible with changes of semiring coefficients. -/
@[simp]
theorem map_rankOneUnits {R : Type u} {S : Type v}
    [Semiring R] [Semiring S] (f : R →+* S) (unit : Rˣ) :
    map f (rankOneUnits R unit) = rankOneUnits S (Units.map f unit) := by
  simp only [rankOneUnits_apply, map_stage, Matrix.GeneralLinearGroup.mapRingHom_scalar]

/-- Determinants agree under initial-segment stabilization. -/
theorem det_finStabilize (R : Type u) [CommRing R]
    (n m : ℕ) (h : n ≤ m) (g : GL (Fin n) R) :
    (Matrix.GeneralLinearGroup.det (finStabilize R h g) : Rˣ) =
      Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  change Matrix.det ((finStabilize R h g : GL (Fin m) R) :
    Matrix (Fin m) (Fin m) R) =
      Matrix.det (g : Matrix (Fin n) (Fin n) R)
  change Matrix.det (Matrix.reindex (finBlockEquiv h) (finBlockEquiv h)
    (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) R) 0 0 1)) =
      Matrix.det (g : Matrix (Fin n) (Fin n) R)
  simp

/-- The compatible determinants of all finite ranks, including rank zero. -/
def det (R : Type u) [CommRing R] : StableGL R →* Rˣ :=
  lift R (fun _ => Matrix.GeneralLinearGroup.det) (det_finStabilize R)

/-- The stable determinant evaluates to the original determinant at every finite rank. -/
@[simp]
theorem det_stage (R : Type u) [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    det R (stage R n g) = Matrix.GeneralLinearGroup.det g :=
  lift_stage R _ _ n g

/-- A rank-one scalar has determinant equal to its defining unit. -/
@[simp]
theorem det_rankOneUnits (R : Type u) [CommRing R] (unit : Rˣ) :
    det R (rankOneUnits R unit) = unit := by
  simp [Matrix.GeneralLinearGroup.det_scalar]

/-- The rank-one map is a right inverse of the stable determinant. -/
theorem det_comp_rankOneUnits (R : Type u) [CommRing R] :
    (det R).comp (rankOneUnits R) = MonoidHom.id (Rˣ) := by
  apply MonoidHom.ext
  intro unit
  exact det_rankOneUnits R unit

theorem det_surjective (R : Type u) [CommRing R] :
    Function.Surjective (det R) := by
  intro unit
  exact ⟨rankOneUnits R unit, det_rankOneUnits R unit⟩

/-- Stable determinant commutes with homomorphisms of commutative rings. -/
@[simp]
theorem det_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (g : StableGL R) :
    det S (map f g) = Units.map f (det R g) := by
  obtain ⟨n, representative, rfl⟩ := exists_stage R g
  rw [map_stage, det_stage, det_stage, Matrix.GeneralLinearGroup.mapRingHom_eq_map]
  exact Matrix.GeneralLinearGroup.map_det f representative

/-- Every stable elementary matrix has unit determinant. -/
theorem det_elementary (R : Type u) [CommRing R]
    {g : StableGL R} (hg : g ∈ stableElementarySubgroup R) : det R g = 1 := by
  obtain ⟨n, e, rfl⟩ := (mem_stableElementarySubgroup_iff R g).mp hg
  exact Matrix.det_elementarySubgroup_eq_one e

/-- Stable elementary matrices have unit determinant; no reverse inclusion is asserted. -/
theorem elementary_le_ker_det (R : Type u) [CommRing R] :
    stableElementarySubgroup R ≤ (det R).ker := by
  intro g hg
  exact MonoidHom.mem_ker.mpr (det_elementary R hg)

/-- The determinant induced on the existing stable elementary quotient. -/
noncomputable def quotientDet (R : Type u) [CommRing R] :
    (StableGL R ⧸ stableElementarySubgroup R) →* Rˣ :=
  QuotientGroup.lift (stableElementarySubgroup R) (det R) (elementary_le_ker_det R)

/-- The rank-one map followed by the existing quotient projection. -/
noncomputable def quotientRankOneUnits (R : Type u) [Ring R] :
    Rˣ →* (StableGL R ⧸ stableElementarySubgroup R) :=
  (QuotientGroup.mk' (stableElementarySubgroup R)).comp (rankOneUnits R)

/-- The quotient determinant evaluates on a stable representative. -/
@[simp]
theorem quotientDet_mk (R : Type u) [CommRing R] (g : StableGL R) :
    quotientDet R (QuotientGroup.mk' (stableElementarySubgroup R) g) = det R g :=
  rfl

/-- The elementary quotient rank-one map is projection of the stable map. -/
@[simp]
theorem quotientRankOneUnits_apply (R : Type u) [Ring R] (unit : Rˣ) :
    quotientRankOneUnits R unit =
      QuotientGroup.mk' (stableElementarySubgroup R) (rankOneUnits R unit) :=
  rfl

/-- Rank-one units split the determinant of the elementary quotient. -/
@[simp]
theorem quotientDet_quotientRankOneUnits (R : Type u) [CommRing R] (unit : Rˣ) :
    quotientDet R (quotientRankOneUnits R unit) = unit := by
  rw [quotientRankOneUnits_apply, quotientDet_mk]
  exact det_rankOneUnits R unit

theorem quotientRankOneUnits_injective (R : Type u) [CommRing R] :
    Function.Injective (quotientRankOneUnits R) := by
  intro first second equality
  have := congrArg (quotientDet R) equality
  simpa only [quotientDet_quotientRankOneUnits] using this

theorem quotientDet_surjective (R : Type u) [CommRing R] :
    Function.Surjective (quotientDet R) := by
  intro unit
  exact ⟨quotientRankOneUnits R unit, quotientDet_quotientRankOneUnits R unit⟩

/-- The determinant factored through the canonical abelianization. -/
noncomputable def abelianizationDet (R : Type u) [CommRing R] :
    Abelianization (StableGL R) →* Rˣ :=
  Abelianization.lift (det R)

/-- Rank-one units projected to the abelianization, over any semiring. -/
noncomputable def abelianizationRankOneUnits (R : Type u) [Semiring R] :
    Rˣ →* Abelianization (StableGL R) :=
  Abelianization.of.comp (rankOneUnits R)

/-- The abelianization determinant evaluates on a stable representative. -/
@[simp]
theorem abelianizationDet_of (R : Type u) [CommRing R] (g : StableGL R) :
    abelianizationDet R (Abelianization.of g) = det R g :=
  Abelianization.lift_apply_of (det R) g

/-- The abelianization rank-one map is projection of the stable map. -/
@[simp]
theorem abelianizationRankOneUnits_apply (R : Type u) [Semiring R] (unit : Rˣ) :
    abelianizationRankOneUnits R unit = Abelianization.of (rankOneUnits R unit) :=
  rfl

/-- Rank-one units split the determinant on the abelianization. -/
@[simp]
theorem abelianizationDet_abelianizationRankOneUnits
    (R : Type u) [CommRing R] (unit : Rˣ) :
    abelianizationDet R (abelianizationRankOneUnits R unit) = unit := by
  simp

theorem abelianizationRankOneUnits_injective (R : Type u) [CommRing R] :
    Function.Injective (abelianizationRankOneUnits R) := by
  intro first second equality
  have := congrArg (abelianizationDet R) equality
  simpa using this

/-- The two determinant factorizations agree under the canonical equivalence. -/
theorem quotientDet_eq_abelianizationDet (R : Type u) [CommRing R] :
    quotientDet R = (abelianizationDet R).comp
      (stableElementaryAbelianizationEquiv R).toMonoidHom := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  change quotientDet R (QuotientGroup.mk' (stableElementarySubgroup R) g) =
    abelianizationDet R
      (stableElementaryAbelianizationEquiv R
        (QuotientGroup.mk' (stableElementarySubgroup R) g))
  simp only [quotientDet_mk, stableElementaryAbelianizationEquiv_mk, abelianizationDet_of]

/-- The canonical equivalence carries quotient rank-one units to their abelianization. -/
@[simp]
theorem abelianizationEquiv_quotientRankOneUnits (R : Type u) [Ring R]
    (unit : Rˣ) :
    stableElementaryAbelianizationEquiv R (quotientRankOneUnits R unit) =
      abelianizationRankOneUnits R unit := by
  rw [quotientRankOneUnits_apply, stableElementaryAbelianizationEquiv_mk]
  rfl

/-- Naturality of the determinant induced on the stable elementary quotient. -/
theorem quotientDet_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (q : StableGL R ⧸ stableElementarySubgroup R) :
    quotientDet S
      (QuotientGroup.map (stableElementarySubgroup R)
        (stableElementarySubgroup S) (map f)
        ((Subgroup.map_le_iff_le_comap).mp (map_elementarySubgroup_le f)) q) =
      Units.map f (quotientDet R q) := by
  refine QuotientGroup.induction_on q ?_
  intro g
  change quotientDet S
      (QuotientGroup.map (stableElementarySubgroup R)
        (stableElementarySubgroup S) (map f)
        ((Subgroup.map_le_iff_le_comap).mp (map_elementarySubgroup_le f))
          (QuotientGroup.mk' (stableElementarySubgroup R) g)) =
    Units.map f (quotientDet R (QuotientGroup.mk' (stableElementarySubgroup R) g))
  rw [QuotientGroup.map_mk']
  change quotientDet S (QuotientGroup.mk' (stableElementarySubgroup S) (map f g)) =
    Units.map f (quotientDet R (QuotientGroup.mk' (stableElementarySubgroup R) g))
  simpa only [quotientDet_mk] using det_map f g

/-- Naturality of rank-one units in the elementary quotient over rings. -/
theorem quotientRankOneUnits_map {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (unit : Rˣ) :
    QuotientGroup.map (stableElementarySubgroup R)
      (stableElementarySubgroup S) (map f)
      ((Subgroup.map_le_iff_le_comap).mp (map_elementarySubgroup_le f))
        (quotientRankOneUnits R unit) =
      quotientRankOneUnits S (Units.map f unit) := by
  rw [quotientRankOneUnits_apply, QuotientGroup.map_mk', quotientRankOneUnits_apply,
    map_rankOneUnits]
  rfl

/-- Naturality of the determinant on abelianizations. -/
theorem abelianizationDet_map {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (q : Abelianization (StableGL R)) :
    abelianizationDet S (Abelianization.map (map f) q) =
      Units.map f (abelianizationDet R q) := by
  refine QuotientGroup.induction_on q ?_
  intro g
  change abelianizationDet S (Abelianization.map (map f) (Abelianization.of g)) =
    Units.map f (abelianizationDet R (Abelianization.of g))
  simpa only [Abelianization.map_of, abelianizationDet_of] using det_map f g

/-- Naturality of rank-one units in the abelianization over semirings. -/
theorem abelianizationRankOneUnits_map {R : Type u} {S : Type v}
    [Semiring R] [Semiring S] (f : R →+* S) (unit : Rˣ) :
    Abelianization.map (map f) (abelianizationRankOneUnits R unit) =
      abelianizationRankOneUnits S (Units.map f unit) := by
  simp only [abelianizationRankOneUnits_apply, Abelianization.map_of, map_rankOneUnits]

/-- Split the abelian stable elementary quotient into its determinant kernel and
rank-one units. The kernel factor is retained without any vanishing assumption. -/
noncomputable def quotientDetKernelMulEquiv (R : Type u) [CommRing R] :
    (quotientDet R).ker × Rˣ ≃* (StableGL R ⧸ stableElementarySubgroup R) where
  toFun pair := pair.1.1 * quotientRankOneUnits R pair.2
  invFun q :=
    (⟨q * (quotientRankOneUnits R (quotientDet R q))⁻¹,
      by
        apply MonoidHom.mem_ker.mpr
        simp only [map_mul, map_inv, quotientDet_quotientRankOneUnits, mul_inv_cancel]⟩,
      quotientDet R q)
  left_inv := by
    intro pair
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_mul, MonoidHom.mem_ker.mp pair.1.property,
        quotientDet_quotientRankOneUnits, one_mul, mul_assoc, mul_inv_cancel, mul_one]
    · simp only [map_mul, MonoidHom.mem_ker.mp pair.1.property,
        quotientDet_quotientRankOneUnits, one_mul]
  right_inv := by
    intro q
    change (q * (quotientRankOneUnits R (quotientDet R q))⁻¹) *
      quotientRankOneUnits R (quotientDet R q) = q
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  map_mul' := by
    intro first second
    change ((first.1 : StableGL R ⧸ stableElementarySubgroup R) * second.1) *
        quotientRankOneUnits R (first.2 * second.2) =
      ((first.1 : StableGL R ⧸ stableElementarySubgroup R) *
          quotientRankOneUnits R first.2) *
        ((second.1 : StableGL R ⧸ stableElementarySubgroup R) *
          quotientRankOneUnits R second.2)
    rw [map_mul]
    ac_rfl

/-- Forward coordinates of the determinant-kernel/unit decomposition. -/
@[simp]
theorem quotientDetKernelMulEquiv_apply (R : Type u) [CommRing R]
    (pair : (quotientDet R).ker × Rˣ) :
    quotientDetKernelMulEquiv R pair =
      (pair.1 : StableGL R ⧸ stableElementarySubgroup R) *
        quotientRankOneUnits R pair.2 := by rfl

/-- The kernel coordinate removes the rank-one image of the determinant. -/
@[simp]
theorem quotientDetKernelMulEquiv_symm_apply_fst (R : Type u) [CommRing R]
    (q : StableGL R ⧸ stableElementarySubgroup R) :
    (((quotientDetKernelMulEquiv R).symm q).1 :
      StableGL R ⧸ stableElementarySubgroup R) =
      q * (quotientRankOneUnits R (quotientDet R q))⁻¹ := by rfl

/-- The unit coordinate of a quotient class is its determinant. -/
@[simp]
theorem quotientDetKernelMulEquiv_symm_apply_snd (R : Type u) [CommRing R]
    (q : StableGL R ⧸ stableElementarySubgroup R) :
    ((quotientDetKernelMulEquiv R).symm q).2 = quotientDet R q := by rfl

/-- The determinant of a product-coordinate class is its unit coordinate. -/
@[simp]
theorem quotientDet_quotientDetKernelMulEquiv (R : Type u) [CommRing R]
    (pair : (quotientDet R).ker × Rˣ) :
    quotientDet R (quotientDetKernelMulEquiv R pair) = pair.2 := by
  rw [quotientDetKernelMulEquiv_apply, map_mul,
    MonoidHom.mem_ker.mp pair.1.property, quotientDet_quotientRankOneUnits, one_mul]

/-- The kernel factor is included without altering its quotient class. -/
@[simp]
theorem quotientDetKernelMulEquiv_ker (R : Type u) [CommRing R]
    (kernel : (quotientDet R).ker) :
    quotientDetKernelMulEquiv R (kernel, 1) =
      (kernel : StableGL R ⧸ stableElementarySubgroup R) := by
  simp only [quotientDetKernelMulEquiv_apply, map_one, mul_one]

/-- The unit factor is the existing rank-one section. -/
@[simp]
theorem quotientDetKernelMulEquiv_units (R : Type u) [CommRing R]
    (unit : Rˣ) :
    quotientDetKernelMulEquiv R (1, unit) = quotientRankOneUnits R unit := by
  simp only [quotientDetKernelMulEquiv_apply, OneMemClass.coe_one, one_mul]

/-- The kernel and unit factors of a quotient class are unique. -/
theorem quotientDetKernelMulEquiv_unique (R : Type u) [CommRing R]
    (first second : (quotientDet R).ker) (firstUnit secondUnit : Rˣ) :
    ((first : StableGL R ⧸ stableElementarySubgroup R) *
        quotientRankOneUnits R firstUnit =
      (second : StableGL R ⧸ stableElementarySubgroup R) *
        quotientRankOneUnits R secondUnit) ↔
      first = second ∧ firstUnit = secondUnit := by
  constructor
  · intro equality
    have coordinates : (first, firstUnit) = (second, secondUnit) :=
      (quotientDetKernelMulEquiv R).injective
        (by simpa only [quotientDetKernelMulEquiv_apply] using equality)
    exact ⟨congrArg Prod.fst coordinates, congrArg Prod.snd coordinates⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Coefficient maps preserve the determinant-normalized kernel coordinate. -/
theorem quotientDetKernelMulEquiv_symm_map_fst {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (q : StableGL R ⧸ stableElementarySubgroup R) :
    (((quotientDetKernelMulEquiv S).symm
        (QuotientGroup.map (stableElementarySubgroup R)
          (stableElementarySubgroup S) (map f)
          ((Subgroup.map_le_iff_le_comap).mp (map_elementarySubgroup_le f)) q)).1 :
      StableGL S ⧸ stableElementarySubgroup S) =
      QuotientGroup.map (stableElementarySubgroup R)
        (stableElementarySubgroup S) (map f)
        ((Subgroup.map_le_iff_le_comap).mp (map_elementarySubgroup_le f))
          (((quotientDetKernelMulEquiv R).symm q).1 :
            StableGL R ⧸ stableElementarySubgroup R) := by
  rw [quotientDetKernelMulEquiv_symm_apply_fst,
    quotientDetKernelMulEquiv_symm_apply_fst, map_mul, map_inv,
    quotientDet_map, quotientRankOneUnits_map]

/-- The unit coordinate changes coefficients by the usual map on units. -/
theorem quotientDetKernelMulEquiv_symm_map_snd {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (q : StableGL R ⧸ stableElementarySubgroup R) :
    ((quotientDetKernelMulEquiv S).symm
      (QuotientGroup.map (stableElementarySubgroup R)
        (stableElementarySubgroup S) (map f)
        ((Subgroup.map_le_iff_le_comap).mp (map_elementarySubgroup_le f)) q)).2 =
      Units.map f ((quotientDetKernelMulEquiv R).symm q).2 := by
  rw [quotientDetKernelMulEquiv_symm_apply_snd,
    quotientDetKernelMulEquiv_symm_apply_snd, quotientDet_map]

/-- The canonical abelianization map carries the product factors to the kernel
class and the existing rank-one class, respectively. -/
theorem abelianizationEquiv_quotientDetKernelMulEquiv (R : Type u) [CommRing R]
    (pair : (quotientDet R).ker × Rˣ) :
    stableElementaryAbelianizationEquiv R (quotientDetKernelMulEquiv R pair) =
      stableElementaryAbelianizationEquiv R
        (pair.1 : StableGL R ⧸ stableElementarySubgroup R) *
          abelianizationRankOneUnits R pair.2 := by
  rw [quotientDetKernelMulEquiv_apply, map_mul,
    abelianizationEquiv_quotientRankOneUnits]

end StableGL
end Matrix.GeneralLinearGroup
