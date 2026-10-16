/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.QuasiregularIdeal
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Principal units and additive ideal layers

For a left ideal `I` in a ring `R`, principal units are the stabilizer of
`[1]` in the quotient left module `R / I` under the scalar action of `Rˣ`.
Thus the carrier uses Mathlib's existing `MulAction.stabilizer`, without a
separate principal-unit subgroup definition. If `I ^ 2 ≤ J`, subtracting `1`
and reducing modulo `J` is a homomorphism to the additive subquotient
`I / (I ∩ J)`, written multiplicatively. Its kernel consists exactly of the
original-ring units that are also congruent to `1` modulo `J`. When
`I ≤ Ring.jacobson R`, every coordinate has a lift with value `1 + x`.

Neither ideal needs to be two-sided. The hypothesis `J ≤ I` is unnecessary:
`Submodule.comap I.subtype J` and the relative subgroup of stabilizers already
take intersections. The quotient by the coordinate homomorphism's kernel
uses Mathlib's canonical normal-subgroup instance. Its kernel equality
identifies this denominator with the relative stabilizer subgroup, without an
additional normality hypothesis or a new quotient construction.

## Limitations

No valuation-ring filtration, uniformizer coordinate or residue-field
identification is supplied. In particular, identifying a discrete valuation
ring's ideal layer with its additive residue field is a separate construction.

## References

The first-order unit multiplication underlying the construction appears in
Fesenko and Vostokov, *Local Fields and Their Extensions*, second edition,
Chapter I, (5.3) and (5.4)(3). The formulation here concerns arbitrary left ideal
layers, not only successive powers of a discrete valuation ring's maximal ideal.
Mathlib supplies the ideal, submodule quotient, unit group and group quotient
APIs. The Jacobson lifting construction uses the noncommutative quasi-regularity
of the Jacobson radical from `GeneralLinearGroups.QuasiregularIdeal`.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [Ring R]

/-- Stabilizing the class of `1` in a quotient left module is precisely
congruence to `1` in the original ring. -/
@[simp]
theorem mem_stabilizer_quotient_one (I : Ideal R) (u : Rˣ) :
    u ∈ MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I) ↔
      (u : R) - 1 ∈ I := by
  rw [MulAction.mem_stabilizer_iff, Units.smul_def, ← Submodule.Quotient.mk_smul]
  simpa only [smul_eq_mul, mul_one] using (Submodule.Quotient.eq I :
    (Submodule.Quotient.mk (u : R) : R ⧸ I) = Submodule.Quotient.mk 1 ↔ _)

/-- Inclusion of left ideals gives inclusion of their principal-unit stabilizers. -/
theorem stabilizer_quotient_one_mono {I J : Ideal R} (h : I ≤ J) :
    MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I) ≤
      MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ J) := by
  intro u hu
  exact (J.mem_stabilizer_quotient_one u).mpr
    (h ((I.mem_stabilizer_quotient_one u).mp hu))

/-- For a two-sided ideal, the stabilizer of `[1]` in the quotient module is
the kernel of reduction on units. Both sides are Mathlib subgroup carriers. -/
theorem stabilizer_quotient_one_eq_ker_unitsMap (I : Ideal R) [I.IsTwoSided] :
    MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I) =
      (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker := by
  ext u
  rw [mem_stabilizer_quotient_one, MonoidHom.mem_ker, Units.ext_iff]
  exact (Ideal.Quotient.eq (I := I)).symm

private theorem isUnit_one_add_of_mem_ringJacobson (x : R)
    (hx : x ∈ Ring.jacobson R) : IsUnit (1 + x) :=
  (TwoSidedIdeal.isQuasiregular_iff_forall_isUnit_one_add
    (Ring.jacobson R).toTwoSided).mp
      TwoSidedIdeal.ringJacobson_isQuasiregular x (Ideal.mem_toTwoSided.mpr hx)

/-- Lift an ideal coordinate to an original-ring principal unit using the
Jacobson-radical condition. Its ring value is `1 + x`. -/
noncomputable def principalUnitsMk (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (x : I) : MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I) :=
  ⟨(show IsUnit (1 + (x : R)) from by
    exact isUnit_one_add_of_mem_ringJacobson (x : R) (hI x.property)).unit, by
    rw [mem_stabilizer_quotient_one, IsUnit.unit_spec]
    simpa only [add_sub_cancel_left] using x.property⟩

/-- The Jacobson lift has value `1 + x` in the original ring. -/
@[simp]
theorem principalUnitsMk_coe (I : Ideal R) (hI : I ≤ Ring.jacobson R) (x : I) :
    ((I.principalUnitsMk hI x).1 : R) = 1 + (x : R) := by
  exact IsUnit.unit_spec _

/-- Subtract `1` from a principal unit and reduce its ideal coordinate modulo `J`.
The square containment kills the product cross term. -/
def principalUnitsToQuotient (I J : Ideal R) (hsq : I ^ 2 ≤ J) :
    MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I) →*
      Multiplicative (I ⧸ Submodule.comap I.subtype J) where
  toFun u := Multiplicative.ofAdd
    (Submodule.Quotient.mk (⟨(u.1 : R) - 1, (I.mem_stabilizer_quotient_one u.1).mp u.property⟩ : I))
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (1 : R) - 1 ∈ J
    simp
  map_mul' := by
    intro a b
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul]
    rw [← Submodule.Quotient.mk_add]
    apply (Submodule.Quotient.eq _).mpr
    change (a.1 : R) * (b.1 : R) - 1 - ((a.1 : R) - 1 + ((b.1 : R) - 1)) ∈ J
    have hcross : ((a.1 : R) - 1) * ((b.1 : R) - 1) ∈ I ^ 2 := by
      rw [Submodule.pow_succ, Submodule.pow_one]
      exact Ideal.mul_mem_mul
        ((I.mem_stabilizer_quotient_one a.1).mp a.property)
        ((I.mem_stabilizer_quotient_one b.1).mp b.property)
    convert hsq hcross using 1
    noncomm_ring

/-- The coordinate homomorphism is given by the value of the unit minus `1`. -/
@[simp]
theorem principalUnitsToQuotient_apply (I J : Ideal R) (hsq : I ^ 2 ≤ J)
    (u : MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I)) :
    I.principalUnitsToQuotient J hsq u = Multiplicative.ofAdd
      (Submodule.Quotient.mk
        (⟨(u.1 : R) - 1, (I.mem_stabilizer_quotient_one u.1).mp u.property⟩ : I)) := rfl

/-- The coordinate of the Jacobson lift of `x` is the class of `x`. -/
@[simp]
theorem principalUnitsToQuotient_mk (I J : Ideal R) (hsq : I ^ 2 ≤ J)
    (hI : I ≤ Ring.jacobson R) (x : I) :
    I.principalUnitsToQuotient J hsq (I.principalUnitsMk hI x) =
      Multiplicative.ofAdd (Submodule.Quotient.mk x) := by
  rw [principalUnitsToQuotient_apply]
  congr 2
  apply Subtype.ext
  simp

/-- The denominator is precisely the subgroup of original-ring units that are
principal modulo both `I` and `J`. When `J ≤ I`, this is the embedded `J` subgroup. -/
theorem principalUnitsToQuotient_ker (I J : Ideal R) (hsq : I ^ 2 ≤ J) :
    (I.principalUnitsToQuotient J hsq).ker =
      (MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ J)).subgroupOf
        (MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I)) := by
  ext u
  rw [MonoidHom.mem_ker, principalUnitsToQuotient_apply, ofAdd_eq_one,
    Submodule.Quotient.mk_eq_zero, Subgroup.mem_subgroupOf]
  exact (J.mem_stabilizer_quotient_one u.1).symm

/-- The smaller congruence subgroup is normal relative to the principal-unit stabilizer
under the square containment, even for left ideals. -/
theorem principalUnits_subgroupOf_normal (I J : Ideal R) (hsq : I ^ 2 ≤ J) :
    ((MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ J)).subgroupOf
      (MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I))).Normal := by
  rw [← principalUnitsToQuotient_ker I J hsq]
  infer_instance

/-- The Jacobson condition supplies a principal-unit lift for every additive
ideal-quotient coordinate; it is not a surjectivity hypothesis on the statement. -/
theorem principalUnitsToQuotient_surjective (I J : Ideal R) (hsq : I ^ 2 ≤ J)
    (hI : I ≤ Ring.jacobson R) :
    Function.Surjective (I.principalUnitsToQuotient J hsq) := by
  intro y
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective
    (Submodule.comap I.subtype J) (Multiplicative.toAdd y)
  exact ⟨I.principalUnitsMk hI x, (I.principalUnitsToQuotient_mk J hsq hI x).trans
    (congrArg Multiplicative.ofAdd hx)⟩

/-- The quotient of original-ring principal units by those principal modulo `J`
is the additive ideal subquotient, written multiplicatively. The denominator is
expressed as a kernel for its canonical normality instance; see
`principalUnitsToQuotient_ker` for its equality with
the relative stabilizer subgroup.

This is the generic first-order ideal-layer construction underlying
Fesenko–Vostokov, Chapter I, (5.4)(3), before identifying a discrete valuation
ring's ideal layer with its additive residue field. -/
noncomputable def principalUnitsQuotientEquiv (I J : Ideal R) (hsq : I ^ 2 ≤ J)
    (hI : I ≤ Ring.jacobson R) :
    MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I) ⧸
        (I.principalUnitsToQuotient J hsq).ker ≃*
      Multiplicative (I ⧸ Submodule.comap I.subtype J) :=
  QuotientGroup.quotientKerEquivOfSurjective (I.principalUnitsToQuotient J hsq)
    (I.principalUnitsToQuotient_surjective J hsq hI)

/-- On an original-unit representative, the quotient equivalence subtracts `1`. -/
@[simp]
theorem principalUnitsQuotientEquiv_mk (I J : Ideal R) (hsq : I ^ 2 ≤ J)
    (hI : I ≤ Ring.jacobson R)
    (u : MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I)) :
    I.principalUnitsQuotientEquiv J hsq hI (QuotientGroup.mk u) =
      I.principalUnitsToQuotient J hsq u := rfl

/-- The inverse sends the class of `x` to the class of the original-ring unit
with value `1 + x`; it does not choose a unit only in a quotient ring. -/
@[simp]
theorem principalUnitsQuotientEquiv_symm_mk (I J : Ideal R) (hsq : I ^ 2 ≤ J)
    (hI : I ≤ Ring.jacobson R) (x : I) :
    (I.principalUnitsQuotientEquiv J hsq hI).symm
        (Multiplicative.ofAdd (Submodule.Quotient.mk x)) =
      QuotientGroup.mk (I.principalUnitsMk hI x) := by
  apply (I.principalUnitsQuotientEquiv J hsq hI).injective
  simp

/-- The quotient equivalence is the descent of the coordinate homomorphism. -/
theorem principalUnitsQuotientEquiv_comp_mk' (I J : Ideal R) (hsq : I ^ 2 ≤ J)
    (hI : I ≤ Ring.jacobson R) :
    (I.principalUnitsQuotientEquiv J hsq hI).toMonoidHom.comp
        (QuotientGroup.mk' (I.principalUnitsToQuotient J hsq).ker) =
      I.principalUnitsToQuotient J hsq := by
  ext u
  exact I.principalUnitsQuotientEquiv_mk J hsq hI u

/-- Two original-unit representatives have the same layer class exactly when
the difference of their ring values belongs to `J`. No Jacobson condition is
needed for this injective description of the quotient. -/
theorem principalUnits_quotient_mk_eq_mk_iff (I J : Ideal R) (hsq : I ^ 2 ≤ J)
    (u v : MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I)) :
    (QuotientGroup.mk u :
        MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I) ⧸
          (I.principalUnitsToQuotient J hsq).ker) =
        QuotientGroup.mk v ↔ (u.1 : R) - (v.1 : R) ∈ J := by
  rw [← (QuotientGroup.kerLift_injective (I.principalUnitsToQuotient J hsq)).eq_iff]
  simp only [QuotientGroup.kerLift_mk, principalUnitsToQuotient_apply,
    Multiplicative.ofAdd.injective.eq_iff, Submodule.Quotient.eq]
  change ((u.1 : R) - 1) - ((v.1 : R) - 1) ∈ J ↔ _
  rw [sub_sub_sub_cancel_right]

end Ideal
