/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.NilIdeal
public import GeneralLinearGroups.NilpotentExpLog
public import GeneralLinearGroups.PrincipalUnits

/-!
# Exponential coordinates on principal units of a nil ideal

For a left ideal whose elements are nilpotent, exponential and logarithm restrict
to a plain equivalence between its elements and the existing principal-unit
stabilizer. No uniform exponent or two-sidedness is required. A vanishing ideal
power gives a specialization, rather than replacing pointwise nilness.

`TwoSidedIdeal.IsNil.expLogEquiv` specializes this construction to the existing
nil two-sided ideal predicate. Two-sidedness is needed for compatibility with
conjugation by arbitrary ambient units, not for the equivalence itself.
This is not an additive-to-multiplicative group equivalence.

## References

The exponential and its unit proof are from Mathlib's formalization in
`Mathlib.RingTheory.Nilpotent.Exp`. The logarithm and global correspondence are
from `GeneralLinearGroups.NilpotentExpLog`; the principal-unit stabilizer and
membership API are from `GeneralLinearGroups.PrincipalUnits`.
-/

@[expose] public section

universe u v

variable {R : Type u} [Ring R] [Algebra ℚ R]
variable {S : Type v} [Ring S] [Algebra ℚ S]

private theorem log_mem_leftIdeal (I : Ideal R)
    (u : {u : Rˣ // IsNilpotent ((u : R) - 1)}) (hu : (u.val : R) - 1 ∈ I) :
    Units.log u ∈ I := by
  obtain ⟨N, hN⟩ := u.property
  rw [Units.log_eq_sum u N hN]
  apply I.sum_mem
  intro n hn
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ (I.pow_mem_of_mem hu n (Finset.mem_Ico.mp hn).1)

namespace IsNilpotent

/-- Exponential preserves the coordinate in every left ideal. -/
theorem exp_sub_one_mem (I : Ideal R) {x : R} (hx : IsNilpotent x)
    (hxI : x ∈ I) : exp x - 1 ∈ I := by
  obtain ⟨N, hN⟩ := hx
  have hN' : x ^ (N + 1) = 0 := by rw [_root_.pow_succ, hN, zero_mul]
  rw [exp_eq_sum hN', Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    add_sub_cancel_right]
  apply I.sum_mem
  intro n _
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ (I.pow_mem_of_mem hxI (n + 1) (Nat.succ_pos n))

/-- Membership of an exponential coordinate is exactly membership of its nilpotent input. -/
theorem exp_sub_one_mem_iff (I : Ideal R) {x : R} (hx : IsNilpotent x) :
    exp x - 1 ∈ I ↔ x ∈ I := by
  constructor
  · intro h
    have hlog := log_mem_leftIdeal I
      ⟨hx.expUnit, by simpa using hx.isNilpotent_exp_sub_one⟩
      (by simpa only [coe_expUnit] using h)
    simpa only [log_expUnit] using hlog
  · exact exp_sub_one_mem I hx

end IsNilpotent

namespace Units

/-- Logarithm preserves membership of the coordinate in every left ideal. -/
theorem log_mem (I : Ideal R)
    (u : {u : Rˣ // IsNilpotent ((u : R) - 1)}) (hu : (u.val : R) - 1 ∈ I) :
    log u ∈ I := by
  exact log_mem_leftIdeal I u hu

/-- Membership of a logarithm is exactly membership of the coordinate at one. -/
theorem log_mem_iff (I : Ideal R)
    (u : {u : Rˣ // IsNilpotent ((u : R) - 1)}) :
    log u ∈ I ↔ (u.val : R) - 1 ∈ I := by
  constructor
  · intro h
    simpa only [IsNilpotent.exp_log] using
      IsNilpotent.exp_sub_one_mem I (isNilpotent_log u) h
  · exact log_mem I u

end Units

namespace Ideal

omit [Algebra ℚ R] in
private theorem principalUnit_nilpotent (I : Ideal R)
    (hNil : ∀ x : R, x ∈ I → IsNilpotent x)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ I)) :
    IsNilpotent ((u.val : R) - 1) :=
  hNil _ ((I.mem_stabilizer_quotient_one u.val).mp u.property)

/-- Exponential coordinates identify a pointwise-nil left ideal with its principal units
as types. -/
noncomputable def expLogEquivOfForallIsNilpotent (I : Ideal R)
    (hNil : ∀ x : R, x ∈ I → IsNilpotent x) :
    I ≃ MulAction.stabilizer Rˣ (1 : R ⧸ I) where
  toFun x := ⟨(hNil x.val x.property).expUnit, by
    apply (I.mem_stabilizer_quotient_one _).mpr
    simpa only [IsNilpotent.coe_expUnit] using
      IsNilpotent.exp_sub_one_mem I (hNil x.val x.property) x.property⟩
  invFun u := ⟨Units.log ⟨u.val, by exact principalUnit_nilpotent I hNil u⟩, by
    exact Units.log_mem I ⟨u.val, principalUnit_nilpotent I hNil u⟩
      ((I.mem_stabilizer_quotient_one u.val).mp u.property)⟩
  left_inv x := Subtype.ext (IsNilpotent.log_expUnit (hNil x.val x.property))
  right_inv u := by
    exact Subtype.ext (IsNilpotent.expUnit_log
      ⟨u.val, principalUnit_nilpotent I hNil u⟩)

/-- The principal-unit equivalence evaluates to the exponential unit. -/
@[simp] theorem expLogEquivOfForallIsNilpotent_apply_coe (I : Ideal R)
    (hNil : ∀ x : R, x ∈ I → IsNilpotent x) (x : I) :
    (I.expLogEquivOfForallIsNilpotent hNil x).val = (hNil x.val x.property).expUnit := rfl

/-- The inverse principal-unit equivalence evaluates to the logarithm. -/
@[simp] theorem expLogEquivOfForallIsNilpotent_symm_apply_coe (I : Ideal R)
    (hNil : ∀ x : R, x ∈ I → IsNilpotent x)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ I)) :
    ((I.expLogEquivOfForallIsNilpotent hNil).symm u).val =
      Units.log ⟨u.val, by exact principalUnit_nilpotent I hNil u⟩ := rfl

/-- The zero coordinate corresponds to the identity principal unit. -/
@[simp] theorem expLogEquivOfForallIsNilpotent_zero (I : Ideal R)
    (hNil : ∀ x : R, x ∈ I → IsNilpotent x) :
    I.expLogEquivOfForallIsNilpotent hNil 0 = 1 := by
  apply Subtype.ext
  exact IsNilpotent.expUnit_zero

/-- The identity principal unit has zero logarithm. -/
@[simp] theorem expLogEquivOfForallIsNilpotent_symm_one (I : Ideal R)
    (hNil : ∀ x : R, x ∈ I → IsNilpotent x) :
    (I.expLogEquivOfForallIsNilpotent hNil).symm 1 = 0 := by
  apply Subtype.ext
  exact Units.log_one

/-- Negation corresponds to inversion in the principal-unit subgroup. -/
theorem expLogEquivOfForallIsNilpotent_neg (I : Ideal R)
    (hNil : ∀ x : R, x ∈ I → IsNilpotent x) (x : I) :
    I.expLogEquivOfForallIsNilpotent hNil (-x) =
      (I.expLogEquivOfForallIsNilpotent hNil x)⁻¹ := by
  apply Subtype.ext
  exact IsNilpotent.expUnit_neg (hNil x.val x.property)

/-- Inversion of a principal unit corresponds to negation of its logarithm. -/
theorem expLogEquivOfForallIsNilpotent_symm_inv (I : Ideal R)
    (hNil : ∀ x : R, x ∈ I → IsNilpotent x)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ I)) :
    (I.expLogEquivOfForallIsNilpotent hNil).symm u⁻¹ =
      -(I.expLogEquivOfForallIsNilpotent hNil).symm u := by
  apply Subtype.ext
  exact Units.log_inv ⟨u.val, principalUnit_nilpotent I hNil u⟩

/-- Exponential ideal coordinates commute with rational algebra maps carrying the ideals
into one another. -/
theorem expLogEquivOfForallIsNilpotent_map (I : Ideal R) (J : Ideal S)
    (hI : ∀ x : R, x ∈ I → IsNilpotent x) (hJ : ∀ y : S, y ∈ J → IsNilpotent y)
    (f : R →ₐ[ℚ] S) (hIJ : ∀ x : R, x ∈ I → f x ∈ J) (x : I) :
    (J.expLogEquivOfForallIsNilpotent hJ ⟨f x.val, hIJ x.val x.property⟩).val =
      Units.map f.toMonoidHom (I.expLogEquivOfForallIsNilpotent hI x).val := by
  exact (IsNilpotent.map_expUnit (hI x.val x.property) f).symm

private theorem map_principalUnit_mem (I : Ideal R) (J : Ideal S)
    (f : R →ₐ[ℚ] S) (hIJ : ∀ x : R, x ∈ I → f x ∈ J)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ I)) :
    Units.map f.toMonoidHom u.val ∈ MulAction.stabilizer Sˣ (1 : S ⧸ J) := by
  apply (J.mem_stabilizer_quotient_one _).mpr
  change f (u.val : R) - 1 ∈ J
  simpa only [map_sub, map_one] using
    hIJ _ ((I.mem_stabilizer_quotient_one u.val).mp u.property)

/-- Principal-unit logarithms commute with rational algebra maps carrying the ideals
into one another. -/
theorem expLogEquivOfForallIsNilpotent_symm_map (I : Ideal R) (J : Ideal S)
    (hI : ∀ x : R, x ∈ I → IsNilpotent x) (hJ : ∀ y : S, y ∈ J → IsNilpotent y)
    (f : R →ₐ[ℚ] S) (hIJ : ∀ x : R, x ∈ I → f x ∈ J)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ I)) :
    ((J.expLogEquivOfForallIsNilpotent hJ).symm
      ⟨Units.map f.toMonoidHom u.val, by exact map_principalUnit_mem I J f hIJ u⟩).val =
      f ((I.expLogEquivOfForallIsNilpotent hI).symm u).val := by
  exact Units.log_map f ⟨u.val, principalUnit_nilpotent I hI u⟩

/-- The principal-unit equivalence specialized to a uniformly nilpotent left ideal. -/
noncomputable def expLogEquivOfPowEqBot (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥) :
    I ≃ MulAction.stabilizer Rˣ (1 : R ⧸ I) :=
  I.expLogEquivOfForallIsNilpotent fun x hx =>
    ⟨N, by simpa only [hN, Ideal.mem_bot] using (Ideal.pow_mem_pow hx N)⟩

/-- Uniform nilpotence gives the pointwise-nil equivalence, independently of the bound. -/
@[simp] theorem expLogEquivOfPowEqBot_eq (I : Ideal R) (N : ℕ) (hN : I ^ N = ⊥)
    (hNil : ∀ x : R, x ∈ I → IsNilpotent x) :
    I.expLogEquivOfPowEqBot N hN = I.expLogEquivOfForallIsNilpotent hNil := rfl

end Ideal

namespace TwoSidedIdeal

/-- The exponential equivalence for the existing nil two-sided ideal predicate. -/
noncomputable def IsNil.expLogEquiv {I : TwoSidedIdeal R} (hI : I.IsNil) :
    I.asIdeal ≃ MulAction.stabilizer Rˣ (1 : R ⧸ I.asIdeal) :=
  I.asIdeal.expLogEquivOfForallIsNilpotent fun x hx => hI x (mem_asIdeal.mp hx)

/-- The nil two-sided ideal specialization evaluates to the same exponential unit. -/
@[simp] theorem IsNil.expLogEquiv_apply_coe {I : TwoSidedIdeal R} (hI : I.IsNil)
    (x : I.asIdeal) :
    (hI.expLogEquiv x).val = (hI _ (mem_asIdeal.mp x.property)).expUnit := rfl

/-- The inverse specialization evaluates to the same logarithm. -/
@[simp] theorem IsNil.expLogEquiv_symm_apply_coe {I : TwoSidedIdeal R} (hI : I.IsNil)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ I.asIdeal)) :
    (hI.expLogEquiv.symm u).val = Units.log
      ⟨u.val, hI _ (mem_asIdeal.mp
        ((I.asIdeal.mem_stabilizer_quotient_one u.val).mp u.property))⟩ := rfl

omit [Algebra ℚ R] in
private theorem conj_mem_asIdeal (I : TwoSidedIdeal R) (x : I.asIdeal) (a : Rˣ) :
    (a : R) * x.val * (↑a⁻¹ : R) ∈ I.asIdeal :=
  mem_asIdeal.mpr (I.mul_mem_right _ _
    (I.mul_mem_left _ _ (mem_asIdeal.mp x.property)))

/-- Exponential ideal coordinates commute with conjugation by arbitrary ambient units. -/
theorem IsNil.expLogEquiv_conj {I : TwoSidedIdeal R} (hI : I.IsNil)
    (x : I.asIdeal) (a : Rˣ) :
    (hI.expLogEquiv
      ⟨(a : R) * x.val * (↑a⁻¹ : R), by exact conj_mem_asIdeal I x a⟩).val =
      a * (hI.expLogEquiv x).val * a⁻¹ := by
  exact IsNilpotent.expUnit_conj (hI _ (mem_asIdeal.mp x.property)) a

omit [Algebra ℚ R] in
private theorem conj_principalUnit_mem (I : TwoSidedIdeal R)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ I.asIdeal)) (a : Rˣ) :
    a * u.val * a⁻¹ ∈ MulAction.stabilizer Rˣ (1 : R ⧸ I.asIdeal) := by
  apply (I.asIdeal.mem_stabilizer_quotient_one _).mpr
  change (a : R) * (u.val : R) * (↑a⁻¹ : R) - 1 ∈ I.asIdeal
  have hu := (I.asIdeal.mem_stabilizer_quotient_one u.val).mp u.property
  simpa only [mul_sub, sub_mul, mul_one, Units.mul_inv] using
    conj_mem_asIdeal I ⟨(u.val : R) - 1, hu⟩ a

/-- Principal-unit logarithms commute with conjugation by arbitrary ambient units. -/
theorem IsNil.expLogEquiv_symm_conj {I : TwoSidedIdeal R} (hI : I.IsNil)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ I.asIdeal)) (a : Rˣ) :
    (hI.expLogEquiv.symm ⟨a * u.val * a⁻¹, by exact conj_principalUnit_mem I u a⟩).val =
      (a : R) * (hI.expLogEquiv.symm u).val * (↑a⁻¹ : R) := by
  exact Units.log_conj ⟨u.val, hI _ (mem_asIdeal.mp
    ((I.asIdeal.mem_stabilizer_quotient_one u.val).mp u.property))⟩ a

end TwoSidedIdeal
