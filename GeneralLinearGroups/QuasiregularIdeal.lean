/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Quasi-regular two-sided ideals

This file defines a quasi-regular two-sided ideal as one whose elements are all
quasi-regular. It proves that a globally quantified right-quasi-inverse
condition is already two-sided, without assuming that the ambient ring is
directly finite.
-/

set_option warningAsError true

@[expose] public section

namespace TwoSidedIdeal

universe u

variable {R : Type u} [Ring R]

/-- A two-sided ideal is quasi-regular if each of its elements is
quasi-regular in the ambient ring. -/
def IsQuasiregular (I : TwoSidedIdeal R) : Prop :=
  ∀ x : R, x ∈ I → _root_.IsQuasiregular x

/-- A two-sided ideal is right quasi-regular if each `x` in it has a
right quasi-inverse `y` in the ideal, so `(1 + x) * (1 + y) = 1`. -/
def IsRightQuasiregular (I : TwoSidedIdeal R) : Prop :=
  ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x + y + x * y = 0

/-- An ideal is quasi-regular exactly when `1 + x` is a unit for every element
`x` of the ideal. -/
theorem isQuasiregular_iff_forall_isUnit_one_add (I : TwoSidedIdeal R) :
    I.IsQuasiregular ↔ ∀ x : R, x ∈ I → IsUnit (1 + x) := by
  constructor
  · intro h x hx
    exact isQuasiregular_iff_isUnit.mp (h x hx)
  · intro h x hx
    exact isQuasiregular_iff_isUnit.mpr (h x hx)

/-- If `1 + x` is a unit and `x` lies in a two-sided ideal, a right
quasi-inverse of `x` can be chosen in that ideal. -/
theorem exists_rightQuasiInverse_mem_of_isUnit_one_add
    (I : TwoSidedIdeal R) {x : R} (hxI : x ∈ I) (hx : IsUnit (1 + x)) :
    ∃ y : R, y ∈ I ∧ x + y + x * y = 0 := by
  have hq : _root_.IsQuasiregular x := isQuasiregular_iff_isUnit.mpr hx
  obtain ⟨y, hyRight, _hyLeft⟩ := isQuasiregular_iff.mp hq
  have hxyI : x + x * y ∈ I :=
    I.add_mem hxI (I.mul_mem_right x y hxI)
  have hyEq : y = -(x + x * y) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [add_assoc, add_left_comm, add_comm] using hyRight
  refine ⟨y, ?_, ?_⟩
  · rw [hyEq]
    exact I.neg_mem hxyI
  · simpa [add_comm] using hyRight

/-- In a right quasi-regular two-sided ideal, every element has a two-sided
quasi-inverse in the ideal. The global hypothesis is used a second time on the
defect `y + x + y * x`. -/
theorem exists_quasiInverse_mem_of_isRightQuasiregular
    {I : TwoSidedIdeal R} (h : I.IsRightQuasiregular)
    {x : R} (hxI : x ∈ I) :
    ∃ y : R, y ∈ I ∧
      x + y + x * y = 0 ∧ x + y + y * x = 0 := by
  obtain ⟨y, hyI, hxy⟩ := h x hxI
  have hab : (1 + x) * (1 + y) = 1 := by
    calc
      (1 + x) * (1 + y) = 1 + (x + y + x * y) := by noncomm_ring
      _ = 1 := by rw [hxy, add_zero]
  let z : R := y + x + y * x
  have hzI : z ∈ I :=
    I.add_mem (I.add_mem hyI hxI) (I.mul_mem_right y x hyI)
  obtain ⟨w, _hwI, hzw⟩ := h z hzI
  have hbaRight : ((1 + y) * (1 + x)) * (1 + w) = 1 := by
    calc
      ((1 + y) * (1 + x)) * (1 + w) =
          (1 + z) * (1 + w) := by
            congr 1
            simp only [z]
            noncomm_ring
      _ = 1 + (z + w + z * w) := by noncomm_ring
      _ = 1 := by rw [hzw, add_zero]
  have hidem :
      ((1 + y) * (1 + x)) * ((1 + y) * (1 + x)) =
        (1 + y) * (1 + x) := by
    calc
      ((1 + y) * (1 + x)) * ((1 + y) * (1 + x)) =
          (1 + y) * ((1 + x) * (1 + y)) * (1 + x) := by
            simp only [mul_assoc]
      _ = (1 + y) * (1 + x) := by rw [hab]; simp
  have hba : (1 + y) * (1 + x) = 1 := by
    calc
      (1 + y) * (1 + x) = ((1 + y) * (1 + x)) * 1 := by rw [mul_one]
      _ = ((1 + y) * (1 + x)) *
          (((1 + y) * (1 + x)) * (1 + w)) := by rw [hbaRight]
      _ = (((1 + y) * (1 + x)) * ((1 + y) * (1 + x))) *
          (1 + w) :=
        (mul_assoc ((1 + y) * (1 + x)) ((1 + y) * (1 + x)) (1 + w)).symm
      _ = ((1 + y) * (1 + x)) * (1 + w) := by rw [hidem]
      _ = 1 := hbaRight
  refine ⟨y, hyI, hxy, ?_⟩
  have hyx : (1 + y) * (1 + x) = 1 + (x + y + y * x) := by
    noncomm_ring
  rw [hyx] at hba
  exact add_left_cancel (hba.trans (add_zero 1).symm)

/-- For a two-sided ideal, globally quantified right quasi-regularity is
equivalent to quasi-regularity. -/
theorem isQuasiregular_iff_isRightQuasiregular (I : TwoSidedIdeal R) :
    I.IsQuasiregular ↔ I.IsRightQuasiregular := by
  constructor
  · intro h x hxI
    exact I.exists_rightQuasiInverse_mem_of_isUnit_one_add hxI
      (isQuasiregular_iff_isUnit.mp (h x hxI))
  · intro h x hxI
    obtain ⟨y, _hyI, hxy, hyx⟩ :=
      exists_quasiInverse_mem_of_isRightQuasiregular h hxI
    exact isQuasiregular_iff.mpr
      ⟨y, by simpa [add_comm] using hxy, hyx⟩

/-- Right quasi-regularity of a two-sided ideal is equivalent to every `1 + x`
being a unit. -/
theorem isRightQuasiregular_iff_forall_isUnit_one_add (I : TwoSidedIdeal R) :
    I.IsRightQuasiregular ↔ ∀ x : R, x ∈ I → IsUnit (1 + x) :=
  (I.isQuasiregular_iff_isRightQuasiregular).symm.trans
    I.isQuasiregular_iff_forall_isUnit_one_add

/-- The Jacobson radical, bundled as a two-sided ideal, is quasi-regular.

In the noncommutative case, the Jacobson characterization first gives a left
inverse of `1 + x`. Applying it again to the difference between that inverse
and `1` shows that the inverse is two-sided. -/
theorem ringJacobson_isQuasiregular :
    ((Ring.jacobson R).toTwoSided).IsQuasiregular := by
  rw [isQuasiregular_iff_forall_isUnit_one_add]
  intro x hx
  have hxJ : x ∈ Ring.jacobson R := Ideal.mem_toTwoSided.mp hx
  have hxBot : x ∈ (⊥ : Ideal R).jacobson := by
    simpa only [Ideal.jacobson_bot] using hxJ
  obtain ⟨z, hz⟩ := Ideal.exists_mul_add_sub_mem_of_mem_jacobson x hxBot
  change z * (x + 1) - 1 = 0 at hz
  have hzx : z * (1 + x) = 1 := by
    simpa only [add_comm] using sub_eq_zero.mp hz
  let y : R := z - 1
  have hyEq : y = -(z * x) := by
    apply eq_neg_of_add_eq_zero_left
    calc
      y + z * x = z * (1 + x) - 1 := by
        simp only [y]
        noncomm_ring
      _ = 0 := sub_eq_zero.mpr hzx
  have hyJ : y ∈ Ring.jacobson R := by
    rw [hyEq]
    exact (Ring.jacobson R).neg_mem ((Ring.jacobson R).mul_mem_left z hxJ)
  have hyBot : y ∈ (⊥ : Ideal R).jacobson := by
    simpa only [Ideal.jacobson_bot] using hyJ
  obtain ⟨w, hw⟩ := Ideal.exists_mul_add_sub_mem_of_mem_jacobson y hyBot
  change w * (y + 1) - 1 = 0 at hw
  have hwz : w * z = 1 := by
    have : y + 1 = z := by simp [y]
    rw [this] at hw
    exact sub_eq_zero.mp hw
  have hwEq : w = 1 + x := by
    calc
      w = w * 1 := by rw [mul_one]
      _ = w * (z * (1 + x)) := by rw [hzx]
      _ = (w * z) * (1 + x) := by rw [mul_assoc]
      _ = 1 + x := by rw [hwz, one_mul]
  have hxz : (1 + x) * z = 1 := by
    rw [← hwEq]
    exact hwz
  exact ⟨⟨1 + x, z, hxz, hzx⟩, rfl⟩

/-- Every quasi-regular two-sided ideal is contained in the Jacobson radical. -/
theorem IsQuasiregular.le_ringJacobson {I : TwoSidedIdeal R}
    (hI : I.IsQuasiregular) : I ≤ (Ring.jacobson R).toTwoSided := by
  intro x hxI
  have hxBot : x ∈ (⊥ : Ideal R).jacobson := by
    apply Ideal.mem_jacobson_iff.mpr
    intro r
    have hrxI : r * x ∈ I := I.mul_mem_left r x hxI
    obtain ⟨u, hu⟩ := isQuasiregular_iff_isUnit.mp (hI (r * x) hrxI)
    refine ⟨(↑(u⁻¹) : R), ?_⟩
    change (↑(u⁻¹) : R) * r * x + ↑(u⁻¹) - 1 = 0
    have hleft : (↑(u⁻¹) : R) * (1 + r * x) = 1 := by
      rw [← hu]
      exact Units.inv_mul u
    calc
      (↑(u⁻¹) : R) * r * x + ↑(u⁻¹) - 1 =
          (↑(u⁻¹) : R) * (1 + r * x) - 1 := by noncomm_ring
      _ = 0 := sub_eq_zero.mpr hleft
  have hxJ : x ∈ Ring.jacobson R := by
    simpa only [Ideal.jacobson_bot] using hxBot
  exact Ideal.mem_toTwoSided.mpr hxJ

/-- The Jacobson radical is the greatest quasi-regular two-sided ideal. -/
theorem ringJacobson_isGreatest_isQuasiregular :
    IsGreatest {I : TwoSidedIdeal R | I.IsQuasiregular}
      (Ring.jacobson R).toTwoSided :=
  ⟨ringJacobson_isQuasiregular, fun _ hI ↦ hI.le_ringJacobson⟩

end TwoSidedIdeal
