/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Scalar local homomorphisms and independent kernel controls

The reduction of two-by-two matrices from `ZMod 4` to `ZMod 2` has a nonzero
square-zero kernel, and both matrix rings contain noncommuting elements and
explicit units and nonunits. These kernel and surjectivity facts are proved
independently of unit reflection. The scalar class is consumed through
Mathlib's unit equivalence and surjectivity of the induced units map.

## References

* Mathlib, `Algebra.Group.Units.Hom`, `RingTheory.LocalRing.RingHom.Basic`,
  `RingTheory.TwoSidedIdeal.Kernel`, `Data.ZMod.Basic` and `Data.Matrix.Basis`.
* `GeneralLinearGroups.NilIdeal`, `QuasiregularQuotient`, `Elementary` and
  `Whitehead`, for pointwise nil ideals, unit reflection and explicit matrix lifts.
-/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.LocalHom

universe u v

section Consumers

variable {R : Type u} {S : Type v} [Ring R] [Semiring S]

example (f : R →+* S) (hf : Function.Surjective f)
    (hker : (TwoSidedIdeal.ker f).IsNil) : IsLocalHom f :=
  f.isLocalHom_of_surjective_of_isQuasiregular_ker hf hker.isQuasiregular

example (f : R →+* S) (hf : Function.Surjective f)
    (hker : (TwoSidedIdeal.ker f).IsQuasiregular) (a : R) :
    IsUnit (f a) ↔ IsUnit a := by
  let : IsLocalHom f := f.isLocalHom_of_surjective_of_isQuasiregular_ker hf hker
  exact isUnit_map_iff f a

example (f : R →+* S) (hf : Function.Surjective f)
    (hker : (TwoSidedIdeal.ker f).IsQuasiregular) :
    Function.Surjective (Units.map f.toMonoidHom) :=
  IsLocalRing.surjective_units_map_of_local_ringHom f hf
    (f.isLocalHom_of_surjective_of_isQuasiregular_ker hf hker)

end Consumers

section MatrixReduction

private def reduction : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)

private def reductionMatrix : Matrix (Fin 2) (Fin 2) (ZMod 4) →+*
    Matrix (Fin 2) (Fin 2) (ZMod 2) := reduction.mapMatrix

@[simp] private theorem reductionMatrix_apply
    (A : Matrix (Fin 2) (Fin 2) (ZMod 4)) (i j : Fin 2) :
    reductionMatrix A i j = reduction (A i j) := rfl

private theorem reduction_two : reduction 2 = 0 := by decide

private theorem reduction_surjective : Function.Surjective reduction :=
  ZMod.castHom_surjective (show 2 ∣ 4 by decide)

private theorem reductionMatrix_surjective : Function.Surjective reductionMatrix := by
  intro A
  exact ⟨Matrix.GeneralLinearGroup.liftMatrix reduction reduction_surjective A,
    Matrix.GeneralLinearGroup.mapMatrix_liftMatrix reduction reduction_surjective A⟩

private theorem reduction_kernel_mul_zero :
    ∀ a b : ZMod 4, reduction a = 0 → reduction b = 0 → a * b = 0 := by
  decide

private theorem reductionMatrix_kernel_mul_zero
    (A B : Matrix (Fin 2) (Fin 2) (ZMod 4))
    (hA : A ∈ TwoSidedIdeal.ker reductionMatrix)
    (hB : B ∈ TwoSidedIdeal.ker reductionMatrix) : A * B = 0 := by
  have hA0 := (TwoSidedIdeal.mem_ker reductionMatrix).mp hA
  have hB0 := (TwoSidedIdeal.mem_ker reductionMatrix).mp hB
  ext i j
  change (∑ k, A i k * B k j) = 0
  apply Finset.sum_eq_zero
  intro k _
  exact reduction_kernel_mul_zero (A i k) (B k j)
    (congrFun (congrFun hA0 i) k) (congrFun (congrFun hB0 k) j)

private theorem reductionMatrix_kernel_isNil :
    (TwoSidedIdeal.ker reductionMatrix).IsNil := by
  intro A hA
  exact ⟨2, by simpa only [pow_two] using reductionMatrix_kernel_mul_zero A A hA hA⟩

private theorem reductionMatrix_kernel_isQuasiregular :
    (TwoSidedIdeal.ker reductionMatrix).IsQuasiregular :=
  reductionMatrix_kernel_isNil.isQuasiregular

private theorem two_single_mem_kernel :
    Matrix.single (0 : Fin 2) (0 : Fin 2) (2 : ZMod 4) ∈
      TwoSidedIdeal.ker reductionMatrix := by
  rw [TwoSidedIdeal.mem_ker reductionMatrix]
  change (Matrix.single (0 : Fin 2) (0 : Fin 2) (2 : ZMod 4)).map reduction = 0
  simp only [Matrix.map_single, reduction_two, Matrix.single_zero]

private theorem two_single_ne_zero :
    Matrix.single (0 : Fin 2) (0 : Fin 2) (2 : ZMod 4) ≠ 0 := by
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod 4) => A 0 0) h
  have htwo : (2 : ZMod 4) ≠ 0 := by decide
  apply htwo
  simpa only [Matrix.single_apply_same, Matrix.zero_apply] using h00

private theorem matrix_noncommuting {R : Type u} [Ring R] [Nontrivial R] :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : R) *
        Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : R) ≠
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : R) *
        Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : R) := by
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 0 0) h
  norm_num [Matrix.single_mul_single_same, Matrix.single_apply] at h00

private theorem matrix_one_add_single_isUnit {R : Type u} [Ring R] :
    IsUnit (1 + Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : R)) := by
  refine ⟨Matrix.GeneralLinearGroup.elementaryUnit
    (0 : Fin 2) (1 : Fin 2) (by decide) (1 : R), ?_⟩
  exact Matrix.GeneralLinearGroup.elementaryUnit_val
    (0 : Fin 2) (1 : Fin 2) (by decide) (1 : R)

private theorem matrix_single_not_isUnit {R : Type u} [Ring R] [Nontrivial R] :
    ¬ IsUnit (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : R)) := by
  apply IsNilpotent.not_isUnit
  refine ⟨2, ?_⟩
  rw [pow_two]
  exact Matrix.single_mul_single_of_ne
    (1 : R) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) (by decide) (1 : R)

/-- Entrywise reduction of two-by-two matrices from `ZMod 4` to `ZMod 2` is
surjective and has a nil, quasi-regular, square-zero kernel containing the
nonzero matrix `2E₀₀`. -/
theorem zmod_four_two_mapMatrix_surjective_ker_square_zero :
    let f : Matrix (Fin 2) (Fin 2) (ZMod 4) →+* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
      (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)).mapMatrix
    Function.Surjective f ∧
      (TwoSidedIdeal.ker f).IsNil ∧
      (TwoSidedIdeal.ker f).IsQuasiregular ∧
      Matrix.single (0 : Fin 2) (0 : Fin 2) (2 : ZMod 4) ≠ 0 ∧
      Matrix.single (0 : Fin 2) (0 : Fin 2) (2 : ZMod 4) ∈ TwoSidedIdeal.ker f ∧
      (∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 4),
        A ∈ TwoSidedIdeal.ker f → B ∈ TwoSidedIdeal.ker f → A * B = 0) :=
  ⟨reductionMatrix_surjective, reductionMatrix_kernel_isNil,
    reductionMatrix_kernel_isQuasiregular, two_single_ne_zero, two_single_mem_kernel,
    reductionMatrix_kernel_mul_zero⟩

example : Matrix.single (0 : Fin 2) (0 : Fin 2) (2 : ZMod 4) =
    (2 : Matrix (Fin 2) (Fin 2) (ZMod 4)) *
      Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ZMod 4) := by
  rw [two_mul, ← Matrix.single_add]
  norm_num

example :
    (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 4) *
        Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ZMod 4) ≠
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ZMod 4) *
        Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 4)) ∧
    (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 2) *
        Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ZMod 2) ≠
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ZMod 2) *
        Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 2)) := by
  have : Fact (1 < 4) := ⟨by decide⟩
  have : Fact (1 < 2) := ⟨by decide⟩
  exact ⟨matrix_noncommuting, matrix_noncommuting⟩

example : IsUnit (1 + Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 4)) ∧
    ¬ IsUnit (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 4)) ∧
    IsUnit (1 + Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 2)) ∧
    ¬ IsUnit (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod 2)) := by
  have : Fact (1 < 4) := ⟨by decide⟩
  have : Fact (1 < 2) := ⟨by decide⟩
  exact ⟨matrix_one_add_single_isUnit, matrix_single_not_isUnit,
    matrix_one_add_single_isUnit, matrix_single_not_isUnit⟩

example : IsLocalHom reductionMatrix ∧
    (∀ A : Matrix (Fin 2) (Fin 2) (ZMod 4), IsUnit (reductionMatrix A) ↔ IsUnit A) ∧
    Function.Surjective (Units.map reductionMatrix.toMonoidHom) := by
  let : IsLocalHom reductionMatrix :=
    reductionMatrix.isLocalHom_of_surjective_of_isQuasiregular_ker
      reductionMatrix_surjective reductionMatrix_kernel_isQuasiregular
  exact ⟨inferInstance, isUnit_map_iff reductionMatrix,
    IsLocalRing.surjective_units_map_of_local_ringHom reductionMatrix
      reductionMatrix_surjective inferInstance⟩

end MatrixReduction

end GeneralLinearGroupsTests.LocalHom
