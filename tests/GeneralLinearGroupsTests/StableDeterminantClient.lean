/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.StableDeterminant
public import Mathlib.Data.ZMod.Basic

/-!
# Stable determinant clients

The rank-one image of `-1` survives over the integers and modulo three, while
an elementary matrix is nonidentity but disappears in the elementary quotient.
The determinant-kernel/unit coordinates retain this distinction. The empty
rank, zero ring and a noncommutative coefficient ring exercise the boundaries.
-/

set_option warningAsError true

@[expose] public section

open Matrix.GeneralLinearGroup

private def reduceThree : ℤ →+* ZMod 3 := Int.castRingHom (ZMod 3)

private theorem integerNegOne_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro equality
  have valueEquality := congrArg Units.val equality
  norm_num at valueEquality

private theorem modThreeNegOne_ne_one : (-1 : (ZMod 3)ˣ) ≠ 1 := by
  intro equality
  have valueEquality := congrArg Units.val equality
  have inequality : (-1 : ZMod 3) ≠ 1 := by decide
  exact inequality valueEquality

theorem integerRankOneUnits_ne_one : StableGL.rankOneUnits ℤ (-1) ≠ 1 := by
  intro equality
  apply integerNegOne_ne_one
  have detEquality := congrArg (StableGL.det ℤ) equality
  simpa only [map_one, StableGL.det_rankOneUnits] using detEquality

example : StableGL.quotientRankOneUnits ℤ (-1) ≠ 1 := by
  intro equality
  apply integerNegOne_ne_one
  have detEquality := congrArg (StableGL.quotientDet ℤ) equality
  simpa only [map_one, StableGL.quotientDet_quotientRankOneUnits] using detEquality

example : StableGL.quotientDetKernelMulEquiv ℤ (1, (-1 : ℤˣ)) ≠ 1 := by
  intro equality
  apply integerNegOne_ne_one
  have detEquality := congrArg (StableGL.quotientDet ℤ) equality
  simpa only [map_one, StableGL.quotientDet_quotientDetKernelMulEquiv] using detEquality

example : ((StableGL.quotientDetKernelMulEquiv (ZMod 3)).symm
    (QuotientGroup.map (stableElementarySubgroup ℤ)
      (stableElementarySubgroup (ZMod 3)) (StableGL.map reduceThree)
      ((Subgroup.map_le_iff_le_comap).mp
        (StableGL.map_elementarySubgroup_le reduceThree))
        (StableGL.quotientDetKernelMulEquiv ℤ (1, (-1 : ℤˣ))))).2 =
      (-1 : (ZMod 3)ˣ) := by
  rw [StableGL.quotientDetKernelMulEquiv_symm_map_snd,
    StableGL.quotientDetKernelMulEquiv_units,
    StableGL.quotientDetKernelMulEquiv_symm_apply_snd,
    StableGL.quotientDet_quotientRankOneUnits]
  apply Units.ext
  norm_num [reduceThree]

example (q : StableGL ℤ ⧸ stableElementarySubgroup ℤ) :
    StableGL.quotientDet ℤ
      (q * (StableGL.quotientRankOneUnits ℤ (StableGL.quotientDet ℤ q))⁻¹) = 1 := by
  rw [← StableGL.quotientDetKernelMulEquiv_symm_apply_fst]
  exact MonoidHom.mem_ker.mp ((StableGL.quotientDetKernelMulEquiv ℤ).symm q).1.property

example : (StableGL.quotientDetKernelMulEquiv ℤ).symm
      (StableGL.quotientRankOneUnits ℤ (-1)) = (1, (-1 : ℤˣ)) := by
  apply Prod.ext
  · apply Subtype.ext
    simp only [StableGL.quotientDetKernelMulEquiv_symm_apply_fst,
      StableGL.quotientDet_quotientRankOneUnits, mul_inv_cancel,
      OneMemClass.coe_one]
  · simp only [StableGL.quotientDetKernelMulEquiv_symm_apply_snd,
      StableGL.quotientDet_quotientRankOneUnits]

example (q : StableGL (ZMod 1) ⧸ stableElementarySubgroup (ZMod 1)) :
    ((StableGL.quotientDetKernelMulEquiv (ZMod 1)).symm q).2 = 1 := by
  rw [StableGL.quotientDetKernelMulEquiv_symm_apply_snd]
  exact Subsingleton.elim _ _

example : ¬ ∀ g : StableGL ℤ,
    StableGL.rankOneUnits ℤ (-1) * g = g * StableGL.rankOneUnits ℤ (-1) := by
  intro commutes
  let diagonal : GL (Fin 2) ℤ :=
    finStabilize ℤ (by decide)
      (Matrix.GeneralLinearGroup.scalar (Fin 1) (-1))
  let elementary : GL (Fin 2) ℤ := elementaryUnit 0 1 (by decide) 1
  have diagonal_stage : StableGL.stage ℤ 2 diagonal = StableGL.rankOneUnits ℤ (-1) :=
    StableGL.stage_finStabilize ℤ (by decide : 1 ≤ 2)
      (Matrix.GeneralLinearGroup.scalar (Fin 1) (-1))
  have finite_commutes : diagonal * elementary = elementary * diagonal := by
    apply StableGL.stage_injective ℤ 2
    simpa only [map_mul, diagonal_stage] using commutes (StableGL.stage ℤ 2 elementary)
  have entry_equality := congrArg
    (fun matrix : GL (Fin 2) ℤ => (matrix : Matrix (Fin 2) (Fin 2) ℤ) 0 1)
    finite_commutes
  norm_num [diagonal, elementary, Matrix.mul_apply, Fin.sum_univ_two,
    finStabilize_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply, elementaryUnit_val,
    Matrix.single_apply, Matrix.one_apply] at entry_equality

example : StableGL.abelianizationRankOneUnits ℤ (-1) ≠ 1 := by
  intro equality
  apply integerNegOne_ne_one
  have detEquality := congrArg (StableGL.abelianizationDet ℤ) equality
  simpa only [map_one, StableGL.abelianizationDet_abelianizationRankOneUnits]
    using detEquality

example : StableGL.abelianizationDet ℤ
      (stableElementaryAbelianizationEquiv ℤ (StableGL.quotientRankOneUnits ℤ (-1))) =
        (-1 : ℤˣ) := by
  rw [StableGL.abelianizationEquiv_quotientRankOneUnits,
    StableGL.abelianizationDet_abelianizationRankOneUnits]

example : StableGL.map reduceThree (StableGL.rankOneUnits ℤ (-1)) ≠ 1 := by
  rw [StableGL.map_rankOneUnits]
  intro equality
  apply modThreeNegOne_ne_one
  have detEquality := congrArg (StableGL.det (ZMod 3)) equality
  simpa [reduceThree] using detEquality

example : StableGL.quotientDet (ZMod 3)
      (QuotientGroup.map (stableElementarySubgroup ℤ)
        (stableElementarySubgroup (ZMod 3)) (StableGL.map reduceThree)
        ((Subgroup.map_le_iff_le_comap).mp (StableGL.map_elementarySubgroup_le reduceThree))
          (StableGL.quotientRankOneUnits ℤ (-1))) = (-1 : (ZMod 3)ˣ) := by
  rw [StableGL.quotientRankOneUnits_map, StableGL.quotientDet_quotientRankOneUnits]
  apply Units.ext
  norm_num [reduceThree]

example : QuotientGroup.map (stableElementarySubgroup ℤ)
      (stableElementarySubgroup (ZMod 3)) (StableGL.map reduceThree)
      ((Subgroup.map_le_iff_le_comap).mp (StableGL.map_elementarySubgroup_le reduceThree))
        (StableGL.quotientRankOneUnits ℤ (-1)) ≠ 1 := by
  rw [StableGL.quotientRankOneUnits_map]
  intro equality
  apply modThreeNegOne_ne_one
  have detEquality := congrArg (StableGL.quotientDet (ZMod 3)) equality
  have imageEquality : Units.map reduceThree (-1 : ℤˣ) = (1 : (ZMod 3)ˣ) := by
    simpa only [map_one, StableGL.quotientDet_quotientRankOneUnits] using detEquality
  simpa [reduceThree] using imageEquality

example : Abelianization.map (StableGL.map reduceThree)
      (stableElementaryAbelianizationEquiv ℤ (StableGL.quotientRankOneUnits ℤ (-1))) =
        stableElementaryAbelianizationEquiv (ZMod 3)
          (QuotientGroup.map (stableElementarySubgroup ℤ)
            (stableElementarySubgroup (ZMod 3)) (StableGL.map reduceThree)
            ((Subgroup.map_le_iff_le_comap).mp
              (StableGL.map_elementarySubgroup_le reduceThree))
                (StableGL.quotientRankOneUnits ℤ (-1))) := by
  exact (stableElementaryAbelianizationEquiv_map reduceThree _).symm

example : Abelianization.map (StableGL.map reduceThree)
      (StableGL.abelianizationRankOneUnits ℤ (-1)) ≠ 1 := by
  rw [StableGL.abelianizationRankOneUnits_map]
  intro equality
  apply modThreeNegOne_ne_one
  have detEquality := congrArg (StableGL.abelianizationDet (ZMod 3)) equality
  simpa [reduceThree] using detEquality

example : Units.map (Int.castRingHom (ZMod 2)).toMonoidHom (-1 : ℤˣ) = 1 := by
  apply Units.ext
  norm_num

example : StableGL.stage ℤ 2 (elementaryUnit 0 1 (by decide) (1 : ℤ)) ≠ 1 ∧
    StableGL.det ℤ (StableGL.stage ℤ 2
      (elementaryUnit 0 1 (by decide) (1 : ℤ))) = 1 ∧
    QuotientGroup.mk' (stableElementarySubgroup ℤ)
      (StableGL.stage ℤ 2 (elementaryUnit 0 1 (by decide) (1 : ℤ))) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro equality
    have finiteEquality : (elementaryUnit 0 1 (by decide) (1 : ℤ) : GL (Fin 2) ℤ) = 1 :=
      StableGL.stage_injective ℤ 2 (by simpa using equality)
    have entryEquality := congrArg (fun g : GL (Fin 2) ℤ => g 0 1) finiteEquality
    norm_num [elementaryUnit_val, Matrix.single_apply, Matrix.one_apply] at entryEquality
  · exact StableGL.det_elementary ℤ
      (elementaryUnit_mem_stableElementarySubgroup ℤ 2 0 1 (by decide) 1)
  · exact (QuotientGroup.eq_one_iff _).mpr
      (elementaryUnit_mem_stableElementarySubgroup ℤ 2 0 1 (by decide) 1)

example (g : GL (Fin 0) ℤ) : StableGL.det ℤ (StableGL.stage ℤ 0 g) = 1 := by
  apply Units.ext
  simpa only [StableGL.det_stage, Matrix.GeneralLinearGroup.val_det_apply,
    Units.val_one] using
    (Matrix.det_isEmpty (A := (g : Matrix (Fin 0) (Fin 0) ℤ)))

example (unit : (ZMod 1)ˣ) :
    StableGL.det (ZMod 1) (StableGL.rankOneUnits (ZMod 1) unit) = unit := by
  simp

private abbrev MatrixCoefficients := Matrix (Fin 2) (Fin 2) ℤ

private def matrixNegOne : MatrixCoefficientsˣ :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)

private theorem matrixNegOne_ne_one : matrixNegOne ≠ 1 := by
  intro equality
  have entryEquality := congrArg (fun unit : MatrixCoefficientsˣ =>
    (unit : MatrixCoefficients) 0 0) equality
  norm_num [matrixNegOne, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply] at entryEquality

example : StableGL.rankOneUnits MatrixCoefficients matrixNegOne ≠ 1 := by
  intro equality
  exact matrixNegOne_ne_one
    (StableGL.rankOneUnits_injective MatrixCoefficients (by simpa using equality))

example : StableGL.map (RingHom.mapMatrix reduceThree)
      (StableGL.rankOneUnits MatrixCoefficients matrixNegOne) =
    StableGL.rankOneUnits (Matrix (Fin 2) (Fin 2) (ZMod 3))
      (Units.map (RingHom.mapMatrix reduceThree).toMonoidHom matrixNegOne) := by
  simp
