/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.LocalElementaryGeneration
public import GeneralLinearGroupsTests.LocalElementaryGenerationExamples

/-!
# Local elementary generation examples

Signed row exchange and an invertible matrix over the nonfield local ring of
2-adic integers illustrate that a unit leading entry is not required. Empty and
one-element index types, and a field example, exercise the rank boundaries.
-/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.LocalElementaryGeneration

open Matrix.GeneralLinearGroup
open GeneralLinearGroupsTests.LocalElementaryGenerationExamples

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

example (R : Type*) [CommRing R] [IsLocalRing R] :
    signedExchange R ∈ elementarySubgroup (Fin 2) R :=
  (mem_elementarySubgroup_iff_det_eq_one_local _).2 (signedExchange_det R)

/-- The nonfield example is elementary despite its nonunit leading entry. -/
theorem nonfieldMatrix_mem_elementarySubgroup :
    nonfieldMatrix ∈ elementarySubgroup (Fin 2) ℤ_[2] :=
  (mem_elementarySubgroup_iff_det_eq_one_local _).2 nonfieldMatrix_det

example : ∃ (left right : elementarySubgroup (Fin 2) ℤ_[2])
    (diagonal : Fin 2 → ℤ_[2]ˣ),
    (left : GL (Fin 2) ℤ_[2]) * nonfieldMatrix * (right : GL (Fin 2) ℤ_[2]) =
      diagonalUnit diagonal ∧ (diagonal 0 : ℤ_[2]) ≠ 0 := by
  obtain ⟨left, right, diagonal, hfactor⟩ :=
    exists_elementary_diagonalization_local nonfieldMatrix
  exact ⟨left, right, diagonal, hfactor, Units.ne_zero _⟩

example : QuotientGroup.mk' (stableElementarySubgroup ℤ_[2])
    (StableGL.stage ℤ_[2] 2 nonfieldMatrix) = 1 := by
  apply (StableGL.quotientDetMulEquiv ℤ_[2]).injective
  simpa only [StableGL.quotientDetMulEquiv_apply, StableGL.quotientDet_mk,
    StableGL.det_stage, map_one] using nonfieldMatrix_det

example (g : GL (Fin 0) ℤ_[2]) : g ∈ elementarySubgroup (Fin 0) ℤ_[2] := by
  apply (mem_elementarySubgroup_iff_det_eq_one_local _).2
  apply Units.ext
  simp

example (g : GL (Fin 1) ℤ_[2]) (hdet : Matrix.GeneralLinearGroup.det g = 1) :
    g = 1 := by
  have hg := (mem_elementarySubgroup_iff_det_eq_one_local g).2 hdet
  rw [elementarySubgroup_eq_bot_of_subsingleton] at hg
  exact Subgroup.mem_bot.mp hg

example : signedExchange ℚ ∈ elementarySubgroup (Fin 2) ℚ :=
  (mem_elementarySubgroup_iff_det_eq_one_local _).2 (signedExchange_det ℚ)

example : ∃ (left right : List (Matrix.TransvectionStruct (Fin 2) ℚ))
    (diagonal : Fin 2 → ℚˣ),
    (left.map (fun factor => elementaryUnit factor.i factor.j factor.hij factor.c)).prod *
        signedExchange ℚ *
      (right.map (fun factor => elementaryUnit factor.i factor.j factor.hij factor.c)).prod =
        diagonalUnit diagonal ∧ (diagonal 0 : ℚ) ≠ 0 := by
  obtain ⟨left, right, diagonal, hfactor⟩ :=
    exists_elementary_transvection_diagonalization_field (signedExchange ℚ)
  exact ⟨left, right, diagonal, hfactor, Units.ne_zero _⟩

end GeneralLinearGroupsTests.LocalElementaryGeneration
