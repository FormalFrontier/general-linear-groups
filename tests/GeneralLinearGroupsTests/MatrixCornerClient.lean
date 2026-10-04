/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups
import Mathlib.Data.ZMod.Basic

/-! Clients of single-entry corners over semirings and their boundary cases. -/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests

private abbrev NatCorner :=
  (Matrix.isIdempotentElem_single_one (R := ℕ) (1 : Fin 3)).Corner

private def natCorner (n : ℕ) : NatCorner :=
  ⟨Matrix.single 1 1 n,
    (Matrix.mem_single_corner_iff (R := ℕ) (1 : Fin 3) _).2 (by simp)⟩

private theorem nat_corner_entry :
    Matrix.singleCornerRingEquiv (R := ℕ) (1 : Fin 3) (natCorner 7) = 7 := by
  rw [Matrix.singleCornerRingEquiv_apply]
  simp [natCorner]

private theorem nat_corner_inverse_off_support :
    ((Matrix.singleCornerRingEquiv (R := ℕ) (1 : Fin 3)).symm 8).1 0 0 = 0 := by
  rw [Matrix.singleCornerRingEquiv_symm_apply_coe]
  simp

public theorem nat_corner_raw_member :
    (Matrix.single (1 : Fin 3) (1 : Fin 3) (7 : ℕ) : Matrix (Fin 3) (Fin 3) ℕ) ∈
      Subsemigroup.corner (Matrix.single (1 : Fin 3) (1 : Fin 3) (1 : ℕ)) := by
  exact ⟨Matrix.single 1 1 (7 : ℕ), by simp⟩

private theorem nat_corner_unit_ne_ambient_unit :
    (1 : (Matrix.isIdempotentElem_single_one (R := ℕ) (1 : Fin 3)).Corner).1 ≠
      (1 : Matrix (Fin 3) (Fin 3) ℕ) := by
  intro h
  have hentry := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℕ => A 0 0) h
  simp at hentry

private abbrev Coeff := Matrix (Fin 2) (Fin 2) ℕ
private abbrev Outer := Matrix (Fin 3) (Fin 3) Coeff
private abbrev OuterCorner :=
  (Matrix.isIdempotentElem_single_one (R := Coeff) (1 : Fin 3)).Corner

private def upper : Coeff := Matrix.single 0 1 1
private def lower : Coeff := Matrix.single 1 0 1

private def supported (r : Coeff) : OuterCorner :=
  ⟨Matrix.single 1 1 r,
    (Matrix.mem_single_corner_iff (R := Coeff) (1 : Fin 3) _).2 (by simp)⟩

private theorem supported_raw_member (r : Coeff) :
    (Matrix.single (1 : Fin 3) 1 r : Outer) ∈
      Subsemigroup.corner (Matrix.single 1 1 (1 : Coeff)) := by
  exact ⟨Matrix.single 1 1 r, by simp⟩

private theorem coefficient_order : upper * lower ≠ lower * upper := by
  intro h
  have hentry := congrArg (fun A : Coeff => A 0 0) h
  simp [upper, lower] at hentry

private theorem corner_order :
    supported upper * supported lower ≠ supported lower * supported upper := by
  intro h
  have hmatrix :
      (Matrix.single (1 : Fin 3) 1 upper : Outer) * Matrix.single 1 1 lower =
        Matrix.single 1 1 lower * Matrix.single 1 1 upper :=
    congrArg Subtype.val h
  have hentry := congrArg (fun A : Outer => (A 1 1) 0 0) hmatrix
  simp [upper, lower] at hentry

private theorem outer_corner_entry :
    Matrix.singleCornerRingEquiv (R := Coeff) (1 : Fin 3) (supported upper) = upper := by
  rw [Matrix.singleCornerRingEquiv_apply]
  simp [supported]

private abbrev SingletonCorner :=
  (Matrix.isIdempotentElem_single_one (R := ℕ) PUnit.unit).Corner

private theorem singleton_comparison :
    Matrix.uniqueRingEquiv
      ((Matrix.singleCornerRingEquiv (R := ℕ) PUnit.unit).symm 7).1 = (7 : ℕ) := by
  calc
    _ = Matrix.singleCornerRingEquiv PUnit.unit
          ((Matrix.singleCornerRingEquiv (R := ℕ) PUnit.unit).symm 7) :=
        (Matrix.singleCornerRingEquiv_apply_eq_uniqueRingEquiv PUnit.unit _).symm
    _ = 7 := (Matrix.singleCornerRingEquiv (R := ℕ) PUnit.unit).apply_symm_apply 7

private theorem singleton_corner_unit_is_ambient_unit :
    (1 : SingletonCorner).1 = (1 : Matrix PUnit PUnit ℕ) := by
  ext j k
  have hj : j = PUnit.unit := Subsingleton.elim _ _
  have hk : k = PUnit.unit := Subsingleton.elim _ _
  subst j
  subst k
  simp

private abbrev ZeroCorner :=
  (Matrix.isIdempotentElem_single_one (R := ZMod 1) (1 : Fin 3)).Corner

private theorem zero_coefficient_boundary (C : ZeroCorner) : C = 0 := by
  apply Subtype.ext
  ext j k
  exact Subsingleton.elim _ _

end GeneralLinearGroupsTests
