/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups.UnitPivotDiagonalization
import Mathlib.Data.ZMod.Basic

/-! Public-import clients of unit-pivot elementary diagonalization. -/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.UnitPivotDiagonalization

example (M : Matrix (Fin 0) (Fin 0) (ZMod 1)) :
    ∃ L Q : Matrix.GeneralLinearGroup.elementarySubgroup (Fin 0) (ZMod 1),
      ∃ d : Fin 0 → (ZMod 1)ˣ,
        ((L : GL (Fin 0) (ZMod 1)) : Matrix (Fin 0) (Fin 0) (ZMod 1)) * M *
          ((Q : GL (Fin 0) (ZMod 1)) : Matrix (Fin 0) (Fin 0) (ZMod 1)) =
            Matrix.diagonal (fun i => (d i : ZMod 1)) := by
  exact Matrix.exists_elementary_diagonalization_of_unit_leadingPrincipalMinors 0 M
    (by intro k hk hkpos; omega)

example (M : Matrix (Fin 2) (Fin 2) (ZMod 1)) :
    ∃ L Q : Matrix.GeneralLinearGroup.elementarySubgroup (Fin 2) (ZMod 1),
      ∃ d : Fin 2 → (ZMod 1)ˣ,
        ((L : GL (Fin 2) (ZMod 1)) : Matrix (Fin 2) (Fin 2) (ZMod 1)) * M *
          ((Q : GL (Fin 2) (ZMod 1)) : Matrix (Fin 2) (Fin 2) (ZMod 1)) =
            Matrix.diagonal (fun i => (d i : ZMod 1)) := by
  apply Matrix.exists_elementary_diagonalization_of_unit_leadingPrincipalMinors 2 M
  intro k hk hkpos
  have heq : Matrix.leadingPrincipalMinor M k hk = (1 : ZMod 1) :=
    Subsingleton.elim _ _
  rw [heq]
  exact isUnit_one

example (M : Matrix (Fin 1) (Fin 1) ℤ) (h : IsUnit M.det) :
    ∃ L Q : Matrix.GeneralLinearGroup.elementarySubgroup (Fin 1) ℤ,
      ∃ d : Fin 1 → ℤˣ,
        ((L : GL (Fin 1) ℤ) : Matrix (Fin 1) (Fin 1) ℤ) * M *
          ((Q : GL (Fin 1) ℤ) : Matrix (Fin 1) (Fin 1) ℤ) =
            Matrix.diagonal (fun i => (d i : ℤ)) := by
  apply Matrix.exists_elementary_diagonalization_of_unit_leadingPrincipalMinors 1 M
  intro k hk hkpos
  have hk1 : k = 1 := by omega
  subst k
  simpa using h

example (M : Matrix (Fin 2) (Fin 2) (ZMod 6))
    (h : ∀ (k : ℕ) (hk : k ≤ 2), 0 < k →
      IsUnit (Matrix.leadingPrincipalMinor M k hk)) :
    ∃ L Q : Matrix.GeneralLinearGroup.elementarySubgroup (Fin 2) (ZMod 6),
      ∃ d : Fin 2 → (ZMod 6)ˣ,
        ((L : GL (Fin 2) (ZMod 6)) : Matrix (Fin 2) (Fin 2) (ZMod 6)) * M *
          ((Q : GL (Fin 2) (ZMod 6)) : Matrix (Fin 2) (Fin 2) (ZMod 6)) =
            Matrix.diagonal (fun i => (d i : ZMod 6)) := by
  exact Matrix.exists_elementary_diagonalization_of_unit_leadingPrincipalMinors 2 M h

example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ (k : ℕ) (hk : k ≤ n), 0 < k →
      IsUnit (Matrix.leadingPrincipalMinor M k hk)) (hSL : M.det = 1) :
    ∃ L Q : Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) ℤ,
      ∃ d : Fin n → ℤˣ,
        ((L : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) * M *
            ((Q : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) =
              Matrix.diagonal (fun i => (d i : ℤ)) ∧
          (∏ i, (d i : ℤ)) = 1 := by
  obtain ⟨L, Q, d, hd⟩ :=
    Matrix.exists_elementary_diagonalization_of_unit_leadingPrincipalMinors n M h
  exact ⟨L, Q, d, hd, (Matrix.det_eq_prod_of_elementary_diagonalization hd).symm.trans hSL⟩

end GeneralLinearGroupsTests.UnitPivotDiagonalization
