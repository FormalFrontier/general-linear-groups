/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups.ElementaryDiagonal
import Mathlib.Data.ZMod.Basic

/-! Public-import clients for elementary product-one diagonals. -/

set_option warningAsError true

@[expose] public section

namespace GeneralLinearGroupsTests.ElementaryDiagonal

open Matrix.GeneralLinearGroup

example (d : Fin 0 → (ZMod 1)ˣ) :
    diagonalUnit d ∈ elementarySubgroup (Fin 0) (ZMod 1) :=
  diagonalUnit_mem_elementarySubgroup 0 d (by simp)

example (d : Fin 1 → ℤˣ) (h : d 0 = 1) :
    diagonalUnit d ∈ elementarySubgroup (Fin 1) ℤ :=
  diagonalUnit_mem_elementarySubgroup 1 d (by simpa using h)

example :
    diagonalUnit (Fin.cases (-1 : ℤˣ) (fun _ : Fin 1 => -1)) ∈
      elementarySubgroup (Fin 2) ℤ := by
  apply diagonalUnit_mem_elementarySubgroup 2
  simp [Fin.prod_univ_succ]

example :
    diagonalUnit (Fin.cases (⟨5, 5, by decide, by decide⟩ : (ZMod 6)ˣ)
      (fun _ : Fin 1 => (⟨5, 5, by decide, by decide⟩ : (ZMod 6)ˣ))) ∈
        elementarySubgroup (Fin 2) (ZMod 6) := by
  let u : (ZMod 6)ˣ := ⟨5, 5, by decide, by decide⟩
  have hu : u * u = 1 := by
    apply Units.ext
    decide
  change diagonalUnit (Fin.cases u (fun _ : Fin 1 => u)) ∈ _
  apply diagonalUnit_mem_elementarySubgroup 2
  simpa [Fin.prod_univ_succ] using hu

example {n : ℕ} (g : GL (Fin n) (ZMod 6))
    (hdet : (g : Matrix (Fin n) (Fin n) (ZMod 6)).det = 1)
    (hpivots : ∀ (k : ℕ) (hk : k ≤ n), 0 < k →
      IsUnit (Matrix.leadingPrincipalMinor
        (g : Matrix (Fin n) (Fin n) (ZMod 6)) k hk)) :
    g ∈ elementarySubgroup (Fin n) (ZMod 6) :=
  mem_elementarySubgroup_of_det_one_of_unit_leadingPrincipalMinors g hdet hpivots

end GeneralLinearGroupsTests.ElementaryDiagonal
