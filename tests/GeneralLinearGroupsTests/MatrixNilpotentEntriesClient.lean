/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups
import Mathlib.Data.ZMod.Basic

/-!
# Nilpotent-entry matrix examples

The one-by-one matrix with entry `2 : ZMod 4` is nonzero, has square zero,
and has nilpotent entries. These elementary checks adapt the Formal Frontier
Agents' entrywise-nilpotence example. The nilpotence conclusion uses the generic
matrix theorem; an empty-index example checks the boundary separately.
-/

@[expose] public section

namespace Matrix

private def twoModFour : Matrix (Fin 1) (Fin 1) (ZMod 4) :=
  fun _ _ => 2

private theorem twoModFour_ne_zero : twoModFour ≠ 0 := by
  decide

private theorem twoModFour_sq : twoModFour ^ 2 = 0 := by
  decide

private theorem twoModFour_entries_isNilpotent :
    ∀ i j, IsNilpotent (twoModFour i j) := by
  intro i j
  change IsNilpotent (2 : ZMod 4)
  exact ⟨2, by decide⟩

example : twoModFour ≠ 0 ∧ twoModFour ^ 2 = 0 ∧ IsNilpotent twoModFour := by
  exact ⟨twoModFour_ne_zero, twoModFour_sq,
    isNilpotent_of_isNilpotent_entries twoModFour twoModFour_entries_isNilpotent⟩

example (A : Matrix (Fin 0) (Fin 0) ℕ) : IsNilpotent A := by
  exact isNilpotent_of_subsingleton

end Matrix
