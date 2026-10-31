/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups.MatrixIdeal

open scoped Matrix

/-!
# A singleton matrix over the natural numbers

The square of the matrix with entry `2` places `4` in the square of the ideal
spanned by `2`.
-/

example : (4 : ℕ) ∈ (Ideal.span ({2} : Set ℕ)) ^ 2 := by
  let A : Matrix Unit Unit ℕ := fun _ _ => 2
  have hA : ∀ i j, A i j ∈ Ideal.span ({2} : Set ℕ) := by
    intro i j
    exact Ideal.subset_span (by simp [A])
  have h := Matrix.mul_apply_mem_ideal_mul
    (Ideal.span ({2} : Set ℕ)) (Ideal.span ({2} : Set ℕ)) hA hA () ()
  rw [Matrix.mul_apply] at h
  simpa [A, pow_two] using h
