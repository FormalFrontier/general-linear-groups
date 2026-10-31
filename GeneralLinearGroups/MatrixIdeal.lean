/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Ideal bounds for matrix products

Entries of a rectangular matrix product lie in the ordered product of the
ideals containing the entries of its two factors.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

universe u v w x

/-- Each entry of a rectangular matrix product lies in the product of the ideals
containing the entries of its factors. Only the common index type is finite. -/
theorem mul_apply_mem_ideal_mul
    {R : Type u} {ι : Type v} {κ : Type w} {η : Type x}
    [Semiring R] [Fintype κ]
    (P Q : Ideal R) {A : Matrix ι κ R} {B : Matrix κ η R}
    (hA : ∀ i j, A i j ∈ P) (hB : ∀ j k, B j k ∈ Q)
    (i : ι) (k : η) : (A * B) i k ∈ P * Q := by
  rw [Matrix.mul_apply]
  exact Submodule.sum_mem _ fun j _ =>
    Ideal.mul_mem_mul (hA i j) (hB j k)

end Matrix
