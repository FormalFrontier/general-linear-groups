/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Matrix powers and nilpotent left ideals

For a finite square matrix over a semiring, entries in a left ideal give entries
of its `k`th power in the `k`th ideal power. Consequently any exponent annihilating
the ideal also annihilates the matrix. The coefficient and index universes are
independent, and the index type may be empty.

## Proof and power conventions

Ideal powers are the stock submodule powers on the regular left module, with
`I ^ 0 = ⊤` and `I ^ (k + 1) = I ^ k * I`. Induction follows the matching matrix
recursion `A ^ (k + 1) = A ^ k * A`: each summand in an entry of the product lies
in `I ^ k * I`, and this left ideal is closed under finite sums. If `I ^ N = 0`,
the bound at that same `N` makes every entry of `A ^ N` zero, so matrix
extensionality gives `A ^ N = 0`. No multiplicative monoid structure on arbitrary
left ideals is needed.

## Limitations

Uniform ideal nilpotence is essential; no assertion about arbitrary pointwise
nil ideals is made. No two-sidedness, commutativity, additive inverses or
nontriviality hypothesis is imposed. Both the power bound at exponent zero and
a nilpotence witness of zero are allowed, as are empty indices and zero semirings.

## References

The matrix, left-ideal, submodule-power and nilpotence interfaces are from mathlib.
The proofs use `Submodule.pow_zero`, `Submodule.pow_succ`, `Ideal.mul_mem_mul`,
`Submodule.sum_mem` and `Submodule.mem_bot`, together with matrix multiplication
and extensionality.
-/

@[expose] public section

universe uR uN

namespace Matrix

variable {R : Type uR} [Semiring R]
variable {n : Type uN} [Fintype n] [DecidableEq n]

/-- If every entry of `A` lies in the left ideal `I`, each entry of `A ^ k` lies in `I ^ k`. -/
theorem pow_apply_mem_ideal_pow (I : Ideal R) (A : Matrix n n R)
    (hA : ∀ i j, A i j ∈ I) (k : ℕ) (i j : n) :
    (A ^ k) i j ∈ I ^ k := by
  induction k generalizing i j with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ k ih =>
      rw [pow_succ, Submodule.pow_succ, Matrix.mul_apply]
      exact Submodule.sum_mem _ fun r _ => Ideal.mul_mem_mul (ih i r) (hA r j)

/-- A finite square matrix with entries in a uniformly nilpotent left ideal is nilpotent. -/
theorem isNilpotent_of_isNilpotent_ideal (I : Ideal R) (A : Matrix n n R)
    (hA : ∀ i j, A i j ∈ I) (hI : IsNilpotent I) : IsNilpotent A := by
  obtain ⟨k, hk⟩ := hI
  refine ⟨k, ?_⟩
  ext i j
  have hij := pow_apply_mem_ideal_pow I A hA k i j
  rw [hk, Ideal.zero_eq_bot] at hij
  exact (Submodule.mem_bot R).mp hij

end Matrix
