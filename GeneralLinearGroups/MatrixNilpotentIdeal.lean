/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Data.List.Induction
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Ordered matrix products and nilpotent left ideals

For a list of finite square matrices over a semiring, if every entry of every
factor lies in a left ideal, then each entry of the ordered product lies in the
ideal power indexed by the list's length. Matrix powers are the repeated-factor
case, obtained by taking a replicated list. Consequently any exponent
annihilating the ideal also annihilates a matrix with entries in that ideal.
The coefficient and index universes are independent, and the index type may be
empty.

## Proof and power conventions

Ideal powers are the stock submodule powers on the regular left module, with
`I ^ 0 = ⊤` and `I ^ (k + 1) = I ^ k * I`. Right-append list induction matches
`(As ++ [A]).prod = As.prod * A`: each summand in an entry of this matrix product
lies in `I ^ As.length * I`, and this left ideal is closed under finite sums.
The empty product has its entries in `I ^ 0 = ⊤`. Specializing to
`List.replicate k A` gives the bound for `A ^ k`. If `I ^ N = 0`, the bound at
that same `N` makes every entry of `A ^ N` zero, so matrix extensionality gives
`A ^ N = 0`. No multiplicative monoid structure on arbitrary left ideals is
needed.

## Limitations

Uniform ideal nilpotence is essential; no assertion about arbitrary pointwise
nil ideals is made. No two-sidedness, commutativity, additive inverses or
nontriviality hypothesis is imposed. Both the power bound at exponent zero and
a nilpotence witness of zero are allowed, as are empty indices and zero semirings.

## References

The matrix, left-ideal, submodule-power, list-product and nilpotence interfaces
are from mathlib. The proofs use `List.reverseRecOn`, `List.prod_replicate`,
`Submodule.pow_zero`, `Submodule.pow_succ`, `Ideal.mul_mem_mul`,
`Submodule.sum_mem` and `Submodule.mem_bot`, together with matrix multiplication
and extensionality.
-/

@[expose] public section

universe uR uN

namespace Matrix

variable {R : Type uR} [Semiring R]
variable {n : Type uN} [Fintype n] [DecidableEq n]

/-- If every entry of every matrix in `As` lies in the left ideal `I`, each entry of the
ordered product `As.prod` lies in `I ^ As.length`. -/
theorem list_prod_apply_mem_ideal_pow
    (I : Ideal R) (As : List (Matrix n n R))
    (hAs : ∀ A ∈ As, ∀ i j, A i j ∈ I) (i j : n) :
    As.prod i j ∈ I ^ As.length := by
  revert hAs i j
  induction As using List.reverseRecOn with
  | nil =>
      intro _ i j
      rw [List.length_nil, Submodule.pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | append_singleton As A ih =>
      intro hAs i j
      have hAs' : ∀ B ∈ As, ∀ i j, B i j ∈ I :=
        fun B hB => hAs B (List.mem_append.mpr (Or.inl hB))
      have hA : ∀ i j, A i j ∈ I :=
        hAs A (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
      rw [List.prod_append, List.prod_singleton, List.length_append,
        List.length_singleton, Submodule.pow_succ, Matrix.mul_apply]
      exact Submodule.sum_mem _ fun r _ =>
        Ideal.mul_mem_mul (ih hAs' i r) (hA r j)

/-- If every entry of `A` lies in the left ideal `I`, each entry of `A ^ k` lies in `I ^ k`.
This is the repeated-factor case of `list_prod_apply_mem_ideal_pow`. -/
theorem pow_apply_mem_ideal_pow (I : Ideal R) (A : Matrix n n R)
    (hA : ∀ i j, A i j ∈ I) (k : ℕ) (i j : n) :
    (A ^ k) i j ∈ I ^ k := by
  simpa only [List.prod_replicate, List.length_replicate] using
    list_prod_apply_mem_ideal_pow I (List.replicate k A)
      (fun B hB => by simpa only [List.eq_of_mem_replicate hB] using hA) i j

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
