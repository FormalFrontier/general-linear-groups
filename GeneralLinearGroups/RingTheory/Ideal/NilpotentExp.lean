/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

The finite-sum argument is adapted from Mathlib.RingTheory.Nilpotent.Exp:
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Rat
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Nilpotent.Exp

/-!
# Nilpotent exponentials modulo a left ideal

The stock algebraic exponential of a nilpotent member of a left ideal is
congruent to one modulo that ideal. The proof splits off the constant term in
`IsNilpotent.exp_eq_sum`; the finite-sum argument also follows the approach of
Janos Wolosz's `IsNilpotent.isNilpotent_exp_sub_one`.

Only the given rational module on the ambient ring is needed. Stock rational
scalar compatibility expresses each positive-degree term as a left multiple
of an element of the ideal.
-/

@[expose] public section

universe u

namespace Ideal

variable {A : Type u} [Ring A] [Module ℚ A]

/-- The exponential of a nilpotent member of a left ideal differs from one by
an element of that ideal. -/
theorem exp_sub_one_mem (I : Ideal A) {x : A} (hxI : x ∈ I) (hxNil : IsNilpotent x) :
    IsNilpotent.exp x - 1 ∈ I := by
  obtain ⟨n, hn⟩ := hxNil
  have hn' : x ^ (n + 1) = 0 := by
    rw [pow_succ, hn, zero_mul]
  rw [IsNilpotent.exp_eq_sum hn', Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    add_sub_cancel_right]
  apply Submodule.sum_mem I
  intro i _
  simpa only [smul_mul_assoc, one_mul] using
    I.mul_mem_left (((i + 1).factorial : ℚ)⁻¹ • (1 : A))
      (I.pow_mem_of_mem hxI (i + 1) (Nat.zero_lt_succ i))

end Ideal
