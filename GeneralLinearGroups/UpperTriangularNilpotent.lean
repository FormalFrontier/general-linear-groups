/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.NonUnitalNilpotent
public import Mathlib.Data.Finset.Max

/-!
# Nilpotence of upper triangular matrices over semirings

For a finite linearly ordered index type, an upper triangular matrix over an
arbitrary semiring is nilpotent exactly when all its diagonal entries are
nilpotent. More quantitatively, diagonal killing exponents give a matrix killing
exponent equal to their sum. The coefficient and index universes are independent;
coefficients need not commute. The index type may be empty, and the supplied
exponents may be zero.

## References

* Mathlib contributors, `Mathlib.LinearAlgebra.Matrix.Block`, for the triangular
  predicate and its multiplication and power APIs;
  `Mathlib.Data.Matrix.Mul`, for persistence of zero rows of matrix powers; and
  `Mathlib.Data.Finset.Max`, for ordered finite-set induction.
* Formal Frontier Agents, Algebraic Groups library,
  `AlgebraicGroups.GroupTheory.UnitriangularExponent`, for the zero-diagonal
  cardinal-power specialization over commutative rings.
-/

@[expose] public section

universe u v

namespace Matrix

section Semiring

variable {ι : Type u} {R : Type v}
variable [Fintype ι] [LinearOrder ι] [Semiring R]
variable {A : Matrix ι ι R}

/-- If each diagonal entry of an upper triangular matrix is killed by its supplied
exponent, the matrix is killed by the sum of those exponents. Empty index types
and zero exponents are included. -/
theorem IsUpperTriangular.pow_eq_zero_of_diagonal_pow_eq_zero
    (hA : A.IsUpperTriangular) (e : ι → ℕ)
    (he : ∀ i : ι, (A i i) ^ e i = 0) :
    A ^ (∑ i : ι, e i) = 0 := by
  classical
  -- Eliminate rows from greatest to least. A vanished row remains zero after
  -- further right multiplication, so only the newly inserted row needs attention.
  have hrows : ∀ s : Finset ι,
      (∀ i ∈ s, ∀ j, i < j → j ∈ s) →
      ∀ i ∈ s, ∀ j, (A ^ (∑ l ∈ s, e l)) i j = 0 := by
    intro s
    induction s using Finset.induction_on_min with
    | empty => simp
    | insert a s has ih =>
        intro hs
        have ha : a ∉ s := fun h => (has a h).false
        have hs' : ∀ i ∈ s, ∀ j, i < j → j ∈ s := by
          intro i hi j hij
          rcases Finset.mem_insert.mp (hs i (Finset.mem_insert_of_mem hi) j hij) with h | h
          · subst j
            exact ((has i hi).trans hij).false.elim
          · exact h
        have hz := ih hs'
        have hz' (k : ℕ) (i : ι) (hi : i ∈ s) (j : ι) :
            (A ^ ((∑ l ∈ s, e l) + k)) i j = 0 := by
          have hrow : (A ^ (∑ l ∈ s, e l)).row i = 0 := by
            ext l
            exact hz i hi l
          exact congr_fun (Matrix.pow_row_eq_zero_of_le
            (l := (∑ l ∈ s, e l) + k) hrow (Nat.le_add_right _ _)) j
        -- Once all higher rows vanish, left multiplication acts on row a by
        -- its diagonal entry. This preserves the order of all scalar factors.
        have harow : ∀ k : ℕ, ∀ j : ι,
            (A ^ ((∑ l ∈ s, e l) + k)) a j =
              (A a a) ^ k * (A ^ (∑ l ∈ s, e l)) a j := by
          intro k
          induction k with
          | zero => simp
          | succ k ihk =>
              intro j
              rw [Nat.add_succ, pow_succ', Matrix.mul_apply]
              rw [Finset.sum_eq_single a]
              · rw [ihk, pow_succ', mul_assoc]
              · intro b _ hba
                rcases lt_or_gt_of_ne hba with hba | hab
                · rw [hA hba, zero_mul]
                · have hb : b ∈ s := by
                    rcases Finset.mem_insert.mp
                        (hs a (Finset.mem_insert_self a s) b hab) with h | h
                    · exact (hba h).elim
                    · exact h
                  rw [hz' k b hb j, mul_zero]
              · simp
        intro i hi j
        rw [Finset.sum_insert ha, Nat.add_comm (e a)]
        rcases Finset.mem_insert.mp hi with hia | hi
        · subst i
          rw [harow, he a, zero_mul]
        · exact hz' (e a) i hi j
  ext i j
  exact hrows Finset.univ (by simp) i (Finset.mem_univ i) j

/-- An upper triangular matrix over a semiring is nilpotent if and only if all its
diagonal entries are nilpotent. No commutativity assumption is needed, and the
index type may be empty. -/
theorem IsUpperTriangular.isNilpotent_iff (hA : A.IsUpperTriangular) :
    IsNilpotent A ↔ ∀ i : ι, IsNilpotent (A i i) := by
  classical
  have hdiagPow : ∀ k : ℕ, ∀ i : ι, (A ^ k) i i = (A i i) ^ k := by
    intro k
    induction k with
    | zero =>
        intro i
        simp
    | succ k ih =>
        intro i
        rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i]
        · rw [ih, pow_succ]
        · intro j _ hji
          rcases lt_or_gt_of_ne hji with hlt | hgt
          · rw [(hA.pow k) hlt, zero_mul]
          · rw [hA hgt, mul_zero]
        · simp
  constructor
  · rintro ⟨k, hk⟩ i
    refine ⟨k, ?_⟩
    have hi := congrArg (fun M : Matrix ι ι R => M i i) hk
    rw [hdiagPow] at hi
    simpa using hi
  · intro h
    choose e he using h
    exact ⟨∑ i : ι, e i,
      Matrix.IsUpperTriangular.pow_eq_zero_of_diagonal_pow_eq_zero hA e he⟩

end Semiring

private theorem pow_card_eq_zero_of_zero_diagonal
    {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]
    (N : Matrix ι ι R) (hupper : N.IsUpperTriangular)
    (hdiag : ∀ i, N i i = 0) : N ^ Fintype.card ι = 0 := by
  have hone : ∀ i : ι, (N i i) ^ (1 : ℕ) = 0 := by
    simpa only [pow_one] using hdiag
  simpa only [← Fintype.card_eq_sum_ones] using
    (Matrix.IsUpperTriangular.pow_eq_zero_of_diagonal_pow_eq_zero
      (ι := ι) (R := R) (A := N) (hA := hupper) (fun _ : ι => 1) hone)

end Matrix
