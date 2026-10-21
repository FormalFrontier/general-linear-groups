/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.StableGeneralLinear

/-!
# Entry formulas for finite general-linear stabilization

Finite stabilization has zero entries between original and added coordinates in either
direction, and its added-coordinate block is the identity matrix. Successive finite
stabilizations agree entrywise with stabilization along the composite inequality.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u

/-- Finite stabilization has zero entries from original rows to added columns. -/
theorem finStabilize_apply_castLE_tail (R : Type u) [Semiring R]
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R)
    (i : Fin n) (j : Fin (m - n)) :
    finStabilize R h g (Fin.castLE h i)
        (Fin.cast (Nat.add_sub_of_le h) (Fin.natAdd n j)) = 0 := by
  simpa only [finBlockEquiv_inl, finBlockEquiv_inr] using
    (finStabilize_apply_inl_inr R h g i j)

/-- Finite stabilization has zero entries from added rows to original columns. -/
theorem finStabilize_apply_tail_castLE (R : Type u) [Semiring R]
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R)
    (i : Fin (m - n)) (j : Fin n) :
    finStabilize R h g (Fin.cast (Nat.add_sub_of_le h) (Fin.natAdd n i))
        (Fin.castLE h j) = 0 := by
  simpa only [finBlockEquiv_inr, finBlockEquiv_inl] using
    (finStabilize_apply_inr_inl R h g i j)

/-- The added-coordinate block of finite stabilization is the identity matrix. -/
theorem finStabilize_apply_tail_tail (R : Type u) [Semiring R]
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R) (i j : Fin (m - n)) :
    finStabilize R h g
        (Fin.cast (Nat.add_sub_of_le h) (Fin.natAdd n i))
        (Fin.cast (Nat.add_sub_of_le h) (Fin.natAdd n j)) =
      (1 : Matrix (Fin (m - n)) (Fin (m - n)) R) i j := by
  simpa only [finBlockEquiv_inr] using (finStabilize_apply_inr_inr R h g i j)

/-- Two successive stabilizations agree entrywise with stabilization along the composite
inequality. -/
theorem finStabilize_comp_apply (R : Type u) [Semiring R]
    {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) (g : GL (Fin n) R) (i j : Fin k) :
    finStabilize R h' (finStabilize R h g) i j =
      finStabilize R (h.trans h') g i j := by
  have hg :
      finStabilize R (h.trans h') g =
        finStabilize R h' (finStabilize R h g) := by
    simpa only [MonoidHom.comp_apply] using
      congrArg (fun f : GL (Fin n) R →* GL (Fin k) R => f g)
        (finStabilize_comp R h h')
  exact (congrArg (fun x : GL (Fin k) R => x i j) hg).symm

end Matrix.GeneralLinearGroup
