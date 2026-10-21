/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups.StableGeneralLinearEntries
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A negative unit through finite-rank stabilization

The rank-one integer unit `-1` becomes the diagonal matrix with entries `-1, 1, 1`
after two inclusions. The intermediate rank-two matrix exhibits all four block faces.
-/

namespace Matrix.GeneralLinearGroup

example :
    let h12 : 1 ≤ 2 := by decide
    let h23 : 2 ≤ 3 := by decide
    let g : GL (Fin 1) ℤ := -1
    let head : Fin 2 := Fin.castLE h12 (0 : Fin 1)
    let tail : Fin 2 :=
      Fin.cast (Nat.add_sub_of_le h12) (Fin.natAdd 1 (0 : Fin (2 - 1)))
    let g₂ := finStabilize ℤ h12 g
    g ≠ 1 ∧
      g₂ head head = -1 ∧
      g₂ head tail = 0 ∧
      g₂ tail head = 0 ∧
      g₂ tail tail = 1 ∧
      (∀ i j : Fin 3,
        finStabilize ℤ h23 g₂ i j = finStabilize ℤ (h12.trans h23) g i j) ∧
      (fun i j : Fin 3 => finStabilize ℤ h23 g₂ i j) =
        fun i j => if i = j then if i = 0 then (-1 : ℤ) else 1 else 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h00 := congrArg (fun x : GL (Fin 1) ℤ => x 0 0) h
    norm_num at h00
  · simpa using finStabilize_apply_castLE ℤ (by decide : 1 ≤ 2)
      (-1 : GL (Fin 1) ℤ) 0 0
  · exact finStabilize_apply_castLE_tail ℤ (by decide) (-1 : GL (Fin 1) ℤ) 0 0
  · exact finStabilize_apply_tail_castLE ℤ (by decide) (-1 : GL (Fin 1) ℤ) 0 0
  · simpa using finStabilize_apply_tail_tail ℤ (by decide : 1 ≤ 2)
      (-1 : GL (Fin 1) ℤ) 0 0
  · intro i j
    exact finStabilize_comp_apply ℤ (by decide) (by decide) (-1 : GL (Fin 1) ℤ) i j
  · funext i j
    rw [finStabilize_comp_apply]
    fin_cases i <;> fin_cases j <;> norm_num [finStabilize_apply]

end Matrix.GeneralLinearGroup

/-! Empty rank, equal rank, identity, and a zero coefficient semiring. -/

namespace Matrix.GeneralLinearGroup

universe u

example (R : Type u) [Semiring R] {m : ℕ} (h : 0 ≤ m)
    (g : GL (Fin 0) R) : finStabilize R h g = 1 := by
  have hg : g = 1 := Subsingleton.elim _ _
  rw [hg, map_one]

example (R : Type u) [Semiring R] (n : ℕ) (g : GL (Fin n) R) :
    finStabilize R (le_refl n) g = g := by
  simpa only [MonoidHom.id_apply] using
    congrArg (fun f : GL (Fin n) R →* GL (Fin n) R => f g) (finStabilize_id R n)

example (R : Type u) [Semiring R] {n m : ℕ} (h : n ≤ m) :
    finStabilize R h (1 : GL (Fin n) R) = (1 : GL (Fin m) R) :=
  (finStabilize R h).map_one

example {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) PUnit.{1}) (i j : Fin m) :
    finStabilize PUnit.{1} h g i j = 0 :=
  Subsingleton.elim _ _

end Matrix.GeneralLinearGroup
