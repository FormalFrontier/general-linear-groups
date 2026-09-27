/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.Elementary
public import Mathlib.GroupTheory.IsPerfect

/-!
# Elementary commutators over arbitrary rings

Disjoint elementary positions commute, and elementary units in three distinct
positions satisfy the ordered Steinberg commutator relation. When the index type
has at least three elements, these relations make its elementary subgroup perfect.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {R : Type v} [Ring R]

open scoped commutatorElement

/-- Elementary units commute when neither off-diagonal position composes with the other. -/
theorem elementaryUnit_commute_disjoint (i j k l : ι)
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    Commute (elementaryUnit i j hij a) (elementaryUnit k l hkl b) := by
  change elementaryUnit i j hij a * elementaryUnit k l hkl b =
    elementaryUnit k l hkl b * elementaryUnit i j hij a
  apply Units.ext
  simp only [Units.val_mul, elementaryUnit_val]
  simp only [add_mul, mul_add, one_mul, mul_one]
  rw [Matrix.single_mul_single_of_ne a i j k hjk b,
    Matrix.single_mul_single_of_ne b k l i hli a]
  abel

private theorem elementaryUnit_mul_cross (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    elementaryUnit i j hij a * elementaryUnit j k hjk b =
      elementaryUnit i k hik (a * b) *
        (elementaryUnit j k hjk b * elementaryUnit i j hij a) := by
  apply Units.ext
  simp only [Units.val_mul, elementaryUnit_val]
  simp only [add_mul, mul_add, one_mul, mul_one]
  simp only [Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne b j k i hik.symm a,
    Matrix.single_mul_single_of_ne (a * b) i k j hjk.symm b,
    Matrix.single_mul_single_of_ne (a * b) i k i hik.symm a,
    mul_zero, add_zero]
  abel

/-- The ordered elementary commutator relation, valid for noncommutative rings. -/
theorem elementaryUnit_commutator (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅elementaryUnit i j hij a, elementaryUnit j k hjk b⁆ =
      elementaryUnit i k hik (a * b) := by
  have hmul := elementaryUnit_mul_cross i j k hij hjk hik a b
  calc
    ⁅elementaryUnit i j hij a, elementaryUnit j k hjk b⁆ =
        (elementaryUnit i j hij a * elementaryUnit j k hjk b) *
          (elementaryUnit j k hjk b * elementaryUnit i j hij a)⁻¹ := by
            simp [commutatorElement_def, mul_assoc]
    _ = elementaryUnit i k hik (a * b) := by rw [hmul]; group

/-- A third index expresses every elementary generator as a commutator of generators. -/
theorem elementaryUnit_eq_commutator (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (a : R) :
    elementaryUnit i j hij a =
      ⁅elementaryUnit i k hik a, elementaryUnit k j hkj (1 : R)⁆ := by
  simpa only [mul_one] using
    (elementaryUnit_commutator i k j hik hkj hij a (1 : R)).symm

/-- The finite-rank elementary subgroup is perfect as soon as there are three indices. -/
theorem elementarySubgroup_isPerfect_of_three_le_card
    (hcard : 3 ≤ Fintype.card ι) : Group.IsPerfect (elementarySubgroup ι R) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro x hx y hy
    rw [commutatorElement_def]
    exact (elementarySubgroup ι R).mul_mem
      ((elementarySubgroup ι R).mul_mem
        ((elementarySubgroup ι R).mul_mem hx hy)
        ((elementarySubgroup ι R).inv_mem hx))
      ((elementarySubgroup ι R).inv_mem hy)
  · change Subgroup.closure _ ≤ ⁅elementarySubgroup ι R, elementarySubgroup ι R⁆
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, j, hij, a, rfl⟩
    have hthird : ∃ k : ι, k ≠ i ∧ k ≠ j := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset ι) ⊆ {i, j} := by
        intro x _
        by_cases hxi : x = i
        · simp [hxi]
        · simp [h x hxi]
      have hsmall := Finset.card_le_card hsub
      have hpair : ({i, j} : Finset ι).card = 2 := by simp [hij]
      simp only [Finset.card_univ, hpair] at hsmall
      omega
    obtain ⟨k, hki, hkj⟩ := hthird
    rw [elementaryUnit_eq_commutator i j k hij hki.symm hkj a]
    exact Subgroup.commutator_mem_commutator
      (elementaryUnit_mem i k hki.symm a)
      (elementaryUnit_mem k j hkj (1 : R))

end Matrix.GeneralLinearGroup
