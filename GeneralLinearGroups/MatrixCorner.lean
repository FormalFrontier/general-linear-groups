/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.RingTheory.Idempotents

/-!
# A single-entry matrix corner

The corner supported at a chosen diagonal entry of a finite matrix semiring is
equivalent to its coefficient semiring. The identity of this corner is the
diagonal matrix unit, not necessarily the identity of the ambient matrix semiring.
-/

@[expose] public section

universe u v

namespace Matrix

variable {R : Type u} [Semiring R] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- A diagonal matrix unit is idempotent, even when the coefficient semiring is trivial. -/
theorem isIdempotentElem_single_one (i : ι) :
    IsIdempotentElem (single i i (1 : R)) := by
  simp [IsIdempotentElem]

/-- A matrix belongs to a single-entry corner precisely when it is its supported entry. -/
theorem mem_single_corner_iff (i : ι) (A : Matrix ι ι R) :
    A ∈ Subsemigroup.corner (single i i (1 : R)) ↔ A = single i i (A i i) := by
  rw [Subsemigroup.mem_corner_iff (isIdempotentElem_single_one (R := R) i)]
  constructor
  · rintro ⟨hleft, hright⟩
    calc
      A = single i i (1 : R) * A * single i i 1 := by rw [hleft, hright]
      _ = single i i (A i i) := by simp
  · intro h
    constructor <;> rw [h] <;> simp

/-- Equivalently, every entry outside the chosen diagonal position vanishes. -/
theorem mem_single_corner_iff_support (i : ι) (A : Matrix ι ι R) :
    A ∈ Subsemigroup.corner (single i i (1 : R)) ↔
      ∀ j k, (j ≠ i ∨ k ≠ i) → A j k = 0 := by
  rw [mem_single_corner_iff]
  constructor
  · intro h j k hne
    rw [h]
    apply single_apply_of_ne
    rintro ⟨hij, hik⟩
    rcases hne with hj | hk
    · exact hj hij.symm
    · exact hk hik.symm
  · intro h
    ext j k
    by_cases hj : j = i
    · by_cases hk : k = i
      · subst j; subst k; simp
      · calc
          A j k = 0 := h j k (Or.inr hk)
          _ = single i i (A i i) j k :=
            (single_apply_of_ne i i (A i i) j k (by
              rintro ⟨_, hki⟩
              exact hk hki.symm)).symm
    · calc
        A j k = 0 := h j k (Or.inl hj)
        _ = single i i (A i i) j k :=
          (single_apply_of_ne i i (A i i) j k (by
            rintro ⟨hji, _⟩
            exact hj hji.symm)).symm

/-- The entry map identifies a diagonal matrix-unit corner with the coefficient
semiring. Its inverse inserts a coefficient at the chosen diagonal position. -/
def singleCornerRingEquiv (i : ι) :
    (isIdempotentElem_single_one (R := R) i).Corner ≃+* R where
  toFun C := C.1 i i
  invFun r := ⟨single i i r,
    (mem_single_corner_iff i _).2 (by simp)⟩
  left_inv := by
    intro C
    apply Subtype.ext
    exact ((mem_single_corner_iff i C.1).1 C.2).symm
  right_inv := by
    intro r
    simp
  map_mul' := by
    intro C D
    change (C.1 * D.1) i i = C.1 i i * D.1 i i
    rw [(mem_single_corner_iff i C.1).1 C.2,
      (mem_single_corner_iff i D.1).1 D.2]
    simp
  map_add' := by
    intro C D
    rfl

@[simp]
theorem singleCornerRingEquiv_apply (i : ι)
    (C : (isIdempotentElem_single_one (R := R) i).Corner) :
    singleCornerRingEquiv i C = C.1 i i := rfl

@[simp]
theorem singleCornerRingEquiv_symm_apply_coe (i : ι) (r : R) :
    ((singleCornerRingEquiv i).symm r).1 = single i i r := rfl

@[simp]
theorem single_corner_one_coe (i : ι) :
    (1 : (isIdempotentElem_single_one (R := R) i).Corner).1 =
      single i i (1 : R) := rfl

@[simp]
theorem single_corner_zero_coe (i : ι) :
    (0 : (isIdempotentElem_single_one (R := R) i).Corner).1 =
      (0 : Matrix ι ι R) := rfl

/-- On a singleton index, entry extraction agrees with the full-matrix equivalence. -/
theorem singleCornerRingEquiv_apply_eq_uniqueRingEquiv [Unique ι] (i : ι)
    (C : (isIdempotentElem_single_one (R := R) i).Corner) :
    singleCornerRingEquiv i C = uniqueRingEquiv C.1 := by
  have hi : i = default := Subsingleton.elim _ _
  subst i
  rfl

end Matrix
