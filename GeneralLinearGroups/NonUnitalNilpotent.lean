/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.CongruenceSubgroup
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Nilpotent matrices over nonunital semirings

This file defines strictly positive powers and nilpotence without assuming a
multiplicative identity. It proves their agreement with ordinary powers and
nilpotence when a unit is present. Strict upper triangularity is defined using
only zero; its positive-power support bound holds over nonunital,
nonassociative semirings, and its nilpotence over nonunital semirings.
No commutativity is assumed.

For nonunital rings, entrywise inclusion into the canonical unitization relates
nonunital nilpotence to ordinary nilpotence and constructs the corresponding
element of the relative general linear group. These constructions retain their
nonunital ring hypotheses.

Positive-power index `k` always means `k + 1` factors, including on empty matrices.
-/

set_option warningAsError true

@[expose] public section

namespace NonUnital

universe u

variable {A : Type u}

/-- The product of `k + 1` copies of an element, defined without a
multiplicative identity. -/
def positivePow [Mul A] (x : A) : ℕ → A :=
  Nat.rec x (fun _ y => y * x)

/-- The zeroth index of the positive-power sequence is the product of one copy of `x`. -/
@[simp]
theorem positivePow_zero [Mul A] (x : A) : positivePow x 0 = x := rfl

/-- The next positive power is obtained by multiplying the preceding product by `x` on the right. -/
@[simp]
theorem positivePow_succ [Mul A] (x : A) (k : ℕ) :
    positivePow x (k + 1) = positivePow x k * x := rfl

/-- Nilpotence in a possibly nonunital multiplicative structure: some
strictly positive power is zero. -/
def IsNilpotent [SemigroupWithZero A] (x : A) : Prop :=
  ∃ k, positivePow x k = 0

/-- In a monoid, positive-power index `k` agrees with the ordinary power `k + 1`. -/
theorem positivePow_eq_pow [Monoid A] (x : A) (k : ℕ) :
    positivePow x k = x ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      simpa only [positivePow_succ, ih] using (pow_succ x (k + 1)).symm

/-- In a monoid with zero, strictly-positive-power nilpotence agrees with ordinary
nilpotence, including when an ordinary nilpotence witness is zero. -/
theorem isNilpotent_iff [MonoidWithZero A] (x : A) :
    NonUnital.IsNilpotent x ↔ _root_.IsNilpotent x := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    rwa [positivePow_eq_pow] at hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [positivePow_eq_pow, pow_succ, hk, zero_mul]

end NonUnital

/-- If `r ^ k = 0`, package `1 + r` as a unit with its explicit finite
alternating geometric-series inverse. -/
def IsNilpotent.oneAddUnitOfPowEqZero {A : Type*} [Ring A]
    (r : A) (k : ℕ) (hk : r ^ k = 0) : Aˣ where
  val := 1 + r
  inv := ∑ i ∈ Finset.range k, (-r) ^ i
  val_inv := by
    have hneg : (-r : A) ^ k = 0 := by
      rw [neg_pow, hk, mul_zero]
    change (1 + r) * (∑ i ∈ Finset.range k, (-r) ^ i) = 1
    rw [show 1 + r = 1 - (-r) by abel, mul_neg_geom_sum, hneg, sub_zero]
  inv_val := by
    have hneg : (-r : A) ^ k = 0 := by
      rw [neg_pow, hk, mul_zero]
    change (∑ i ∈ Finset.range k, (-r) ^ i) * (1 + r) = 1
    rw [show 1 + r = 1 - (-r) by abel, geom_sum_mul_neg, hneg, sub_zero]

/-- The unit constructed from `r ^ k = 0` has underlying ring element `1 + r`. -/
@[simp]
theorem IsNilpotent.oneAddUnitOfPowEqZero_val {A : Type*} [Ring A]
    (r : A) (k : ℕ) (hk : r ^ k = 0) :
    (IsNilpotent.oneAddUnitOfPowEqZero r k hk : A) = 1 + r := rfl

/-- The inverse unit of `1 + r` has underlying ring element equal to the finite sum of
`(-r) ^ i` for `i < k`. -/
@[simp]
theorem IsNilpotent.oneAddUnitOfPowEqZero_coe_inv {A : Type*} [Ring A]
    (r : A) (k : ℕ) (hk : r ^ k = 0) :
    (↑((IsNilpotent.oneAddUnitOfPowEqZero r k hk)⁻¹) : A) =
      ∑ i ∈ Finset.range k, (-r) ^ i := rfl

/-- The stored inverse of the unit `1 + r` is the finite sum of `(-r) ^ i` for `i < k`.
This is also the simplification of the coerced inverse unit. -/
theorem IsNilpotent.oneAddUnitOfPowEqZero_inv {A : Type*} [Ring A]
    (r : A) (k : ℕ) (hk : r ^ k = 0) :
    (IsNilpotent.oneAddUnitOfPowEqZero r k hk).inv =
      ∑ i ∈ Finset.range k, (-r) ^ i := by
  simp

namespace Matrix

universe u

variable {I : Type u}

section Zero

variable [Zero I] {n : ℕ}

/-- Strict upper triangularity: diagonal and below-diagonal entries vanish. -/
def IsStrictlyUpperTriangular (x : Matrix (Fin n) (Fin n) I) : Prop :=
  ∀ i j, j.val ≤ i.val → x i j = 0

/-- Strict upper triangularity is upper triangularity together with zero diagonal. -/
theorem isStrictlyUpperTriangular_iff (x : Matrix (Fin n) (Fin n) I) :
    x.IsStrictlyUpperTriangular ↔
      x.IsUpperTriangular ∧ ∀ i : Fin n, x i i = 0 := by
  constructor
  · intro hx
    constructor
    · intro i j hij
      exact hx i j (le_of_lt hij)
    · intro i
      exact hx i i le_rfl
  · rintro ⟨hupper, hdiag⟩ i j hij
    rcases lt_or_eq_of_le (show j ≤ i from hij) with hlt | hEq
    · exact hupper hlt
    · subst j
      exact hdiag i

end Zero

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring I] {n : ℕ}

/-- After multiplying `k + 1` copies of a strictly upper triangular matrix,
possible nonzero entries lie at least `k + 1` places above the diagonal. -/
theorem positivePow_apply_eq_zero_of_isStrictlyUpperTriangular
    {x : Matrix (Fin n) (Fin n) I} (hx : x.IsStrictlyUpperTriangular) :
    ∀ (k : ℕ) (i j : Fin n),
      j.val < i.val + (k + 1) → NonUnital.positivePow x k i j = 0 := by
  intro k
  induction k with
  | zero =>
      intro i j hij
      exact hx i j (by omega)
  | succ k ih =>
      intro i j hij
      rw [NonUnital.positivePow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hil : l.val < i.val + (k + 1)
      · rw [ih i l hil, zero_mul]
      · have hjl : j.val ≤ l.val := by omega
        rw [hx l j hjl, mul_zero]

end NonUnitalNonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring I] {n : ℕ}

/-- A strictly upper triangular `n × n` matrix over a nonunital semiring is
nilpotent. The uniform positive-power witness `n` means `n + 1` factors,
including for an empty matrix. -/
theorem IsStrictlyUpperTriangular.isNilpotent
    {x : Matrix (Fin n) (Fin n) I} (hx : x.IsStrictlyUpperTriangular) :
    NonUnital.IsNilpotent x := by
  refine ⟨n, ?_⟩
  ext i j
  apply positivePow_apply_eq_zero_of_isStrictlyUpperTriangular hx
  omega

end NonUnitalSemiring

section NonUnitalRing

variable [NonUnitalRing I] {n : ℕ}

private theorem isStrictlyUpperTriangular_iff_le_entries_eq_zero
    (x : Matrix (Fin n) (Fin n) I) :
    IsStrictlyUpperTriangular (I := I) (n := n) x ↔
      ∀ i j : Fin n, j.val ≤ i.val → x i j = 0 :=
  Iff.rfl

private theorem positivePow_apply_eq_zero_of_strictlyUpperTriangular
    {x : Matrix (Fin n) (Fin n) I} (hx : x.IsStrictlyUpperTriangular) :
    ∀ (k : ℕ) (i j : Fin n),
      j.val < i.val + (k + 1) → NonUnital.positivePow x k i j = 0 :=
  Matrix.positivePow_apply_eq_zero_of_isStrictlyUpperTriangular
    (I := I) (n := n) (x := x) (hx := hx)

private theorem strictlyUpperTriangular_isNilpotent
    {x : Matrix (Fin n) (Fin n) I} (hx : x.IsStrictlyUpperTriangular) :
    NonUnital.IsNilpotent x :=
  Matrix.IsStrictlyUpperTriangular.isNilpotent
    (I := I) (n := n) (x := x) (hx := hx)

namespace GeneralLinearGroup

universe v

variable {n : Type v} [Fintype n] [DecidableEq n]

/-- Entrywise inclusion of a matrix over a nonunital ring into its canonical
unitization. -/
def unitizationMatrix (x : Matrix n n I) : Matrix n n (Unitization ℤ I) :=
  x.map fun a ↦ (a : Unitization ℤ I)

omit [Fintype n] [DecidableEq n] in
/-- Entrywise inclusion into the unitization sends the zero matrix to zero. -/
@[simp]
theorem unitizationMatrix_zero :
    unitizationMatrix (0 : Matrix n n I) = 0 := by
  apply Matrix.ext
  intro i j
  apply Unitization.ext <;> simp [unitizationMatrix]

omit [DecidableEq n] in
/-- Entrywise inclusion into the unitization preserves multiplication of finite square matrices. -/
theorem unitizationMatrix_mul (x y : Matrix n n I) :
    unitizationMatrix (x * y) = unitizationMatrix x * unitizationMatrix y := by
  apply Matrix.ext
  intro i j
  apply Unitization.ext
  · change 0 = (Unitization.fstHom (R := ℤ) (A := I)).toRingHom
      (∑ k, (x i k : Unitization ℤ I) * (y k j : Unitization ℤ I))
    rw [map_sum]
    simp
  · change (∑ k, x i k * y k j) =
      (Unitization.sndHom ℤ ℤ I)
        (∑ k, (x i k : Unitization ℤ I) * (y k j : Unitization ℤ I))
    rw [map_sum]
    simp [Unitization.snd_mul]

/-- A product of `k + 1` nonunital matrix factors maps to the ordinary `(k + 1)`st power. -/
theorem unitizationMatrix_positivePow (x : Matrix n n I) (k : ℕ) :
    unitizationMatrix (NonUnital.positivePow x k) =
      unitizationMatrix x ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        unitizationMatrix (NonUnital.positivePow x (k + 1)) =
            unitizationMatrix (NonUnital.positivePow x k) *
              unitizationMatrix x := by
                rw [NonUnital.positivePow_succ, unitizationMatrix_mul]
        _ = unitizationMatrix x ^ (k + 1) * unitizationMatrix x := by
          rw [ih]
        _ = unitizationMatrix x ^ (k + 1 + 1) :=
          (pow_succ (unitizationMatrix x) (k + 1)).symm

/-- Nonunital nilpotence becomes ordinary nilpotence after entrywise
inclusion into the canonical unitization. -/
theorem isNilpotent_unitizationMatrix (x : Matrix n n I)
    (hx : NonUnital.IsNilpotent x) : IsNilpotent (unitizationMatrix x) := by
  obtain ⟨k, hk⟩ := hx
  refine ⟨k + 1, ?_⟩
  rw [← unitizationMatrix_positivePow, hk, unitizationMatrix_zero]

/-- The augmentation from the general linear group over a nonunital ring's
unitization to the general linear group over `ℤ`. -/
def nonUnitalAugmentation : GL n (Unitization ℤ I) →* GL n ℤ :=
  mapRingHom (Unitization.fstHom (R := ℤ) (A := I)).toRingHom

/-- The general linear group of an arbitrary nonunital ring, defined as the
kernel of the augmentation on its canonical unitization. -/
def nonUnitalGeneralLinearGroup : Subgroup (GL n (Unitization ℤ I)) :=
  MonoidHom.ker (nonUnitalAugmentation (n := n) (I := I))

/-- A matrix whose entrywise image in the canonical unitization has a
vanishing power determines an element of the nonunital general linear group. -/
def nilpotentMatrixElement
    (x : Matrix n n I) (k : ℕ) (hk : unitizationMatrix x ^ k = 0) :
    nonUnitalGeneralLinearGroup (n := n) (I := I) := by
  refine ⟨IsNilpotent.oneAddUnitOfPowEqZero (unitizationMatrix x) k hk, ?_⟩
  apply Units.ext
  ext i j
  by_cases h : i = j <;>
    simp [nonUnitalAugmentation, unitizationMatrix, h]

/-- The relative general-linear-group element from a vanishing power has matrix `1 + x`
after entrywise inclusion into the unitization. -/
@[simp]
theorem nilpotentMatrixElement_val
    (x : Matrix n n I) (k : ℕ) (hk : unitizationMatrix x ^ k = 0) :
    ((nilpotentMatrixElement x k hk).1 : Matrix n n (Unitization ℤ I)) =
      1 + unitizationMatrix x := rfl

/-- The inverse of the relative element has underlying matrix equal to the finite alternating
geometric series in the unitized matrix, with length the supplied nilpotence exponent. -/
@[simp]
theorem nilpotentMatrixElement_coe_inv
    (x : Matrix n n I) (k : ℕ) (hk : unitizationMatrix x ^ k = 0) :
    (↑((nilpotentMatrixElement x k hk).1⁻¹) : Matrix n n (Unitization ℤ I)) =
      ∑ i ∈ Finset.range k, (-unitizationMatrix x) ^ i := rfl

/-- The stored inverse of the relative element is the finite alternating geometric series
in the unitized matrix, with length the supplied nilpotence exponent. -/
theorem nilpotentMatrixElement_inv
    (x : Matrix n n I) (k : ℕ) (hk : unitizationMatrix x ^ k = 0) :
    (nilpotentMatrixElement x k hk).1.inv =
      ∑ i ∈ Finset.range k, (-unitizationMatrix x) ^ i := by
  simp

/-- A nilpotent matrix over a nonunital ring canonically determines the
relative general-linear-group element represented by `1 + x`. -/
noncomputable def nonUnitalGeneralLinearGroupOfIsNilpotent
    (x : Matrix n n I) (hx : NonUnital.IsNilpotent x) :
    nonUnitalGeneralLinearGroup (n := n) (I := I) :=
  nilpotentMatrixElement x (isNilpotent_unitizationMatrix x hx).choose
    (isNilpotent_unitizationMatrix x hx).choose_spec

/-- Choosing a nilpotence exponent does not change the underlying matrix `1 + x`
of the resulting relative general-linear-group element. -/
@[simp]
theorem nonUnitalGeneralLinearGroupOfIsNilpotent_val
    (x : Matrix n n I) (hx : NonUnital.IsNilpotent x) :
    ((nonUnitalGeneralLinearGroupOfIsNilpotent x hx).1 :
      Matrix n n (Unitization ℤ I)) = 1 + unitizationMatrix x :=
  nilpotentMatrixElement_val _ _ _

end GeneralLinearGroup

end NonUnitalRing

end Matrix
