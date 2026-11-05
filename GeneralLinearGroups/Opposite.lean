/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.StableGeneralLinear
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# General linear groups over the opposite semiring

Inversion in the group of units, followed by transpose and passage to opposite
coefficients, gives a group isomorphism from `GL ι R` to `GL ι Rᵐᵒᵖ`.
The construction uses the unit inverse, so it applies to noncommutative semirings
and does not require a nonempty index type or a nonzero semiring.

The isomorphism commutes with reindexing, finite stabilization, and coefficient
homomorphisms. Applying it twice is entrywise passage to the double opposite.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uκ uR uS

/-- The inverse-transpose isomorphism to the general linear group over the
opposite semiring. Its `(i, j)` entry is `MulOpposite.op ((g⁻¹) j i)`, where the
inverse is taken in the group of units of the matrix semiring. -/
def opEquiv {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (R : Type uR) [Semiring R] : GL ι R ≃* GL ι Rᵐᵒᵖ :=
  (MulEquiv.inv' (GL ι R)).trans
    (Units.opEquiv.symm.trans
      (Units.mapEquiv (RingEquiv.mopMatrix (m := ι) (α := R)).symm.toMulEquiv))

variable {ι : Type uι} {κ : Type uκ}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The entries of inverse-transpose are the transposed entries of the unit inverse. -/
@[simp]
theorem opEquiv_apply (R : Type uR) [Semiring R] (g : GL ι R) (i j : ι) :
    opEquiv R g i j = MulOpposite.op ((g⁻¹) j i) := rfl

/-- Inverse transport takes the transposed entries of the unit inverse back from
opposite coefficients. -/
@[simp]
theorem opEquiv_symm_apply (R : Type uR) [Semiring R]
    (g : GL ι Rᵐᵒᵖ) (i j : ι) :
    (opEquiv R).symm g i j = MulOpposite.unop ((g⁻¹) j i) := rfl

/-- Inverse-transpose commutes with a change of finite indices. -/
theorem opEquiv_reindexEquiv (R : Type uR) [Semiring R]
    (e : ι ≃ κ) (g : GL ι R) :
    opEquiv R (reindexEquiv R e g) =
      reindexEquiv (Rᵐᵒᵖ) e (opEquiv R g) := by
  apply Units.ext
  ext i j
  simp only [opEquiv_apply, ← map_inv, reindexEquiv_apply]

/-- Inverse transport commutes with a change of finite indices. -/
theorem opEquiv_symm_reindexEquiv (R : Type uR) [Semiring R]
    (e : ι ≃ κ) (g : GL ι Rᵐᵒᵖ) :
    (opEquiv R).symm (reindexEquiv (Rᵐᵒᵖ) e g) =
      reindexEquiv R e ((opEquiv R).symm g) := by
  apply (opEquiv R).injective
  simp only [MulEquiv.apply_symm_apply, opEquiv_reindexEquiv]

/-- Inverse-transpose commutes with adjoining an identity block. -/
theorem opEquiv_stabilize (R : Type uR) [Semiring R] (g : GL ι R) :
    opEquiv R (stabilize (Y := κ) g) =
      stabilize (Y := κ) (opEquiv R g) := by
  apply Units.ext
  ext i j
  rw [opEquiv_apply, ← map_inv (stabilize (Y := κ)) g]
  rcases i with i | i <;> rcases j with j | j
  · simp only [stabilize_apply_inl_inl, opEquiv_apply]
  · simp only [stabilize_apply_inr_inl, stabilize_apply_inl_inr, MulOpposite.op_zero]
  · simp only [stabilize_apply_inl_inr, stabilize_apply_inr_inl, MulOpposite.op_zero]
  · simp only [stabilize_apply_inr_inr, Matrix.one_apply]
    by_cases h : j = i
    · rw [ite_eq_left h, ite_eq_left h.symm, MulOpposite.op_one]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), MulOpposite.op_zero]

/-- Inverse-transpose commutes with every initial-segment stabilization,
including rank zero and equal ranks. -/
theorem opEquiv_finStabilize (R : Type uR) [Semiring R]
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R) :
    opEquiv R (finStabilize R h g) =
      finStabilize (Rᵐᵒᵖ) h (opEquiv R g) := by
  exact (opEquiv_reindexEquiv R (finBlockEquiv h)
    (stabilize (Y := Fin (m - n)) g)).trans
      (congrArg (reindexEquiv (Rᵐᵒᵖ) (finBlockEquiv h))
        (opEquiv_stabilize (κ := Fin (m - n)) R g))

/-- Inverse transport commutes with every initial-segment stabilization. -/
theorem opEquiv_symm_finStabilize (R : Type uR) [Semiring R]
    {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) Rᵐᵒᵖ) :
    (opEquiv R).symm (finStabilize (Rᵐᵒᵖ) h g) =
      finStabilize R h ((opEquiv R).symm g) := by
  apply (opEquiv R).injective
  simp only [MulEquiv.apply_symm_apply, opEquiv_finStabilize]

/-- Inverse-transpose is natural in arbitrary unital coefficient homomorphisms. -/
theorem mapRingHom_opEquiv {R : Type uR} {S : Type uS}
    [Semiring R] [Semiring S] (f : R →+* S) (g : GL ι R) :
    mapRingHom f.op (opEquiv R g) = opEquiv S (mapRingHom f g) := by
  apply Units.ext
  ext i j
  simp only [mapRingHom_apply, opEquiv_apply, ← map_inv]
  rfl

/-- Inverse transport is natural in arbitrary unital coefficient homomorphisms. -/
theorem mapRingHom_opEquiv_symm {R : Type uR} {S : Type uS}
    [Semiring R] [Semiring S] (f : R →+* S) (g : GL ι Rᵐᵒᵖ) :
    mapRingHom f ((opEquiv R).symm g) =
      (opEquiv S).symm (mapRingHom f.op g) := by
  apply (opEquiv S).injective
  rw [← mapRingHom_opEquiv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- Applying inverse-transpose twice agrees with the canonical coefficient
isomorphism to the double opposite. -/
theorem opEquiv_opEquiv (R : Type uR) [Semiring R] (g : GL ι R) :
    opEquiv (Rᵐᵒᵖ) (opEquiv R g) =
      mapRingHom (RingEquiv.opOp R).toRingHom g := by
  apply Units.ext
  ext i j
  simp only [opEquiv_apply, ← map_inv, inv_inv, mapRingHom_apply]
  exact (RingEquiv.opOp_apply R (g i j)).symm

end Matrix.GeneralLinearGroup
