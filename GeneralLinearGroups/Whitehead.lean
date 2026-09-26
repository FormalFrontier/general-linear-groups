/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The Whitehead block factorization

This file proves the standard four-factor decomposition of the block diagonal
unit `diag(g, g⁻¹)`. As an application, it lifts this block diagonal through a
surjective ring homomorphism by lifting the entries of `g` and `g⁻¹`
separately. It does not assert that the map on the original general linear
group is surjective.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uR uS uT

/-- The map on general linear groups induced by a homomorphism of arbitrary
semirings. This is the noncommutative counterpart of the existing commutative
API `GeneralLinearGroup.map`. -/
def mapRingHom {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    (f : R →+* S) : GL ι R →* GL ι S :=
  Units.map f.mapMatrix.toMonoidHom

/-- The induced map on general linear groups applies the coefficient homomorphism to each entry. -/
@[simp]
lemma mapRingHom_apply {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    (f : R →+* S) (g : GL ι R) (i j : ι) :
    mapRingHom f g i j = f (g i j) := rfl

/-- The identity coefficient homomorphism induces the identity on the general linear group. -/
@[simp]
lemma mapRingHom_id {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {R : Type uR} [Semiring R] :
    mapRingHom (RingHom.id R) = MonoidHom.id (GL ι R) := rfl

/-- Composition of coefficient homomorphisms induces composition of the corresponding group maps. -/
@[simp]
lemma mapRingHom_comp {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {R : Type uR} {S : Type uS} {T : Type uT}
    [Semiring R] [Semiring S] [Semiring T]
    (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom (ι := ι) f) := rfl

section Blocks

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
  {R : Type uR} [Ring R]

/-- A block matrix with two copies of the same index type. -/
abbrev BlockMatrix := Matrix (ι ⊕ ι) (ι ⊕ ι) R

/-- The upper unitriangular block matrix with upper-right block `a`. -/
def upperUnit (a : Matrix ι ι R) : (BlockMatrix (ι := ι) (R := R))ˣ where
  val := Matrix.fromBlocks 1 a 0 1
  inv := Matrix.fromBlocks 1 (-a) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

/-- The lower unitriangular block matrix with lower-left block `-a`. -/
def lowerUnit (a : Matrix ι ι R) : (BlockMatrix (ι := ι) (R := R))ˣ where
  val := Matrix.fromBlocks 1 0 (-a) 1
  inv := Matrix.fromBlocks 1 0 a 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

/-- The signed block-swap unit. -/
def swapUnit : (BlockMatrix (ι := ι) (R := R))ˣ where
  val := Matrix.fromBlocks 0 (-1) 1 0
  inv := Matrix.fromBlocks 0 1 (-1) 0
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

/-- The block diagonal unit with diagonal entries `g` and `g⁻¹`. -/
def blockDiagonalUnit (g : GL ι R) : (BlockMatrix (ι := ι) (R := R))ˣ where
  val := Matrix.fromBlocks (g : Matrix ι ι R) 0 0
    ((g⁻¹ : GL ι R) : Matrix ι ι R)
  inv := Matrix.fromBlocks ((g⁻¹ : GL ι R) : Matrix ι ι R) 0 0
    (g : Matrix ι ι R)
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

/-- The Whitehead factorization of `diag(g, g⁻¹)`. The factor order is valid
over an arbitrary, possibly noncommutative, ring. -/
theorem blockDiagonalUnit_eq (g : GL ι R) :
    blockDiagonalUnit g =
      upperUnit (g : Matrix ι ι R) *
        lowerUnit ((g⁻¹ : GL ι R) : Matrix ι ι R) *
          upperUnit (g : Matrix ι ι R) * swapUnit := by
  apply Units.ext
  simp [blockDiagonalUnit, upperUnit, lowerUnit, swapUnit,
    Matrix.fromBlocks_multiply]

end Blocks

section MapBlocks

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
  {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- A coefficient homomorphism sends an upper block unit to the upper unit of its mapped block. -/
@[simp]
theorem mapRingHom_upperUnit (f : R →+* S) (a : Matrix ι ι R) :
    mapRingHom f (upperUnit a) = upperUnit (f.mapMatrix a) := by
  apply Units.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases h : i = j <;> simp [mapRingHom, upperUnit, h]

/-- A coefficient homomorphism sends a lower block unit to the lower unit of its mapped block. -/
@[simp]
theorem mapRingHom_lowerUnit (f : R →+* S) (a : Matrix ι ι R) :
    mapRingHom f (lowerUnit a) = lowerUnit (f.mapMatrix a) := by
  apply Units.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases h : i = j <;> simp [mapRingHom, lowerUnit, h]

/-- The signed block-swap unit is preserved by every coefficient ring homomorphism. -/
@[simp]
theorem mapRingHom_swapUnit (f : R →+* S) :
    mapRingHom f (swapUnit (ι := ι)) = swapUnit := by
  apply Units.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases h : i = j <;> simp [mapRingHom, swapUnit, h]

/-- An entrywise choice of matrix preimages under a surjective ring
homomorphism. -/
noncomputable def liftMatrix (f : R →+* S) (hf : Function.Surjective f)
    (a : Matrix ι ι S) : Matrix ι ι R :=
  fun i j ↦ Classical.choose (hf (a i j))

/-- Mapping a chosen entrywise lift along the surjective homomorphism recovers the matrix. -/
@[simp]
theorem mapMatrix_liftMatrix (f : R →+* S) (hf : Function.Surjective f)
    (a : Matrix ι ι S) :
    f.mapMatrix (liftMatrix f hf a) = a := by
  ext i j
  exact Classical.choose_spec (hf (a i j))

/-- Lift `diag(g, g⁻¹)` through a surjective ring homomorphism. The entries of
`g` and `g⁻¹` are lifted separately inside unitriangular block factors. -/
noncomputable def liftBlockDiagonal (f : R →+* S)
    (hf : Function.Surjective f) (g : GL ι S) : GL (ι ⊕ ι) R :=
  upperUnit (liftMatrix f hf (g : Matrix ι ι S)) *
    lowerUnit (liftMatrix f hf ((g⁻¹ : GL ι S) : Matrix ι ι S)) *
      upperUnit (liftMatrix f hf (g : Matrix ι ι S)) * swapUnit

/-- The lifted Whitehead product maps to the block diagonal unit `diag(g, g⁻¹)`. -/
@[simp]
theorem mapRingHom_liftBlockDiagonal (f : R →+* S)
    (hf : Function.Surjective f) (g : GL ι S) :
    mapRingHom f (liftBlockDiagonal f hf g) = blockDiagonalUnit g := by
  simp only [liftBlockDiagonal, map_mul, mapRingHom_upperUnit,
    mapRingHom_lowerUnit, mapRingHom_swapUnit, mapMatrix_liftMatrix]
  exact (blockDiagonalUnit_eq g).symm

end MapBlocks

end Matrix.GeneralLinearGroup
