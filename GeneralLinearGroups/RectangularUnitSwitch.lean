/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.ZeroProductStabilization
import GeneralLinearGroups.RectangularIsomorphisms
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Matrix.Invertible
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Switching rectangular unit products

Over an arbitrary ring, a unit with matrix `1 + A * B` determines a unit with
matrix `1 + B * A`. Its inverse is read back through the ordered product
`1 - B * (1 + A * B)⁻¹ * A`. The diagonal pair of the original unit and the
inverse switched unit admits an ordered factorization into four rectangular
elementary shears. Empty blocks and the zero ring are permitted.

## References

The inverse-value proof specializes the two-object preadditive Jacobson identity.
It uses Mathlib's `Mat_` and `SingleObj` categories, finite-index reindexing and the
`Units`/`Aut` correspondence. The unit construction retains Mathlib's matrix
invertibility interfaces.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR} [Ring R]

/-- Switch the rectangular factors of a unit represented by `1 + A * B`. -/
def rectangularUnitSwitch (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) : GL Y R := by
  letI : Invertible (1 + A * B : Matrix X X R) := hg ▸ g.invertible
  letI : Invertible (1 : Matrix X X R) := invertibleOne
  letI : Invertible (1 : Matrix Y Y R) := invertibleOne
  letI : Invertible (⅟(1 : Matrix X X R) + A * ⅟(1 : Matrix Y Y R) * B) := by
    simpa only [invOf_one, Matrix.one_mul, Matrix.mul_one] using
      (inferInstance : Invertible (1 + A * B : Matrix X X R))
  letI : Invertible (1 + B * A : Matrix Y Y R) := by
    simpa only [Matrix.mul_one] using
      (Matrix.invertibleAddMulMul (1 : Matrix Y Y R) B (1 : Matrix X X R) A)
  exact unitOfInvertible (1 + B * A)

/-- The switched unit has matrix `1 + B * A`. -/
@[simp]
theorem rectangularUnitSwitch_val (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) :
    (rectangularUnitSwitch A B g hg : Matrix Y Y R) = 1 + B * A := rfl

open CategoryTheory in
/-- The inverse switched unit has the ordered inverse from the preadditive Jacobson identity. -/
@[simp]
theorem rectangularUnitSwitch_inv_val (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) :
    (((rectangularUnitSwitch A B g hg)⁻¹ : GL Y R) : Matrix Y Y R) =
      1 - B * ((g⁻¹ : GL X R) : Matrix X X R) * A := by
  -- Reindex before forming the stock matrix category: its indices are small,
  -- while X, Y and the coefficient ring retain their independent universes.
  let eX := Fintype.equivFin X
  let eY := Fintype.equivFin Y
  let rX := Matrix.reindexRingEquiv R eX
  let rY := Matrix.reindexRingEquiv R eY
  let Af := Matrix.reindex eX eY A
  let Bf := Matrix.reindex eY eX B
  let J (ι : Type) [Fintype ι] : Mat_ (SingleObj R) :=
    ⟨ι, fun _ => SingleObj.star R⟩
  let T {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix ι κ R) : J κ ⟶ J ι :=
    fun i j => M j i
  have T_one (ι : Type) [Fintype ι] [DecidableEq ι] :
      T (1 : Matrix ι ι R) = 𝟙 (J ι) := by
    apply Mat_.hom_ext
    intro i j
    by_cases h : i = j
    · subst j
      simp [T, J, SingleObj.id_as_one]
    · simp [T, J, h, Ne.symm h]
  have T_mul {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]
      (M : Matrix ι κ R) (N : Matrix κ ν R) : T (M * N) = T N ≫ T M := rfl
  have T_add {ι κ : Type} [Fintype ι] [Fintype κ] (M N : Matrix ι κ R) :
      T (M + N) = T M + T N := rfl
  have T_sub {ι κ : Type} [Fintype ι] [Fintype κ] (M N : Matrix ι κ R) :
      T (M - N) = T M - T N := rfl
  have T_injective {ι κ : Type} [Fintype ι] [Fintype κ] :
      Function.Injective (T (ι := ι) (κ := κ)) := by
    intro M N h
    ext i j
    exact congrFun (congrFun h j) i
  -- End multiplication reverses composition, so this transpose is multiplicative.
  let F (ι : Type) [Fintype ι] [DecidableEq ι] : Matrix ι ι R →+* End (J ι) :=
    { toFun := T
      map_zero' := rfl
      map_one' := T_one ι
      map_add' := T_add
      map_mul' := T_mul }
  let fX := (F (Fin (Fintype.card X))).comp rX.toRingHom
  let fY := (F (Fin (Fintype.card Y))).comp rY.toRingHom
  let w := rectangularUnitSwitch A B g hg
  let ig : Aut (J (Fin (Fintype.card X))) :=
    Aut.unitsEndEquivAut _ (Units.map fX.toMonoidHom g)
  let iw : Aut (J (Fin (Fintype.card Y))) :=
    Aut.unitsEndEquivAut _ (Units.map fY.toMonoidHom w)
  have ig_hom : ig.hom = T (rX (g : Matrix X X R)) := rfl
  have ig_inv : ig.inv = T (rX ((g⁻¹ : GL X R) : Matrix X X R)) := rfl
  have iw_hom : iw.hom = T (rY (w : Matrix Y Y R)) := rfl
  have iw_inv : iw.inv = T (rY ((w⁻¹ : GL Y R) : Matrix Y Y R)) := rfl
  have hAB : rX (A * B) = Af * Bf :=
    (Matrix.submatrix_mul_equiv A B eX.symm eY.symm eX.symm).symm
  have hBA : rY (B * A) = Bf * Af :=
    (Matrix.submatrix_mul_equiv B A eY.symm eX.symm eY.symm).symm
  have hg' : rX (g : Matrix X X R) = 1 + Af * Bf := by
    rw [hg, map_add, map_one, hAB]
  have hw' : rY (w : Matrix Y Y R) = 1 + Bf * Af := by
    change rY (rectangularUnitSwitch A B g hg : Matrix Y Y R) = _
    rw [rectangularUnitSwitch_val, map_add, map_one, hBA]
  let a : J (Fin (Fintype.card Y)) ⟶ J (Fin (Fintype.card X)) := -T Af
  let b : J (Fin (Fintype.card X)) ⟶ J (Fin (Fintype.card Y)) := T Bf
  have hp : 𝟙 _ - b ≫ a = ig.hom := by
    dsimp only [a, b]
    rw [ig_hom, hg', T_add, T_one, T_mul, Preadditive.comp_neg, sub_neg_eq_add]
  have hq : 𝟙 _ - a ≫ b = iw.hom := by
    dsimp only [a, b]
    rw [iw_hom, hw', T_add, T_one, T_mul, Preadditive.neg_comp, sub_neg_eq_add]
  let : IsIso (𝟙 _ - b ≫ a) := by rw [hp]; exact ig.isIso_hom
  let : IsIso (𝟙 _ - a ≫ b) := (isIso_id_sub_comp_iff a b).mpr inferInstance
  have hpi : CategoryTheory.inv (𝟙 _ - b ≫ a) = ig.inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [hp]
    exact ig.hom_inv_id
  have hqi : CategoryTheory.inv (𝟙 _ - a ≫ b) = iw.inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [hq]
    exact iw.hom_inv_id
  have h := inv_id_sub_comp a b
  rw [hqi, hpi, iw_inv, ig_inv] at h
  have hfinite : rY ((w⁻¹ : GL Y R) : Matrix Y Y R) =
      1 - Bf * rX ((g⁻¹ : GL X R) : Matrix X X R) * Af := by
    apply T_injective
    calc
      T (rY ((w⁻¹ : GL Y R) : Matrix Y Y R)) =
          𝟙 _ + a ≫ T (rX ((g⁻¹ : GL X R) : Matrix X X R)) ≫ b := h
      _ = T (1 - Bf * rX ((g⁻¹ : GL X R) : Matrix X X R) * Af) := by
        rw [T_sub, T_one, T_mul, T_mul]
        simp only [a, b, Preadditive.neg_comp, sub_eq_add_neg]
  have hproduct : Bf * rX ((g⁻¹ : GL X R) : Matrix X X R) * Af =
      (B * ((g⁻¹ : GL X R) : Matrix X X R) * A).submatrix eY.symm eY.symm := by
    change B.submatrix eY.symm eX.symm *
      (((g⁻¹ : GL X R) : Matrix X X R).submatrix eX.symm eX.symm) *
      A.submatrix eX.symm eY.symm = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  apply rY.injective
  change rY ((w⁻¹ : GL Y R) : Matrix Y Y R) = _
  rw [hfinite, map_sub, map_one]
  exact congrArg
    (fun M : Matrix (Fin (Fintype.card Y)) (Fin (Fintype.card Y)) R => 1 - M) hproduct

/-- The switched unit is uniquely characterized by its matrix value. -/
theorem eq_rectangularUnitSwitch (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B)
    (h : GL Y R) (hh : (h : Matrix Y Y R) = 1 + B * A) :
    h = rectangularUnitSwitch A B g hg := by
  apply Units.ext
  rw [hh, rectangularUnitSwitch_val]

/-- Switching the factors twice recovers the original unit. -/
@[simp]
theorem rectangularUnitSwitch_switch (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) :
    rectangularUnitSwitch B A (rectangularUnitSwitch A B g hg)
      (rectangularUnitSwitch_val A B g hg) = g := by
  apply Units.ext
  rw [rectangularUnitSwitch_val]
  exact hg.symm

/-- The diagonal pair is an ordered product of four rectangular shears. -/
theorem diagonalPairUnit_rectangularUnitSwitch_inv_eq
    (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) :
    diagonalPairUnit g ((rectangularUnitSwitch A B g hg)⁻¹) =
      rectangularUpperUnit A * rectangularLowerUnit B *
        rectangularUpperUnit (-(((g⁻¹ : GL X R) : Matrix X X R) * A)) *
        rectangularLowerUnit (-(B * (g : Matrix X X R))) := by
  let P : Matrix X X R := g
  let T : Matrix X X R := ((g⁻¹ : GL X R) : Matrix X X R)
  let S : Matrix Y Y R := 1 - B * T * A
  have hPT : P * T = 1 := by
    simpa only [P, T, Units.val_mul, Units.val_one] using
      congrArg (fun u : GL X R => (u : Matrix X X R)) (mul_inv_cancel g)
  have hTP : T * P = 1 := by
    simpa only [P, T, Units.val_mul, Units.val_one] using
      congrArg (fun u : GL X R => (u : Matrix X X R)) (inv_mul_cancel g)
  have hAP : A * B = P - 1 := by
    dsimp [P]
    rw [hg]
    simp
  have hPTA : P * (T * A) = A := by
    rw [← Matrix.mul_assoc, hPT, Matrix.one_mul]
  have hTAB : T * A * B = 1 - T := by
    rw [Matrix.mul_assoc, hAP, Matrix.mul_sub, hTP, Matrix.mul_one]
  have hSB : S * B = B * T := by
    simp only [S, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T A B, hTAB, Matrix.mul_sub, Matrix.mul_one]
    simp
  have hSBP : S * (B * P) = B := by
    rw [← Matrix.mul_assoc, hSB, Matrix.mul_assoc, hTP, Matrix.mul_one]
  have hfirst : ((rectangularUpperUnit A * rectangularLowerUnit B : GL (X ⊕ Y) R) :
      Matrix (X ⊕ Y) (X ⊕ Y) R) = Matrix.fromBlocks P A B 1 := by
    rw [Units.val_mul, rectangularUpperUnit_val, rectangularLowerUnit_val,
      Matrix.fromBlocks_multiply]
    simp [P, ← hg]
  have hsecond : ((rectangularUpperUnit A * rectangularLowerUnit B *
      rectangularUpperUnit (-(T * A)) : GL (X ⊕ Y) R) :
      Matrix (X ⊕ Y) (X ⊕ Y) R) = Matrix.fromBlocks P 0 B S := by
    rw [Units.val_mul, hfirst, rectangularUpperUnit_val, Matrix.fromBlocks_multiply]
    simp [hPTA, S, Matrix.mul_assoc, Matrix.mul_neg, sub_eq_add_neg, add_comm]
  apply Units.ext
  rw [diagonalPairUnit_val, rectangularUnitSwitch_inv_val]
  change Matrix.fromBlocks P 0 0 S = _
  rw [Units.val_mul, hsecond, rectangularLowerUnit_val, Matrix.fromBlocks_multiply]
  simp only [mul_one, Matrix.mul_neg, Matrix.zero_mul, neg_zero, add_zero,
    Matrix.mul_zero, Matrix.mul_one, zero_add, Matrix.fromBlocks_inj, and_true, true_and]
  change 0 = B + -(S * (B * P))
  rw [hSBP]
  exact (add_neg_cancel B).symm

/-- The diagonal pair of a unit and its inverse switched unit is elementary. -/
theorem diagonalPairUnit_rectangularUnitSwitch_inv_mem_elementarySubgroup
    (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) :
    diagonalPairUnit g ((rectangularUnitSwitch A B g hg)⁻¹) ∈
      elementarySubgroup (X ⊕ Y) R := by
  rw [diagonalPairUnit_rectangularUnitSwitch_inv_eq A B g hg]
  exact (elementarySubgroup (X ⊕ Y) R).mul_mem
    ((elementarySubgroup (X ⊕ Y) R).mul_mem
      ((elementarySubgroup (X ⊕ Y) R).mul_mem
        (rectangularUpperUnit_mem_elementarySubgroup A)
        (rectangularLowerUnit_mem_elementarySubgroup B))
      (rectangularUpperUnit_mem_elementarySubgroup
        (-(((g⁻¹ : GL X R) : Matrix X X R) * A))))
    (rectangularLowerUnit_mem_elementarySubgroup (-(B * (g : Matrix X X R))))

/-- Switching a zero-product unit gives the identity on the other block. -/
@[simp]
theorem rectangularUnitSwitch_zeroProductUnit (A : Matrix X Y R) (B : Matrix Y X R)
    (hBA : B * A = 0) :
    rectangularUnitSwitch A B (zeroProductUnit A B hBA)
      (zeroProductUnit_val A B hBA) = 1 := by
  apply Units.ext
  simp [rectangularUnitSwitch_val, hBA]

/-- For zero-product blocks the switched diagonal pair is the published stabilization
commutator. -/
theorem diagonalPairUnit_zeroProductUnit_rectangularUnitSwitch_inv_eq
    (A : Matrix X Y R) (B : Matrix Y X R) (hBA : B * A = 0) :
    diagonalPairUnit (zeroProductUnit A B hBA)
      ((rectangularUnitSwitch A B (zeroProductUnit A B hBA)
        (zeroProductUnit_val A B hBA))⁻¹) =
      rectangularUpperUnit A * rectangularLowerUnit B *
        (rectangularUpperUnit A)⁻¹ * (rectangularLowerUnit B)⁻¹ := by
  rw [rectangularUnitSwitch_zeroProductUnit, inv_one, diagonalPairUnit_one_right]
  exact stabilize_zeroProductUnit_eq A B hBA

end Matrix.GeneralLinearGroup
