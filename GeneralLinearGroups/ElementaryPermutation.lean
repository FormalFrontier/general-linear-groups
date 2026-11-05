/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.RelativeElementary
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Signed coordinate swaps and even permutation matrices

The signed coordinate swap with block `[0,1;-1,0]` is the ordered product of
three elementary units. Products on overlapping coordinate pairs give positive
three-cycles. Even permutation matrices therefore belong to the elementary
subgroup over any ring.

Permutation units use Mathlib's `Matrix.permMatrixHom` followed by
`MonoidHom.toHomUnits`. In particular, the unit associated with `σ` has matrix
`σ⁻¹.permMatrix R` and sends the standard column vector `e_i` to `e_(σ i)`.
This differs from the row-pullback convention of `σ.permMatrix R`.

## References

* Charles A. Weibel, *The K-book*, Chapter III, Example 1.2.1.
* Mathlib's permutation matrices and generation of the alternating group by
  three-cycles.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uR uS

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

section Ring

variable {R : Type uR} [Ring R]

/-- The signed coordinate swap `[0,1;-1,0]` on the ordered pair `(i,j)`,
fixing all other coordinates. -/
def signedSwapUnit (i j : ι) (hij : i ≠ j) : GL ι R :=
  elementaryUnit i j hij 1 * elementaryUnit j i hij.symm (-1) *
    elementaryUnit i j hij 1

/-- The matrix of the signed coordinate swap. -/
@[simp]
theorem signedSwapUnit_val (i j : ι) (hij : i ≠ j) :
    (signedSwapUnit (R := R) i j hij : Matrix ι ι R) =
      1 - Matrix.single i i 1 - Matrix.single j j 1 +
        Matrix.single i j 1 - Matrix.single j i 1 := by
  simp [signedSwapUnit, mul_add, add_mul, Matrix.single_mul_single_of_ne,
    hij.symm, ← Matrix.single_neg]
  abel

/-- On column vectors the signed swap replaces the `i` coordinate by the old
`j` coordinate and the `j` coordinate by the negative old `i` coordinate. -/
theorem signedSwapUnit_mulVec (i j : ι) (hij : i ≠ j) (v : ι → R) :
    (signedSwapUnit (R := R) i j hij : Matrix ι ι R) *ᵥ v =
      fun a => if a = i then v j else if a = j then -v i else v a := by
  rw [signedSwapUnit_val]
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec, one_mul]
  funext a
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    simp_all

/-- The signed coordinate swap belongs to the original finite elementary
subgroup; this is Weibel, Chapter III, Example 1.2.1. -/
theorem signedSwapUnit_mem_elementarySubgroup (i j : ι) (hij : i ≠ j) :
    signedSwapUnit (R := R) i j hij ∈ elementarySubgroup ι R := by
  exact (elementarySubgroup ι R).mul_mem
    ((elementarySubgroup ι R).mul_mem (elementaryUnit_mem i j hij 1)
      (elementaryUnit_mem j i hij.symm (-1)))
    (elementaryUnit_mem i j hij 1)

/-- The indicated product sends `e_i` to `e_k`, `e_j` to `e_i`, and `e_k`
to `e_j`, with positive signs, fixing every other standard column vector.
This is the three-cycle product in Weibel, Chapter III, Example 1.2.1. -/
theorem signedSwapUnit_mul_signedSwapUnit (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    signedSwapUnit (R := R) j k hjk * signedSwapUnit i j hij =
      (Matrix.permMatrixHom (n := ι) (R := R)).toHomUnits
        (Equiv.swap j k * Equiv.swap i j) := by
  apply Units.ext
  apply Matrix.mulVec_injective
  funext v
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, signedSwapUnit_mulVec,
    MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mulVec]
  funext a
  by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hak : a = k <;>
    simp_all [Function.comp_apply, Equiv.swap_apply_def, eq_comm]

/-- The permutation unit sending `e_i` to `e_(σ i)` is elementary when `σ`
is even, over an arbitrary ring and in the original finite index type.
This is Weibel, Chapter III, Example 1.2.1; generation by three-cycles is
provided by Mathlib. -/
theorem permMatrixHom_toHomUnits_mem_elementarySubgroup
    (σ : Equiv.Perm ι) (hσ : Equiv.Perm.sign σ = 1) :
    (Matrix.permMatrixHom (n := ι) (R := R)).toHomUnits σ ∈
      elementarySubgroup ι R := by
  let K := (elementarySubgroup ι R).comap
    (Matrix.permMatrixHom (n := ι) (R := R)).toHomUnits
  have hK : alternatingGroup ι ≤ K := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro g hg
    obtain ⟨a, ha⟩ := hg.isCycle.nonempty_support
    have hn := hg.nodup_iff_mem_support.mpr ha
    have hij : g (g a) ≠ g a := by grind
    have hjk : g a ≠ a := by grind
    have hik : g (g a) ≠ a := by grind
    change (Matrix.permMatrixHom (n := ι) (R := R)).toHomUnits g ∈
      elementarySubgroup ι R
    rw [hg.eq_swap_mul_swap_iff_mem_support.mpr ha,
      Equiv.swap_comm a (g a), Equiv.swap_comm (g a) (g (g a)),
      ← signedSwapUnit_mul_signedSwapUnit (R := R) (g (g a)) (g a) a hij hjk hik]
    exact (elementarySubgroup ι R).mul_mem
      (signedSwapUnit_mem_elementarySubgroup (g a) a hjk)
      (signedSwapUnit_mem_elementarySubgroup (g (g a)) (g a) hij)
  exact hK (Equiv.Perm.mem_alternatingGroup.mpr hσ)

/-- Coefficient homomorphisms preserve the signed coordinate swap. -/
@[simp]
theorem mapRingHom_signedSwapUnit {S : Type uS} [Ring S]
    (f : R →+* S) (i j : ι) (hij : i ≠ j) :
    mapRingHom f (signedSwapUnit (R := R) i j hij) =
      signedSwapUnit (R := S) i j hij := by
  simp [signedSwapUnit, map_mul]

end Ring

/-- Coefficient homomorphisms preserve the permutation units obtained from
Mathlib's permutation-matrix homomorphism. -/
@[simp]
theorem mapRingHom_permMatrixHom_toHomUnits
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    (f : R →+* S) (σ : Equiv.Perm ι) :
    mapRingHom f ((Matrix.permMatrixHom (n := ι) (R := R)).toHomUnits σ) =
      (Matrix.permMatrixHom (n := ι) (R := S)).toHomUnits σ := by
  apply Units.ext
  exact PEquiv.map_toMatrix f (σ⁻¹).toPEquiv

end Matrix.GeneralLinearGroup
