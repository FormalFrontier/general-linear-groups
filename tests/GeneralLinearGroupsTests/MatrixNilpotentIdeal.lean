/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups.MatrixNilpotentIdeal
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# A nonzero diagonal over the dual numbers

The coefficient ring is the stock `DualNumber ℤ`. The ideal is the kernel of the
stock first-coordinate ring homomorphism, and the matrix is the standard `Fin 2`
diagonal with entry `TrivSqZeroExt.inr 1`.

The projection kernel has square zero, and the diagonal is nonzero with every
entry in that kernel. The entrywise ideal-power bound gives its square-zero
identity; the uniform-ideal nilpotence theorem gives its nilpotence with the same
exponent two. The dual-number, kernel and coordinate interfaces are from mathlib.
-/

namespace Matrix

private abbrev D : Type := DualNumber ℤ

private abbrev projection : D →+* ℤ :=
  (TrivSqZeroExt.fstHom ℤ ℤ ℤ).toRingHom

private abbrev kernelIdeal : Ideal D := RingHom.ker projection

private abbrev epsilon : D := TrivSqZeroExt.inr (1 : ℤ)

private abbrev epsilonDiagonal : Matrix (Fin 2) (Fin 2) D :=
  Matrix.diagonal (fun _ : Fin 2 => epsilon)

private theorem kernelIdeal_eq_kerIdeal :
    kernelIdeal = TrivSqZeroExt.kerIdeal ℤ ℤ := by
  apply Ideal.ext
  intro x
  constructor
  · intro hx
    have hx0 : projection x = 0 := (RingHom.mem_ker (f := projection)).mp hx
    change x.fst = 0 at hx0
    apply (TrivSqZeroExt.mem_kerIdeal_iff_inr ℤ ℤ x).mpr
    exact TrivSqZeroExt.ext
      (by simpa only [TrivSqZeroExt.fst_inr] using hx0)
      (by simp only [TrivSqZeroExt.snd_inr])
  · intro hx
    apply (RingHom.mem_ker (f := projection)).mpr
    change x.fst = 0
    have hx' := (TrivSqZeroExt.mem_kerIdeal_iff_inr ℤ ℤ x).mp hx
    simpa only [TrivSqZeroExt.fst_inr] using congrArg TrivSqZeroExt.fst hx'

/-- The projection kernel is square-zero and contains a nonzero square-zero diagonal entry. -/
private theorem epsilonDiagonal_nonvacuity :
    kernelIdeal ^ 2 = ⊥ ∧ epsilon ∈ kernelIdeal ∧ epsilon ≠ 0 ∧ epsilon ^ 2 = 0 ∧
      (∀ i j, epsilonDiagonal i j ∈ kernelIdeal) ∧ epsilonDiagonal ≠ 0 := by
  have hkernel : kernelIdeal ^ 2 = ⊥ := by
    rw [kernelIdeal_eq_kerIdeal]
    exact TrivSqZeroExt.kerIdeal_sq ℤ ℤ
  have hepsilon_mem : epsilon ∈ kernelIdeal :=
    (RingHom.mem_ker (f := projection)).mpr (TrivSqZeroExt.fst_inr ℤ (1 : ℤ))
  have hepsilon_ne : epsilon ≠ 0 := by
    intro h
    have h' : (1 : ℤ) = 0 := by
      simpa only [epsilon, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero] using
        congrArg (TrivSqZeroExt.snd : D → ℤ) h
    exact one_ne_zero h'
  have hepsilon_sq : epsilon ^ 2 = 0 := by
    simpa only [epsilon, pow_two] using TrivSqZeroExt.inr_mul_inr ℤ (1 : ℤ) 1
  have hentries : ∀ i j, epsilonDiagonal i j ∈ kernelIdeal := by
    intro i j
    change Matrix.diagonal (fun _ : Fin 2 => epsilon) i j ∈ kernelIdeal
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq] using hepsilon_mem
    · simpa only [Matrix.diagonal_apply_ne _ hij] using kernelIdeal.zero_mem
  have hdiagonal_ne : epsilonDiagonal ≠ 0 := by
    intro h
    apply hepsilon_ne
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) D => A 0 0) h
    simpa only [epsilonDiagonal, Matrix.diagonal_apply_eq, Matrix.zero_apply] using h00
  exact ⟨hkernel, hepsilon_mem, hepsilon_ne, hepsilon_sq, hentries, hdiagonal_ne⟩

/-- The exponent-two consequence of `Matrix.pow_apply_mem_ideal_pow` on this diagonal. -/
private theorem epsilonDiagonal_sq_eq_zero : epsilonDiagonal ^ 2 = 0 := by
  rcases epsilonDiagonal_nonvacuity with ⟨hkernel, _, _, _, hentries, _⟩
  apply Matrix.ext
  intro i j
  have hmem := Matrix.pow_apply_mem_ideal_pow kernelIdeal epsilonDiagonal hentries 2 i j
  rw [hkernel, Submodule.mem_bot] at hmem
  simpa only [Matrix.zero_apply] using hmem

/-- The consequence of `Matrix.isNilpotent_of_isNilpotent_ideal` on the same diagonal. -/
private theorem epsilonDiagonal_isNilpotent : IsNilpotent epsilonDiagonal := by
  rcases epsilonDiagonal_nonvacuity with ⟨hkernel, _, _, _, hentries, _⟩
  exact Matrix.isNilpotent_of_isNilpotent_ideal kernelIdeal epsilonDiagonal hentries
    ⟨2, by simpa only [Ideal.zero_eq_bot] using hkernel⟩

end Matrix
