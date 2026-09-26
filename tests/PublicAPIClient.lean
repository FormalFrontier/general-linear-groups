/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups

/-!
# Ordinary public-root clients

These named private declarations retain proof terms for representative uses of
every non-trace layer. They intentionally use neither leaf imports nor `import all`.
The trace quotient and its empty/singleton/zero/noncommutative cases have their
own client. These examples are not additional exported library API.
-/

set_option warningAsError true

open Matrix Matrix.GeneralLinearGroup

namespace PublicAPIClient

universe uR uS uN uK uI

section Rings

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
  {n : Type uN} {k : Type uK} [Fintype n] [DecidableEq n]
  [Fintype k] [DecidableEq k]

private theorem coefficient_entry (f : R →+* S) (g : GL n R) (i j : n) :
    mapRingHom f g i j = f (g i j) := rfl

private theorem upper_inverse (A : Matrix n n R) :
    (upperUnit A).inv = Matrix.fromBlocks 1 (-A) 0 1 := rfl

private theorem lower_sign (A : Matrix n n R) :
    (lowerUnit A).val = Matrix.fromBlocks 1 0 (-A) 1 := rfl

private theorem whitehead (g : GL n R) :
    blockDiagonalUnit g = upperUnit (g : Matrix n n R) *
      lowerUnit ((g⁻¹ : GL n R) : Matrix n n R) *
        upperUnit (g : Matrix n n R) * swapUnit :=
  blockDiagonalUnit_eq g

private theorem doubled_lift (f : R →+* S) (hf : Function.Surjective f)
    (g : GL n S) :
    mapRingHom f (liftBlockDiagonal f hf g) = blockDiagonalUnit g :=
  mapRingHom_liftBlockDiagonal f hf g

private theorem reindex_entry (e : n ≃ k) (g : GL n R) (i j : k) :
    reindexEquiv R e g i j = g (e.symm i) (e.symm j) := rfl

private theorem reindex_natural (f : R →+* S) (e : n ≃ k) (g : GL n R) :
    mapRingHom f (reindexEquiv R e g) = reindexEquiv S e (mapRingHom f g) :=
  mapRingHom_reindexEquiv f e g

private theorem right_to_two_sided (I : TwoSidedIdeal R)
    (hI : I.IsRightQuasiregular) {x : R} (hx : x ∈ I) :
    ∃ y : R, y ∈ I ∧ x + y + x * y = 0 ∧ x + y + y * x = 0 :=
  TwoSidedIdeal.exists_quasiInverse_mem_of_isRightQuasiregular hI hx

private theorem pointwise_nil_radical (I : TwoSidedIdeal R) (hI : I.IsNil) :
    I ≤ (Ring.jacobson R).toTwoSided :=
  hI.le_ringJacobson

private theorem nil_to_quasiregular (I : TwoSidedIdeal R) (hI : I.IsNil) :
    I.IsQuasiregular :=
  hI.isQuasiregular

private theorem jacobson_greatest :
    IsGreatest {I : TwoSidedIdeal R | I.IsQuasiregular}
      (Ring.jacobson R).toTwoSided :=
  TwoSidedIdeal.ringJacobson_isGreatest_isQuasiregular

private theorem matrix_quasiregular (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) :
    (I.matrix n).IsQuasiregular :=
  hI.matrix n

private theorem local_quotient_inverse (I : TwoSidedIdeal R) (hI : I ≠ ⊤)
    (hunit : ∀ x : R, x ∉ I → IsUnit x) :
    letI := I.quotientDivisionRing hI hunit
    ∀ x : R ⧸ I.asIdeal, x ≠ 0 → x * x⁻¹ = 1 := by
  let _ := I.quotientDivisionRing hI hunit
  intro x hx
  exact mul_inv_cancel₀ hx

private theorem congruence_injective (I : TwoSidedIdeal R) :
    Function.Injective (idealGeneralLinearGroupToRing (n := n) I) :=
  idealGeneralLinearGroupToRing_injective I

private theorem congruence_exact (I : TwoSidedIdeal R) :
    Function.MulExact (idealGeneralLinearGroupToRing (n := n) I)
      (mapRingHom (Ideal.Quotient.mk I.asIdeal) : GL n R →* GL n (R ⧸ I.asIdeal)) :=
  idealGeneralLinearGroupToRing_mulExact I

private theorem specified_matrix (I : TwoSidedIdeal R) (hI : I.IsQuasiregular)
    (A : Matrix n n R) (hA : IsUnit ((Ideal.Quotient.mk I.asIdeal).mapMatrix A)) :
    IsUnit A :=
  isUnit_of_mapMatrix_quotient_isUnit I hI A hA

private theorem short_exact_surjective (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) :
    Function.Surjective
      (mapRingHom (Ideal.Quotient.mk I.asIdeal) : GL n R →* GL n (R ⧸ I.asIdeal)) :=
  (idealGeneralLinearGroupToRing_shortExact I hI).2.2

private theorem unital_comparison_value
    (g : nonUnitalGeneralLinearGroup (n := n) (I := R)) :
    nonUnitalGeneralLinearGroupEquiv R g =
      (unitizationGeneralLinearEquivProd ℤ R g.1).2 := rfl

private theorem unital_comparison_inverse (g : GL n R) :
    nonUnitalGeneralLinearGroupEquiv R ((nonUnitalGeneralLinearGroupEquiv R).symm g) =
      g :=
  (nonUnitalGeneralLinearGroupEquiv R).apply_symm_apply g

private theorem empty_matrix_quasiregular (I : TwoSidedIdeal R)
    (hI : I.IsQuasiregular) : (I.matrix (Fin 0)).IsQuasiregular :=
  hI.matrix (Fin 0)

private theorem empty_congruence_injective (I : TwoSidedIdeal R) :
    Function.Injective (idealGeneralLinearGroupToRing (n := Fin 0) I) :=
  idealGeneralLinearGroupToRing_injective I

private theorem empty_unital_comparison (g : GL (Fin 0) R) :
    nonUnitalGeneralLinearGroupEquiv R ((nonUnitalGeneralLinearGroupEquiv R).symm g) =
      g :=
  (nonUnitalGeneralLinearGroupEquiv R).apply_symm_apply g

end Rings

section NonUnital

variable {I : Type uI} [NonUnitalRing I] {n : Type uN}
  [Fintype n] [DecidableEq n]

private theorem positive_power (x : I) (k : ℕ) :
    NonUnital.positivePow x (k + 1) = NonUnital.positivePow x k * x := rfl

private theorem strict_upper_nil {d : ℕ} (A : Matrix (Fin d) (Fin d) I)
    (hA : A.IsStrictlyUpperTriangular) : NonUnital.IsNilpotent A :=
  hA.isNilpotent

private theorem empty_nil (A : Matrix (Fin 0) (Fin 0) I) :
    NonUnital.IsNilpotent A := by
  apply Matrix.IsStrictlyUpperTriangular.isNilpotent
  intro i
  exact Fin.elim0 i

private theorem nilpotent_value (A : Matrix n n I) (k : ℕ)
    (hk : unitizationMatrix A ^ k = 0) :
    ((nilpotentMatrixElement A k hk).1 : Matrix n n (Unitization ℤ I)) =
      1 + unitizationMatrix A := rfl

-- Regression: use the explicit inverse law, not the historically failing bare `simp`.
private theorem nilpotent_inverse (A : Matrix n n I) (k : ℕ)
    (hk : unitizationMatrix A ^ k = 0) :
    (nilpotentMatrixElement A k hk).1.inv =
      ∑ i ∈ Finset.range k, (-unitizationMatrix A) ^ i :=
  nilpotentMatrixElement_inv A k hk

private theorem quasiregular_unit (A : Matrix n n I) :
    IsUnit (1 + unitizationMatrix A : Matrix n n (Unitization ℤ I)) ↔
      IsQuasiregular A :=
  isUnit_one_add_unitizationMatrix_iff_isQuasiregular A

private theorem quasiregular_representative (A : Matrix n n I) :
    (∃ g : nonUnitalGeneralLinearGroup (n := n) (I := I),
      (g.1 : Matrix n n (Unitization ℤ I)) = 1 + unitizationMatrix A) ↔
      IsQuasiregular A :=
  exists_nonUnitalGeneralLinearGroup_iff_isQuasiregular A

end NonUnital

private theorem unitization_product {K : Type uR} [CommRing K]
    {A : Type uS} [Ring A] [Algebra K A] (x : Unitization K A) :
    Unitization.ringEquivProd K A x = (x.fst, algebraMap K A x.fst + x.snd) := rfl

private theorem zero_exponent (r : ZMod 1) :
    (IsNilpotent.oneAddUnitOfPowEqZero r 0 (Subsingleton.elim _ _)).inv = 0 := rfl

private theorem noncommutative_coefficient (g : GL (Fin 1) (Matrix (Fin 2) (Fin 2) ℤ)) :
    mapRingHom (RingHom.id (Matrix (Fin 2) (Fin 2) ℤ)) g = g := rfl

private theorem zero_ring_whitehead (g : GL (Fin 1) (ZMod 1)) :
    blockDiagonalUnit g = upperUnit (g : Matrix (Fin 1) (Fin 1) (ZMod 1)) *
      lowerUnit ((g⁻¹ : GL (Fin 1) (ZMod 1)) : Matrix (Fin 1) (Fin 1) (ZMod 1)) *
        upperUnit (g : Matrix (Fin 1) (Fin 1) (ZMod 1)) * swapUnit :=
  blockDiagonalUnit_eq g

end PublicAPIClient
