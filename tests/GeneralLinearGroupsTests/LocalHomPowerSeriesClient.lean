/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups
public import Mathlib.Algebra.Field.Rat
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# Local power-series maps and a quasi-regular kernel that is not nil

The constant-coefficient map on power series over `ℚ` is surjective, and its
canonical two-sided kernel is quasi-regular but not nil. A series in the kernel
has zero constant coefficient, so adding `1` gives a unit. The series `X` lies
in the kernel, but the coefficient of degree `n` in `X ^ n` is `1` for every `n`.

These examples use Mathlib's power-series coefficient and invertibility APIs.
The independently established kernel and surjectivity facts also supply the
scalar local-homomorphism interface, its standard unit equivalence, and the
kernel necessity/iff APIs. Here locality is obtained from the quasi-regular
kernel, rather than established independently of that kernel property.

The inclusion of rational constants is local by its constant-coefficient
retraction, but is not surjective: `X` has nonzero coefficient in degree one.
This local input does not use kernel quasi-regularity. Its canonical kernel is
zero, and necessity places it in the Jacobson radical.
-/

set_option warningAsError true

@[expose] public section

namespace PowerSeries

private theorem X_mem_constantCoeff_ker :
    (X : PowerSeries ℚ) ∈ TwoSidedIdeal.ker (constantCoeff (R := ℚ)) := by
  exact (TwoSidedIdeal.mem_ker (constantCoeff (R := ℚ))).mpr constantCoeff_X

private theorem X_pow_ne_zero (n : ℕ) : (X : PowerSeries ℚ) ^ n ≠ 0 := by
  intro h
  have hcoeff : (1 : ℚ) = 0 := by
    simpa only [coeff_X_pow_self, map_zero] using
      congrArg (coeff (R := ℚ) n) h
  exact one_ne_zero hcoeff

private theorem constantCoeff_ker_isQuasiregular :
    (TwoSidedIdeal.ker (constantCoeff (R := ℚ))).IsQuasiregular := by
  apply (TwoSidedIdeal.isQuasiregular_iff_forall_isUnit_one_add _).mpr
  intro φ hφ
  have hφ0 : constantCoeff φ = 0 :=
    (TwoSidedIdeal.mem_ker (constantCoeff (R := ℚ))).mp hφ
  apply isUnit_iff_constantCoeff.mpr
  simpa only [map_add, map_one, hφ0, add_zero] using
    (isUnit_one : IsUnit (1 : ℚ))

/-- The constant-coefficient map on rational power series is surjective and
has a quasi-regular kernel that is not nil. -/
theorem constantCoeff_rat_surjective_ker_isQuasiregular_not_isNil :
    Function.Surjective (constantCoeff (R := ℚ)) ∧
      (TwoSidedIdeal.ker (constantCoeff (R := ℚ))).IsQuasiregular ∧
      ¬ (TwoSidedIdeal.ker (constantCoeff (R := ℚ))).IsNil := by
  refine ⟨constantCoeff_surj, constantCoeff_ker_isQuasiregular, ?_⟩
  intro hnil
  obtain ⟨n, hn⟩ := hnil (X : PowerSeries ℚ) X_mem_constantCoeff_ker
  exact X_pow_ne_zero n hn

example :
    (X : PowerSeries ℚ) ≠ 0 ∧
      (X : PowerSeries ℚ) ∈ TwoSidedIdeal.ker (constantCoeff (R := ℚ)) ∧
      ∀ n : ℕ, (X : PowerSeries ℚ) ^ n ≠ 0 :=
  ⟨X_ne_zero, X_mem_constantCoeff_ker, X_pow_ne_zero⟩

-- Locality comes from the quasi-regular kernel; nonnilness is supplied by the
-- existing powers-of-X witnesses, independently of unit reflection.
example (φ : PowerSeries ℚ) :
    (IsUnit (constantCoeff φ) ↔ IsUnit φ) ∧
      (TwoSidedIdeal.ker (constantCoeff (R := ℚ))).IsQuasiregular ∧
      (IsLocalHom (constantCoeff (R := ℚ)) ↔
        (TwoSidedIdeal.ker (constantCoeff (R := ℚ))).IsQuasiregular) ∧
      ¬ (TwoSidedIdeal.ker (constantCoeff (R := ℚ))).IsNil := by
  let : IsLocalHom (constantCoeff (R := ℚ)) :=
    (constantCoeff (R := ℚ)).isLocalHom_of_surjective_of_isQuasiregular_ker
      constantCoeff_surj constantCoeff_ker_isQuasiregular
  exact ⟨isUnit_map_iff (constantCoeff (R := ℚ)) φ,
    (constantCoeff (R := ℚ)).isQuasiregular_ker,
    (constantCoeff (R := ℚ)).isLocalHom_iff_isQuasiregular_ker constantCoeff_surj,
    constantCoeff_rat_surjective_ker_isQuasiregular_not_isNil.2.2⟩

-- The retraction proves locality without a quasi-regular-kernel constructor.
example : IsLocalHom (C (R := ℚ)) ∧
    ¬ Function.Surjective (C (R := ℚ)) ∧
    TwoSidedIdeal.ker (C (R := ℚ)) = ⊥ ∧
    (TwoSidedIdeal.ker (C (R := ℚ))).IsQuasiregular ∧
    TwoSidedIdeal.ker (C (R := ℚ)) ≤ (Ring.jacobson ℚ).toTwoSided := by
  have hlocal : IsLocalHom (C (R := ℚ)) :=
    isLocalHom_of_leftInverse (f := C (R := ℚ)) (constantCoeff (R := ℚ))
      (fun a => constantCoeff_C a)
  have hnotSurj : ¬ Function.Surjective (C (R := ℚ)) := by
    intro hsurj
    obtain ⟨a, ha⟩ := hsurj (X : PowerSeries ℚ)
    have hcoeff : (0 : ℚ) = 1 := by
      simpa only [coeff_succ_C, coeff_one_X] using
        congrArg (coeff (R := ℚ) 1) ha
    exact zero_ne_one hcoeff
  have hker : TwoSidedIdeal.ker (C (R := ℚ)) = ⊥ :=
    (TwoSidedIdeal.ker_eq_bot (C (R := ℚ))).mpr C_injective
  let : IsLocalHom (C (R := ℚ)) := hlocal
  exact ⟨hlocal, hnotSurj, hker, (C (R := ℚ)).isQuasiregular_ker,
    (C (R := ℚ)).isQuasiregular_ker.le_ringJacobson⟩

end PowerSeries
