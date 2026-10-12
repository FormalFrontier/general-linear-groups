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
# A quasi-regular kernel that is not nil

The constant-coefficient map on power series over `ℚ` is surjective, and its
canonical two-sided kernel is quasi-regular but not nil. A series in the kernel
has zero constant coefficient, so adding `1` gives a unit. The series `X` lies
in the kernel, but the coefficient of degree `n` in `X ^ n` is `1` for every `n`.

These examples use Mathlib's power-series coefficient and invertibility APIs.
The independently established kernel and surjectivity facts also supply the
scalar local-homomorphism interface and its standard unit equivalence.
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

example (φ : PowerSeries ℚ) : IsUnit (constantCoeff φ) ↔ IsUnit φ := by
  let : IsLocalHom (constantCoeff (R := ℚ)) :=
    (constantCoeff (R := ℚ)).isLocalHom_of_surjective_of_isQuasiregular_ker
      constantCoeff_surj constantCoeff_ker_isQuasiregular
  exact isUnit_map_iff (constantCoeff (R := ℚ)) φ

end PowerSeries
