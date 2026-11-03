/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.RingTheory.Ideal.NilpotentExp
public import GeneralLinearGroups.RingTheory.TwoSidedIdeal.PrincipalUnits

/-!
# Nilpotent exponentials as principal units

For an elementwise nil two-sided ideal, the stock algebraic exponential gives
a canonical function to the existing principal-unit subgroup. Its underlying
ring value determines the function uniquely. This is a plain function, not a
homomorphism from ideal multiplication or a rational-linear exponential.

The scalar action is the given `Module ℚ A`. In particular a given rational
algebra specializes the same definition through its induced module, without
changing the carrier, exponential, or canonical unit.
-/

@[expose] public section

universe u v

namespace TwoSidedIdeal

variable {A : Type u} [Ring A] [Module ℚ A]

/-- The stock exponential, as its canonical unit in the principal-unit kernel. -/
noncomputable def expToPrincipalUnits (I : TwoSidedIdeal A)
    (h_nil : ∀ u : I, IsNilpotent (u : A)) (u : I) : I.principalUnits :=
  ⟨(h_nil u).isUnit_exp.unit, by
    apply (I.mem_principalUnits _).2
    change IsNilpotent.exp (u : A) - 1 ∈ I
    exact I.asIdeal.exp_sub_one_mem u.property (h_nil u)⟩

/-- Forgetting kernel membership gives exactly the stock unit. -/
@[simp]
theorem expToPrincipalUnits_apply_coe (I : TwoSidedIdeal A)
    (h_nil : ∀ u : I, IsNilpotent (u : A)) (u : I) :
    (I.expToPrincipalUnits h_nil u : Aˣ) = (h_nil u).isUnit_exp.unit :=
  rfl

/-- The underlying ring value is the stock nilpotent exponential. -/
@[simp]
theorem coe_expToPrincipalUnits (I : TwoSidedIdeal A)
    (h_nil : ∀ u : I, IsNilpotent (u : A)) (u : I) :
    ((I.expToPrincipalUnits h_nil u : Aˣ) : A) = IsNilpotent.exp (u : A) :=
  rfl

/-- The underlying exponential values uniquely characterize the forward function. -/
theorem expToPrincipalUnits_unique (I : TwoSidedIdeal A)
    (h_nil : ∀ u : I, IsNilpotent (u : A)) (F : I → I.principalUnits)
    (hF : ∀ u : I, ((F u : Aˣ) : A) = IsNilpotent.exp (u : A)) :
    F = I.expToPrincipalUnits h_nil := by
  funext u
  apply Subtype.ext
  apply Units.ext
  exact (hF u).trans (I.coe_expToPrincipalUnits h_nil u).symm

/-- Zero maps to the identity principal unit. -/
@[simp]
theorem expToPrincipalUnits_zero (I : TwoSidedIdeal A)
    (h_nil : ∀ u : I, IsNilpotent (u : A)) :
    I.expToPrincipalUnits h_nil 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change IsNilpotent.exp (0 : A) = 1
  exact IsNilpotent.exp_zero

/-- Negation maps to inversion in the existing principal-unit group. -/
@[simp]
theorem expToPrincipalUnits_neg (I : TwoSidedIdeal A)
    (h_nil : ∀ u : I, IsNilpotent (u : A)) (u : I) :
    I.expToPrincipalUnits h_nil (-u) = (I.expToPrincipalUnits h_nil u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  apply Units.ext
  change IsNilpotent.exp (-(u : A)) * IsNilpotent.exp (u : A) = 1
  exact (h_nil u).exp_neg_mul_exp_self

/-- Natural multiples in the unchanged additive ideal give natural powers. -/
theorem expToPrincipalUnits_nsmul (I : TwoSidedIdeal A)
    (h_nil : ∀ u : I, IsNilpotent (u : A)) (n : ℕ) (u : I) :
    I.expToPrincipalUnits h_nil (n • u) = (I.expToPrincipalUnits h_nil u) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : Commute ((n • u : I) : A) (u : A) := by
      change (n • (u : A)) * (u : A) = (u : A) * (n • (u : A))
      rw [_root_.smul_mul_assoc, _root_.mul_smul_comm]
    calc
      I.expToPrincipalUnits h_nil ((n + 1) • u) =
          I.expToPrincipalUnits h_nil (n • u) * I.expToPrincipalUnits h_nil u := by
        apply Subtype.ext
        apply Units.ext
        rw [add_nsmul, one_nsmul]
        change IsNilpotent.exp (((n • u : I) : A) + (u : A)) =
          IsNilpotent.exp ((n • u : I) : A) * IsNilpotent.exp (u : A)
        exact IsNilpotent.exp_add_of_commute hc (h_nil (n • u)) (h_nil u)
      _ = (I.expToPrincipalUnits h_nil u) ^ (n + 1) := by rw [ih, pow_succ]

/-- Integer multiples in the unchanged additive ideal give integer powers. -/
theorem expToPrincipalUnits_zsmul (I : TwoSidedIdeal A)
    (h_nil : ∀ u : I, IsNilpotent (u : A)) (z : ℤ) (u : I) :
    I.expToPrincipalUnits h_nil (z • u) = (I.expToPrincipalUnits h_nil u) ^ z := by
  cases z with
  | ofNat n =>
    change I.expToPrincipalUnits h_nil ((n : ℤ) • u) =
      (I.expToPrincipalUnits h_nil u) ^ (n : ℤ)
    rw [_root_.natCast_zsmul, _root_.zpow_natCast]
    exact expToPrincipalUnits_nsmul I h_nil n u
  | negSucc n =>
    rw [negSucc_zsmul, expToPrincipalUnits_neg, expToPrincipalUnits_nsmul, zpow_negSucc]

/-- Ideal-preserving ring homomorphisms commute with the canonical exponential function. -/
theorem principalUnitsMap_expToPrincipalUnits {B : Type v} [Ring B] [Module ℚ B]
    {I : TwoSidedIdeal A} {J : TwoSidedIdeal B} (f : A →+* B)
    (hIJ : ∀ a : A, a ∈ I → f a ∈ J)
    (h_nilI : ∀ u : I, IsNilpotent (u : A))
    (h_nilJ : ∀ u : J, IsNilpotent (u : B)) (u : I) :
    principalUnitsMap f hIJ (I.expToPrincipalUnits h_nilI u) =
      J.expToPrincipalUnits h_nilJ ⟨f (u : A), hIJ (u : A) u.property⟩ := by
  apply Subtype.ext
  apply Units.ext
  simp only [coe_principalUnitsMap_apply, coe_expToPrincipalUnits]
  exact (h_nilI u).map_exp f

end TwoSidedIdeal
