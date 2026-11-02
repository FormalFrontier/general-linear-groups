/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.PrincipalUnits
public import Mathlib.GroupTheory.Nilpotent

/-!
# Commutators and filtrations of principal units

For a left ideal `I` of an arbitrary ring `R`, principal units use the
existing stabilizer of `1` in the quotient left module `R ⧸ I`.
For two-sided `I`, `Ideal.stabilizer_quotient_one_eq_ker_unitsMap` identifies
this subgroup with the canonical kernel of reduction on units.

For arbitrary left ideals `A` and `B`, the commutator of their principal-unit
subgroups is contained in the principal-unit subgroup at `A * B + B * A`.
For a two-sided ideal `I`, the
commutator estimate at powers `a` and `b` lands at `I ^ (a + b)`, including
zero exponents and without a nilpotence assumption.

For any left ideal `I`, the lower central series of its principal-unit
subgroup is bounded by the positive powers of `I`. These statements do not
assume that the subgroup is normal in the ambient unit group. If `I ^ N = ⊥`,
they give nilpotence of the principal-unit subgroup, not of the full unit
group. Mathlib's zeroth lower-central term is the subgroup itself, so the
class bound is the natural truncated subtraction `N - 1`. The exponent `N`
may be zero; then the ring is the zero ring. At `N = 1` the subgroup is
already trivial.

For positive powers `a` and `b` of any left ideal `I`, the coordinate
`↑⁅u, v⁆ - 1` of a commutator agrees with the ring commutator of `↑u - 1`
and `↑v - 1` modulo `I ^ (a + b + min a b)`. In particular, their classes
agree in the quotient left module `R ⧸ I ^ (a + b + 1)`. This is the ordinary
commutator `u * v * u⁻¹ * v⁻¹`, with no degree-dependent sign.

For positive successive layers, `GeneralLinearGroups.PrincipalUnits`
provides the additive quotient equivalence and its lifting API under square
containment and Jacobson hypotheses. This does not give an additive
description of the zeroth unit layer.

Inverse images of left ideals under semiring homomorphisms preserve ordered
products and natural powers up to containment, including the zeroth power.
A containment in an inverse image therefore induces containments at every power.
-/

@[expose] public section

universe u v w

namespace Ideal

section Semiring

variable {R : Type u} {S : Type v} {F : Type w} [Semiring R] [Semiring S]
  [FunLike F R S] [RingHomClass F R S]

/-- The product of the inverse images of two left ideals is contained in the
inverse image of their ordered product. Neither ideal needs to be two-sided. -/
theorem comap_mul_comap_le (f : F) (K L : Ideal S) :
    K.comap f * L.comap f ≤ (K * L).comap f := by
  apply Ideal.mul_le.mpr
  intro x hx y hy
  change f (x * y) ∈ K * L
  rw [map_mul]
  exact Ideal.mul_mem_mul hx hy

/-- Every natural power of the inverse image of a left ideal is contained in
the inverse image of its power. At exponent zero both ideals are the top ideal. -/
theorem pow_comap_le (f : F) (K : Ideal S) (n : ℕ) :
    K.comap f ^ n ≤ (K ^ n).comap f := by
  induction n with
  | zero => simp only [Submodule.pow_zero, Ideal.one_eq_top, Ideal.comap_top, le_refl]
  | succ n ih =>
      rw [Submodule.pow_succ, Submodule.pow_succ]
      exact (Ideal.mul_mono ih le_rfl).trans (comap_mul_comap_le f (K ^ n) K)

/-- A containment in the inverse image of a left ideal induces containments
at all natural powers, including exponent zero. -/
theorem pow_le_comap_pow (f : F) {I : Ideal R} {J : Ideal S}
    (h : I ≤ J.comap f) (n : ℕ) : I ^ n ≤ (J ^ n).comap f :=
  (Ideal.pow_right_mono h n).trans (pow_comap_le f J n)

end Semiring

variable {R : Type u} [Ring R]

open scoped commutatorElement in
private theorem commutator_sub_one_eq (u v : Rˣ) :
    (↑⁅u, v⁆ : R) - 1 =
      (((u : R) - 1) * ((v : R) - 1) - ((v : R) - 1) * ((u : R) - 1)) *
        (1 + ((↑u⁻¹ : R) - 1)) * (1 + ((↑v⁻¹ : R) - 1)) := by
  calc
    (↑⁅u, v⁆ : R) - 1 =
        ((u : R) * (v : R) - (v : R) * (u : R)) * ↑u⁻¹ * ↑v⁻¹ := by
      simp only [commutatorElement_def, Units.val_mul, sub_mul,
        Units.mul_inv_cancel_right, Units.mul_inv]
    _ = _ := by noncomm_ring

private theorem commutator_coordinate_mem (A B : Ideal R) {a b a' b' : R}
    (ha : a ∈ A) (hb : b ∈ B) (ha' : a' ∈ A) (hb' : b' ∈ B) :
    (a * b - b * a) * (1 + a') * (1 + b') ∈ A * B + B * A := by
  let c := a * b - b * a
  have hc : c ∈ A * B + B * A :=
    (A * B + B * A).sub_mem (Submodule.mem_sup_left (mul_mem_mul ha hb))
      (Submodule.mem_sup_right (mul_mem_mul hb ha))
  -- These products use only left absorption; the sum need not be right-stable.
  have hca' : c * a' ∈ B * A := by
    dsimp [c]
    rw [sub_mul, mul_assoc, mul_assoc]
    exact (B * A).sub_mem ((B * A).mul_mem_left a (mul_mem_mul hb ha'))
      (mul_mem_mul hb (A.mul_mem_left a ha'))
  have hcb' : c * b' ∈ A * B := by
    dsimp [c]
    rw [sub_mul, mul_assoc, mul_assoc]
    exact (A * B).sub_mem (mul_mem_mul ha (B.mul_mem_left b hb'))
      ((A * B).mul_mem_left b (mul_mem_mul ha hb'))
  have hca'b' : c * a' * b' ∈ A * B :=
    mul_mem_mul (A.mul_mem_left c ha') hb'
  have hexpand : c * (1 + a') * (1 + b') = c + c * a' + c * b' + c * a' * b' := by
    noncomm_ring
  rw [show a * b - b * a = c from rfl, hexpand]
  exact (A * B + B * A).add_mem
    ((A * B + B * A).add_mem
      ((A * B + B * A).add_mem hc (Submodule.mem_sup_right hca'))
      (Submodule.mem_sup_left hcb'))
    (Submodule.mem_sup_left hca'b')

open scoped commutatorElement in
/-- The commutator of the principal-unit subgroups of two left ideals is
contained in the principal-unit subgroup at the sum of their two ordered products.
Neither ideal needs to be two-sided, and no ambient normality is assumed. -/
theorem commutator_stabilizer_quotient_one_le (A B : Ideal R) :
    ⁅MulAction.stabilizer Rˣ (1 : R ⧸ A),
      MulAction.stabilizer Rˣ (1 : R ⧸ B)⁆ ≤
      MulAction.stabilizer Rˣ (1 : R ⧸ (A * B + B * A : Ideal R)) := by
  apply Subgroup.commutator_le.mpr
  intro u hu v hv
  apply ((A * B + B * A).mem_stabilizer_quotient_one ⁅u, v⁆).mpr
  have hcoord := commutator_coordinate_mem A B
    ((A.mem_stabilizer_quotient_one u).mp hu)
    ((B.mem_stabilizer_quotient_one v).mp hv)
    ((A.mem_stabilizer_quotient_one u⁻¹).mp
      ((MulAction.stabilizer Rˣ (1 : R ⧸ A)).inv_mem hu))
    ((B.mem_stabilizer_quotient_one v⁻¹).mp
      ((MulAction.stabilizer Rˣ (1 : R ⧸ B)).inv_mem hv))
  rw [commutator_sub_one_eq]
  exact hcoord

open scoped commutatorElement in
/-- For positive powers of a left ideal, the difference between the unit
commutator coordinate and the ring commutator of the two coordinates lies in
`I ^ (a + b + min a b)`. The ideal need not be two-sided or nilpotent. -/
theorem commutator_sub_one_sub_mul_sub_mem_pow (I : Ideal R)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {u v : Rˣ}
    (hu : (u : R) - 1 ∈ I ^ a) (hv : (v : R) - 1 ∈ I ^ b) :
    ((↑⁅u, v⁆ : R) - 1) -
        (((u : R) - 1) * ((v : R) - 1) - ((v : R) - 1) * ((u : R) - 1)) ∈
      I ^ (a + b + min a b) := by
  let c := ((u : R) - 1) * ((v : R) - 1) - ((v : R) - 1) * ((u : R) - 1)
  let p := (↑u⁻¹ : R) - 1
  let q := (↑v⁻¹ : R) - 1
  have hp : p ∈ I ^ a :=
    ((I ^ a).mem_stabilizer_quotient_one u⁻¹).mp
      ((MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ a : Ideal R))).inv_mem
        (((I ^ a).mem_stabilizer_quotient_one u).mpr hu))
  have hq : q ∈ I ^ b :=
    ((I ^ b).mem_stabilizer_quotient_one v⁻¹).mp
      ((MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ b : Ideal R))).inv_mem
        (((I ^ b).mem_stabilizer_quotient_one v).mpr hv))
  -- The right exponent must be positive for products of left-ideal powers.
  have hmul {m n : ℕ} (hn : n ≠ 0) {x y : R}
      (hx : x ∈ I ^ m) (hy : y ∈ I ^ n) : x * y ∈ I ^ (m + n) := by
    rw [Submodule.pow_add _ hn]
    exact mul_mem_mul hx hy
  have hc : c ∈ I ^ (a + b) :=
    (I ^ (a + b)).sub_mem (hmul (Nat.ne_of_gt hb) hu hv)
      (by simpa only [Nat.add_comm b a] using hmul (Nat.ne_of_gt ha) hv hu)
  have hcp : c * p ∈ I ^ (a + b + a) := hmul (Nat.ne_of_gt ha) hc hp
  have hcq : c * q ∈ I ^ (a + b + b) := hmul (Nat.ne_of_gt hb) hc hq
  have hcpq : c * p * q ∈ I ^ (a + b + a + b) := hmul (Nat.ne_of_gt hb) hcp hq
  have hrem : ((↑⁅u, v⁆ : R) - 1) - c = c * p + c * q + c * p * q := by
    rw [commutator_sub_one_eq]
    change c * (1 + p) * (1 + q) - c = _
    noncomm_ring
  change ((↑⁅u, v⁆ : R) - 1) - c ∈ _
  rw [hrem]
  exact (I ^ (a + b + min a b)).add_mem
    ((I ^ (a + b + min a b)).add_mem
      (Ideal.pow_le_pow_right (by omega) hcp)
      (Ideal.pow_le_pow_right (by omega) hcq))
    (Ideal.pow_le_pow_right (by omega) hcpq)

open scoped commutatorElement in
/-- For positive powers of a left ideal, the unit commutator coordinate and
the ring commutator of the coordinates have the same class modulo
`I ^ (a + b + 1)`. This is an equality in a quotient left module; it does not
require a quotient ring or a two-sided ideal. -/
theorem quotient_mk_commutator_sub_one_eq (I : Ideal R)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {u v : Rˣ}
    (hu : (u : R) - 1 ∈ I ^ a) (hv : (v : R) - 1 ∈ I ^ b) :
    (Submodule.Quotient.mk ((↑⁅u, v⁆ : R) - 1) :
        R ⧸ (I ^ (a + b + 1) : Ideal R)) =
      Submodule.Quotient.mk
        (((u : R) - 1) * ((v : R) - 1) - ((v : R) - 1) * ((u : R) - 1)) := by
  apply (Submodule.Quotient.eq _).mpr
  exact Ideal.pow_le_pow_right (by omega)
    (I.commutator_sub_one_sub_mul_sub_mem_pow ha hb hu hv)

/-- Principal units at powers `a` and `b` of a two-sided ideal have commutator
in the principal units at power `a + b`. Both exponents may be zero, and the
ideal need not be nilpotent. -/
theorem commutator_stabilizer_quotient_one_pow_le (I : Ideal R) [I.IsTwoSided]
    (a b : ℕ) :
    ⁅MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ a : Ideal R)),
      MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ b : Ideal R))⁆ ≤
      MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (a + b) : Ideal R)) := by
  refine (commutator_stabilizer_quotient_one_le (I ^ a) (I ^ b)).trans
    (stabilizer_quotient_one_mono ?_)
  simpa only [← IsTwoSided.pow_add, Nat.add_comm b a, add_eq_sup, sup_idem] using
    (le_refl (I ^ (a + b)))

/-- The `k`th lower-central term of the principal-unit subgroup of a left
ideal `I`, computed in the ambient unit group, is contained in the principal-unit
subgroup at `I ^ (k + 1)`. At `k = 0` the left-hand side is the principal-unit
subgroup itself. -/
theorem stabilizer_quotient_one_lowerCentralSeries_le_pow
    (I : Ideal R) (k : ℕ) :
    (MulAction.stabilizer Rˣ (1 : R ⧸ I)).lowerCentralSeries k ≤
      MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (k + 1) : Ideal R)) := by
  induction k with
  | zero =>
      exact stabilizer_quotient_one_mono (Submodule.pow_one I).ge
  | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      refine (Subgroup.commutator_mono ih le_rfl).trans ?_
      have hproducts :
          I ^ (k + 1) * I + I * I ^ (k + 1) = I ^ (k + 1 + 1) := by
        rw [← Submodule.pow_succ, ← Submodule.pow_succ' I (Nat.succ_ne_zero k),
          add_eq_sup, sup_idem]
      exact (commutator_stabilizer_quotient_one_le (I ^ (k + 1)) I).trans
        (stabilizer_quotient_one_mono hproducts.le)

/-- If a left ideal satisfies `I ^ N = ⊥`, the lower central series of its
principal-unit subgroup vanishes at Mathlib index `N - 1`. Natural subtraction
includes `N = 0`; for `N = 0` or `N = 1`, the zeroth term is already trivial. -/
theorem stabilizer_quotient_one_lowerCentralSeries_eq_bot_of_pow_eq_bot
    (I : Ideal R) (N : ℕ) (hI : I ^ N = ⊥) :
    (MulAction.stabilizer Rˣ (1 : R ⧸ I)).lowerCentralSeries (N - 1) = ⊥ := by
  have hpow : I ^ (N - 1 + 1) ≤ (⊥ : Ideal R) := by
    rw [← hI]
    apply Ideal.pow_le_pow_right
    cases N <;> simp
  apply le_antisymm ?_ bot_le
  intro u hu
  have hu' := (I.stabilizer_quotient_one_lowerCentralSeries_le_pow (N - 1)) hu
  have huI := ((I ^ (N - 1 + 1) : Ideal R).mem_stabilizer_quotient_one u).mp hu'
  rw [Subgroup.mem_bot]
  apply Units.ext
  change (u : R) = 1
  simpa only [Submodule.mem_bot, sub_eq_zero] using hpow huI

/-- The principal-unit subgroup of a nilpotent left ideal is a nilpotent
group. No nilpotence assertion about the full ambient unit group is made. -/
theorem isNilpotent_stabilizer_quotient_one_of_pow_eq_bot
    (I : Ideal R) (N : ℕ) (hI : I ^ N = ⊥) :
    Group.IsNilpotent (MulAction.stabilizer Rˣ (1 : R ⧸ I)) := by
  exact Subgroup.isNilpotent_of_lowerCentralSeries_eq_bot
    (I.stabilizer_quotient_one_lowerCentralSeries_eq_bot_of_pow_eq_bot N hI)

/-- The nilpotency class of the principal-unit subgroup of a left ideal is at
most `N - 1` when `I ^ N = ⊥`, including the trivial-group cases `N = 0` and
`N = 1`. Nilpotence is asserted separately by
`Ideal.isNilpotent_stabilizer_quotient_one_of_pow_eq_bot`, so this bound does
not use the class function's junk value as a substitute for nilpotence. -/
theorem nilpotencyClass_stabilizer_quotient_one_le_of_pow_eq_bot
    (I : Ideal R) (N : ℕ) (hI : I ^ N = ⊥) :
    Group.nilpotencyClass (MulAction.stabilizer Rˣ (1 : R ⧸ I)) ≤ N - 1 := by
  let : Group.IsNilpotent (MulAction.stabilizer Rˣ (1 : R ⧸ I)) :=
    I.isNilpotent_stabilizer_quotient_one_of_pow_eq_bot N hI
  apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
  rw [← Subgroup.map_subtype_inj, Subgroup.map_bot,
    Subgroup.top_subtype_lowerCentralSeries]
  exact I.stabilizer_quotient_one_lowerCentralSeries_eq_bot_of_pow_eq_bot N hI

end Ideal
