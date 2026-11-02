/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.PrincipalUnits.Filtration
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Data.PNat.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Commutator pairings on positive principal-unit layers

For a left ideal `I` of a ring `R`, the positive unit layer is the quotient
of the stabilizer of `1` modulo `I ^ n` by the kernel of its coordinate map
modulo `I ^ (n + 1)`. Its group operations are the quotient-group operations.
The coordinate map embeds this group into the multiplicative tag of the
successive ideal layer, making the unit layer commutative. The additive tag
therefore carries the usual integer module structure.

The ring commutator `x * y - y * x` descends to an integer-bilinear pairing
of ideal layers in degrees `a`, `b` and `a + b`. On symbols of unit classes,
its values lie in the symbol image in degree `a + b`; restriction to this
image gives the pairing of unit layers. The latter is characterized by the
class of the commutator of original-ring unit representatives. Both pairings
are alternating in each degree; swapping the slots gives ordinary negation
after the canonical identification of the two sum degrees.

Degrees are positive natural numbers. No additive identification at degree
zero, two-sidedness, Jacobson-radical condition or surjectivity of the symbol
map is assumed. The scalar ring of both pairings is `ℤ`, not `R`.

## References

The principal-unit coordinate map is from
`GeneralLinearGroups.PrincipalUnits`. The constructions use Mathlib's
injective commutative-group constructor, additive type tag, bilinear quotient
descent and restriction of a bilinear map along an injective linear map.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [Ring R]

private theorem principalUnitsPowLayer_square (I : Ideal R) (n : ℕ+) :
    (I ^ (n : ℕ)) ^ 2 ≤ I ^ ((n : ℕ) + 1) := by
  rw [Submodule.pow_succ, Submodule.pow_one, ← Submodule.pow_add _ n.ne_zero]
  exact Ideal.pow_le_pow_right (by have := n.pos; omega)

/-- The successive ideal layer in positive degree `n`, with its quotient-module
operations. -/
abbrev powLayer (I : Ideal R) (n : ℕ+) :=
  (I ^ (n : ℕ) : Ideal R) ⧸ Submodule.comap (I ^ (n : ℕ)).subtype (I ^ ((n : ℕ) + 1))

/-- An ideal-layer representative vanishes precisely in the next ideal power. -/
theorem powLayer_mk_eq_zero_iff (I : Ideal R) (n : ℕ+)
    (x : (I ^ (n : ℕ) : Ideal R)) :
    (Submodule.Quotient.mk x : I.powLayer n) = 0 ↔
      (x : R) ∈ I ^ ((n : ℕ) + 1) :=
  Submodule.Quotient.mk_eq_zero _

/-- Equality of ideal-layer representatives is congruence in the original ring. -/
theorem powLayer_mk_eq_mk_iff (I : Ideal R) (n : ℕ+)
    (x y : (I ^ (n : ℕ) : Ideal R)) :
    (Submodule.Quotient.mk x : I.powLayer n) = Submodule.Quotient.mk y ↔
      (x : R) - (y : R) ∈ I ^ ((n : ℕ) + 1) :=
  Submodule.Quotient.eq _

/-- The positive principal-unit layer, using the kernel quotient of the
coordinate homomorphism on the stabilizer of `1`. -/
abbrev principalUnitsPowLayer (I : Ideal R) (n : ℕ+) :=
  MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (n : ℕ) : Ideal R)) ⧸
    ((I ^ (n : ℕ)).principalUnitsToQuotient (I ^ ((n : ℕ) + 1))
      (by exact principalUnitsPowLayer_square I n)).ker

/-- Commutativity of the positive unit layer extends its quotient-group structure. -/
instance principalUnitsPowLayerCommGroup (I : Ideal R) (n : ℕ+) :
    CommGroup (I.principalUnitsPowLayer n) :=
  letI : Group (I.principalUnitsPowLayer n) := QuotientGroup.Quotient.group _
  MonoidHom.commGroupOfInjective
    (QuotientGroup.kerLift ((I ^ (n : ℕ)).principalUnitsToQuotient (I ^ ((n : ℕ) + 1))
      (by exact principalUnitsPowLayer_square I n)))
    (QuotientGroup.kerLift_injective ((I ^ (n : ℕ)).principalUnitsToQuotient (I ^ ((n : ℕ) + 1))
      (by exact principalUnitsPowLayer_square I n)))

/-- The additive tag of the positive principal-unit kernel quotient. -/
abbrev principalUnitsPowAdditiveLayer (I : Ideal R) (n : ℕ+) :=
  Additive (I.principalUnitsPowLayer n)

/-- The additive layer uses the additive type tag's commutative-group structure. -/
instance principalUnitsPowAdditiveLayerAddCommGroup (I : Ideal R) (n : ℕ+) :
    AddCommGroup (I.principalUnitsPowAdditiveLayer n) :=
  Additive.addCommGroup

/-- The injective integer-linear symbol of a positive unit layer. It need not be
surjective for an arbitrary left ideal. -/
def principalUnitsPowLayerSymbol (I : Ideal R) (n : ℕ+) :
    I.principalUnitsPowAdditiveLayer n →ₗ[ℤ] I.powLayer n :=
  (QuotientGroup.kerLift ((I ^ (n : ℕ)).principalUnitsToQuotient (I ^ ((n : ℕ) + 1))
      (by exact principalUnitsPowLayer_square I n))).toAdditiveLeft.toIntLinearMap

/-- On a unit representative, the symbol is its ring value minus `1`. -/
@[simp]
theorem principalUnitsPowLayerSymbol_mk (I : Ideal R) (n : ℕ+)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (n : ℕ) : Ideal R))) :
    I.principalUnitsPowLayerSymbol n (Additive.ofMul (QuotientGroup.mk u)) =
      Submodule.Quotient.mk
        (⟨(u.1 : R) - 1,
          ((I ^ (n : ℕ)).mem_stabilizer_quotient_one u.1).mp u.property⟩ :
            (I ^ (n : ℕ) : Ideal R)) :=
  rfl

/-- The symbol distinguishes all classes of original-ring principal units. -/
theorem principalUnitsPowLayerSymbol_injective (I : Ideal R) (n : ℕ+) :
    Function.Injective (I.principalUnitsPowLayerSymbol n) := by
  intro x y h
  apply Additive.toMul.injective
  apply QuotientGroup.kerLift_injective ((I ^ (n : ℕ)).principalUnitsToQuotient (I ^ ((n : ℕ) + 1))
      (by exact principalUnitsPowLayer_square I n))
  exact Multiplicative.toAdd.injective h

/-- The injective symbol has trivial kernel. -/
@[simp]
theorem principalUnitsPowLayerSymbol_ker (I : Ideal R) (n : ℕ+) :
    (I.principalUnitsPowLayerSymbol n).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (I.principalUnitsPowLayerSymbol_injective n)

private theorem powLayer_bracket_mem (I : Ideal R) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {x y : R}
    (hx : x ∈ I ^ m) (hy : y ∈ I ^ n) : x * y - y * x ∈ I ^ (m + n) := by
  apply (I ^ (m + n)).sub_mem
  · rw [Submodule.pow_add _ (Nat.ne_of_gt hn)]
    exact mul_mem_mul hx hy
  · rw [Nat.add_comm m n, Submodule.pow_add _ (Nat.ne_of_gt hm)]
    exact mul_mem_mul hy hx

private theorem powLayer_commutator_mem (I : Ideal R) (a b : ℕ+)
    (x : (I ^ (a : ℕ) : Ideal R)) (y : (I ^ (b : ℕ) : Ideal R)) :
    (x : R) * (y : R) - (y : R) * (x : R) ∈ I ^ ((a + b : ℕ+) : ℕ) := by
  exact powLayer_bracket_mem I a.pos b.pos x.property y.property

/-- The ring commutator, descended to the original successive ideal quotients
and bilinear over the integers. -/
def powLayerCommutator (I : Ideal R) (a b : ℕ+) :
    I.powLayer a →ₗ[ℤ] I.powLayer b →ₗ[ℤ] I.powLayer (a + b) :=
  let Da := Submodule.comap (I ^ (a : ℕ)).subtype (I ^ ((a : ℕ) + 1))
  let Db := Submodule.comap (I ^ (b : ℕ)).subtype (I ^ ((b : ℕ) + 1))
  let f : (I ^ (a : ℕ) : Ideal R) →ₗ[ℤ]
      (I ^ (b : ℕ) : Ideal R) →ₗ[ℤ] I.powLayer (a + b) :=
    LinearMap.mk₂ ℤ
      (fun x y => Submodule.Quotient.mk
        (⟨(x : R) * (y : R) - (y : R) * (x : R),
          by exact powLayer_commutator_mem I a b x y⟩ :
            (I ^ ((a + b : ℕ+) : ℕ) : Ideal R)))
      (by
        intro x₁ x₂ y
        rw [← Submodule.Quotient.mk_add]
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        simp only [Submodule.coe_add]
        noncomm_ring)
      (by
        intro c x y
        rw [← Submodule.Quotient.mk_smul]
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        simp only [Submodule.coe_smul_of_tower, smul_sub, smul_mul_assoc, mul_smul_comm])
      (by
        intro x y₁ y₂
        rw [← Submodule.Quotient.mk_add]
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        simp only [Submodule.coe_add]
        noncomm_ring)
      (by
        intro c x y
        rw [← Submodule.Quotient.mk_smul]
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        simp only [Submodule.coe_smul_of_tower, smul_sub, smul_mul_assoc, mul_smul_comm])
  -- A denominator in either slot raises the product degree by one.
  have hDa : Da.restrictScalars ℤ ≤ f.ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    ext y
    apply (I.powLayer_mk_eq_zero_iff (a + b) _).mpr
    have hx' : (x : R) ∈ I ^ ((a : ℕ) + 1) := hx
    simpa only [PNat.add_coe, Nat.add_right_comm] using
      powLayer_bracket_mem I (Nat.succ_pos _) b.pos hx' y.property
  have hDb : Db.restrictScalars ℤ ≤ f.flip.ker := by
    intro y hy
    apply LinearMap.mem_ker.mpr
    ext x
    apply (I.powLayer_mk_eq_zero_iff (a + b) _).mpr
    have hy' : (y : R) ∈ I ^ ((b : ℕ) + 1) := hy
    simpa only [PNat.add_coe, Nat.add_assoc] using
      powLayer_bracket_mem I a.pos (Nat.succ_pos _) x.property hy'
  (LinearMap.liftQ₂ (Da.restrictScalars ℤ) (Db.restrictScalars ℤ) f hDa hDb).compl₁₂
    (Submodule.Quotient.restrictScalarsEquiv ℤ Da).symm.toLinearMap
    (Submodule.Quotient.restrictScalarsEquiv ℤ Db).symm.toLinearMap

/-- On ideal representatives, the coordinate pairing is the class of `xy - yx`. -/
@[simp]
theorem powLayerCommutator_mk_mk (I : Ideal R) (a b : ℕ+)
    (x : (I ^ (a : ℕ) : Ideal R)) (y : (I ^ (b : ℕ) : Ideal R)) :
    I.powLayerCommutator a b (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        (⟨(x : R) * (y : R) - (y : R) * (x : R),
          by exact powLayer_commutator_mem I a b x y⟩ : (I ^ ((a + b : ℕ+) : ℕ) : Ideal R)) :=
  rfl

/-- The coordinate pairing vanishes when the two entries in one degree agree. -/
@[simp]
theorem powLayerCommutator_self (I : Ideal R) (a : ℕ+) (x : I.powLayer a) :
    I.powLayerCommutator a a x x = 0 := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  rw [powLayerCommutator_mk_mk]
  apply (I.powLayer_mk_eq_zero_iff (a + a) _).mpr
  simp

private theorem powLayer_cast_mk (I : Ideal R) {m n : ℕ+} (h : m = n)
    (x : (I ^ (m : ℕ) : Ideal R)) :
    cast (congrArg I.powLayer h) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨(x : R), by simpa only [h] using x.property⟩ : (I ^ (n : ℕ) : Ideal R)) := by
  subst n
  rfl

/-- Swapping the coordinates negates their pairing, after the canonical
identification of the two sum degrees. There is no degree-dependent sign. -/
theorem powLayerCommutator_swap (I : Ideal R) (a b : ℕ+)
    (x : I.powLayer a) (y : I.powLayer b) :
    cast (congrArg I.powLayer (add_comm b a)) (I.powLayerCommutator b a y x) =
      -I.powLayerCommutator a b x y := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  refine Submodule.Quotient.induction_on _ y ?_
  intro y
  simp only [powLayerCommutator_mk_mk]
  rw [powLayer_cast_mk I (add_comm b a), ← Submodule.Quotient.mk_neg]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simp only [Submodule.coe_neg]
  noncomm_ring

open scoped commutatorElement

private theorem principalUnitsPowLayer_commutator_mem (I : Ideal R) (a b : ℕ+)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (a : ℕ) : Ideal R)))
    (v : MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (b : ℕ) : Ideal R))) :
    ⁅u.1, v.1⁆ ∈
      MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ ((a + b : ℕ+) : ℕ) : Ideal R)) := by
  have h := (Subgroup.commutator_le.mp
    (commutator_stabilizer_quotient_one_le (I ^ (a : ℕ)) (I ^ (b : ℕ))))
      u.1 u.property v.1 v.property
  have hp : I ^ (a : ℕ) * I ^ (b : ℕ) + I ^ (b : ℕ) * I ^ (a : ℕ) =
      I ^ ((a + b : ℕ+) : ℕ) := by
    rw [← Submodule.pow_add _ b.ne_zero, ← Submodule.pow_add _ a.ne_zero,
      Nat.add_comm (b : ℕ) (a : ℕ), add_eq_sup, sup_idem, PNat.add_coe]
  exact stabilizer_quotient_one_mono hp.le h

private theorem principalUnitsPowLayerSymbol_commutator_mk_mk (I : Ideal R) (a b : ℕ+)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (a : ℕ) : Ideal R)))
    (v : MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (b : ℕ) : Ideal R))) :
    I.principalUnitsPowLayerSymbol (a + b)
        (Additive.ofMul (QuotientGroup.mk
          (⟨⁅u.1, v.1⁆, principalUnitsPowLayer_commutator_mem I a b u v⟩ :
            MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ ((a + b : ℕ+) : ℕ) : Ideal R))))) =
      I.powLayerCommutator a b
        (I.principalUnitsPowLayerSymbol a (Additive.ofMul (QuotientGroup.mk u)))
        (I.principalUnitsPowLayerSymbol b (Additive.ofMul (QuotientGroup.mk v))) := by
  simp only [principalUnitsPowLayerSymbol_mk, powLayerCommutator_mk_mk]
  apply (I.powLayer_mk_eq_mk_iff (a + b) _ _).mpr
  exact (Submodule.Quotient.eq _).mp
    (I.quotient_mk_commutator_sub_one_eq a.pos b.pos
      (((I ^ (a : ℕ)).mem_stabilizer_quotient_one u.1).mp u.property)
      (((I ^ (b : ℕ)).mem_stabilizer_quotient_one v.1).mp v.property))

private theorem principalUnitsPowLayerCommutator_range (I : Ideal R) (a b : ℕ+) :
    ∀ x y, (I.powLayerCommutator a b).compl₁₂
      (I.principalUnitsPowLayerSymbol a) (I.principalUnitsPowLayerSymbol b) x y ∈
        LinearMap.range (I.principalUnitsPowLayerSymbol (a + b)) := by
  intro x y
  -- These are unit classes, so unit representatives suffice without symbol surjectivity.
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
  have hx : Additive.ofMul (QuotientGroup.mk u) = x := congrArg Additive.ofMul hu
  have hy : Additive.ofMul (QuotientGroup.mk v) = y := congrArg Additive.ofMul hv
  rw [← hx, ← hy]
  exact ⟨Additive.ofMul (QuotientGroup.mk
    (⟨⁅u.1, v.1⁆, principalUnitsPowLayer_commutator_mem I a b u v⟩ :
      MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ ((a + b : ℕ+) : ℕ) : Ideal R)))),
    principalUnitsPowLayerSymbol_commutator_mk_mk I a b u v⟩

/-- The integer-bilinear commutator pairing of positive principal-unit layers,
with values in the same additive kernel quotient in degree `a + b`. -/
noncomputable def principalUnitsPowLayerCommutator (I : Ideal R) (a b : ℕ+) :
    I.principalUnitsPowAdditiveLayer a →ₗ[ℤ]
      I.principalUnitsPowAdditiveLayer b →ₗ[ℤ] I.principalUnitsPowAdditiveLayer (a + b) :=
  ((I.powLayerCommutator a b).compl₁₂
    (I.principalUnitsPowLayerSymbol a) (I.principalUnitsPowLayerSymbol b)).codRestrict₂
      (I.principalUnitsPowLayerSymbol (a + b))
      (I.principalUnitsPowLayerSymbol_injective (a + b))
      (by exact principalUnitsPowLayerCommutator_range I a b)

/-- Taking the symbol of a unit-layer commutator gives the coordinate pairing. -/
@[simp]
theorem principalUnitsPowLayerSymbol_commutator (I : Ideal R) (a b : ℕ+)
    (x : I.principalUnitsPowAdditiveLayer a) (y : I.principalUnitsPowAdditiveLayer b) :
    I.principalUnitsPowLayerSymbol (a + b) (I.principalUnitsPowLayerCommutator a b x y) =
      I.powLayerCommutator a b (I.principalUnitsPowLayerSymbol a x)
        (I.principalUnitsPowLayerSymbol b y) :=
  LinearMap.codRestrict₂_apply _ _ _ _ x y

/-- On original-unit representatives, the unit pairing is the class of their
ordered group commutator. -/
theorem principalUnitsPowLayerCommutator_mk_mk (I : Ideal R) (a b : ℕ+)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (a : ℕ) : Ideal R)))
    (v : MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (b : ℕ) : Ideal R))) :
    I.principalUnitsPowLayerCommutator a b
        (Additive.ofMul (QuotientGroup.mk u)) (Additive.ofMul (QuotientGroup.mk v)) =
      Additive.ofMul (QuotientGroup.mk
        (⟨⁅u.1, v.1⁆, by exact principalUnitsPowLayer_commutator_mem I a b u v⟩ :
          MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ ((a + b : ℕ+) : ℕ) : Ideal R)))) := by
  apply I.principalUnitsPowLayerSymbol_injective (a + b)
  rw [principalUnitsPowLayerSymbol_commutator]
  exact (principalUnitsPowLayerSymbol_commutator_mk_mk I a b u v).symm

/-- The symbol square uniquely determines the bilinear unit-layer pairing. -/
theorem principalUnitsPowLayerCommutator_unique (I : Ideal R) (a b : ℕ+)
    (f : I.principalUnitsPowAdditiveLayer a →ₗ[ℤ]
      I.principalUnitsPowAdditiveLayer b →ₗ[ℤ] I.principalUnitsPowAdditiveLayer (a + b))
    (hf : ∀ x y, I.principalUnitsPowLayerSymbol (a + b) (f x y) =
      I.powLayerCommutator a b (I.principalUnitsPowLayerSymbol a x)
        (I.principalUnitsPowLayerSymbol b y)) :
    f = I.principalUnitsPowLayerCommutator a b := by
  ext x y
  apply I.principalUnitsPowLayerSymbol_injective (a + b)
  exact (hf x y).trans (I.principalUnitsPowLayerSymbol_commutator a b x y).symm

/-- The unit-layer pairing is alternating in each positive degree. -/
@[simp]
theorem principalUnitsPowLayerCommutator_self (I : Ideal R) (a : ℕ+)
    (x : I.principalUnitsPowAdditiveLayer a) :
    I.principalUnitsPowLayerCommutator a a x x = 0 := by
  apply I.principalUnitsPowLayerSymbol_injective (a + a)
  simpa only [principalUnitsPowLayerSymbol_commutator, map_zero] using
    I.powLayerCommutator_self a (I.principalUnitsPowLayerSymbol a x)

private theorem principalUnitsPowLayerSymbol_cast (I : Ideal R) {m n : ℕ+} (h : m = n)
    (x : I.principalUnitsPowAdditiveLayer m) :
    I.principalUnitsPowLayerSymbol n
        (cast (congrArg I.principalUnitsPowAdditiveLayer h) x) =
      cast (congrArg I.powLayer h) (I.principalUnitsPowLayerSymbol m x) := by
  subst n
  rfl

/-- Swapping unit-layer entries negates their pairing, after the canonical
identification of the two sum degrees. -/
theorem principalUnitsPowLayerCommutator_swap (I : Ideal R) (a b : ℕ+)
    (x : I.principalUnitsPowAdditiveLayer a) (y : I.principalUnitsPowAdditiveLayer b) :
    cast (congrArg I.principalUnitsPowAdditiveLayer (add_comm b a))
        (I.principalUnitsPowLayerCommutator b a y x) =
      -I.principalUnitsPowLayerCommutator a b x y := by
  apply I.principalUnitsPowLayerSymbol_injective (a + b)
  rw [principalUnitsPowLayerSymbol_cast I (add_comm b a)]
  simp only [principalUnitsPowLayerSymbol_commutator, map_neg]
  exact I.powLayerCommutator_swap a b
    (I.principalUnitsPowLayerSymbol a x) (I.principalUnitsPowLayerSymbol b y)

end Ideal
