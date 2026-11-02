/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.PrincipalUnits.Commutator

/-!
# Ring maps on positive principal-unit layers

A unital ring map carrying a left ideal `I` into a left ideal `J` induces
integer-linear maps on their positive successive ideal layers and on their
additive principal-unit layers. The constructions use the submodule quotients,
kernel quotients and additive type tags from
`GeneralLinearGroups.PrincipalUnits.Commutator`.

The theorem statements describe these maps on representatives, their identity
and composition laws, the symbol square, and compatibility with both
commutator pairings. No ideal needs to be two-sided, and no Jacobson-radical,
injectivity or surjectivity condition is imposed. Degrees remain positive;
the scalar ring is `ℤ`.

## References

Mathlib supplies restriction of homomorphisms, maps of quotient groups,
additive type tags and the integer-linear map associated to an additive
homomorphism. The principal-unit layers, symbols and commutator pairings are
from `GeneralLinearGroups.PrincipalUnits.Commutator`.
-/

@[expose] public section

universe u v w

namespace Ideal

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

section Maps

variable {F : Type*} [FunLike F R S] [RingHomClass F R S]

/-- The integer-linear map on successive ideal layers induced by a unital
ring map carrying `I` into `J`. It sends the class of `x` to the class of `f x`. -/
def powLayerMap (I : Ideal R) (J : Ideal S) (f : F)
    (h : I ≤ J.comap f) (n : ℕ+) : I.powLayer n →ₗ[ℤ] J.powLayer n :=
  let g : (I ^ (n : ℕ) : Ideal R) →+ (J ^ (n : ℕ) : Ideal S) :=
    (((f : R →+* S).toAddMonoidHom).comp
      (I ^ (n : ℕ) : Ideal R).subtype.toAddMonoidHom).codRestrict
        (J ^ (n : ℕ) : Ideal S) (fun x => pow_le_comap_pow f h (n : ℕ) x.property)
  (QuotientAddGroup.map
    (Submodule.comap (I ^ (n : ℕ)).subtype (I ^ ((n : ℕ) + 1))).toAddSubgroup
    (Submodule.comap (J ^ (n : ℕ)).subtype (J ^ ((n : ℕ) + 1))).toAddSubgroup
    g
    (by
      intro x hx
      exact pow_le_comap_pow f h ((n : ℕ) + 1) hx)).toIntLinearMap

/-- On an ideal representative, the forward layer map applies the ring map. -/
@[simp]
theorem powLayerMap_mk (I : Ideal R) (J : Ideal S) (f : F)
    (h : I ≤ J.comap f) (n : ℕ+) (x : (I ^ (n : ℕ) : Ideal R)) :
    I.powLayerMap J f h n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨f (x : R), pow_le_comap_pow f h (n : ℕ) x.property⟩ :
          (J ^ (n : ℕ) : Ideal S)) := by
  rfl

private theorem principalUnitsPowMap_mem (I : Ideal R) (J : Ideal S) (f : F)
    (h : I ≤ J.comap f) (n : ℕ+)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (n : ℕ) : Ideal R))) :
    Units.map (f : R →* S) u.1 ∈
      MulAction.stabilizer Sˣ (1 : S ⧸ (J ^ (n : ℕ) : Ideal S)) := by
  apply ((J ^ (n : ℕ)).mem_stabilizer_quotient_one _).mpr
  have hu := ((I ^ (n : ℕ)).mem_stabilizer_quotient_one u.1).mp u.property
  have hmap : f ((u.1 : R) - 1) ∈ J ^ (n : ℕ) :=
    pow_le_comap_pow f h (n : ℕ) hu
  simpa only [Units.coe_map, MonoidHom.coe_coe, map_sub, map_one] using hmap

/-- The integer-linear map on additive principal-unit layers induced by a
unital ring map carrying `I` into `J`. It descends the map on original-ring units. -/
def principalUnitsPowLayerMap (I : Ideal R) (J : Ideal S) (f : F)
    (h : I ≤ J.comap f) (n : ℕ+) :
    I.principalUnitsPowAdditiveLayer n →ₗ[ℤ] J.principalUnitsPowAdditiveLayer n :=
  let f' : MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (n : ℕ) : Ideal R)) →*
      MulAction.stabilizer Sˣ (1 : S ⧸ (J ^ (n : ℕ) : Ideal S)) :=
    ((Units.map (f : R →* S)).comp
      (MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (n : ℕ) : Ideal R))).subtype).codRestrict
        (MulAction.stabilizer Sˣ (1 : S ⧸ (J ^ (n : ℕ) : Ideal S)))
        (by exact principalUnitsPowMap_mem I J f h n)
  let g : I.principalUnitsPowLayer n →* J.principalUnitsPowLayer n :=
    QuotientGroup.map _ _ f' (by
      intro u hu
      rw [Subgroup.mem_comap, principalUnitsToQuotient_ker]
      rw [principalUnitsToQuotient_ker] at hu
      change Units.map (f : R →* S) u.1 ∈
        MulAction.stabilizer Sˣ (1 : S ⧸ (J ^ ((n : ℕ) + 1) : Ideal S))
      apply ((J ^ ((n : ℕ) + 1)).mem_stabilizer_quotient_one _).mpr
      have hu' := ((I ^ ((n : ℕ) + 1)).mem_stabilizer_quotient_one u.1).mp hu
      have hmap : f ((u.1 : R) - 1) ∈ J ^ ((n : ℕ) + 1) :=
        pow_le_comap_pow f h ((n : ℕ) + 1) hu'
      simpa only [Units.coe_map, MonoidHom.coe_coe, map_sub, map_one] using hmap)
  g.toAdditive.toIntLinearMap

/-- On an original-unit representative, the forward layer map applies the
induced homomorphism on units before taking its quotient class. -/
@[simp]
theorem principalUnitsPowLayerMap_mk (I : Ideal R) (J : Ideal S) (f : F)
    (h : I ≤ J.comap f) (n : ℕ+)
    (u : MulAction.stabilizer Rˣ (1 : R ⧸ (I ^ (n : ℕ) : Ideal R))) :
    I.principalUnitsPowLayerMap J f h n (Additive.ofMul (QuotientGroup.mk u)) =
      Additive.ofMul (QuotientGroup.mk
        (⟨Units.map (f : R →* S) u.1, by exact principalUnitsPowMap_mem I J f h n u⟩ :
          MulAction.stabilizer Sˣ (1 : S ⧸ (J ^ (n : ℕ) : Ideal S)))) := by
  rfl

/-- Taking symbols commutes with the forward maps on unit and ideal layers. -/
@[simp]
theorem principalUnitsPowLayerSymbol_map (I : Ideal R) (J : Ideal S) (f : F)
    (h : I ≤ J.comap f) (n : ℕ+) (x : I.principalUnitsPowAdditiveLayer n) :
    J.principalUnitsPowLayerSymbol n (I.principalUnitsPowLayerMap J f h n x) =
      I.powLayerMap J f h n (I.principalUnitsPowLayerSymbol n x) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  have hx : Additive.ofMul (QuotientGroup.mk u) = x := congrArg Additive.ofMul hu
  rw [← hx, principalUnitsPowLayerMap_mk, principalUnitsPowLayerSymbol_mk,
    principalUnitsPowLayerSymbol_mk, powLayerMap_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simp only [Units.coe_map, MonoidHom.coe_coe, map_sub, map_one]

/-- Applying a ring map to a coordinate commutator equals taking the
commutator of the two mapped coordinates. -/
theorem powLayerMap_commutator (I : Ideal R) (J : Ideal S) (f : F)
    (h : I ≤ J.comap f) (a b : ℕ+) (x : I.powLayer a) (y : I.powLayer b) :
    I.powLayerMap J f h (a + b) (I.powLayerCommutator a b x y) =
      J.powLayerCommutator a b (I.powLayerMap J f h a x) (I.powLayerMap J f h b y) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  refine Submodule.Quotient.induction_on _ y ?_
  intro y
  simp only [powLayerCommutator_mk_mk, powLayerMap_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simp only [map_sub, map_mul]

/-- Applying a ring map to a unit-layer commutator equals taking the
commutator of the two mapped unit-layer classes. -/
theorem principalUnitsPowLayerMap_commutator (I : Ideal R) (J : Ideal S) (f : F)
    (h : I ≤ J.comap f) (a b : ℕ+)
    (x : I.principalUnitsPowAdditiveLayer a) (y : I.principalUnitsPowAdditiveLayer b) :
    I.principalUnitsPowLayerMap J f h (a + b) (I.principalUnitsPowLayerCommutator a b x y) =
      J.principalUnitsPowLayerCommutator a b
        (I.principalUnitsPowLayerMap J f h a x) (I.principalUnitsPowLayerMap J f h b y) := by
  apply J.principalUnitsPowLayerSymbol_injective (a + b)
  simp only [principalUnitsPowLayerSymbol_map, principalUnitsPowLayerSymbol_commutator]
  exact I.powLayerMap_commutator J f h a b
    (I.principalUnitsPowLayerSymbol a x) (I.principalUnitsPowLayerSymbol b y)

end Maps

/-- The identity ring map induces the identity on each successive ideal layer. -/
@[simp]
theorem powLayerMap_id (I : Ideal R) (n : ℕ+)
    (h : I ≤ I.comap (RingHom.id R) := by intro x hx; exact hx) :
    I.powLayerMap I (RingHom.id R) h n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  rw [powLayerMap_mk]
  rfl

/-- The identity ring map induces the identity on each additive principal-unit layer. -/
@[simp]
theorem principalUnitsPowLayerMap_id (I : Ideal R) (n : ℕ+)
    (h : I ≤ I.comap (RingHom.id R) := by intro x hx; exact hx) :
    I.principalUnitsPowLayerMap I (RingHom.id R) h n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply I.principalUnitsPowLayerSymbol_injective n
  simp only [principalUnitsPowLayerSymbol_map, powLayerMap_id, LinearMap.id_apply]

section Composition

variable {T : Type w} [Ring T]
variable {F G : Type*} [FunLike F R S] [RingHomClass F R S]
  [FunLike G S T] [RingHomClass G S T]

/-- Successive ideal-layer maps preserve composition of ring maps. The
containment for the composite is the one induced by the two given containments. -/
theorem powLayerMap_comp (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (f : F) (g : G) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) (n : ℕ+)
    (hgf : I ≤ K.comap ((g : S →+* T).comp (f : R →+* S)) := by
      intro x hx
      exact hg (hf hx)) :
    (J.powLayerMap K g hg n).comp (I.powLayerMap J f hf n) =
      I.powLayerMap K ((g : S →+* T).comp (f : R →+* S)) hgf n := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  simp only [LinearMap.comp_apply, powLayerMap_mk]
  rfl

/-- Additive principal-unit-layer maps preserve composition of ring maps,
with the containment induced by the two given containments. -/
theorem principalUnitsPowLayerMap_comp (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (f : F) (g : G) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) (n : ℕ+)
    (hgf : I ≤ K.comap ((g : S →+* T).comp (f : R →+* S)) := by
      intro x hx
      exact hg (hf hx)) :
    (J.principalUnitsPowLayerMap K g hg n).comp (I.principalUnitsPowLayerMap J f hf n) =
      I.principalUnitsPowLayerMap K ((g : S →+* T).comp (f : R →+* S)) hgf n := by
  apply LinearMap.ext
  intro x
  apply K.principalUnitsPowLayerSymbol_injective n
  simp only [LinearMap.comp_apply, principalUnitsPowLayerSymbol_map]
  exact LinearMap.congr_fun (I.powLayerMap_comp J K f g hf hg n hgf)
    (I.principalUnitsPowLayerSymbol n x)

end Composition

end Ideal
