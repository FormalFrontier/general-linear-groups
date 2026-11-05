/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.StableElementary
public import GeneralLinearGroups.UnitalComparison
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.GroupTheory.Commutator.Finite

/-!
# Finite coefficient products of stable general linear groups

Coefficient projections identify stable GL over a binary product of semirings
with the product of the two stable groups. More generally, stable GL commutes
with products indexed by a finite type. Over rings, these equivalences carry
the stable elementary subgroup onto the product of the elementary subgroups
and induce equivalences on the existing elementary quotients, compatibly with
coefficient maps and the Whitehead comparisons to abelianizations.

These are semiring and finite-index generalizations of the binary ring example
in Weibel, *The K-book*, Example III.1.1.3. The binary factors may have independent
universes. Empty coefficient indices, zero semirings and matrix rank zero are
included. Inverse computations first raise independently chosen representative
ranks to any common upper bound; finiteness supplies such a bound for every
finite family of stable elements. No unrestricted infinite-product equivalence
of stable groups is asserted.

The finite matrix comparisons use the existing `matrixRingEquivProd` and
Mathlib's `Matrix.piRingEquiv`, lifted by `Units.mapEquiv` and the product/Pi
unit equivalences. The elementary-subgroup comparison uses Whitehead and
Mathlib's binary and finite-Pi commutator formulas. Quotient coefficient maps
are Mathlib's `QuotientGroup.map`; the Whitehead compatibility squares use
its canonical abelianization projection maps.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*
  (2013-08-29 version), Example III.1.1.3.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v u' v' w

namespace StableGL

private theorem matrixProdUnits_apply
    (R : Type u) (S : Type v) [Semiring R] [Semiring S]
    (n : ℕ) (g : GL (Fin n) (R × S)) :
    ((Units.mapEquiv (matrixRingEquivProd (n := Fin n) R S).toMulEquiv).trans
      MulEquiv.prodUnits) g =
        (mapRingHom (RingHom.fst R S) g, mapRingHom (RingHom.snd R S) g) := rfl

private theorem prod_stage_assemble
    (R : Type u) (S : Type v) [Semiring R] [Semiring S]
    {n m k : ℕ} (hn : n ≤ k) (hm : m ≤ k)
    (g : GL (Fin n) R) (h : GL (Fin m) S) :
    ((map (RingHom.fst R S)).prod (map (RingHom.snd R S)))
      (stage (R × S) k
        (((Units.mapEquiv (matrixRingEquivProd (n := Fin k) R S).toMulEquiv).trans
          MulEquiv.prodUnits).symm
            (finStabilize R hn g, finStabilize S hm h))) =
        (stage R n g, stage S m h) := by
  let e := (Units.mapEquiv (matrixRingEquivProd (n := Fin k) R S).toMulEquiv).trans
    MulEquiv.prodUnits
  have he := e.apply_symm_apply (finStabilize R hn g, finStabilize S hm h)
  rw [matrixProdUnits_apply] at he
  apply Prod.ext
  · simpa only [MonoidHom.prod_apply, map_stage, stage_finStabilize] using
      congrArg (fun z => stage R k z.1) he
  · simpa only [MonoidHom.prod_apply, map_stage, stage_finStabilize] using
      congrArg (fun z => stage S k z.2) he

/-- Stable GL over a binary product of semirings, with coefficient projections
as its forward map. This extends the ring example in Weibel, *The K-book*,
Example III.1.1.3. -/
noncomputable def prodMulEquiv
    (R : Type u) (S : Type v) [Semiring R] [Semiring S] :
    StableGL (R × S) ≃* (StableGL R × StableGL S) :=
  MulEquiv.ofBijective
    ((map (RingHom.fst R S)).prod (map (RingHom.snd R S))) (by
      constructor
      · intro x y hxy
        obtain ⟨n, g, rfl⟩ := exists_stage (R × S) x
        obtain ⟨m, h, rfl⟩ := exists_stage (R × S) y
        let k := max n m
        let a := finStabilize (R × S) (le_max_left n m) g
        let b := finStabilize (R × S) (le_max_right n m) h
        have hfst : stage R k (mapRingHom (RingHom.fst R S) a) =
            stage R k (mapRingHom (RingHom.fst R S) b) := by
          simpa only [a, b, map_stage, ← finStabilize_mapRingHom,
            stage_finStabilize, MonoidHom.prod_apply] using congrArg Prod.fst hxy
        have hsnd : stage S k (mapRingHom (RingHom.snd R S) a) =
            stage S k (mapRingHom (RingHom.snd R S) b) := by
          simpa only [a, b, map_stage, ← finStabilize_mapRingHom,
            stage_finStabilize, MonoidHom.prod_apply] using congrArg Prod.snd hxy
        have hab : a = b := by
          apply ((Units.mapEquiv
            (matrixRingEquivProd (n := Fin k) R S).toMulEquiv).trans
              MulEquiv.prodUnits).injective
          rw [matrixProdUnits_apply, matrixProdUnits_apply]
          exact Prod.ext (stage_injective R k hfst) (stage_injective S k hsnd)
        calc
          stage (R × S) n g = stage (R × S) k a := (stage_finStabilize _ _ _).symm
          _ = stage (R × S) k b := congrArg (stage (R × S) k) hab
          _ = stage (R × S) m h := stage_finStabilize _ _ _
      · rintro ⟨x, y⟩
        obtain ⟨n, g, rfl⟩ := exists_stage R x
        obtain ⟨m, h, rfl⟩ := exists_stage S y
        exact ⟨_, prod_stage_assemble R S (le_max_left n m) (le_max_right n m) g h⟩)

/-- The forward homomorphism is the pair of coefficient projection maps. -/
theorem prodMulEquiv_toMonoidHom
    (R : Type u) (S : Type v) [Semiring R] [Semiring S] :
    (prodMulEquiv R S).toMonoidHom =
      (map (RingHom.fst R S)).prod (map (RingHom.snd R S)) := by rfl

/-- The first coordinate is coefficient projection onto the first factor. -/
@[simp]
theorem prodMulEquiv_fst
    (R : Type u) (S : Type v) [Semiring R] [Semiring S] (x : StableGL (R × S)) :
    (prodMulEquiv R S x).1 = map (RingHom.fst R S) x := by rfl

/-- The second coordinate is coefficient projection onto the second factor. -/
@[simp]
theorem prodMulEquiv_snd
    (R : Type u) (S : Type v) [Semiring R] [Semiring S] (x : StableGL (R × S)) :
    (prodMulEquiv R S x).2 = map (RingHom.snd R S) x := by rfl

/-- The product comparison computes on every original finite stage. -/
theorem prodMulEquiv_stage
    (R : Type u) (S : Type v) [Semiring R] [Semiring S]
    (n : ℕ) (g : GL (Fin n) (R × S)) :
    prodMulEquiv R S (stage (R × S) n g) =
      (stage R n (mapRingHom (RingHom.fst R S) g),
       stage S n (mapRingHom (RingHom.snd R S) g)) := by
  exact Prod.ext (map_stage _ _ _) (map_stage _ _ _)

/-- Assemble representatives of possibly different ranks at any common upper bound. -/
theorem prodMulEquiv_symm_stage_of_le
    (R : Type u) (S : Type v) [Semiring R] [Semiring S]
    {n m k : ℕ} (hn : n ≤ k) (hm : m ≤ k)
    (g : GL (Fin n) R) (h : GL (Fin m) S) :
    (prodMulEquiv R S).symm (stage R n g, stage S m h) =
      stage (R × S) k
        (((Units.mapEquiv (matrixRingEquivProd (n := Fin k) R S).toMulEquiv).trans
          MulEquiv.prodUnits).symm
            (finStabilize R hn g, finStabilize S hm h)) := by
  apply (prodMulEquiv R S).injective
  rw [MulEquiv.apply_symm_apply]
  exact (prod_stage_assemble R S hn hm g h).symm

/-- For unequal chosen ranks, their maximum is a common assembly stage. -/
theorem prodMulEquiv_symm_stage
    (R : Type u) (S : Type v) [Semiring R] [Semiring S]
    (n m : ℕ) (g : GL (Fin n) R) (h : GL (Fin m) S) :
    (prodMulEquiv R S).symm (stage R n g, stage S m h) =
      stage (R × S) (max n m)
        (((Units.mapEquiv
          (matrixRingEquivProd (n := Fin (max n m)) R S).toMulEquiv).trans
          MulEquiv.prodUnits).symm
            (finStabilize R (le_max_left n m) g,
             finStabilize S (le_max_right n m) h)) := by
  exact prodMulEquiv_symm_stage_of_le R S (le_max_left n m) (le_max_right n m) g h

/-- The whole product comparison homomorphism is natural in arbitrary coefficient
maps, with four independent coefficient universes. -/
theorem prodMulEquiv_map
    {R : Type u} {S : Type v} {R' : Type u'} {S' : Type v'}
    [Semiring R] [Semiring S] [Semiring R'] [Semiring S']
    (f : R →+* R') (g : S →+* S') :
    (prodMulEquiv R' S').toMonoidHom.comp (map (RingHom.prodMap f g)) =
      (MonoidHom.prodMap (map f) (map g)).comp (prodMulEquiv R S).toMonoidHom := by
  apply hom_ext (R × S)
  intro n
  apply MonoidHom.ext
  intro x
  apply Prod.ext <;>
    simp only [MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
      MulEquiv.coe_toMonoidHom, prodMulEquiv_fst, prodMulEquiv_snd, map_stage] <;>
    apply congrArg (stage _ n) <;> apply Units.ext <;> ext i j <;> rfl

private theorem piUnits_apply
    {ι : Type w} (R : ι → Type u) [∀ i, Semiring (R i)]
    (n : ℕ) (g : GL (Fin n) (∀ i, R i)) (i : ι) :
    ((Units.mapEquiv (Matrix.piRingEquiv (n := Fin n) (β := R)).toMulEquiv).trans
      MulEquiv.piUnits) g i = mapRingHom (Pi.evalRingHom R i) g := by
  apply Units.ext
  ext a b
  rfl

/-- Stable GL over a finite coefficient product, with evaluation maps as its
forward map. This generalizes Weibel, *The K-book*, Example III.1.1.3 to finite
families of semirings, including the empty family. -/
noncomputable def piMulEquiv
    {ι : Type w} [Finite ι] (R : ι → Type u) [∀ i, Semiring (R i)] :
    StableGL (∀ i, R i) ≃* (∀ i, StableGL (R i)) :=
  MulEquiv.ofBijective
    (MonoidHom.pi (fun i => map (Pi.evalRingHom R i))) (by
      constructor
      · intro x y hxy
        obtain ⟨n, g, rfl⟩ := exists_stage (∀ i, R i) x
        obtain ⟨m, h, rfl⟩ := exists_stage (∀ i, R i) y
        have hcoord (i : ι) :
            mapRingHom (Pi.evalRingHom R i)
                (finStabilize (∀ i, R i) (le_max_left n m) g) =
              mapRingHom (Pi.evalRingHom R i)
                (finStabilize (∀ i, R i) (le_max_right n m) h) := by
          apply stage_injective (R i) (max n m)
          simpa only [MonoidHom.pi_apply, ← map_stage, stage_finStabilize] using
            congrFun hxy i
        have hmat :
            finStabilize (∀ i, R i) (le_max_left n m) g =
              finStabilize (∀ i, R i) (le_max_right n m) h := by
          apply Units.ext
          ext a b i
          exact congrArg (fun z : GL (Fin (max n m)) (R i) => z a b) (hcoord i)
        calc
          stage (∀ i, R i) n g =
              stage (∀ i, R i) (max n m)
                (finStabilize (∀ i, R i) (le_max_left n m) g) :=
            (stage_finStabilize (∀ i, R i) (le_max_left n m) g).symm
          _ = stage (∀ i, R i) (max n m)
              (finStabilize (∀ i, R i) (le_max_right n m) h) :=
            congrArg (stage (∀ i, R i) (max n m)) hmat
          _ = stage (∀ i, R i) m h :=
            stage_finStabilize (∀ i, R i) (le_max_right n m) h
      · intro x
        classical
        let : Fintype ι := Fintype.ofFinite ι
        choose n g hg using fun i => exists_stage (R i) (x i)
        let k : ℕ := Finset.univ.sup n
        have hn (i : ι) : n i ≤ k := Finset.le_sup (Finset.mem_univ i)
        let e : GL (Fin k) (∀ i, R i) ≃* (∀ i, GL (Fin k) (R i)) :=
          (Units.mapEquiv (Matrix.piRingEquiv (n := Fin k) (β := R)).toMulEquiv).trans
            MulEquiv.piUnits
        refine ⟨stage (∀ i, R i) k
          (e.symm (fun i => finStabilize (R i) (hn i) (g i))), ?_⟩
        funext i
        have hi :
            mapRingHom (Pi.evalRingHom R i)
                (e.symm (fun i => finStabilize (R i) (hn i) (g i))) =
              finStabilize (R i) (hn i) (g i) :=
          (piUnits_apply R k _ i).symm.trans (congrFun (e.apply_symm_apply _) i)
        rw [MonoidHom.pi_apply, map_stage, hi, stage_finStabilize]
        exact hg i)

/-- The forward homomorphism is the family of coefficient evaluation maps. -/
theorem piMulEquiv_toMonoidHom
    {ι : Type w} [Finite ι] (R : ι → Type u) [∀ i, Semiring (R i)] :
    (piMulEquiv R).toMonoidHom =
      MonoidHom.pi (fun i => map (Pi.evalRingHom R i)) := rfl

/-- Evaluation of the stable product comparison is coefficient evaluation. -/
@[simp]
theorem piMulEquiv_apply
    {ι : Type w} [Finite ι] (R : ι → Type u) [∀ i, Semiring (R i)]
    (x : StableGL (∀ i, R i)) (i : ι) :
    piMulEquiv R x i = map (Pi.evalRingHom R i) x := rfl

/-- Every coordinate computes at the same original finite stage. -/
theorem piMulEquiv_stage_apply
    {ι : Type w} [Finite ι] (R : ι → Type u) [∀ i, Semiring (R i)]
    (n : ℕ) (g : GL (Fin n) (∀ i, R i)) (i : ι) :
    piMulEquiv R (stage (∀ i, R i) n g) i =
      stage (R i) n (mapRingHom (Pi.evalRingHom R i) g) :=
  map_stage (Pi.evalRingHom R i) n g

/-- Assemble any chosen representatives at any supplied common upper bound.
The equivalence itself needs no caller-supplied uniform bound. -/
theorem piMulEquiv_symm_stage_of_le
    {ι : Type w} [Finite ι] (R : ι → Type u) [∀ i, Semiring (R i)]
    (n : ι → ℕ) (g : ∀ i, GL (Fin (n i)) (R i))
    (k : ℕ) (hn : ∀ i, n i ≤ k) :
    (piMulEquiv R).symm (fun i => stage (R i) (n i) (g i)) =
      stage (∀ i, R i) k
        (((Units.mapEquiv
          (Matrix.piRingEquiv (n := Fin k) (β := R)).toMulEquiv).trans
          MulEquiv.piUnits).symm (fun i => finStabilize (R i) (hn i) (g i))) := by
  let e : GL (Fin k) (∀ i, R i) ≃* (∀ i, GL (Fin k) (R i)) :=
    (Units.mapEquiv (Matrix.piRingEquiv (n := Fin k) (β := R)).toMulEquiv).trans
      MulEquiv.piUnits
  apply (piMulEquiv R).injective
  funext i
  have hi :
      mapRingHom (Pi.evalRingHom R i)
          (e.symm (fun i => finStabilize (R i) (hn i) (g i))) =
        finStabilize (R i) (hn i) (g i) :=
    (piUnits_apply R k _ i).symm.trans (congrFun (e.apply_symm_apply _) i)
  rw [(piMulEquiv R).apply_symm_apply, piMulEquiv_stage_apply, hi,
    stage_finStabilize]

/-- The whole finite-product homomorphism is natural in arbitrary coefficient
maps, with independent source and target fiber universes. -/
theorem piMulEquiv_map
    {ι : Type w} [Finite ι] {R : ι → Type u} {S : ι → Type v}
    [∀ i, Semiring (R i)] [∀ i, Semiring (S i)] (f : ∀ i, R i →+* S i) :
    (piMulEquiv S).toMonoidHom.comp
        (map (RingHom.pi (fun i => (f i).comp (Pi.evalRingHom R i)))) =
      (MonoidHom.piMap (fun i => map (f i))).comp (piMulEquiv R).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  funext i
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, piMulEquiv_apply,
    MonoidHom.piMap_apply]
  have hcomp :
      (Pi.evalRingHom S i).comp
          (RingHom.pi (fun i => (f i).comp (Pi.evalRingHom R i))) =
        (f i).comp (Pi.evalRingHom R i) := by
    ext a
    rfl
  calc
    map (Pi.evalRingHom S i)
        (map (RingHom.pi (fun i => (f i).comp (Pi.evalRingHom R i))) x) =
      map ((Pi.evalRingHom S i).comp
        (RingHom.pi (fun i => (f i).comp (Pi.evalRingHom R i)))) x := by
          rw [map_comp, MonoidHom.comp_apply]
    _ = map ((f i).comp (Pi.evalRingHom R i)) x := by rw [hcomp]
    _ = map (f i) (map (Pi.evalRingHom R i) x) := by
      rw [map_comp, MonoidHom.comp_apply]

end StableGL

/-- The product comparison carries the stable elementary subgroup onto the
product of the stable elementary subgroups, as in Weibel, *The K-book*,
Example III.1.1.3, using Whitehead and the commutator product formula. -/
theorem stableElementarySubgroup_map_prodMulEquiv
    (R : Type u) (S : Type v) [Ring R] [Ring S] :
    (stableElementarySubgroup (R × S)).map (StableGL.prodMulEquiv R S).toMonoidHom =
      (stableElementarySubgroup R).prod (stableElementarySubgroup S) := by
  simp_rw [stableElementarySubgroup_eq_commutator]
  rw [map_commutator_eq]
  have hrange : (StableGL.prodMulEquiv R S).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (StableGL.prodMulEquiv R S).surjective
  rw [hrange]
  have htop : (⊤ : Subgroup (StableGL R × StableGL S)) =
      (⊤ : Subgroup (StableGL R)).prod (⊤ : Subgroup (StableGL S)) :=
    Subgroup.top_prod_top.symm
  change ⁅(⊤ : Subgroup (StableGL R × StableGL S)), ⊤⁆ =
    Subgroup.prod ⁅(⊤ : Subgroup (StableGL R)), ⊤⁆ ⁅(⊤ : Subgroup (StableGL S)), ⊤⁆
  rw [htop, Subgroup.commutator_prod_prod]

/-- Whitehead and the finite-Pi commutator formula identify the image of the
stable elementary subgroup with the product of the elementary subgroups. -/
theorem stableElementarySubgroup_map_piMulEquiv
    {ι : Type w} [Finite ι] (R : ι → Type u) [∀ i, Ring (R i)] :
    (stableElementarySubgroup (∀ i, R i)).map (StableGL.piMulEquiv R).toMonoidHom =
      Subgroup.pi Set.univ (fun i => stableElementarySubgroup (R i)) := by
  simp_rw [stableElementarySubgroup_eq_commutator]
  rw [map_commutator_eq]
  have hrange : (StableGL.piMulEquiv R).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (StableGL.piMulEquiv R).surjective
  rw [hrange]
  have htop : (⊤ : Subgroup (∀ i, StableGL (R i))) =
      Subgroup.pi Set.univ (fun i => (⊤ : Subgroup (StableGL (R i)))) :=
    (Subgroup.pi_top Set.univ).symm
  change ⁅(⊤ : Subgroup (∀ i, StableGL (R i))), ⊤⁆ =
    Subgroup.pi Set.univ (fun i => ⁅(⊤ : Subgroup (StableGL (R i))), ⊤⁆)
  rw [htop, Subgroup.commutator_pi_pi_of_finite]

/-- The binary coefficient-product equivalence on the existing stable elementary
quotients, with the quotient maps induced by coefficient projections as its
forward map. This is the quotient decomposition in Weibel, *The K-book*,
Example III.1.1.3. -/
noncomputable def stableElementaryQuotientProdMulEquiv
    (R : Type u) (S : Type v) [Ring R] [Ring S] :
    (StableGL (R × S) ⧸ stableElementarySubgroup (R × S)) ≃*
      ((StableGL R ⧸ stableElementarySubgroup R) ×
       (StableGL S ⧸ stableElementarySubgroup S)) :=
  MulEquiv.ofBijective
    ((QuotientGroup.map (stableElementarySubgroup (R × S)) (stableElementarySubgroup R)
      (StableGL.map (RingHom.fst R S))
      ((Subgroup.map_le_iff_le_comap).mp
        (StableGL.map_elementarySubgroup_le (RingHom.fst R S)))).prod
      (QuotientGroup.map (stableElementarySubgroup (R × S)) (stableElementarySubgroup S)
        (StableGL.map (RingHom.snd R S))
        ((Subgroup.map_le_iff_le_comap).mp
          (StableGL.map_elementarySubgroup_le (RingHom.snd R S))))) (by
      let e := (QuotientGroup.congr (stableElementarySubgroup (R × S))
        ((stableElementarySubgroup R).prod (stableElementarySubgroup S))
        (StableGL.prodMulEquiv R S) (stableElementarySubgroup_map_prodMulEquiv R S)).trans
          (QuotientGroup.prodMulEquiv (stableElementarySubgroup R)
            (stableElementarySubgroup S))
      have he : ∀ q, e q =
          ((QuotientGroup.map (stableElementarySubgroup (R × S)) (stableElementarySubgroup R)
            (StableGL.map (RingHom.fst R S))
            ((Subgroup.map_le_iff_le_comap).mp
              (StableGL.map_elementarySubgroup_le (RingHom.fst R S)))).prod
            (QuotientGroup.map (stableElementarySubgroup (R × S)) (stableElementarySubgroup S)
              (StableGL.map (RingHom.snd R S))
              ((Subgroup.map_le_iff_le_comap).mp
                (StableGL.map_elementarySubgroup_le (RingHom.snd R S))))) q := by
        intro q
        refine QuotientGroup.induction_on q ?_
        intro x
        rfl
      exact ⟨fun _ _ h => e.injective (by simpa only [he] using h),
        fun y => ⟨e.symm y, (he _).symm.trans (e.apply_symm_apply y)⟩⟩)

/-- The first quotient coordinate is the map induced by the first coefficient projection. -/
@[simp]
theorem stableElementaryQuotientProdMulEquiv_fst
    (R : Type u) (S : Type v) [Ring R] [Ring S]
    (q : StableGL (R × S) ⧸ stableElementarySubgroup (R × S)) :
    (stableElementaryQuotientProdMulEquiv R S q).1 =
      QuotientGroup.map (stableElementarySubgroup (R × S)) (stableElementarySubgroup R)
        (StableGL.map (RingHom.fst R S))
        ((Subgroup.map_le_iff_le_comap).mp
          (StableGL.map_elementarySubgroup_le (RingHom.fst R S))) q := by rfl

/-- The second quotient coordinate is the map induced by the second coefficient projection. -/
@[simp]
theorem stableElementaryQuotientProdMulEquiv_snd
    (R : Type u) (S : Type v) [Ring R] [Ring S]
    (q : StableGL (R × S) ⧸ stableElementarySubgroup (R × S)) :
    (stableElementaryQuotientProdMulEquiv R S q).2 =
      QuotientGroup.map (stableElementarySubgroup (R × S)) (stableElementarySubgroup S)
        (StableGL.map (RingHom.snd R S))
        ((Subgroup.map_le_iff_le_comap).mp
          (StableGL.map_elementarySubgroup_le (RingHom.snd R S))) q := by rfl

/-- The product quotient comparison computes on original stable representatives. -/
theorem stableElementaryQuotientProdMulEquiv_mk
    (R : Type u) (S : Type v) [Ring R] [Ring S] (x : StableGL (R × S)) :
    stableElementaryQuotientProdMulEquiv R S
        (QuotientGroup.mk' (stableElementarySubgroup (R × S)) x) =
      (QuotientGroup.mk' (stableElementarySubgroup R) (StableGL.map (RingHom.fst R S) x),
       QuotientGroup.mk' (stableElementarySubgroup S) (StableGL.map (RingHom.snd R S) x)) := by rfl

/-- Finite-stage quotient classes are sent to their coefficient projection classes. -/
theorem stableElementaryQuotientProdMulEquiv_stage
    (R : Type u) (S : Type v) [Ring R] [Ring S]
    (n : ℕ) (g : GL (Fin n) (R × S)) :
    stableElementaryQuotientProdMulEquiv R S
        (QuotientGroup.mk' (stableElementarySubgroup (R × S))
          (StableGL.stage (R × S) n g)) =
      (QuotientGroup.mk' (stableElementarySubgroup R)
        (StableGL.stage R n (mapRingHom (RingHom.fst R S) g)),
       QuotientGroup.mk' (stableElementarySubgroup S)
        (StableGL.stage S n (mapRingHom (RingHom.snd R S) g))) := by
  rw [stableElementaryQuotientProdMulEquiv_mk]
  simp only [StableGL.map_stage]

/-- Assemble quotient classes of unequal chosen ranks at any common later stage. -/
theorem stableElementaryQuotientProdMulEquiv_symm_stage_of_le
    (R : Type u) (S : Type v) [Ring R] [Ring S]
    {n m k : ℕ} (hn : n ≤ k) (hm : m ≤ k)
    (g : GL (Fin n) R) (h : GL (Fin m) S) :
    (stableElementaryQuotientProdMulEquiv R S).symm
        (QuotientGroup.mk' (stableElementarySubgroup R) (StableGL.stage R n g),
         QuotientGroup.mk' (stableElementarySubgroup S) (StableGL.stage S m h)) =
      QuotientGroup.mk' (stableElementarySubgroup (R × S))
        (StableGL.stage (R × S) k
          (((Units.mapEquiv (matrixRingEquivProd (n := Fin k) R S).toMulEquiv).trans
            MulEquiv.prodUnits).symm
              (finStabilize R hn g, finStabilize S hm h))) := by
  apply (stableElementaryQuotientProdMulEquiv R S).injective
  rw [MulEquiv.apply_symm_apply]
  rw [← StableGL.prodMulEquiv_symm_stage_of_le R S hn hm g h,
    stableElementaryQuotientProdMulEquiv_mk]
  have he := (StableGL.prodMulEquiv R S).apply_symm_apply
    (StableGL.stage R n g, StableGL.stage S m h)
  exact (congrArg (fun z =>
    (QuotientGroup.mk' (stableElementarySubgroup R) z.1,
     QuotientGroup.mk' (stableElementarySubgroup S) z.2)) he).symm

/-- The whole binary quotient comparison is natural in arbitrary coefficient maps. -/
theorem stableElementaryQuotientProdMulEquiv_map
    {R : Type u} {S : Type v} {R' : Type u'} {S' : Type v'}
    [Ring R] [Ring S] [Ring R'] [Ring S'] (f : R →+* R') (g : S →+* S') :
    (stableElementaryQuotientProdMulEquiv R' S').toMonoidHom.comp
        (QuotientGroup.map (stableElementarySubgroup (R × S))
          (stableElementarySubgroup (R' × S')) (StableGL.map (RingHom.prodMap f g))
          ((Subgroup.map_le_iff_le_comap).mp
            (StableGL.map_elementarySubgroup_le (RingHom.prodMap f g)))) =
      (MonoidHom.prodMap
        (QuotientGroup.map (stableElementarySubgroup R) (stableElementarySubgroup R')
          (StableGL.map f)
          ((Subgroup.map_le_iff_le_comap).mp (StableGL.map_elementarySubgroup_le f)))
        (QuotientGroup.map (stableElementarySubgroup S) (stableElementarySubgroup S')
          (StableGL.map g)
          ((Subgroup.map_le_iff_le_comap).mp (StableGL.map_elementarySubgroup_le g)))).comp
        (stableElementaryQuotientProdMulEquiv R S).toMonoidHom := by
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro x
  have h := DFunLike.congr_fun (StableGL.prodMulEquiv_map f g) x
  apply Prod.ext
  · simpa only [MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
      MonoidHom.coe_fst, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom,
      stableElementaryQuotientProdMulEquiv_fst, stableElementaryQuotientProdMulEquiv_snd,
      QuotientGroup.map_mk, QuotientGroup.mk'_apply,
      StableGL.prodMulEquiv_fst, StableGL.prodMulEquiv_snd] using
        congrArg (fun z => QuotientGroup.mk' (stableElementarySubgroup R') z.1) h
  · simpa only [MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
      MonoidHom.coe_fst, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom,
      stableElementaryQuotientProdMulEquiv_fst, stableElementaryQuotientProdMulEquiv_snd,
      QuotientGroup.map_mk, QuotientGroup.mk'_apply,
      StableGL.prodMulEquiv_fst, StableGL.prodMulEquiv_snd] using
        congrArg (fun z => QuotientGroup.mk' (stableElementarySubgroup S') z.2) h

/-- The finite coefficient-product equivalence on the existing stable elementary
quotients, with quotient evaluation maps as its forward map. This generalizes
Weibel, *The K-book*, Example III.1.1.3 to finite families of rings. -/
noncomputable def stableElementaryQuotientPiMulEquiv
    {ι : Type w} [Finite ι] (R : ι → Type u) [∀ i, Ring (R i)] :
    (StableGL (∀ i, R i) ⧸ stableElementarySubgroup (∀ i, R i)) ≃*
      (∀ i, StableGL (R i) ⧸ stableElementarySubgroup (R i)) :=
  MulEquiv.ofBijective
    (MonoidHom.pi (fun i =>
      QuotientGroup.map (stableElementarySubgroup (∀ i, R i)) (stableElementarySubgroup (R i))
        (StableGL.map (Pi.evalRingHom R i))
        ((Subgroup.map_le_iff_le_comap).mp
          (StableGL.map_elementarySubgroup_le (Pi.evalRingHom R i))))) (by
      let N := fun i => stableElementarySubgroup (R i)
      let φ := MonoidHom.piMap (fun i => QuotientGroup.mk' (N i))
      have hsurj : Function.Surjective φ := by
        intro q
        choose x hx using fun i => QuotientGroup.mk'_surjective (N i) (q i)
        exact ⟨x, funext hx⟩
      have hker : Subgroup.pi Set.univ N = φ.ker := by
        ext x
        simp [Subgroup.mem_pi, φ, MonoidHom.mem_ker, funext_iff]
      let : (Subgroup.pi Set.univ N).Normal := by
        rw [hker]
        infer_instance
      let e := (QuotientGroup.congr (stableElementarySubgroup (∀ i, R i))
        (Subgroup.pi Set.univ N) (StableGL.piMulEquiv R)
        (stableElementarySubgroup_map_piMulEquiv R)).trans
          (QuotientGroup.liftEquiv (Subgroup.pi Set.univ N) hsurj hker)
      have he : ∀ q, e q =
          (MonoidHom.pi (fun i =>
            QuotientGroup.map (stableElementarySubgroup (∀ i, R i))
              (stableElementarySubgroup (R i)) (StableGL.map (Pi.evalRingHom R i))
              ((Subgroup.map_le_iff_le_comap).mp
                (StableGL.map_elementarySubgroup_le (Pi.evalRingHom R i))))) q := by
        intro q
        refine QuotientGroup.induction_on q ?_
        intro x
        rfl
      exact ⟨fun _ _ h => e.injective (by simpa only [he] using h),
        fun y => ⟨e.symm y, (he _).symm.trans (e.apply_symm_apply y)⟩⟩)

/-- A coordinate of the quotient comparison is the induced coefficient evaluation map. -/
@[simp]
theorem stableElementaryQuotientPiMulEquiv_apply
    {ι : Type w} [Finite ι] (R : ι → Type u) [∀ i, Ring (R i)]
    (q : StableGL (∀ i, R i) ⧸ stableElementarySubgroup (∀ i, R i)) (i : ι) :
    stableElementaryQuotientPiMulEquiv R q i =
      QuotientGroup.map (stableElementarySubgroup (∀ i, R i)) (stableElementarySubgroup (R i))
        (StableGL.map (Pi.evalRingHom R i))
        ((Subgroup.map_le_iff_le_comap).mp
          (StableGL.map_elementarySubgroup_le (Pi.evalRingHom R i))) q := by rfl

/-- The finite-product quotient comparison computes on original stable representatives. -/
theorem stableElementaryQuotientPiMulEquiv_mk_apply
    {ι : Type w} [Finite ι] (R : ι → Type u) [∀ i, Ring (R i)]
    (x : StableGL (∀ i, R i)) (i : ι) :
    stableElementaryQuotientPiMulEquiv R
        (QuotientGroup.mk' (stableElementarySubgroup (∀ i, R i)) x) i =
      QuotientGroup.mk' (stableElementarySubgroup (R i))
        (StableGL.map (Pi.evalRingHom R i) x) := by rfl

/-- Each quotient coordinate computes at the original finite stage. -/
theorem stableElementaryQuotientPiMulEquiv_stage_apply
    {ι : Type w} [Finite ι] (R : ι → Type u) [∀ i, Ring (R i)]
    (n : ℕ) (g : GL (Fin n) (∀ i, R i)) (i : ι) :
    stableElementaryQuotientPiMulEquiv R
        (QuotientGroup.mk' (stableElementarySubgroup (∀ i, R i))
          (StableGL.stage (∀ i, R i) n g)) i =
      QuotientGroup.mk' (stableElementarySubgroup (R i))
        (StableGL.stage (R i) n (mapRingHom (Pi.evalRingHom R i) g)) := by
  rw [stableElementaryQuotientPiMulEquiv_mk_apply, StableGL.map_stage]

/-- Assemble finite families of quotient representatives at any common upper bound. -/
theorem stableElementaryQuotientPiMulEquiv_symm_stage_of_le
    {ι : Type w} [Finite ι] (R : ι → Type u) [∀ i, Ring (R i)]
    (n : ι → ℕ) (g : ∀ i, GL (Fin (n i)) (R i))
    (k : ℕ) (hn : ∀ i, n i ≤ k) :
    (stableElementaryQuotientPiMulEquiv R).symm
        (fun i => QuotientGroup.mk' (stableElementarySubgroup (R i))
          (StableGL.stage (R i) (n i) (g i))) =
      QuotientGroup.mk' (stableElementarySubgroup (∀ i, R i))
        (StableGL.stage (∀ i, R i) k
          (((Units.mapEquiv
            (Matrix.piRingEquiv (n := Fin k) (β := R)).toMulEquiv).trans
            MulEquiv.piUnits).symm (fun i => finStabilize (R i) (hn i) (g i)))) := by
  apply (stableElementaryQuotientPiMulEquiv R).injective
  rw [MulEquiv.apply_symm_apply]
  rw [← StableGL.piMulEquiv_symm_stage_of_le R n g k hn]
  funext i
  rw [stableElementaryQuotientPiMulEquiv_mk_apply]
  exact (congrArg (fun z => QuotientGroup.mk' (stableElementarySubgroup (R i)) (z i))
    ((StableGL.piMulEquiv R).apply_symm_apply
      (fun i => StableGL.stage (R i) (n i) (g i)))).symm

/-- The whole finite-product quotient comparison is natural in arbitrary coefficient
maps, with independent source and target fiber universes. -/
theorem stableElementaryQuotientPiMulEquiv_map
    {ι : Type w} [Finite ι] {R : ι → Type u} {S : ι → Type v}
    [∀ i, Ring (R i)] [∀ i, Ring (S i)] (f : ∀ i, R i →+* S i) :
    (stableElementaryQuotientPiMulEquiv S).toMonoidHom.comp
        (QuotientGroup.map (stableElementarySubgroup (∀ i, R i))
          (stableElementarySubgroup (∀ i, S i))
          (StableGL.map (RingHom.pi (fun i => (f i).comp (Pi.evalRingHom R i))))
          ((Subgroup.map_le_iff_le_comap).mp
            (StableGL.map_elementarySubgroup_le
              (RingHom.pi (fun i => (f i).comp (Pi.evalRingHom R i)))))) =
      (MonoidHom.piMap (fun i =>
        QuotientGroup.map (stableElementarySubgroup (R i)) (stableElementarySubgroup (S i))
          (StableGL.map (f i))
          ((Subgroup.map_le_iff_le_comap).mp (StableGL.map_elementarySubgroup_le (f i))))).comp
        (stableElementaryQuotientPiMulEquiv R).toMonoidHom := by
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro x
  funext i
  have h := congrArg (fun z => z i) (DFunLike.congr_fun (StableGL.piMulEquiv_map f) x)
  simpa only [MonoidHom.comp_apply, MonoidHom.pi_apply, MonoidHom.piMap_apply,
    MulEquiv.coe_toMonoidHom, stableElementaryQuotientPiMulEquiv_apply,
    QuotientGroup.map_mk, QuotientGroup.mk'_apply, StableGL.piMulEquiv_apply] using
      congrArg (QuotientGroup.mk' (stableElementarySubgroup (S i))) h

/-- The binary quotient comparison agrees with Whitehead and the canonical stock
abelianization projections, as an equality of homomorphisms. -/
theorem stableElementaryAbelianizationEquiv_prodMulEquiv
    (R : Type u) (S : Type v) [Ring R] [Ring S] :
    (MonoidHom.prodMap (stableElementaryAbelianizationEquiv R).toMonoidHom
      (stableElementaryAbelianizationEquiv S).toMonoidHom).comp
        (stableElementaryQuotientProdMulEquiv R S).toMonoidHom =
      ((Abelianization.map (MonoidHom.fst (StableGL R) (StableGL S))).prod
        (Abelianization.map (MonoidHom.snd (StableGL R) (StableGL S)))).comp
          ((Abelianization.map (StableGL.prodMulEquiv R S).toMonoidHom).comp
            (stableElementaryAbelianizationEquiv (R × S)).toMonoidHom) := by
  have hfst : (MonoidHom.fst (StableGL R) (StableGL S)).comp
      (StableGL.prodMulEquiv R S).toMonoidHom = StableGL.map (RingHom.fst R S) := by
    apply MonoidHom.ext
    intro x
    exact StableGL.prodMulEquiv_fst R S x
  have hsnd : (MonoidHom.snd (StableGL R) (StableGL S)).comp
      (StableGL.prodMulEquiv R S).toMonoidHom = StableGL.map (RingHom.snd R S) := by
    apply MonoidHom.ext
    intro x
    exact StableGL.prodMulEquiv_snd R S x
  apply MonoidHom.ext
  intro q
  apply Prod.ext <;>
    simp only [MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
      MonoidHom.coe_fst, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom,
      stableElementaryQuotientProdMulEquiv_fst, stableElementaryQuotientProdMulEquiv_snd,
      stableElementaryAbelianizationEquiv_map, Abelianization.map_map_apply, hfst, hsnd]

/-- The finite-product quotient comparison agrees with Whitehead and the canonical
stock abelianization evaluation maps, as an equality of homomorphisms. -/
theorem stableElementaryAbelianizationEquiv_piMulEquiv
    {ι : Type w} [Finite ι] (R : ι → Type u) [∀ i, Ring (R i)] :
    (MonoidHom.piMap (fun i => (stableElementaryAbelianizationEquiv (R i)).toMonoidHom)).comp
        (stableElementaryQuotientPiMulEquiv R).toMonoidHom =
      (MonoidHom.pi (fun i =>
        Abelianization.map (Pi.evalMonoidHom (fun i => StableGL (R i)) i))).comp
          ((Abelianization.map (StableGL.piMulEquiv R).toMonoidHom).comp
            (stableElementaryAbelianizationEquiv (∀ i, R i)).toMonoidHom) := by
  apply MonoidHom.ext
  intro q
  funext i
  have heval : (Pi.evalMonoidHom (fun i => StableGL (R i)) i).comp
      (StableGL.piMulEquiv R).toMonoidHom = StableGL.map (Pi.evalRingHom R i) := by
    apply MonoidHom.ext
    intro x
    exact StableGL.piMulEquiv_apply R x i
  simp only [MonoidHom.comp_apply, MonoidHom.piMap_apply, MonoidHom.pi_apply,
    MulEquiv.coe_toMonoidHom, stableElementaryQuotientPiMulEquiv_apply,
    stableElementaryAbelianizationEquiv_map, Abelianization.map_map_apply, heval]

end Matrix.GeneralLinearGroup
