/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.StableDeterminant
public import Mathlib.Data.Matrix.Composition

/-!
# Matrix amplification of stable general-linear groups

For a positive natural matrix size, row-major flattening identifies the canonical
stable general-linear group over a matrix semiring with that over its coefficient
semiring. Over a ring, the existing Whitehead comparison transports this equivalence
to the existing stable elementary quotient. Over a commutative coefficient ring,
its quotient determinant evaluates on a unit in the matrix ring as the ordinary determinant.
The ring formulation of matrix invariance is described in Weibel, *The K-book*,
Example III.1.1.4; the stable-group construction here extends it to semirings.

The finite flattening is the composition of Mathlib's `Matrix.compRingEquiv`,
`Units.mapEquiv`, and the existing general-linear `reindexEquiv` along
`finProdFinEquiv`. The row-major order is fixed; no basis-independent group-level
identification for an unspecified finite index type is asserted.

The positive-size restriction is essential: the size-zero matrix ring is the zero
ring, whose stable group is trivial, whereas the stable group of the coefficient
ring need not be trivial (for example, the integer unit −1 is detected by determinant).

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*
  (2013-08-29 version), Example III.1.1.4 (matrix invariance) and
  Example III.1.1.1 (determinant).
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

private def matrixFlatten (R : Type u) [Semiring R] (n k : ℕ) :
    GL (Fin k) (Matrix (Fin n) (Fin n) R) ≃* GL (Fin (k * n)) R :=
  (Units.mapEquiv (Matrix.compRingEquiv (Fin k) (Fin n) R).toMulEquiv).trans
    (reindexEquiv R (finProdFinEquiv : Fin k × Fin n ≃ Fin (k * n)))

private theorem matrixFlatten_apply (R : Type u) [Semiring R] (n k : ℕ)
    (g : GL (Fin k) (Matrix (Fin n) (Fin n) R))
    (i j : Fin k) (a b : Fin n) :
    matrixFlatten R n k g (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      g i j a b := by
  simp [matrixFlatten, reindexEquiv_apply, Units.coe_mapEquiv,
    Matrix.compRingEquiv_apply, Matrix.comp_apply]

-- Row-major coordinates preserve the boundary of every initial segment.
private theorem rowMajor_lt {n : ℕ} (k i : ℕ) (a : Fin n) :
    a.val + n * i < k * n ↔ i < k := by
  constructor
  · intro h
    by_contra hi
    have hle := Nat.mul_le_mul_right n (Nat.le_of_not_gt hi)
    have : k * n ≤ a.val + n * i := by
      simpa only [Nat.mul_comm i n] using hle.trans (Nat.le_add_left (i * n) a.val)
    omega
  · intro hi
    calc
      a.val + n * i < n + n * i := Nat.add_lt_add_right a.isLt _
      _ = (i + 1) * n := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm i n, Nat.add_comm]
      _ ≤ k * n := Nat.mul_le_mul_right n hi

/-- Nested-matrix flattening commutes with the original initial-segment
stabilizations, including size-zero coefficient matrices. -/
theorem finStabilize_compRingEquiv
    (R : Type u) [Semiring R] (n : ℕ) {k l : ℕ} (h : k ≤ l)
    (g : GL (Fin k) (Matrix (Fin n) (Fin n) R)) :
    reindexEquiv R (finProdFinEquiv : Fin l × Fin n ≃ Fin (l * n))
        (Units.mapEquiv (Matrix.compRingEquiv (Fin l) (Fin n) R).toMulEquiv
          (finStabilize (Matrix (Fin n) (Fin n) R) h g)) =
      finStabilize R (Nat.mul_le_mul_right n h)
        (reindexEquiv R (finProdFinEquiv : Fin k × Fin n ≃ Fin (k * n))
          (Units.mapEquiv (Matrix.compRingEquiv (Fin k) (Fin n) R).toMulEquiv g)) := by
  change matrixFlatten R n l (finStabilize (Matrix (Fin n) (Fin n) R) h g) =
    finStabilize R (Nat.mul_le_mul_right n h) (matrixFlatten R n k g)
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective y
  rw [matrixFlatten_apply]
  have hi : (finProdFinEquiv (i, a)).val < k * n ↔ i.val < k := rowMajor_lt k i.val a
  have hj : (finProdFinEquiv (j, b)).val < k * n ↔ j.val < k := rowMajor_lt k j.val b
  by_cases hik : i.val < k <;> by_cases hjk : j.val < k
  · have ei : Fin.castLE (Nat.mul_le_mul_right n h)
        (finProdFinEquiv (⟨i.val, hik⟩, a)) = finProdFinEquiv (i, a) := Fin.ext rfl
    have ej : Fin.castLE (Nat.mul_le_mul_right n h)
        (finProdFinEquiv (⟨j.val, hjk⟩, b)) = finProdFinEquiv (j, b) := Fin.ext rfl
    rw [← ei, ← ej, finStabilize_apply_castLE, matrixFlatten_apply]
    simp [finStabilize_apply, hik, hjk]
  · simp only [finStabilize_apply, hi, hj, hik, hjk, ↓reduceDIte,
      Matrix.zero_apply]
  · simp only [finStabilize_apply, hi, hj, hik, hjk, ↓reduceDIte, ↓reduceIte,
      Matrix.zero_apply]
  · have heq : (finProdFinEquiv (i, a)).val = (finProdFinEquiv (j, b)).val ↔
        i = j ∧ a = b := by
      rw [← Fin.ext_iff, finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
    simp only [finStabilize_apply, hi, hj, hik, hjk, ↓reduceDIte, ↓reduceIte, heq]
    by_cases hij : i = j <;> by_cases hab : a = b <;>
      simp [hij, hab, ← Fin.ext_iff, Matrix.one_apply]

namespace StableGL

/-- Row-major matrix flattening on the original canonical stable general-linear
groups, for a positive matrix size over an arbitrary semiring. This extends the
ring formulation in Weibel, *The K-book*, Example III.1.1.4, with fixed row-major coordinates. -/
noncomputable def matrixMulEquiv (R : Type u) [Semiring R] (n : ℕ) (hn : 0 < n) :
    StableGL (Matrix (Fin n) (Fin n) R) ≃* StableGL R := by
  let flatten (k : ℕ) :
      GL (Fin k) (Matrix (Fin n) (Fin n) R) ≃* GL (Fin (k * n)) R :=
    (Units.mapEquiv (Matrix.compRingEquiv (Fin k) (Fin n) R).toMulEquiv).trans
      (reindexEquiv R (finProdFinEquiv : Fin k × Fin n ≃ Fin (k * n)))
  have coherent {k l : ℕ} (h : k ≤ l)
      (g : GL (Fin k) (Matrix (Fin n) (Fin n) R)) :
      flatten l (finStabilize (Matrix (Fin n) (Fin n) R) h g) =
        finStabilize R (Nat.mul_le_mul_right n h) (flatten k g) :=
    finStabilize_compRingEquiv R n h g
  have le_mul (k : ℕ) : k ≤ k * n := by
    simpa using Nat.mul_le_mul_left k hn
  let forward : StableGL (Matrix (Fin n) (Fin n) R) →* StableGL R :=
    lift (Matrix (Fin n) (Fin n) R)
      (fun k => (stage R (k * n)).comp (flatten k).toMonoidHom)
      (by
        intro k l h g
        change stage R (l * n) (flatten l (finStabilize _ h g)) = _
        rw [coherent, stage_finStabilize]
        rfl)
  let backward : StableGL R →* StableGL (Matrix (Fin n) (Fin n) R) :=
    lift R
      (fun k => (stage (Matrix (Fin n) (Fin n) R) k).comp
        ((flatten k).symm.toMonoidHom.comp
          (finStabilize R (le_mul k))))
      (by
        intro k l h g
        change stage _ l ((flatten l).symm (finStabilize R (le_mul l)
          (finStabilize R h g))) = stage _ k ((flatten k).symm
            (finStabilize R (le_mul k) g))
        rw [← stage_finStabilize _ h]
        congr 1
        apply (flatten l).injective
        rw [MulEquiv.apply_symm_apply, coherent, MulEquiv.apply_symm_apply]
        exact congrArg (fun f => f g)
          ((finStabilize_comp R h (le_mul l)).symm.trans
            (finStabilize_comp R (le_mul k) (Nat.mul_le_mul_right n h))))
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro x
        obtain ⟨k, g, rfl⟩ := exists_stage (Matrix (Fin n) (Fin n) R) x
        change stage _ (k * n) ((flatten (k * n)).symm
          (finStabilize R (le_mul (k * n)) (flatten k g))) = stage _ k g
        rw [← coherent (le_mul k), MulEquiv.symm_apply_apply, stage_finStabilize]
      right_inv := by
        intro x
        obtain ⟨k, g, rfl⟩ := exists_stage R x
        change stage R (k * n) (flatten k ((flatten k).symm
          (finStabilize R (le_mul k) g))) = stage R k g
        rw [MulEquiv.apply_symm_apply, stage_finStabilize]
      map_mul' := fun x y => map_mul forward x y }

/-- Matrix amplification is characterized on every original finite stage by
stock nested-matrix flattening followed by row-major finite reindexing. -/
theorem matrixMulEquiv_stage (R : Type u) [Semiring R] (n : ℕ) (hn : 0 < n)
    (k : ℕ) (g : GL (Fin k) (Matrix (Fin n) (Fin n) R)) :
    matrixMulEquiv R n hn (stage (Matrix (Fin n) (Fin n) R) k g) =
      stage R (k * n)
        (reindexEquiv R (finProdFinEquiv : Fin k × Fin n ≃ Fin (k * n))
          (Units.mapEquiv (Matrix.compRingEquiv (Fin k) (Fin n) R).toMulEquiv g)) := by
  rfl

/-- The inverse computes on the cofinal family of flattened finite stages. -/
theorem matrixMulEquiv_symm_stage (R : Type u) [Semiring R] (n : ℕ) (hn : 0 < n)
    (k : ℕ) (g : GL (Fin k) (Matrix (Fin n) (Fin n) R)) :
    (matrixMulEquiv R n hn).symm
        (stage R (k * n)
          (reindexEquiv R (finProdFinEquiv : Fin k × Fin n ≃ Fin (k * n))
            (Units.mapEquiv (Matrix.compRingEquiv (Fin k) (Fin n) R).toMulEquiv g))) =
      stage (Matrix (Fin n) (Fin n) R) k g := by
  rw [← matrixMulEquiv_stage R n hn k g, MulEquiv.symm_apply_apply]

/-- Matrix amplification commutes with arbitrary semiring coefficient maps,
with independent source and target universes. -/
theorem matrixMulEquiv_map {R : Type u} {S : Type v} [Semiring R] [Semiring S]
    (f : R →+* S) (n : ℕ) (hn : 0 < n) :
    (matrixMulEquiv S n hn).toMonoidHom.comp (map (RingHom.mapMatrix (m := Fin n) f)) =
      (map f).comp (matrixMulEquiv R n hn).toMonoidHom := by
  apply hom_ext (Matrix (Fin n) (Fin n) R)
  intro k
  apply MonoidHom.ext
  intro g
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    map_stage, matrixMulEquiv_stage, mapRingHom_reindexEquiv]
  congr 1

end StableGL

/-- Matrix amplification carries the original stable elementary subgroup onto
the original stable elementary subgroup over the coefficient ring, as in
Weibel, *The K-book*, Example III.1.1.4. -/
theorem stableElementarySubgroup_map_matrixMulEquiv
    (R : Type u) [Ring R] (n : ℕ) (hn : 0 < n) :
    (stableElementarySubgroup (Matrix (Fin n) (Fin n) R)).map
        (StableGL.matrixMulEquiv R n hn).toMonoidHom =
      stableElementarySubgroup R := by
  rw [stableElementarySubgroup_eq_commutator, stableElementarySubgroup_eq_commutator,
    map_commutator_eq]
  have hrange : (StableGL.matrixMulEquiv R n hn).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (StableGL.matrixMulEquiv R n hn).surjective
  rw [hrange, commutator_def]

/-- Matrix amplification on the existing stable elementary quotients, using
the existing Whitehead quotient comparisons and stock abelianization transport.
This is the positive-size matrix invariance of Weibel, *The K-book*, Example III.1.1.4,
with the fixed row-major stable-group equivalence. -/
noncomputable def stableElementaryQuotientMatrixMulEquiv
    (R : Type u) [Ring R] (n : ℕ) (hn : 0 < n) :
    (StableGL (Matrix (Fin n) (Fin n) R) ⧸
      stableElementarySubgroup (Matrix (Fin n) (Fin n) R)) ≃*
        (StableGL R ⧸ stableElementarySubgroup R) :=
  (stableElementaryAbelianizationEquiv (Matrix (Fin n) (Fin n) R)).trans
    ((MulEquiv.abelianizationCongr (StableGL.matrixMulEquiv R n hn)).trans
      (stableElementaryAbelianizationEquiv R).symm)

/-- Quotient matrix amplification sends the class of a stable matrix to the
class of its canonical row-major amplification. -/
theorem stableElementaryQuotientMatrixMulEquiv_mk
    (R : Type u) [Ring R] (n : ℕ) (hn : 0 < n)
    (g : StableGL (Matrix (Fin n) (Fin n) R)) :
    stableElementaryQuotientMatrixMulEquiv R n hn
        (QuotientGroup.mk' (stableElementarySubgroup (Matrix (Fin n) (Fin n) R)) g) =
      QuotientGroup.mk' (stableElementarySubgroup R) (StableGL.matrixMulEquiv R n hn g) := by
  simp only [stableElementaryQuotientMatrixMulEquiv, MulEquiv.trans_apply,
    stableElementaryAbelianizationEquiv_mk, abelianizationCongr_of,
    stableElementaryAbelianizationEquiv_symm_of]

/-- Matrix amplification of elementary quotient classes agrees with the
original canonical Whitehead comparisons to abelianizations. -/
theorem stableElementaryAbelianizationEquiv_matrixMulEquiv
    (R : Type u) [Ring R] (n : ℕ) (hn : 0 < n)
    (q : StableGL (Matrix (Fin n) (Fin n) R) ⧸
      stableElementarySubgroup (Matrix (Fin n) (Fin n) R)) :
    stableElementaryAbelianizationEquiv R
        (stableElementaryQuotientMatrixMulEquiv R n hn q) =
      MulEquiv.abelianizationCongr (StableGL.matrixMulEquiv R n hn)
        (stableElementaryAbelianizationEquiv (Matrix (Fin n) (Fin n) R) q) := by
  simp [stableElementaryQuotientMatrixMulEquiv]

/-- Matrix amplification of the existing elementary quotients commutes with
arbitrary ring coefficient maps. -/
theorem stableElementaryQuotientMatrixMulEquiv_map
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (n : ℕ) (hn : 0 < n) :
    (stableElementaryQuotientMatrixMulEquiv S n hn).toMonoidHom.comp
        (QuotientGroup.map
          (stableElementarySubgroup (Matrix (Fin n) (Fin n) R))
          (stableElementarySubgroup (Matrix (Fin n) (Fin n) S))
          (StableGL.map (RingHom.mapMatrix (m := Fin n) f))
          ((Subgroup.map_le_iff_le_comap
            (f := StableGL.map (RingHom.mapMatrix (m := Fin n) f))
            (K := stableElementarySubgroup (Matrix (Fin n) (Fin n) R))
            (H := stableElementarySubgroup (Matrix (Fin n) (Fin n) S))).mp
              (StableGL.map_elementarySubgroup_le
                (R := Matrix (Fin n) (Fin n) R) (S := Matrix (Fin n) (Fin n) S)
                (RingHom.mapMatrix (m := Fin n) f)))) =
      (QuotientGroup.map (stableElementarySubgroup R) (stableElementarySubgroup S)
        (StableGL.map f)
        ((Subgroup.map_le_iff_le_comap
          (f := StableGL.map f) (K := stableElementarySubgroup R)
          (H := stableElementarySubgroup S)).mp
            (StableGL.map_elementarySubgroup_le f))).comp
        (stableElementaryQuotientMatrixMulEquiv R n hn).toMonoidHom := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  simp only [MonoidHom.comp_apply]
  exact congrArg (QuotientGroup.mk' (stableElementarySubgroup S))
    (DFunLike.congr_fun (StableGL.matrixMulEquiv_map f n hn) g)

/-- Over a commutative base ring, the transported quotient determinant of a
unit in the matrix ring is its original finite determinant. The matrix coefficient ring
itself need not be commutative. This combines the determinant of Weibel, *The K-book*,
Example III.1.1.1, with the matrix invariance of Example III.1.1.4. -/
theorem quotientDet_matrixMulEquiv_quotientRankOneUnits
    (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) (g : GL (Fin n) R) :
    StableGL.quotientDet R
        (stableElementaryQuotientMatrixMulEquiv R n hn
          (StableGL.quotientRankOneUnits (Matrix (Fin n) (Fin n) R) g)) =
      Matrix.GeneralLinearGroup.det g := by
  rw [StableGL.quotientRankOneUnits_apply, stableElementaryQuotientMatrixMulEquiv_mk,
    StableGL.quotientDet_mk, StableGL.rankOneUnits_apply, StableGL.matrixMulEquiv_stage,
    StableGL.det_stage]
  have hg : reindexEquiv R (finProdFinEquiv : Fin 1 × Fin n ≃ Fin (1 * n))
      (Units.mapEquiv (Matrix.compRingEquiv (Fin 1) (Fin n) R).toMulEquiv
        (scalar (Fin 1) g)) = reindexEquiv R (finCongr (Nat.one_mul n).symm) g := by
    change matrixFlatten R n 1 (scalar (Fin 1) g) = _
    apply Units.ext
    ext x y
    obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective y
    rw [matrixFlatten_apply, reindexEquiv_apply]
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simp [coe_scalar, Matrix.scalar, finProdFinEquiv, finCongr]
  rw [hg]
  apply Units.ext
  change Matrix.det (Matrix.reindex _ _ (g : Matrix (Fin n) (Fin n) R)) = _
  exact Matrix.det_reindex_self _ _

end Matrix.GeneralLinearGroup
