/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.RectangularBlockUnits
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Preorder.Finite
import Mathlib.GroupTheory.DedekindFinite

/-!
# Units of finite block-triangular matrices

The diagonal blocks are the restrictions to the equality fibers of a label map.
The labels may be preordered, with the represented labels forming a strict chain.
For partially ordered labels, a chain for the non-strict order suffices. The
coefficient ring need not be commutative, and the finite matrix index and the
label type may be empty.

Over a semiring, a unit matrix has unit diagonal blocks if their matrix monoids
are Dedekind-finite. Given invertibility of the full matrix and unit diagonal
blocks, its given inverse is block triangular without a direct-finiteness
assumption. These directions do not assert semiring sufficiency from diagonal
units.

## References

* Mathlib contributors, `Matrix.blockTriangular_inv_of_blockTriangular` and
  `Matrix.invOf_eq_nonsing_inv`, for the commutative-ring specialization.

* Mathlib contributors, `Matrix.fromBlocks_multiply`,
  `Equiv.subtypeSubtypeEquivSubtype`, and
  `IsDedekindFiniteMonoid.of_injective`, for block multiplication and transport
  to the remaining diagonal-block matrix monoids.

* Mathlib contributors, `Matrix.BlockTriangular.det` in
  `Mathlib.LinearAlgebra.Matrix.Block`, for the maximal-fiber splitting and
  comparison of restricted fibers.
* Formal Frontier Agents, `GeneralLinearGroups.RectangularBlockUnits`, for
  `Matrix.GeneralLinearGroup.triangularUnit` and its matrix-value formula.
-/

@[expose] public section

universe uM uA uR

namespace Matrix

private theorem isUnit_of_isUnit_compl_submatrix
    {m : Type uM} {R : Type uR}
    [Fintype m] [DecidableEq m] [Ring R]
    (p : m → Prop) [DecidablePred p] (M : Matrix m m R)
    (hA : IsUnit (M.submatrix
      (Subtype.val : {i : m // ¬ p i} → m) (Subtype.val : {i : m // ¬ p i} → m)))
    (hD : IsUnit (M.submatrix
      (Subtype.val : {i : m // p i} → m) (Subtype.val : {i : m // p i} → m)))
    (hzero : ∀ (i : {i : m // p i}) (j : {j : m // ¬ p j}),
      M i j = 0) : IsUnit M := by
  let X := {i : m // ¬ p i}
  let Y := {i : m // p i}
  let A : Matrix X X R := M.submatrix Subtype.val Subtype.val
  let B : Matrix X Y R := M.submatrix Subtype.val Subtype.val
  let D : Matrix Y Y R := M.submatrix Subtype.val Subtype.val
  let e : X ⊕ Y ≃ m := (Equiv.sumComm X Y).trans (Equiv.sumCompl p)
  have he_inl (i : X) : e (Sum.inl i) = i.val := by
    simpa only [e, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inl] using
      (Equiv.sumCompl_apply_inr (p := p) i)
  have he_inr (i : Y) : e (Sum.inr i) = i.val := by
    simpa only [e, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr] using
      (Equiv.sumCompl_apply_inl (p := p) i)
  let T : Matrix (X ⊕ Y) (X ⊕ Y) R :=
    (Matrix.reindexRingEquiv R e.symm) M
  have hT : T = Matrix.fromBlocks A B 0 D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [T, Matrix.coe_reindexRingEquiv, Matrix.reindex_apply,
        Equiv.symm_symm, Matrix.submatrix_apply, he_inl, he_inr,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, A, B, D]
    exact hzero i j
  have hsplit : IsUnit T := by
    rw [hT]
    simpa only [Matrix.GeneralLinearGroup.triangularUnit_val,
      IsUnit.unit_spec] using
      (Units.isUnit
        (Matrix.GeneralLinearGroup.triangularUnit hA.unit B hD.unit))
  have hback : IsUnit ((Matrix.reindexRingEquiv R e) T) :=
    hsplit.map (Matrix.reindexRingEquiv R e).toMonoidHom
  have hread : (Matrix.reindexRingEquiv R e) T = M := by
    simpa only [T, Matrix.symm_reindexRingEquiv] using
      (Matrix.reindexRingEquiv R e).apply_symm_apply M
  simpa only [hread] using hback

variable {m : Type uM} {α : Type uA} {R : Type uR}

section Preorder

variable [Fintype m] [DecidableEq m] [Preorder α] [DecidableEq α] [Ring R]
variable {b : m → α} {M : Matrix m m R}

/-- A finite block-triangular matrix over a ring is a unit if its represented
labels form a strict chain and each equality-fiber diagonal block is a unit.
The ambient preorder need not be antisymmetric, and empty fibers are included. -/
theorem BlockTriangular.isUnit_of_isUnit_toSquareBlock_of_isChain_lt
    (hM : M.BlockTriangular b)
    (hchain : IsChain (fun x y : α => x < y) (Set.range b))
    (hblocks : ∀ k : α, IsUnit (M.toSquareBlock b k)) : IsUnit M := by
  classical
  -- The induction varies the index type as its cardinality decreases.
  suffices ∀ n : ℕ, ∀ (ι : Type uM) [Fintype ι] [DecidableEq ι]
      (c : ι → α) (N : Matrix ι ι R), Fintype.card ι = n →
      N.BlockTriangular c → IsChain (fun x y : α => x < y) (Set.range c) →
      (∀ k : α, IsUnit (N.toSquareBlock c k)) → IsUnit N by
    exact this _ m b M rfl hM hchain hblocks
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m _ _ b M hn hM hchain hblocks
    cases isEmpty_or_nonempty m with
    | inl hm =>
      let := hm
      exact isUnit_of_subsingleton M
    | inr hm =>
      let := hm
      obtain ⟨k, hk⟩ := (Set.finite_range b).exists_maximal (Set.range_nonempty b)
      let X := {i : m // b i ≠ k}
      let bX : X → α := fun i => b i.val
      let A : Matrix X X R := M.submatrix Subtype.val Subtype.val
      -- Strict comparison on distinct represented labels excludes the other maximal branch.
      have hlt : ∀ x : X, b x.val < k := by
        intro x
        rcases hchain (Set.mem_range_self x.val) hk.1 x.property with h | h
        · exact h
        · exact False.elim (not_lt_of_ge (hk.2 (Set.mem_range_self x.val) h.le) h)
      have hchainX : IsChain (fun x y : α => x < y) (Set.range bX) := by
        apply IsChain.mono _ hchain
        rintro _ ⟨x, rfl⟩
        exact ⟨x.val, rfl⟩
      have hblocksX : ∀ l : α, IsUnit (A.toSquareBlock bX l) := by
        intro l
        by_cases hl : l = k
        · subst l
          -- The removed label has an empty fiber in the complement.
          have : IsEmpty {x : X // bX x = k} :=
            ⟨fun x => x.val.property x.property⟩
          exact isUnit_of_subsingleton _
        · -- Collapse the nested fiber; inverse reindexing transports the original block unit.
          let q : {x : X // bX x = l} ≃ {i : m // b i = l} :=
            Equiv.subtypeSubtypeEquivSubtype (fun {i} hi => ne_of_eq_of_ne hi hl)
          exact (hblocks l).map (Matrix.reindexRingEquiv R q.symm).toMonoidHom
      obtain ⟨i, hi⟩ := hk.1
      have hcard : Fintype.card X < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := i) (fun h => h hi)
      have hA : IsUnit A :=
        ih (Fintype.card X) hcard X bX A rfl hM.submatrix hchainX hblocksX
      apply isUnit_of_isUnit_compl_submatrix (fun i => b i = k) M hA (hblocks k)
      intro y x
      apply hM
      rw [y.property]
      exact hlt x

end Preorder

section PartialOrder

variable [Fintype m] [DecidableEq m] [PartialOrder α] [DecidableEq α] [Ring R]
variable {b : m → α} {M : Matrix m m R}

/-- A finite block-triangular matrix over a ring is a unit if its represented
labels form a chain and each diagonal block is a unit. This is the partial-order
specialization of the strict-chain criterion. The blocks are indexed by the
equality fibers of `b`, including empty fibers. -/
theorem BlockTriangular.isUnit_of_isUnit_toSquareBlock
    (hM : M.BlockTriangular b)
    (hchain : IsChain (fun x y : α => x ≤ y) (Set.range b))
    (hblocks : ∀ k : α, IsUnit (M.toSquareBlock b k)) : IsUnit M := by
  exact hM.isUnit_of_isUnit_toSquareBlock_of_isChain_lt hchain.lt_of_le hblocks

end PartialOrder

private theorem inverse_compl_submatrix
    {m : Type uM} {R : Type uR}
    [Fintype m] [DecidableEq m] [Semiring R]
    (p : m → Prop) [DecidablePred p] (M N : Matrix m m R)
    (hMN : M * N = 1) (hNM : N * M = 1)
    (hzero : ∀ (i : {i : m // p i}) (j : {j : m // ¬ p j}), M i j = 0) :
    let A := M.submatrix (Subtype.val : {i : m // ¬ p i} → m)
      (Subtype.val : {i : m // ¬ p i} → m)
    let D := M.submatrix (Subtype.val : {i : m // p i} → m)
      (Subtype.val : {i : m // p i} → m)
    let P := N.submatrix (Subtype.val : {i : m // ¬ p i} → m)
      (Subtype.val : {i : m // ¬ p i} → m)
    let C := N.submatrix (Subtype.val : {i : m // p i} → m)
      (Subtype.val : {i : m // ¬ p i} → m)
    let S := N.submatrix (Subtype.val : {i : m // p i} → m)
      (Subtype.val : {i : m // p i} → m)
    D * S = 1 ∧ (IsUnit D → C = 0 ∧ A * P = 1 ∧ P * A = 1) := by
  let X := {i : m // ¬ p i}
  let Y := {i : m // p i}
  let e : X ⊕ Y ≃ m := (Equiv.sumComm X Y).trans (Equiv.sumCompl p)
  have he_inl (i : X) : e (Sum.inl i) = i.val := by
    simpa only [e, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inl] using
      (Equiv.sumCompl_apply_inr (p := p) i)
  have he_inr (i : Y) : e (Sum.inr i) = i.val := by
    simpa only [e, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr] using
      (Equiv.sumCompl_apply_inl (p := p) i)
  let A : Matrix X X R := M.submatrix Subtype.val Subtype.val
  let B : Matrix X Y R := M.submatrix Subtype.val Subtype.val
  let D : Matrix Y Y R := M.submatrix Subtype.val Subtype.val
  let P : Matrix X X R := N.submatrix Subtype.val Subtype.val
  let Q : Matrix X Y R := N.submatrix Subtype.val Subtype.val
  let C : Matrix Y X R := N.submatrix Subtype.val Subtype.val
  let S : Matrix Y Y R := N.submatrix Subtype.val Subtype.val
  let f := Matrix.reindexRingEquiv R e.symm
  have hsplit (L : Matrix m m R) : f L =
      Matrix.fromBlocks (L.submatrix (Subtype.val : X → m) (Subtype.val : X → m))
        (L.submatrix (Subtype.val : X → m) (Subtype.val : Y → m))
        (L.submatrix (Subtype.val : Y → m) (Subtype.val : X → m))
        (L.submatrix (Subtype.val : Y → m) (Subtype.val : Y → m)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [f, Matrix.coe_reindexRingEquiv, Matrix.reindex_apply,
        Equiv.symm_symm, Matrix.submatrix_apply, he_inl, he_inr,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  have hM : f M = Matrix.fromBlocks A B 0 D := by
    rw [hsplit]
    congr 1
    ext i j
    exact hzero i j
  have hN : f N = Matrix.fromBlocks P Q C S := hsplit N
  -- Read the two inverse identities blockwise, without assuming support of N.
  have hright : Matrix.fromBlocks (A * P + B * C) (A * Q + B * S)
      (D * C) (D * S) = Matrix.fromBlocks 1 0 0 1 := by
    have h := congrArg f hMN
    simpa only [map_mul, map_one, hM, hN, Matrix.fromBlocks_multiply,
      Matrix.zero_mul, zero_add, Matrix.fromBlocks_one] using h
  have hleft : Matrix.fromBlocks (P * A) (P * B + Q * D)
      (C * A) (C * B + S * D) = Matrix.fromBlocks 1 0 0 1 := by
    have h := congrArg f hNM
    simpa only [map_mul, map_one, hM, hN, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, add_zero, Matrix.fromBlocks_one] using h
  obtain ⟨hAP, _, hDC, hDS⟩ := Matrix.fromBlocks_inj.mp hright
  obtain ⟨hPA, _, _, _⟩ := Matrix.fromBlocks_inj.mp hleft
  refine ⟨hDS, ?_⟩
  intro hD
  -- A left inverse of D kills the forbidden lower-left block; DF is not needed here.
  obtain ⟨L, _, hLD⟩ := isUnit_iff_exists.mp hD
  have hC : C = 0 := by
    calc
      C = (1 : Matrix Y Y R) * C := (Matrix.one_mul C).symm
      _ = (L * D) * C := by rw [hLD]
      _ = L * (D * C) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hDC, Matrix.mul_zero]
  exact ⟨hC, by simpa only [hC, Matrix.mul_zero, add_zero] using hAP, hPA⟩

private theorem blockTriangular_of_two_sided_inverse
    {m : Type uM} {α : Type uA} {R : Type uR}
    [Fintype m] [DecidableEq m] [Preorder α] [DecidableEq α] [Semiring R]
    (b : m → α) (M N : Matrix m m R)
    (hM : M.BlockTriangular b)
    (hchain : IsChain (fun x y : α => x < y) (Set.range b))
    (hblocks : ∀ k : α, IsUnit (M.toSquareBlock b k))
    (hMN : M * N = 1) (hNM : N * M = 1) : N.BlockTriangular b := by
  classical
  suffices ∀ n : ℕ, ∀ (ι : Type uM) [Fintype ι] [DecidableEq ι]
      (c : ι → α) (L K : Matrix ι ι R), Fintype.card ι = n →
      L.BlockTriangular c → IsChain (fun x y : α => x < y) (Set.range c) →
      (∀ k : α, IsUnit (L.toSquareBlock c k)) →
      L * K = 1 → K * L = 1 → K.BlockTriangular c by
    exact this _ m b M N rfl hM hchain hblocks hMN hNM
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m _ _ b M N hn hM hchain hblocks hMN hNM
    cases isEmpty_or_nonempty m with
    | inl hm =>
      let := hm
      intro i
      exact isEmptyElim i
    | inr hm =>
      let := hm
      obtain ⟨k, hk⟩ := (Set.finite_range b).exists_maximal (Set.range_nonempty b)
      let X := {i : m // b i ≠ k}
      let bX : X → α := fun i => b i.val
      let A : Matrix X X R := M.submatrix Subtype.val Subtype.val
      let P : Matrix X X R := N.submatrix Subtype.val Subtype.val
      have hlt : ∀ x : X, b x.val < k := by
        intro x
        rcases hchain (Set.mem_range_self x.val) hk.1 x.property with h | h
        · exact h
        · exact False.elim (not_lt_of_ge (hk.2 (Set.mem_range_self x.val) h.le) h)
      have hchainX : IsChain (fun x y : α => x < y) (Set.range bX) := by
        apply IsChain.mono _ hchain
        rintro _ ⟨x, rfl⟩
        exact ⟨x.val, rfl⟩
      have hblocksX : ∀ l : α, IsUnit (A.toSquareBlock bX l) := by
        intro l
        by_cases hl : l = k
        · subst l
          have : IsEmpty {x : X // bX x = k} :=
            ⟨fun x => x.val.property x.property⟩
          exact isUnit_of_subsingleton _
        · let q : {x : X // bX x = l} ≃ {i : m // b i = l} :=
            Equiv.subtypeSubtypeEquivSubtype (fun {i} hi => ne_of_eq_of_ne hi hl)
          exact (hblocks l).map (Matrix.reindexRingEquiv R q.symm).toMonoidHom
      have hzero : ∀ (y : {i : m // b i = k}) (x : X), M y x = 0 := by
        intro y x
        apply hM
        rw [y.property]
        exact hlt x
      obtain ⟨_, hsplit⟩ := inverse_compl_submatrix (fun i => b i = k) M N hMN hNM hzero
      obtain ⟨hC, hAP, hPA⟩ := hsplit (hblocks k)
      obtain ⟨i, hi⟩ := hk.1
      have hcard : Fintype.card X < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := i) (fun h => h hi)
      have hP : P.BlockTriangular bX :=
        ih (Fintype.card X) hcard X bX A P rfl hM.submatrix hchainX hblocksX hAP hPA
      intro i j hij
      by_cases hi : b i = k
      · by_cases hj : b j = k
        · exact False.elim (lt_irrefl k (by simpa only [hi, hj] using hij))
        · exact congrArg (fun L => L ⟨i, hi⟩ ⟨j, hj⟩) hC
      · by_cases hj : b j = k
        · exact False.elim (lt_asymm (hlt ⟨i, hi⟩) (by simpa only [hj] using hij))
        · exact hP (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij

section SemiringPreorder

variable [Fintype m] [DecidableEq m] [Preorder α] [DecidableEq α] [Semiring R]
variable {b : m → α} {M : Matrix m m R}

/-- Every equality-fiber diagonal block of a unit block-triangular matrix is a unit,
provided the represented labels form a strict chain and the diagonal-block matrix
monoids are Dedekind-finite. Empty fibers are included. -/
theorem BlockTriangular.isUnit_toSquareBlock_of_isChain_lt
    (hM : M.BlockTriangular b)
    (hchain : IsChain (fun x y : α => x < y) (Set.range b))
    (hunit : IsUnit M)
    (hfinite : ∀ k : α,
      IsDedekindFiniteMonoid (Matrix {i : m // b i = k} {i : m // b i = k} R))
    (k : α) : IsUnit (M.toSquareBlock b k) := by
  classical
  suffices ∀ n : ℕ, ∀ (ι : Type uM) [Fintype ι] [DecidableEq ι]
      (c : ι → α) (N : Matrix ι ι R), Fintype.card ι = n →
      N.BlockTriangular c → IsChain (fun x y : α => x < y) (Set.range c) →
      IsUnit N →
      (∀ l : α, IsDedekindFiniteMonoid
        (Matrix {i : ι // c i = l} {i : ι // c i = l} R)) →
      ∀ l : α, IsUnit (N.toSquareBlock c l) by
    exact this _ m b M rfl hM hchain hunit hfinite k
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m _ _ b M hn hM hchain hunit hfinite l
    cases isEmpty_or_nonempty m with
    | inl hm =>
      let := hm
      exact isUnit_of_subsingleton _
    | inr hm =>
      let := hm
      obtain ⟨k, hk⟩ := (Set.finite_range b).exists_maximal (Set.range_nonempty b)
      let X := {i : m // b i ≠ k}
      let bX : X → α := fun i => b i.val
      let A : Matrix X X R := M.submatrix Subtype.val Subtype.val
      have hlt : ∀ x : X, b x.val < k := by
        intro x
        rcases hchain (Set.mem_range_self x.val) hk.1 x.property with h | h
        · exact h
        · exact False.elim (not_lt_of_ge (hk.2 (Set.mem_range_self x.val) h.le) h)
      have hchainX : IsChain (fun x y : α => x < y) (Set.range bX) := by
        apply IsChain.mono _ hchain
        rintro _ ⟨x, rfl⟩
        exact ⟨x.val, rfl⟩
      have hzero : ∀ (y : {i : m // b i = k}) (x : X), M y x = 0 := by
        intro y x
        apply hM
        rw [y.property]
        exact hlt x
      obtain ⟨N, hMN, hNM⟩ := isUnit_iff_exists.mp hunit
      obtain ⟨hDS, hsplit⟩ :=
        inverse_compl_submatrix (fun i => b i = k) M N hMN hNM hzero
      -- DF is used only on this original diagonal-block matrix monoid.
      have hD : IsUnit (M.toSquareBlock b k) := by
        let := hfinite k
        exact IsUnit.of_mul_eq_one _ hDS
      by_cases hl : l = k
      · subst l
        exact hD
      · obtain ⟨_, hAP, hPA⟩ := hsplit hD
        have hA : IsUnit A := isUnit_iff_exists.mpr ⟨_, hAP, hPA⟩
        have hfiniteX : ∀ t : α,
            IsDedekindFiniteMonoid (Matrix {i : X // bX i = t} {i : X // bX i = t} R) := by
          intro t
          by_cases ht : t = k
          · subst t
            -- The removed label has an empty remaining fiber, not its old diagonal block.
            let : IsEmpty {i : X // bX i = k} := ⟨fun i => i.val.property i.property⟩
            let : Finite (Matrix {i : X // bX i = k} {i : X // bX i = k} R) :=
              Finite.of_subsingleton
            infer_instance
          · let e : {i : X // bX i = t} ≃ {i : m // b i = t} :=
              Equiv.subtypeSubtypeEquivSubtype (fun {i} hi => ne_of_eq_of_ne hi ht)
            let q := Matrix.reindexRingEquiv R e
            let := hfinite t
            exact IsDedekindFiniteMonoid.of_injective q.toMonoidHom q.injective
        obtain ⟨i, hi⟩ := hk.1
        have hcard : Fintype.card X < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := i) (fun h => h hi)
        have hblock : IsUnit (A.toSquareBlock bX l) :=
          ih (Fintype.card X) hcard X bX A rfl hM.submatrix hchainX hA hfiniteX l
        let e : {i : X // bX i = l} ≃ {i : m // b i = l} :=
          Equiv.subtypeSubtypeEquivSubtype (fun {i} hi => ne_of_eq_of_ne hi hl)
        exact hblock.map (Matrix.reindexRingEquiv R e).toMonoidHom


/-- The given inverse of a block-triangular matrix is block triangular when the
represented labels form a strict chain and every diagonal block is a unit.
This assumes invertibility of the full matrix, not just of its diagonal blocks. -/
theorem BlockTriangular.invOf_of_isUnit_toSquareBlock_of_isChain_lt
    [Invertible M]
    (hM : M.BlockTriangular b)
    (hchain : IsChain (fun x y : α => x < y) (Set.range b))
    (hblocks : ∀ k : α, IsUnit (M.toSquareBlock b k)) :
    (⅟M).BlockTriangular b := by
  exact blockTriangular_of_two_sided_inverse b M (⅟M) hM hchain hblocks
    (mul_invOf_self M) (invOf_mul_self M)

end SemiringPreorder

section SemiringPartialOrder

variable [Fintype m] [DecidableEq m] [PartialOrder α] [DecidableEq α] [Semiring R]
variable {b : m → α} {M : Matrix m m R}

/-- The partial-order chain specialization of diagonal-block unit necessity. -/
theorem BlockTriangular.isUnit_toSquareBlock
    (hM : M.BlockTriangular b)
    (hchain : IsChain (fun x y : α => x ≤ y) (Set.range b))
    (hunit : IsUnit M)
    (hfinite : ∀ k : α,
      IsDedekindFiniteMonoid (Matrix {i : m // b i = k} {i : m // b i = k} R))
    (k : α) : IsUnit (M.toSquareBlock b k) := by
  exact hM.isUnit_toSquareBlock_of_isChain_lt hchain.lt_of_le hunit hfinite k

/-- The partial-order chain specialization of triangularity of the given inverse,
assuming unit diagonal blocks and invertibility of the full matrix. -/
theorem BlockTriangular.invOf_of_isUnit_toSquareBlock
    [Invertible M]
    (hM : M.BlockTriangular b)
    (hchain : IsChain (fun x y : α => x ≤ y) (Set.range b))
    (hblocks : ∀ k : α, IsUnit (M.toSquareBlock b k)) :
    (⅟M).BlockTriangular b := by
  exact hM.invOf_of_isUnit_toSquareBlock_of_isChain_lt hchain.lt_of_le hblocks

end SemiringPartialOrder

private theorem blockTriangular_nonsing_inv_specialization
    [Fintype m] [DecidableEq m] [LinearOrder α] [CommRing R]
    {b : m → α} {M : Matrix m m R} [Invertible M]
    (hM : M.BlockTriangular b) : (M⁻¹).BlockTriangular b := by
  have hchain : IsChain (fun x y : α => x ≤ y) (Set.range b) :=
    isChain_of_trichotomous _
  have hblocks : ∀ k : α, IsUnit (M.toSquareBlock b k) :=
    hM.isUnit_toSquareBlock hchain (isUnit_of_invertible M) (fun _ => inferInstance)
  simpa only [Matrix.invOf_eq_nonsing_inv] using
    hM.invOf_of_isUnit_toSquareBlock hchain hblocks

end Matrix
