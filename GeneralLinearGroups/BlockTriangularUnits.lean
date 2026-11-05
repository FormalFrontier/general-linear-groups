/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.RectangularBlockUnits
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Preorder.Finite

/-!
# Units of finite block-triangular matrices

The diagonal blocks are the restrictions to the equality fibers of a label map.
The labels may be preordered, with the represented labels forming a strict chain.
For partially ordered labels, a chain for the non-strict order suffices. The
coefficient ring need not be commutative, and the finite matrix index and the
label type may be empty.

## References

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

end Matrix
