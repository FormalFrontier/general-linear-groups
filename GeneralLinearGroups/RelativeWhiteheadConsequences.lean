/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.RelativeWhitehead
public import GeneralLinearGroups.ElementaryStabilization

/-!
# Finite relative Whitehead consequences

Block diagonal identities give relative elementary membership after doubling
the index type. Conjugation by an arbitrary general linear unit is used only
after stabilization, where its Whitehead diagonal is elementary.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uR

variable {X : Type uX} [Fintype X] [DecidableEq X]
  {R : Type uR} [Ring R]

/-- Stabilized conjugation by `g` is conjugation by its elementary Whitehead
diagonal, with no congruence assumption on `g`. -/
theorem stabilize_conj_eq_blockDiagonalUnit_conj (g h : GL X R) :
    stabilize (Y := X) (g * h * g⁻¹) =
      blockDiagonalUnit g * stabilize (Y := X) h * (blockDiagonalUnit g)⁻¹ := by
  apply Units.ext
  simp [stabilize, blockDiagonalUnit, Matrix.fromBlocks_multiply, mul_assoc]

/-- The ordered commutator has a three-diagonal factorization after doubling.
The final diagonal is indexed by `(h * g)⁻¹`, not `(g * h)⁻¹`. -/
theorem stabilize_commutator_eq_blockDiagonalUnit_mul (g h : GL X R) :
    stabilize (Y := X) (g * h * g⁻¹ * h⁻¹) =
      blockDiagonalUnit g * blockDiagonalUnit h * blockDiagonalUnit ((h * g)⁻¹) := by
  apply Units.ext
  simp [stabilize, blockDiagonalUnit, Matrix.fromBlocks_multiply, mul_assoc]

/-- An arbitrary general linear conjugator preserves relative elementary
membership after doubling, in the ambient general linear group. -/
theorem stabilize_conj_mem_relativeElementarySubgroup (I : TwoSidedIdeal R)
    (g : GL X R) (h : elementarySubgroup X R)
    (hh : h ∈ relativeElementarySubgroup I) :
    stabilize (Y := X) (g * (h : GL X R) * g⁻¹) ∈
      (relativeElementarySubgroup (ι := X ⊕ X) I).map
        (elementarySubgroup (X ⊕ X) R).subtype := by
  let diagonal : elementarySubgroup (X ⊕ X) R :=
    ⟨blockDiagonalUnit g, blockDiagonalUnit_mem_elementarySubgroup g⟩
  let stabilized : elementarySubgroup (X ⊕ X) R :=
    stabilizeElementarySubgroup (Y := X) h
  have hs : stabilized ∈ relativeElementarySubgroup I :=
    stabilize_relativeElementarySubgroup_le I
      (Subgroup.mem_map_of_mem (stabilizeElementarySubgroup (Y := X)) hh)
  have hc : diagonal * stabilized * diagonal⁻¹ ∈ relativeElementarySubgroup I :=
    (inferInstance : (relativeElementarySubgroup (ι := X ⊕ X) I).Normal).conj_mem
      stabilized hs diagonal
  apply Subgroup.mem_map.mpr
  refine ⟨diagonal * stabilized * diagonal⁻¹, hc, ?_⟩
  change blockDiagonalUnit g * stabilize (Y := X) (h : GL X R) *
    (blockDiagonalUnit g)⁻¹ = stabilize (Y := X) (g * (h : GL X R) * g⁻¹)
  exact (stabilize_conj_eq_blockDiagonalUnit_conj g h).symm

/-- The ordered commutator of two congruence units is relative elementary
after doubling, with no original-rank commutator containment asserted. -/
theorem stabilize_commutator_mem_relativeElementarySubgroup (I : TwoSidedIdeal R)
    (g h : congruenceSubgroup (n := X) I) :
    stabilize (Y := X) (g.1 * h.1 * g.1⁻¹ * h.1⁻¹) ∈
      (relativeElementarySubgroup (ι := X ⊕ X) I).map
        (elementarySubgroup (X ⊕ X) R).subtype := by
  let diagonalG : elementarySubgroup (X ⊕ X) R :=
    ⟨blockDiagonalUnit g.1, blockDiagonalUnit_mem_elementarySubgroup g.1⟩
  let diagonalH : elementarySubgroup (X ⊕ X) R :=
    ⟨blockDiagonalUnit h.1, blockDiagonalUnit_mem_elementarySubgroup h.1⟩
  let diagonalHG : elementarySubgroup (X ⊕ X) R :=
    ⟨blockDiagonalUnit ((h * g)⁻¹).1,
      blockDiagonalUnit_mem_elementarySubgroup ((h * g)⁻¹).1⟩
  have hG : diagonalG ∈ relativeElementarySubgroup I :=
    blockDiagonalUnit_mem_relativeElementarySubgroup I g
  have hH : diagonalH ∈ relativeElementarySubgroup I :=
    blockDiagonalUnit_mem_relativeElementarySubgroup I h
  have hHG : diagonalHG ∈ relativeElementarySubgroup I :=
    blockDiagonalUnit_mem_relativeElementarySubgroup I ((h * g)⁻¹)
  apply Subgroup.mem_map.mpr
  refine ⟨diagonalG * diagonalH * diagonalHG,
    (relativeElementarySubgroup I).mul_mem
      ((relativeElementarySubgroup I).mul_mem hG hH) hHG, ?_⟩
  change blockDiagonalUnit g.1 * blockDiagonalUnit h.1 *
    blockDiagonalUnit ((h.1 * g.1)⁻¹) =
      stabilize (Y := X) (g.1 * h.1 * g.1⁻¹ * h.1⁻¹)
  exact (stabilize_commutator_eq_blockDiagonalUnit_mul g.1 h.1).symm

end Matrix.GeneralLinearGroup
