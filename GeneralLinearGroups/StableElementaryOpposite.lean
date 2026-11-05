/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.StableOpposite
public import GeneralLinearGroups.StableElementary

/-!
# Stable elementary quotients over opposite rings

Inverse-transpose sends each elementary generator to the elementary generator
with reversed indices and negated opposite coefficient. It identifies the original
stable elementary subgroups, and induces an isomorphism of their quotients.

The quotient isomorphism is the composite of the existing Whitehead comparisons
with Mathlib's abelianization congruence. Its characteristics on all representatives
identify it with stable inverse-transpose. Both directions are natural in arbitrary
unital ring homomorphisms, and double application is the canonical double-opposite
coefficient map. No nontriviality, commutativity, or positive-rank premise is needed.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uR uS

/-- Finite inverse-transpose reverses the indices of an elementary unit and
negates its opposite coefficient. -/
theorem opEquiv_elementaryUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Type uR) [Ring R] (i j : ι) (hij : i ≠ j) (a : R) :
    opEquiv R (elementaryUnit i j hij a) =
      elementaryUnit j i hij.symm (-(MulOpposite.op a)) := by
  apply Units.ext
  ext k l
  rw [opEquiv_apply, elementaryUnit_inv]
  change MulOpposite.op ((1 + Matrix.single i j (-a)) l k) =
    (1 + Matrix.single j i (-(MulOpposite.op a))) k l
  by_cases hkl : k = l <;> by_cases hkj : k = j <;> by_cases hli : l = i <;>
    simp_all [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]

/-- Stable inverse-transpose sends every original stage elementary generator to
the generator with reversed indices and negated opposite coefficient. -/
theorem StableGL.opEquiv_stage_elementaryUnit
    (R : Type uR) [Ring R] (n : ℕ)
    (i j : Fin n) (hij : i ≠ j) (a : R) :
    StableGL.opEquiv R (StableGL.stage R n (elementaryUnit i j hij a)) =
      StableGL.stage (Rᵐᵒᵖ) n
        (elementaryUnit j i hij.symm (-(MulOpposite.op a))) := by
  rw [StableGL.opEquiv_stage, opEquiv_elementaryUnit]

/-- Stable inverse-transpose identifies the original stable elementary subgroups. -/
theorem stableElementarySubgroup_map_opEquiv (R : Type uR) [Ring R] :
    (stableElementarySubgroup R).map (StableGL.opEquiv R).toMonoidHom =
      stableElementarySubgroup (Rᵐᵒᵖ) := by
  rw [stableElementarySubgroup_eq_commutator, stableElementarySubgroup_eq_commutator,
    map_commutator_eq]
  have hrange : (StableGL.opEquiv R).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (StableGL.opEquiv R).surjective
  rw [hrange, commutator_def]

/-- Inverse-transpose on the original stable elementary quotients, transported
through their existing canonical Whitehead comparisons to abelianizations. -/
noncomputable def stableElementaryQuotientOpEquiv (R : Type uR) [Ring R] :
    (StableGL R ⧸ stableElementarySubgroup R) ≃*
      (StableGL (Rᵐᵒᵖ) ⧸ stableElementarySubgroup (Rᵐᵒᵖ)) :=
  ((stableElementaryAbelianizationEquiv R).trans
    (MulEquiv.abelianizationCongr (StableGL.opEquiv R))).trans
      (stableElementaryAbelianizationEquiv (Rᵐᵒᵖ)).symm

/-- Quotient inverse-transpose takes the class of any stable matrix to the class
of its stable inverse-transpose. -/
@[simp]
theorem stableElementaryQuotientOpEquiv_mk
    (R : Type uR) [Ring R] (g : StableGL R) :
    stableElementaryQuotientOpEquiv R
      (g : StableGL R ⧸ stableElementarySubgroup R) =
        (StableGL.opEquiv R g :
          StableGL (Rᵐᵒᵖ) ⧸ stableElementarySubgroup (Rᵐᵒᵖ)) := by
  have h :
      stableElementaryQuotientOpEquiv R
          (QuotientGroup.mk' (stableElementarySubgroup R) g) =
        QuotientGroup.mk' (stableElementarySubgroup (Rᵐᵒᵖ))
          (StableGL.opEquiv R g) := by
    simp only [stableElementaryQuotientOpEquiv, MulEquiv.trans_apply,
      stableElementaryAbelianizationEquiv_mk, abelianizationCongr_of,
      stableElementaryAbelianizationEquiv_symm_of]
  simpa only [QuotientGroup.mk'_apply] using h

/-- The inverse quotient isomorphism is characterized on every original stable
representative by the genuine inverse stable isomorphism. -/
@[simp]
theorem stableElementaryQuotientOpEquiv_symm_mk
    (R : Type uR) [Ring R] (g : StableGL (Rᵐᵒᵖ)) :
    (stableElementaryQuotientOpEquiv R).symm
      (g : StableGL (Rᵐᵒᵖ) ⧸ stableElementarySubgroup (Rᵐᵒᵖ)) =
        ((StableGL.opEquiv R).symm g :
          StableGL R ⧸ stableElementarySubgroup R) := by
  apply (stableElementaryQuotientOpEquiv R).injective
  rw [MulEquiv.apply_symm_apply, stableElementaryQuotientOpEquiv_mk,
    MulEquiv.apply_symm_apply]

/-- The quotient isomorphism agrees with abelianization of the fixed stable
isomorphism under the original Whitehead comparisons. -/
theorem stableElementaryAbelianizationEquiv_opEquiv
    (R : Type uR) [Ring R]
    (q : StableGL R ⧸ stableElementarySubgroup R) :
    stableElementaryAbelianizationEquiv (Rᵐᵒᵖ)
      (stableElementaryQuotientOpEquiv R q) =
        MulEquiv.abelianizationCongr (StableGL.opEquiv R)
          (stableElementaryAbelianizationEquiv R q) := by
  simp only [stableElementaryQuotientOpEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]

/-- Quotient inverse-transpose is natural in every unital ring homomorphism. -/
theorem stableElementaryQuotientOpEquiv_map
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (stableElementaryQuotientOpEquiv S).toMonoidHom.comp
      (QuotientGroup.map (stableElementarySubgroup R) (stableElementarySubgroup S)
        (StableGL.map f)
        ((Subgroup.map_le_iff_le_comap).mp
          (StableGL.map_elementarySubgroup_le f))) =
      (QuotientGroup.map (stableElementarySubgroup (Rᵐᵒᵖ))
        (stableElementarySubgroup (Sᵐᵒᵖ)) (StableGL.map f.op)
        ((Subgroup.map_le_iff_le_comap).mp
          (StableGL.map_elementarySubgroup_le f.op))).comp
        (stableElementaryQuotientOpEquiv R).toMonoidHom := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.map_mk, stableElementaryQuotientOpEquiv_mk]
  exact congrArg
    ((↑) : StableGL (Sᵐᵒᵖ) →
      StableGL (Sᵐᵒᵖ) ⧸ stableElementarySubgroup (Sᵐᵒᵖ))
    (DFunLike.congr_fun (StableGL.map_opEquiv f) g).symm

/-- Inverse quotient transport is natural in every unital ring homomorphism. -/
theorem stableElementaryQuotientOpEquiv_symm_map
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (stableElementaryQuotientOpEquiv S).symm.toMonoidHom.comp
      (QuotientGroup.map (stableElementarySubgroup (Rᵐᵒᵖ))
        (stableElementarySubgroup (Sᵐᵒᵖ)) (StableGL.map f.op)
        ((Subgroup.map_le_iff_le_comap).mp
          (StableGL.map_elementarySubgroup_le f.op))) =
      (QuotientGroup.map (stableElementarySubgroup R) (stableElementarySubgroup S)
        (StableGL.map f)
        ((Subgroup.map_le_iff_le_comap).mp
          (StableGL.map_elementarySubgroup_le f))).comp
        (stableElementaryQuotientOpEquiv R).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.map_mk, stableElementaryQuotientOpEquiv_symm_mk]
  exact congrArg
    ((↑) : StableGL S → StableGL S ⧸ stableElementarySubgroup S)
    (DFunLike.congr_fun (StableGL.map_opEquiv_symm f) g).symm

/-- Applying quotient inverse-transpose twice gives the original coefficient
quotient map for the canonical double-opposite ring isomorphism. -/
theorem stableElementaryQuotientOpEquiv_opEquiv
    (R : Type uR) [Ring R] :
    (stableElementaryQuotientOpEquiv (Rᵐᵒᵖ)).toMonoidHom.comp
      (stableElementaryQuotientOpEquiv R).toMonoidHom =
        QuotientGroup.map (stableElementarySubgroup R)
          (stableElementarySubgroup (Rᵐᵒᵖᵐᵒᵖ))
          (StableGL.map ((RingEquiv.opOp R).toRingHom))
          ((Subgroup.map_le_iff_le_comap).mp
            (StableGL.map_elementarySubgroup_le ((RingEquiv.opOp R).toRingHom))) := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.map_mk, stableElementaryQuotientOpEquiv_mk]
  exact congrArg
    ((↑) : StableGL (Rᵐᵒᵖᵐᵒᵖ) →
      StableGL (Rᵐᵒᵖᵐᵒᵖ) ⧸ stableElementarySubgroup (Rᵐᵒᵖᵐᵒᵖ))
    (DFunLike.congr_fun (StableGL.opEquiv_opEquiv R) g)

/-- The genuine inverse quotient isomorphism is quotient inverse-transpose over
the opposite ring followed by the inverse canonical double-opposite coefficient map. -/
theorem stableElementaryQuotientOpEquiv_symm_eq_map_opEquiv
    (R : Type uR) [Ring R] :
    (stableElementaryQuotientOpEquiv R).symm.toMonoidHom =
      (QuotientGroup.map (stableElementarySubgroup (Rᵐᵒᵖᵐᵒᵖ))
        (stableElementarySubgroup R)
        (StableGL.map ((RingEquiv.opOp R).symm.toRingHom))
        ((Subgroup.map_le_iff_le_comap).mp
          (StableGL.map_elementarySubgroup_le
            ((RingEquiv.opOp R).symm.toRingHom)))).comp
          (stableElementaryQuotientOpEquiv (Rᵐᵒᵖ)).toMonoidHom := by
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    stableElementaryQuotientOpEquiv_symm_mk, stableElementaryQuotientOpEquiv_mk,
    QuotientGroup.map_mk]
  exact congrArg
    ((↑) : StableGL R → StableGL R ⧸ stableElementarySubgroup R)
    (DFunLike.congr_fun (StableGL.opEquiv_symm_eq_map_opEquiv R) g)

end Matrix.GeneralLinearGroup
