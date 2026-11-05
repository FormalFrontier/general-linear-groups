/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.Opposite

/-!
# Stable general linear groups over the opposite semiring

Finite inverse-transpose isomorphisms commute with initial-segment stabilization,
so they induce an isomorphism between the stable general linear groups over a
semiring and its opposite. The inverse uses the genuine inverse of the finite
isomorphism. Both directions are characterized on the original finite stages.

The construction is natural in arbitrary unital coefficient homomorphisms.
Applying it twice agrees with the canonical coefficient isomorphism to the double
opposite, which also compares inverse transport with inverse-transpose over the
opposite semiring. All constructions include rank zero and the zero semiring.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup.StableGL

universe uR uS

/-- The finite inverse-transpose isomorphism followed by the opposite-coefficient
stage of the stable general linear group. -/
noncomputable def opStageFamily (R : Type uR) [Semiring R] (n : ℕ) :
    GL (Fin n) R →* StableGL (Rᵐᵒᵖ) :=
  (stage (Rᵐᵒᵖ) n).comp
    (Matrix.GeneralLinearGroup.opEquiv (ι := Fin n) R).toMonoidHom

/-- The genuine inverse of finite inverse-transpose followed by the stage over
the original coefficient semiring. -/
noncomputable def unopStageFamily (R : Type uR) [Semiring R] (n : ℕ) :
    GL (Fin n) (Rᵐᵒᵖ) →* StableGL R :=
  (stage R n).comp
    (Matrix.GeneralLinearGroup.opEquiv (ι := Fin n) R).symm.toMonoidHom

/-- The forward stage family applies finite inverse-transpose before taking the
opposite-coefficient stage. -/
theorem opStageFamily_apply (R : Type uR) [Semiring R]
    (n : ℕ) (g : GL (Fin n) R) :
    opStageFamily R n g =
      stage (Rᵐᵒᵖ) n (Matrix.GeneralLinearGroup.opEquiv R g) := rfl

/-- The reverse stage family applies the genuine finite inverse before taking
the original-coefficient stage. -/
theorem unopStageFamily_apply (R : Type uR) [Semiring R]
    (n : ℕ) (g : GL (Fin n) (Rᵐᵒᵖ)) :
    unopStageFamily R n g =
      stage R n ((Matrix.GeneralLinearGroup.opEquiv R).symm g) := rfl

/-- The forward stage family is compatible with every initial-segment
stabilization. -/
theorem opStageFamily_compatible (R : Type uR) [Semiring R]
    (n m : ℕ) (h : n ≤ m) (g : GL (Fin n) R) :
    opStageFamily R m (finStabilize R h g) = opStageFamily R n g := by
  simp only [opStageFamily_apply, Matrix.GeneralLinearGroup.opEquiv_finStabilize,
    stage_finStabilize]

/-- The reverse stage family is compatible with every initial-segment
stabilization. -/
theorem unopStageFamily_compatible (R : Type uR) [Semiring R]
    (n m : ℕ) (h : n ≤ m) (g : GL (Fin n) (Rᵐᵒᵖ)) :
    unopStageFamily R m (finStabilize (Rᵐᵒᵖ) h g) =
      unopStageFamily R n g := by
  simp only [unopStageFamily_apply, Matrix.GeneralLinearGroup.opEquiv_symm_finStabilize,
    stage_finStabilize]

/-- The homomorphism on stable general linear groups induced by finite
inverse-transpose over the opposite semiring. -/
noncomputable def opHom (R : Type uR) [Semiring R] :
    StableGL R →* StableGL (Rᵐᵒᵖ) :=
  lift R (G := StableGL (Rᵐᵒᵖ))
    (opStageFamily R) (opStageFamily_compatible R)

/-- The homomorphism on stable general linear groups induced by the genuine
inverse of finite inverse-transpose. -/
noncomputable def unopHom (R : Type uR) [Semiring R] :
    StableGL (Rᵐᵒᵖ) →* StableGL R :=
  lift (Rᵐᵒᵖ) (G := StableGL R)
    (unopStageFamily R) (unopStageFamily_compatible R)

/-- The forward stable homomorphism agrees with finite inverse-transpose on
each stage. -/
@[simp]
theorem opHom_stage (R : Type uR) [Semiring R]
    (n : ℕ) (g : GL (Fin n) R) :
    opHom R (stage R n g) =
      stage (Rᵐᵒᵖ) n (Matrix.GeneralLinearGroup.opEquiv R g) := by
  exact (lift_stage R (opStageFamily R) (opStageFamily_compatible R) n g).trans
    (opStageFamily_apply R n g)

/-- The reverse stable homomorphism agrees with the genuine finite inverse on
each stage. -/
@[simp]
theorem unopHom_stage (R : Type uR) [Semiring R]
    (n : ℕ) (g : GL (Fin n) (Rᵐᵒᵖ)) :
    unopHom R (stage (Rᵐᵒᵖ) n g) =
      stage R n ((Matrix.GeneralLinearGroup.opEquiv R).symm g) := by
  exact (lift_stage (Rᵐᵒᵖ) (unopStageFamily R) (unopStageFamily_compatible R) n g).trans
    (unopStageFamily_apply R n g)

/-- Reverse transport is a left inverse of stable inverse-transpose. -/
theorem unopHom_opHom (R : Type uR) [Semiring R] (g : StableGL R) :
    unopHom R (opHom R g) = g := by
  obtain ⟨n, x, rfl⟩ := exists_stage R g
  simp only [opHom_stage, unopHom_stage, MulEquiv.symm_apply_apply]

/-- Reverse transport is a right inverse of stable inverse-transpose. -/
theorem opHom_unopHom (R : Type uR) [Semiring R]
    (g : StableGL (Rᵐᵒᵖ)) :
    opHom R (unopHom R g) = g := by
  obtain ⟨n, x, rfl⟩ := exists_stage (Rᵐᵒᵖ) g
  simp only [unopHom_stage, opHom_stage, MulEquiv.apply_symm_apply]

/-- The inverse-transpose isomorphism between stable general linear groups over
a semiring and its opposite, characterized by its action on every finite stage. -/
noncomputable def opEquiv (R : Type uR) [Semiring R] :
    StableGL R ≃* StableGL (Rᵐᵒᵖ) where
  toFun := opHom R
  invFun := unopHom R
  left_inv := unopHom_opHom R
  right_inv := opHom_unopHom R
  map_mul' := (opHom R).map_mul

/-- Stable inverse-transpose agrees with finite inverse-transpose on every
stage. -/
@[simp]
theorem opEquiv_stage (R : Type uR) [Semiring R]
    (n : ℕ) (g : GL (Fin n) R) :
    opEquiv R (stage R n g) =
      stage (Rᵐᵒᵖ) n (Matrix.GeneralLinearGroup.opEquiv R g) := by
  exact opHom_stage R n g

/-- The inverse stable isomorphism agrees with the genuine finite inverse on
every stage. -/
@[simp]
theorem opEquiv_symm_stage (R : Type uR) [Semiring R]
    (n : ℕ) (g : GL (Fin n) (Rᵐᵒᵖ)) :
    (opEquiv R).symm (stage (Rᵐᵒᵖ) n g) =
      stage R n ((Matrix.GeneralLinearGroup.opEquiv R).symm g) := by
  exact unopHom_stage R n g

/-- Stable inverse-transpose is natural in arbitrary unital coefficient
homomorphisms, as an equality of whole group homomorphisms. -/
theorem map_opEquiv {R : Type uR} {S : Type uS}
    [Semiring R] [Semiring S] (f : R →+* S) :
    (map f.op).comp (opEquiv R).toMonoidHom =
      (opEquiv S).toMonoidHom.comp (map f) := by
  apply hom_ext R
  intro n
  apply MonoidHom.ext
  intro g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, opEquiv_stage, map_stage,
    Matrix.GeneralLinearGroup.mapRingHom_opEquiv]

/-- Inverse stable transport is natural in arbitrary unital coefficient
homomorphisms, as an equality of whole group homomorphisms. -/
theorem map_opEquiv_symm {R : Type uR} {S : Type uS}
    [Semiring R] [Semiring S] (f : R →+* S) :
    (map f).comp (opEquiv R).symm.toMonoidHom =
      (opEquiv S).symm.toMonoidHom.comp (map f.op) := by
  apply hom_ext (Rᵐᵒᵖ)
  intro n
  apply MonoidHom.ext
  intro g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, opEquiv_symm_stage, map_stage,
    Matrix.GeneralLinearGroup.mapRingHom_opEquiv_symm]

/-- Applying stable inverse-transpose twice is the stable coefficient map for
the canonical double-opposite ring isomorphism. -/
theorem opEquiv_opEquiv (R : Type uR) [Semiring R] :
    (opEquiv (Rᵐᵒᵖ)).toMonoidHom.comp (opEquiv R).toMonoidHom =
      map (RingEquiv.opOp R).toRingHom := by
  apply hom_ext R
  intro n
  apply MonoidHom.ext
  intro g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, opEquiv_stage, map_stage,
    Matrix.GeneralLinearGroup.opEquiv_opEquiv]

/-- The genuine inverse stable isomorphism is inverse-transpose over the
opposite semiring followed by the inverse canonical double-opposite coefficient
map. -/
theorem opEquiv_symm_eq_map_opEquiv (R : Type uR) [Semiring R] :
    (opEquiv R).symm.toMonoidHom =
      (map (RingEquiv.opOp R).symm.toRingHom).comp
        (opEquiv (Rᵐᵒᵖ)).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  have h := congrArg
    (fun phi : StableGL R →* StableGL (Rᵐᵒᵖᵐᵒᵖ) => phi ((opEquiv R).symm g))
    (opEquiv_opEquiv R)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] at h
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [h, ← MonoidHom.comp_apply, ← map_comp,
    RingEquiv.symm_toRingHom_comp_toRingHom, map_id, MonoidHom.id_apply]

end Matrix.GeneralLinearGroup.StableGL
