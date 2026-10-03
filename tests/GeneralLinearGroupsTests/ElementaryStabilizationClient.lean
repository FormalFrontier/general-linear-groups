/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups
public import Mathlib.Data.ZMod.Basic

/-! Clients for stabilization, relative transport, quotient reduction, and degenerate blocks. -/

set_option warningAsError true

@[expose] public section

open Matrix.GeneralLinearGroup

private def reduceTwo : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)

private abbrev Coeff := Matrix (Fin 2) (Fin 2) ℤ
private abbrev ReducedCoeff := Matrix (Fin 2) (Fin 2) (ZMod 2)

private def evenMatrices : TwoSidedIdeal Coeff :=
  (⊥ : TwoSidedIdeal ReducedCoeff).comap reduceTwo.mapMatrix

private theorem evenMatrices_ne_top : evenMatrices ≠ ⊤ := by
  intro h
  have h1 : (1 : Coeff) ∈ evenMatrices := by rw [h]; simp
  change reduceTwo.mapMatrix (1 : Coeff) = 0 at h1
  have h00 := congrArg (fun m : ReducedCoeff ↦ m 0 0) h1
  norm_num at h00

private def coefficient : Coeff := Matrix.single 0 1 2
private def conjugatingCoefficient : Coeff := Matrix.single 1 0 1

private theorem coefficient_mem_evenMatrices : coefficient ∈ evenMatrices := by
  change reduceTwo.mapMatrix coefficient ∈ (⊥ : TwoSidedIdeal ReducedCoeff)
  have htwo : reduceTwo (2 : ℤ) = 0 := by decide
  simp [coefficient, htwo]

private theorem coefficients_do_not_commute :
    coefficient * conjugatingCoefficient ≠ conjugatingCoefficient * coefficient := by
  intro h
  have h00 := congrArg (fun m : Coeff ↦ m 0 0) h
  norm_num [coefficient, conjugatingCoefficient, Matrix.mul_apply, Matrix.single] at h00

private def relativeGenerator : elementarySubgroup (Fin 2) Coeff :=
  ⟨elementaryUnit (ι := Fin 2) 0 1 (by decide) coefficient,
    elementaryUnit_mem 0 1 (by decide) coefficient⟩

private def conjugator : elementarySubgroup (Fin 2) Coeff :=
  ⟨elementaryUnit (ι := Fin 2) 1 0 (by decide) conjugatingCoefficient,
    elementaryUnit_mem 1 0 (by decide) conjugatingCoefficient⟩

private theorem conjugated_mem :
    conjugator * relativeGenerator * conjugator⁻¹ ∈
      relativeElementarySubgroup (ι := Fin 2) evenMatrices := by
  exact (inferInstance : (relativeElementarySubgroup (ι := Fin 2) evenMatrices).Normal).conj_mem
    relativeGenerator (elementaryUnit_mem_relativeElementarySubgroup
      evenMatrices 0 1 (by decide) coefficient coefficient_mem_evenMatrices)
    conjugator

private theorem conjugated_ne_generator :
    conjugator * relativeGenerator * conjugator⁻¹ ≠ relativeGenerator := by
  intro h
  have hcomm : conjugator * relativeGenerator = relativeGenerator * conjugator := by
    have := congrArg (fun g : elementarySubgroup (Fin 2) Coeff => g * conjugator) h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using this
  have h00 := congrArg (fun g : elementarySubgroup (Fin 2) Coeff =>
    (g : GL (Fin 2) Coeff) 0 0) hcomm
  norm_num [conjugator, relativeGenerator, coefficient, conjugatingCoefficient,
    Matrix.mul_apply, Matrix.single, Matrix.add_apply, Matrix.one_apply] at h00
  have hentry := congrArg (fun m : Coeff => m 0 0) h00
  norm_num [Matrix.mul_apply, Matrix.single] at hentry

example : stabilizeElementarySubgroup (Y := Fin 1)
    (conjugator * relativeGenerator * conjugator⁻¹) ∈
      relativeElementarySubgroup (ι := Fin 2 ⊕ Fin 1) evenMatrices :=
  stabilize_relativeElementarySubgroup_le evenMatrices
    (Subgroup.mem_map_of_mem (stabilizeElementarySubgroup (Y := Fin 1)) conjugated_mem)

example : stabilize (Y := Fin 1)
    ((conjugator * relativeGenerator * conjugator⁻¹ : elementarySubgroup (Fin 2) Coeff) :
      GL (Fin 2) Coeff) ∈
      congruenceSubgroup (n := Fin 2 ⊕ Fin 1) evenMatrices := by
  apply stabilize_congruenceSubgroup_le evenMatrices
  apply Subgroup.mem_map_of_mem
  exact relativeElementarySubgroup_le_congruenceSubgroup evenMatrices conjugated_mem

example (g : GL (Fin 2) Coeff) :
    mapRingHom (Ideal.Quotient.mk evenMatrices.asIdeal) (stabilize (Y := Fin 1) g) =
      stabilize (Y := Fin 1) (mapRingHom (Ideal.Quotient.mk evenMatrices.asIdeal) g) :=
  mapRingHom_stabilize _ _

example (g : GL (Fin 2) Coeff) (i j : Fin 2) :
    stabilize (Y := Fin 1) g (Sum.inl i) (Sum.inl j) = g i j :=
  stabilize_apply_inl_inl _ _ _

universe uX uY uR

example {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] {R : Type uR} [Semiring R]
    (g h : GL X R)
    (eq : stabilize (Y := Y) g = stabilize (Y := Y) h) : g = h :=
  stabilize_injective eq

example (g : GL (Fin 2) ℤ) (i j : Fin 2) :
    stabilize (Y := PEmpty) g (Sum.inl i) (Sum.inl j) = g i j :=
  stabilize_apply_inl_inl _ _ _

example : (elementarySubgroup PEmpty ℤ).map (stabilize (Y := Fin 2)) ≤
    elementarySubgroup (PEmpty ⊕ Fin 2) ℤ :=
  stabilize_elementarySubgroup_le

example : (relativeElementarySubgroup (ι := PEmpty) (⊥ : TwoSidedIdeal ℤ)).map
    (stabilizeElementarySubgroup (Y := Fin 2)) ≤
      relativeElementarySubgroup (ι := PEmpty ⊕ Fin 2) ⊥ :=
  stabilize_relativeElementarySubgroup_le ⊥

example : (relativeElementarySubgroup (ι := Fin 1) (⊥ : TwoSidedIdeal (ZMod 1))).map
    (stabilizeElementarySubgroup (Y := PEmpty)) ≤
      relativeElementarySubgroup (ι := Fin 1 ⊕ PEmpty) ⊥ :=
  stabilize_relativeElementarySubgroup_le ⊥
