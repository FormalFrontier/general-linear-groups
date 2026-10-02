/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups.ElementaryPaths

/-! Public-import clients for elementary paths, including degenerate indices and real coefficients. -/

set_option warningAsError true

@[expose] public section

open Matrix.GeneralLinearGroup

universe u v

example {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R : Type v} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (i j : ι) (hij : i ≠ j) :
    Continuous (elementaryUnit (R := R) i j hij) :=
  continuous_elementaryUnit i j hij

example : PathConnectedSpace (elementarySubgroup PEmpty ℝ) :=
  elementarySubgroup_pathConnectedSpace

example : PathConnectedSpace (elementarySubgroup (Fin 1) ℝ) :=
  elementarySubgroup_pathConnectedSpace

example : PathConnectedSpace (elementarySubgroup (Fin 2)
    (Matrix (Fin 2) (Fin 2) ℝ)) := by
  let : PathConnectedSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (PathConnectedSpace (Fin 2 → Fin 2 → ℝ))
  exact elementarySubgroup_pathConnectedSpace

private def realCoefficientPath : Path (0 : ℝ) 1 where
  toFun t := t
  continuous_toFun := continuous_subtype_val
  source' := by simp
  target' := by simp

private def realElementaryPath : Path (1 : GL (Fin 2) ℝ)
    (elementaryUnit 0 1 (by decide) (1 : ℝ)) :=
  elementaryUnitPath 0 1 (by decide) realCoefficientPath

example : realElementaryPath 0 ≠ realElementaryPath 1 := by
  intro h
  have h01 := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) h
  norm_num [realElementaryPath, elementaryUnitPath, Matrix.single_apply] at h01

example : Path (1 : elementarySubgroup (Fin 2) ℝ)
    (⟨elementaryUnit 0 1 (by decide) (1 : ℝ),
      elementaryUnit_mem 0 1 (by decide) (1 : ℝ)⟩ : elementarySubgroup (Fin 2) ℝ) :=
  elementaryUnitPathSubtype 0 1 (by decide) realCoefficientPath

example (g : GL (Fin 2) ℝ) (hg : g ∈ elementarySubgroup (Fin 2) ℝ) :
    Joined (1 : GL (Fin 2) ℝ) g :=
  elementarySubgroup_joined_one g hg
