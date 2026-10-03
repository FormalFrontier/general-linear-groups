/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.StableGeneralLinear
public import Mathlib.Data.ZMod.Basic

/-! Boundary, universality, and coefficient clients for stable general linear groups. -/

set_option warningAsError true

@[expose] public section

open Matrix.GeneralLinearGroup

private abbrev NoncommutativeCoefficients := Matrix (Fin 2) (Fin 2) ℤ

private def stageFamily (n : ℕ) : GL (Fin n) ℤ →* StableGL ℤ := StableGL.stage ℤ n

private theorem stageFamily_compatible (n m : ℕ) (h : n ≤ m) (g : GL (Fin n) ℤ) :
    stageFamily m (finStabilize ℤ h g) = stageFamily n g :=
  StableGL.stage_finStabilize ℤ h g

example (g : GL (Fin 2) ℤ) :
    StableGL.lift ℤ stageFamily stageFamily_compatible (StableGL.stage ℤ 2 g) =
      StableGL.stage ℤ 2 g := by
  simp [stageFamily]

example :
    StableGL.stage (ZMod 1) 0 (1 : GL (Fin 0) (ZMod 1)) =
      StableGL.stage (ZMod 1) 1 (1 : GL (Fin 1) (ZMod 1)) := by
  apply (StableGL.stage_eq_stage_iff (ZMod 1) (1 : GL (Fin 0) (ZMod 1))
    (1 : GL (Fin 1) (ZMod 1))).2
  exact ⟨1, Nat.zero_le 1, le_refl 1, by simp⟩

example (g h : GL (Fin 0) (ZMod 1))
    (heq : StableGL.stage (ZMod 1) 0 g = StableGL.stage (ZMod 1) 0 h) : g = h :=
  StableGL.stage_injective (ZMod 1) 0 heq

theorem nat_map_id (g : GL (Fin 1) ℕ) :
    StableGL.map (RingHom.id ℕ) (StableGL.stage ℕ 1 g) = StableGL.stage ℕ 1 g := by
  simp

example (g : GL (Fin 1) NoncommutativeCoefficients) :
    StableGL.map (RingHom.id NoncommutativeCoefficients)
      (StableGL.stage NoncommutativeCoefficients 1 g) =
      StableGL.stage NoncommutativeCoefficients 1 g := by
  simp

example (g : StableGL NoncommutativeCoefficients) :
    StableGL.map ((RingHom.id NoncommutativeCoefficients).comp
      (RingHom.id NoncommutativeCoefficients)) g =
    StableGL.map (RingHom.id NoncommutativeCoefficients)
      (StableGL.map (RingHom.id NoncommutativeCoefficients) g) := by
  rw [StableGL.map_comp]
  rfl
