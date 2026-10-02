/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import GeneralLinearGroups.ElementaryNeighborhood
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Instances.Int

/-! Ordinary-import clients for finite native `SL`, including empty matrices and the zero ring. -/

set_option warningAsError true

@[expose] public section

universe u

example {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {n : ℕ} (hunits : IsOpen {r : R | IsUnit r}) :
    IsOpen (Matrix.SpecialLinearGroup.elementarySubgroup (n := n) (R := R) :
      Set (Matrix.SpecialLinearGroup (Fin n) R)) :=
  Matrix.SpecialLinearGroup.isOpen_elementarySubgroup hunits

example {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {n : ℕ} (hunits : IsOpen {r : R | IsUnit r}) :
    IsClosed (Matrix.SpecialLinearGroup.elementarySubgroup (n := n) (R := R) :
      Set (Matrix.SpecialLinearGroup (Fin n) R)) :=
  Matrix.SpecialLinearGroup.isClosed_elementarySubgroup hunits

example {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [PathConnectedSpace R] {n : ℕ}
    (hunits : IsOpen {r : R | IsUnit r}) :
    Matrix.SpecialLinearGroup.elementarySubgroup (n := n) (R := R) =
      Subgroup.pathComponentOne (Matrix.SpecialLinearGroup (Fin n) R) :=
  Matrix.SpecialLinearGroup.elementarySubgroup_eq_pathComponentOne hunits

example :
    IsOpen (Matrix.SpecialLinearGroup.elementarySubgroup (n := 1) (R := ℤ) :
      Set (Matrix.SpecialLinearGroup (Fin 1) ℤ)) :=
  Matrix.SpecialLinearGroup.isOpen_elementarySubgroup (isOpen_discrete _)

example :
    IsOpen (Matrix.SpecialLinearGroup.elementarySubgroup (n := 0) (R := ZMod 1) :
      Set (Matrix.SpecialLinearGroup (Fin 0) (ZMod 1))) :=
  Matrix.SpecialLinearGroup.isOpen_elementarySubgroup (isOpen_discrete _)

example :
    IsClosed (Matrix.SpecialLinearGroup.elementarySubgroup (n := 1) (R := ZMod 1) :
      Set (Matrix.SpecialLinearGroup (Fin 1) (ZMod 1))) :=
  Matrix.SpecialLinearGroup.isClosed_elementarySubgroup (isOpen_discrete _)
