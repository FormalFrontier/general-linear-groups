/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.Steinberg

/-! Ordinary-import clients of the finite-rank Steinberg presentation. -/

set_option warningAsError true

@[expose] public section

universe uI uR uG

open scoped commutatorElement

namespace SteinbergTest

variable {I : Type uI} {R : Type uR} [Ring R]

private theorem client_add (p : Steinberg.Root I) (a b : R) :
    Steinberg.generator p a * Steinberg.generator p b = Steinberg.generator p (a + b) :=
  Steinberg.generator_add p a b

example (p : Steinberg.Root I) : Steinberg.generator p (0 : R) = 1 := by simp

example (p : Steinberg.Root I) (a : R) :
    Steinberg.generator p (-a) = (Steinberg.generator p a)⁻¹ := by simp

variable {G : Type uG} [Group G]

example (f : Steinberg.Root I → R → G)
    (hadd : ∀ p a b, f p a * f p b = f p (a + b))
    (hdisjoint : ∀ i j k l (hij : i ≠ j) (hkl : k ≠ l)
      (_hjk : j ≠ k) (_hli : l ≠ i) (a b : R),
      ⁅f (Steinberg.root i j hij) a, f (Steinberg.root k l hkl) b⁆ = 1)
    (hcomposable : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k)
      (hik : i ≠ k) (a b : R),
      ⁅f (Steinberg.root i j hij) a, f (Steinberg.root j k hjk) b⁆ =
        f (Steinberg.root i k hik) (a * b))
    (p : Steinberg.Root I) (a : R) :
    Steinberg.lift f hadd hdisjoint hcomposable (Steinberg.generator p a) = f p a := by
  simp

example (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    ⁅Steinberg.generator (Steinberg.root i j hij) a,
      Steinberg.generator (Steinberg.root k l hkl) b⁆ = 1 :=
  Steinberg.generator_commutator_disjoint i j k l hij hkl hjk hli a b

variable [Fintype I] [DecidableEq I]

example : Function.Surjective (Steinberg.toElementary (ι := I) (R := R)) :=
  Steinberg.toElementary_surjective

example : (Steinberg.toGL (ι := I) (R := R)).range =
    Matrix.GeneralLinearGroup.elementarySubgroup I R := Steinberg.toGL_range

example (p : Steinberg.Root I) (a : R) :
    Steinberg.toGL (Steinberg.generator p a) =
      Matrix.GeneralLinearGroup.elementaryUnit p.1.1 p.1.2 p.2 a := by simp

example (a b : R) :
    ⁅Steinberg.generator (Steinberg.root (0 : Fin 3) 1 (by decide)) a,
      Steinberg.generator (Steinberg.root (1 : Fin 3) 2 (by decide)) b⁆ =
    Steinberg.generator (Steinberg.root (0 : Fin 3) 2 (by decide)) (a * b) :=
  Steinberg.generator_commutator (0 : Fin 3) 1 2 (by decide) (by decide) (by decide) a b

example (a b : R) :
    ⁅Steinberg.generator (Steinberg.root (1 : Fin 3) 2 (by decide)) a,
      Steinberg.generator (Steinberg.root (0 : Fin 3) 1 (by decide)) b⁆ =
    Steinberg.generator (Steinberg.root (0 : Fin 3) 2 (by decide)) (-(b * a)) :=
  Steinberg.generator_commutator_reverse (1 : Fin 3) 2 0
    (by decide) (by decide) (by decide) a b

private def coeffA : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 0 1 1

private def coeffB : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 1 0 1

private theorem coeff_noncommute : coeffA * coeffB ≠ coeffB * coeffA := by
  intro h
  have h00 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 0 0) h
  norm_num [coeffA, coeffB, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.single_apply] at h00

private theorem coeff_signed_order : -(coeffB * coeffA) ≠ -(coeffA * coeffB) := by
  intro h
  exact coeff_noncommute (neg_inj.mp h).symm

example :
    ⁅Steinberg.generator (Steinberg.root (1 : Fin 3) 2 (by decide)) coeffA,
      Steinberg.generator (Steinberg.root (0 : Fin 3) 1 (by decide)) coeffB⁆ =
    Steinberg.generator (Steinberg.root (0 : Fin 3) 2 (by decide)) (-(coeffB * coeffA)) :=
  Steinberg.generator_commutator_reverse (1 : Fin 3) 2 0
    (by decide) (by decide) (by decide)
    coeffA coeffB

example : coeffB * coeffA ≠ coeffA * coeffB := Ne.symm coeff_noncommute

example : -(coeffB * coeffA) ≠ -(coeffA * coeffB) := coeff_signed_order

example : Function.Surjective (Steinberg.toElementary (ι := Empty) (R := R)) :=
  Steinberg.toElementary_surjective

example : Function.Surjective (Steinberg.toElementary (ι := Unit) (R := R)) :=
  Steinberg.toElementary_surjective

example (a b : R) :
    Steinberg.generator (Steinberg.root (0 : Fin 2) 1 (by decide)) a *
      Steinberg.generator (Steinberg.root (0 : Fin 2) 1 (by decide)) b =
    Steinberg.generator (Steinberg.root (0 : Fin 2) 1 (by decide)) (a + b) :=
  Steinberg.generator_add _ a b

example : Function.Surjective (Steinberg.toElementary (ι := Fin 2) (R := R)) :=
  Steinberg.toElementary_surjective

end SteinbergTest
