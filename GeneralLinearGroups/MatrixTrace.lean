/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.AdditiveCommutator
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Basis
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Matrix trace modulo additive commutators

For a finite square matrix over an arbitrary unital ring, trace descends to
the additive quotients by commutators. Given an index, a diagonal corner
defines its inverse. The forward map works even for empty index types.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix

open scoped BigOperators

universe uR uM uN

variable {R : Type uR} [Ring R]
variable {m : Type uM} {n : Type uN} [Fintype m] [Fintype n]

/-- Rectangular cyclic trace differences are sums of scalar commutators. -/
theorem trace_mul_sub_trace_mul_commutators (A : Matrix m n R) (B : Matrix n m R) :
    trace (A * B) - trace (B * A) =
      ∑ i, ∑ j, (A i j * B j i - B j i * A i j) := by
  simp only [trace, diag_apply, mul_apply]
  rw [Finset.sum_comm (f := fun j i => B j i * A i j)]
  simp only [Finset.sum_sub_distrib]

/-- The two traces of a rectangular matrix product agree modulo scalar additive commutators. -/
theorem trace_mul_sub_trace_mul_mem_additiveCommutators
    (A : Matrix m n R) (B : Matrix n m R) :
    trace (A * B) - trace (B * A) ∈ Ring.additiveCommutators R := by
  rw [trace_mul_sub_trace_mul_commutators]
  exact (Ring.additiveCommutators R).sum_mem fun i _ =>
    (Ring.additiveCommutators R).sum_mem fun j _ =>
      Ring.commutator_mem_additiveCommutators _ _

variable [DecidableEq n]

/-- Trace carries the entire matrix commutator closure into scalar commutators. -/
theorem additiveCommutators_le_trace_comap :
    Ring.additiveCommutators (Matrix n n R) ≤
      (Ring.additiveCommutators R).comap (traceAddMonoidHom n R) := by
  apply (AddSubgroup.closure_le _).2
  rintro _ ⟨A, B, rfl⟩
  change trace (A * B - B * A) ∈ Ring.additiveCommutators R
  rw [trace_sub]
  exact trace_mul_sub_trace_mul_mem_additiveCommutators A B

/-- The actual trace on the native additive-group quotients, including empty indices. -/
def traceOnCommutatorQuotient :
    (Matrix n n R ⧸ Ring.additiveCommutators (Matrix n n R)) →+
      (R ⧸ Ring.additiveCommutators R) :=
  QuotientAddGroup.map _ _ (traceAddMonoidHom n R)
    additiveCommutators_le_trace_comap

/-- The induced trace sends the class of a matrix to the class of its trace. -/
@[simp] theorem traceOnCommutatorQuotient_mk (A : Matrix n n R) :
    traceOnCommutatorQuotient (QuotientAddGroup.mk A) =
      QuotientAddGroup.mk (trace A) := rfl

/-- A diagonal corner carries scalar commutators into matrix commutators. -/
theorem additiveCommutators_le_corner_comap (p : n) :
    Ring.additiveCommutators R ≤
      (Ring.additiveCommutators (Matrix n n R)).comap (singleAddMonoidHom p p) := by
  apply (AddSubgroup.closure_le _).2
  rintro _ ⟨a, b, rfl⟩
  change (singleAddMonoidHom p p) (a * b - b * a) ∈
    Ring.additiveCommutators (Matrix n n R)
  rw [map_sub]
  simpa only [singleAddMonoidHom_apply, single_mul_single_same] using
    Ring.commutator_mem_additiveCommutators (single p p a) (single p p b)

/-- A matrix supported at a single off-diagonal entry belongs to the additive
commutator subgroup. -/
theorem offDiagonal_single_mem_additiveCommutators (i j : n) (hij : i ≠ j) (r : R) :
    single i j r ∈ Ring.additiveCommutators (Matrix n n R) := by
  simpa [single_mul_single_of_ne, hij.symm] using
    Ring.commutator_mem_additiveCommutators (single i i (1 : R)) (single i j r)

/-- Moving a scalar between two diagonal positions changes the matrix by an additive commutator. -/
theorem diagonal_single_sub_corner_mem_additiveCommutators (p i : n) (r : R) :
    single i i r - single p p r ∈ Ring.additiveCommutators (Matrix n n R) := by
  simpa only [single_mul_single_same, mul_one, one_mul] using
    Ring.commutator_mem_additiveCommutators (single i p r) (single p i (1 : R))

/-- A single-entry matrix agrees modulo additive commutators with its trace placed in corner `p`. -/
theorem single_sub_corner_trace_mem_additiveCommutators (p i j : n) (r : R) :
    single i j r - single p p (trace (single i j r)) ∈
      Ring.additiveCommutators (Matrix n n R) := by
  by_cases hij : i = j
  · subst j
    simpa only [trace_single_eq_same] using
      diagonal_single_sub_corner_mem_additiveCommutators p i r
  · simpa [trace_single_eq_of_ne i j r hij] using
      offDiagonal_single_mem_additiveCommutators i j hij r

/-- Every finite matrix differs from its trace in one corner by commutators. -/
theorem sub_corner_trace_mem_additiveCommutators (p : n) (A : Matrix n n R) :
    A - single p p (trace A) ∈ Ring.additiveCommutators (Matrix n n R) := by
  let difference : Matrix n n R →+ Matrix n n R :=
    AddMonoidHom.id _ - (singleAddMonoidHom p p).comp (traceAddMonoidHom n R)
  change difference A ∈ Ring.additiveCommutators (Matrix n n R)
  rw [matrix_eq_sum_single A]
  simp only [map_sum]
  exact (Ring.additiveCommutators (Matrix n n R)).sum_mem fun i _ =>
    (Ring.additiveCommutators (Matrix n n R)).sum_mem fun j _ =>
      single_sub_corner_trace_mem_additiveCommutators p i j (A i j)

/-- For a nonempty finite index, membership in the matrix commutator closure
is characterized by membership of its trace in the scalar closure. -/
theorem mem_additiveCommutators_iff_trace_mem (p : n) (A : Matrix n n R) :
    A ∈ Ring.additiveCommutators (Matrix n n R) ↔
      trace A ∈ Ring.additiveCommutators R := by
  constructor
  · exact fun membership => additiveCommutators_le_trace_comap membership
  · intro membership
    have corner := additiveCommutators_le_corner_comap p membership
    have difference := sub_corner_trace_mem_additiveCommutators p A
    simpa using (Ring.additiveCommutators (Matrix n n R)).add_mem difference corner

/-- The additive corner map on native additive-group quotients. -/
def cornerOnCommutatorQuotient (p : n) :
    (R ⧸ Ring.additiveCommutators R) →+
      (Matrix n n R ⧸ Ring.additiveCommutators (Matrix n n R)) :=
  QuotientAddGroup.map _ _ (singleAddMonoidHom p p)
    (additiveCommutators_le_corner_comap p)

/-- The induced corner map sends a scalar class to the class of its diagonal single-entry matrix. -/
@[simp] theorem cornerOnCommutatorQuotient_mk (p : n) (r : R) :
    cornerOnCommutatorQuotient p (QuotientAddGroup.mk r) =
      QuotientAddGroup.mk (single p p r) := rfl

/-- Placing the trace in a chosen corner recovers every matrix class modulo additive commutators. -/
theorem corner_traceOnCommutatorQuotient (p : n)
    (x : Matrix n n R ⧸ Ring.additiveCommutators (Matrix n n R)) :
    cornerOnCommutatorQuotient p (traceOnCommutatorQuotient x) = x := by
  refine QuotientAddGroup.induction_on x fun A => ?_
  change QuotientAddGroup.mk (single p p (trace A)) =
    (QuotientAddGroup.mk A : Matrix n n R ⧸ Ring.additiveCommutators (Matrix n n R))
  exact ((QuotientAddGroup.eq_iff_sub_mem).2
    (sub_corner_trace_mem_additiveCommutators p A)).symm

/-- Taking the trace after the corner map recovers each scalar class modulo additive commutators. -/
theorem traceOnCommutatorQuotient_corner (p : n)
    (x : R ⧸ Ring.additiveCommutators R) :
    traceOnCommutatorQuotient (cornerOnCommutatorQuotient p x) = x := by
  refine QuotientAddGroup.induction_on x fun r => ?_
  change QuotientAddGroup.mk (trace (single p p r)) =
    (QuotientAddGroup.mk r : R ⧸ Ring.additiveCommutators R)
  rw [trace_single_eq_same]

/-- A chosen index identifies the matrix and scalar additive-commutator quotients. -/
def traceQuotientEquiv (p : n) :
    (Matrix n n R ⧸ Ring.additiveCommutators (Matrix n n R)) ≃+
      (R ⧸ Ring.additiveCommutators R) where
  toFun := traceOnCommutatorQuotient
  invFun := cornerOnCommutatorQuotient p
  left_inv := corner_traceOnCommutatorQuotient p
  right_inv := traceOnCommutatorQuotient_corner p
  map_add' := map_add traceOnCommutatorQuotient

/-- The trace equivalence evaluates on a matrix representative by taking its trace. -/
@[simp] theorem traceQuotientEquiv_mk (p : n) (A : Matrix n n R) :
    traceQuotientEquiv p (QuotientAddGroup.mk A) =
      QuotientAddGroup.mk (trace A) := rfl

/-- The inverse trace equivalence represents a scalar class in the chosen diagonal corner. -/
@[simp] theorem traceQuotientEquiv_symm_mk (p : n) (r : R) :
    (traceQuotientEquiv p).symm (QuotientAddGroup.mk r) =
      QuotientAddGroup.mk (single p p r) := rfl

/-- The corner map on additive-commutator quotients is independent of the chosen index. -/
theorem cornerOnCommutatorQuotient_independent (p q : n)
    (x : R ⧸ Ring.additiveCommutators R) :
    cornerOnCommutatorQuotient p x = cornerOnCommutatorQuotient q x := by
  apply (traceQuotientEquiv p).injective
  exact (traceOnCommutatorQuotient_corner p x).trans
    (traceOnCommutatorQuotient_corner q x).symm

end Matrix
