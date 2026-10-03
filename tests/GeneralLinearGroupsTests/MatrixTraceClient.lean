/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups

/-! Public-root client for the native matrix trace and additive-commutator quotient. -/

set_option warningAsError true

universe uR uN uM

namespace MatrixTraceClient

variable {R : Type uR} [Ring R] {n : Type uN} {m : Type uM}
  [Fintype n] [Fintype m]

private theorem generator (a b : R) : a * b - b * a ∈ Ring.additiveCommutators R :=
  Ring.commutator_mem_additiveCommutators a b

private theorem rectangular (A : Matrix m n R) (B : Matrix n m R) :
    Matrix.trace (A * B) - Matrix.trace (B * A) ∈
      Ring.additiveCommutators R :=
  Matrix.trace_mul_sub_trace_mul_mem_additiveCommutators A B

variable [DecidableEq n]

private theorem representative (A : Matrix n n R) :
    Matrix.traceOnCommutatorQuotient (QuotientAddGroup.mk A) =
      QuotientAddGroup.mk (Matrix.trace A) := by
  simp

private theorem kernel (p : n) (A : Matrix n n R) :
    A ∈ Ring.additiveCommutators (Matrix n n R) ↔
      Matrix.trace A ∈ Ring.additiveCommutators R :=
  Matrix.mem_additiveCommutators_iff_trace_mem p A

private theorem inverse_representative (p : n) (r : R) :
    (Matrix.traceQuotientEquiv p).symm (QuotientAddGroup.mk r) =
      QuotientAddGroup.mk (Matrix.single p p r) := by
  simp

private theorem independent (p q : n) (x : R ⧸ Ring.additiveCommutators R) :
    Matrix.cornerOnCommutatorQuotient p x =
      Matrix.cornerOnCommutatorQuotient q x :=
  Matrix.cornerOnCommutatorQuotient_independent p q x

private theorem left_inverse (p : n)
    (x : Matrix n n R ⧸ Ring.additiveCommutators (Matrix n n R)) :
    (Matrix.traceQuotientEquiv p).symm ((Matrix.traceQuotientEquiv p) x) = x := by
  simp

private theorem right_inverse (p : n) (x : R ⧸ Ring.additiveCommutators R) :
    (Matrix.traceQuotientEquiv p) ((Matrix.traceQuotientEquiv p).symm x) = x := by
  simp

private theorem empty_forward (A : Matrix (Fin 0) (Fin 0) ℤ) :
    Matrix.traceOnCommutatorQuotient (QuotientAddGroup.mk A) =
      QuotientAddGroup.mk (Matrix.trace A) := by
  simp

private theorem singleton_forward (A : Matrix (Fin 1) (Fin 1) ℤ) :
    (Matrix.traceQuotientEquiv (0 : Fin 1)) (QuotientAddGroup.mk A) =
      QuotientAddGroup.mk (Matrix.trace A) := by
  simp

private theorem subsingleton_ring {S : Type*} [Ring S] [Subsingleton S]
    (A : Matrix (Fin 1) (Fin 1) S) :
    (Matrix.traceQuotientEquiv (0 : Fin 1)) (QuotientAddGroup.mk A) =
      QuotientAddGroup.mk (Matrix.trace A) := by
  simp

private theorem zero_ring (A : Matrix (Fin 1) (Fin 1) (ZMod 1)) :
    (Matrix.traceQuotientEquiv (0 : Fin 1)) (QuotientAddGroup.mk A) =
      QuotientAddGroup.mk (Matrix.trace A) := by
  simp

/-- The trace quotient equivalence evaluates on matrices over a noncommutative ring. -/
public theorem noncommutative_ring
    (A : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ)) :
    (Matrix.traceQuotientEquiv (0 : Fin 2)) (QuotientAddGroup.mk A) =
      QuotientAddGroup.mk (Matrix.trace A) := by
  simp

end MatrixTraceClient
