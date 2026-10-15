/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups
import Mathlib.Algebra.Ring.PUnit

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

private theorem representative (A : Matrix n n R) :
    Matrix.traceOnCommutatorQuotient (QuotientAddGroup.mk A) =
      QuotientAddGroup.mk (Matrix.trace A) := by
  simp

private theorem kernel (p : n) (A : Matrix n n R) :
    A ∈ Ring.additiveCommutators (Matrix n n R) ↔
      Matrix.trace A ∈ Ring.additiveCommutators R :=
  Matrix.mem_additiveCommutators_iff_trace_mem p A

variable [DecidableEq n]

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

private theorem integer_additiveCommutators_eq_bot :
    Ring.additiveCommutators ℤ = ⊥ := by
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).2
    rintro _ ⟨a, b, rfl⟩
    simp [mul_comm]
  · exact bot_le

/-- A standard noncommutative ring has both nonzero commutators and a nonzero
quotient, with the canonical opposite equivalence acting on representatives. -/
private theorem opposite_standard_contract :
    let A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 0 0 1
    let B : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 0 1 1
    B ≠ 0 ∧
    B ∈ Ring.additiveCommutators (Matrix (Fin 2) (Fin 2) ℤ) ∧
    (QuotientAddGroup.mk A :
      Matrix (Fin 2) (Fin 2) ℤ ⧸
        Ring.additiveCommutators (Matrix (Fin 2) (Fin 2) ℤ)) ≠ 0 ∧
    Matrix.traceQuotientEquiv (R := ℤ) (0 : Fin 2) (QuotientAddGroup.mk A) =
      QuotientAddGroup.mk (1 : ℤ) ∧
    Ring.additiveCommutatorQuotientOpEquiv (Matrix (Fin 2) (Fin 2) ℤ)
        (QuotientAddGroup.mk A) = QuotientAddGroup.mk (MulOpposite.op A) ∧
    (Ring.additiveCommutatorQuotientOpEquiv (Matrix (Fin 2) (Fin 2) ℤ)).symm
        (QuotientAddGroup.mk (MulOpposite.op A)) = QuotientAddGroup.mk A ∧
    Ring.additiveCommutatorQuotientOpEquiv ((Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ)
        (Ring.additiveCommutatorQuotientOpEquiv (Matrix (Fin 2) (Fin 2) ℤ)
          (QuotientAddGroup.mk A)) =
      QuotientAddGroup.mk ((RingEquiv.opOp (Matrix (Fin 2) (Fin 2) ℤ)) A) := by
  dsimp only
  let A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 0 0 1
  let B : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 0 1 1
  have hB : B ≠ 0 := by
    intro h
    have hentry := congrArg (fun C : Matrix (Fin 2) (Fin 2) ℤ => C 0 1) h
    simp [B] at hentry
  have hAB : A * B = B := by
    simp [A, B]
  have hBA : B * A = 0 := by
    simp [A, B, Matrix.single_mul_single_of_ne]
  have hBmem : B ∈ Ring.additiveCommutators (Matrix (Fin 2) (Fin 2) ℤ) := by
    simpa only [hAB, hBA, sub_zero] using
      Ring.commutator_mem_additiveCommutators A B
  have htrace :
      Matrix.traceQuotientEquiv (R := ℤ) (0 : Fin 2) (QuotientAddGroup.mk A) =
        QuotientAddGroup.mk (1 : ℤ) := by
    simp [A]
  have hone :
      (QuotientAddGroup.mk (1 : ℤ) : ℤ ⧸ Ring.additiveCommutators ℤ) ≠ 0 := by
    intro h
    have hmem := (QuotientAddGroup.eq_zero_iff (1 : ℤ)).mp h
    simp [integer_additiveCommutators_eq_bot] at hmem
  have hqA :
      (QuotientAddGroup.mk A : Matrix (Fin 2) (Fin 2) ℤ ⧸
        Ring.additiveCommutators (Matrix (Fin 2) (Fin 2) ℤ)) ≠ 0 := by
    intro h
    apply hone
    rw [← htrace, h, map_zero]
  have hop_ne :
      Ring.additiveCommutatorQuotientOpEquiv (Matrix (Fin 2) (Fin 2) ℤ)
        (QuotientAddGroup.mk A) ≠ 0 := by
    intro h
    apply hqA
    apply (Ring.additiveCommutatorQuotientOpEquiv (Matrix (Fin 2) (Fin 2) ℤ)).injective
    simpa only [map_zero] using h
  refine ⟨hB, hBmem, ?_, htrace, ?_, ?_, ?_⟩
  · intro h
    apply hop_ne
    rw [h, map_zero]
  · exact Ring.additiveCommutatorQuotientOpEquiv_mk _ A
  · exact Ring.additiveCommutatorQuotientOpEquiv_symm_mk _ (MulOpposite.op A)
  · exact (DFunLike.congr_fun
      (Ring.additiveCommutatorQuotientOpEquiv_trans_op (Matrix (Fin 2) (Fin 2) ℤ))
      (QuotientAddGroup.mk A)).trans (by rfl)

/-- The zero ring needs no nontriviality hypothesis for the opposite quotient map. -/
private theorem opposite_zero_ring_contract :
    (QuotientAddGroup.mk (1 : PUnit) : PUnit ⧸ Ring.additiveCommutators PUnit) = 0 ∧
    Ring.additiveCommutatorQuotientOpEquiv PUnit
      (QuotientAddGroup.mk (1 : PUnit)) = 0 := by
  have hunit : (1 : PUnit) = 0 := Subsingleton.elim _ _
  have hqone :
      (QuotientAddGroup.mk (1 : PUnit) : PUnit ⧸ Ring.additiveCommutators PUnit) = 0 := by
    rw [hunit, QuotientAddGroup.mk_zero]
  refine ⟨hqone, ?_⟩
  rw [Ring.additiveCommutatorQuotientOpEquiv_mk]
  trans QuotientAddGroup.mk 0
  · exact congrArg QuotientAddGroup.mk (Subsingleton.elim _ _)
  · exact QuotientAddGroup.mk_zero _

end MatrixTraceClient
