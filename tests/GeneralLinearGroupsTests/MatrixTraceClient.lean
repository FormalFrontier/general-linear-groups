/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Matrix trace and additive-commutator quotient clients

The integer matrix units and the permutation-matrix unit give concrete inputs
for cyclicity, unit conjugation and block trace. The compound contract records
their values, nonzero quotient detection and empty-index boundaries.
The unit is constructed by Mathlib's
`Matrix.permMatrixHom` and `MonoidHom.toHomUnits`, including both inverse laws.
-/

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

private abbrev IntegerMatrix := Matrix (Fin 2) (Fin 2) ℤ

private def e00 : IntegerMatrix := Matrix.single 0 0 1
private def e01 : IntegerMatrix := Matrix.single 0 1 1
private def e10 : IntegerMatrix := Matrix.single 1 0 1
private def e11 : IntegerMatrix := Matrix.single 1 1 1

/-- The transposition matrix, with inverse fields supplied by the group-to-units map. -/
private def swapUnit : IntegerMatrixˣ :=
  (Matrix.permMatrixHom (n := Fin 2) (R := ℤ)).toHomUnits (Equiv.swap 0 1)

private def singletonBlock : Matrix (Fin 1) (Fin 1) IntegerMatrix :=
  fun _ _ => e00

private def blockSum : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) IntegerMatrix :=
  Matrix.fromBlocks singletonBlock 0 0 0

private def emptyBlockBoundary : Matrix (Empty ⊕ Fin 1) (Empty ⊕ Fin 1) IntegerMatrix :=
  Matrix.fromBlocks (0 : Matrix Empty Empty IntegerMatrix) 0 0 singletonBlock

/-- Append a zero last row and column; this construction is not a unital ring map.
The equivalence sends `inl i` to `Fin.castAdd 1 i` and `inr j` to `Fin.natAdd n j`. -/
private def zeroBlockStabilization {n : ℕ} (A : Matrix (Fin n) (Fin n) IntegerMatrix) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) IntegerMatrix :=
  Matrix.reindex
    (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
    (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
    (Matrix.fromBlocks A 0 0 (0 : Matrix (Fin 1) (Fin 1) IntegerMatrix))

/-- Distinct cyclic products and a noncentral unit yield the same nonzero
commutator class, while a nonzero off-diagonal matrix is killed. Raw blocks,
the empty boundary and last-coordinate stabilization preserve the indicated
trace. The quotient detector is the existing induced integer trace map. -/
private theorem cyclic_conjugation_block_contract :
    let q := QuotientAddGroup.mk' (Ring.additiveCommutators IntegerMatrix)
    let qZ := QuotientAddGroup.mk' (Ring.additiveCommutators ℤ)
    let t := Matrix.traceOnCommutatorQuotient (R := ℤ) (n := Fin 2)
    let s := (swapUnit : IntegerMatrix)
    let si := (↑(swapUnit⁻¹) : IntegerMatrix)
    e01 * e10 = e00 ∧ e10 * e01 = e11 ∧ e00 ≠ e11 ∧
    s = !![0, 1; 1, 0] ∧ si = !![0, 1; 1, 0] ∧
    swapUnit ≠ 1 ∧ s * e00 ≠ e00 * s ∧ s * e00 * si = e11 ∧
    -- Instances of the cyclic and unit-conjugation characteristic statements.
    q (e01 * e10) = q (e10 * e01) ∧ q (s * e00 * si) = q e00 ∧
    q e00 = q e11 ∧ e01 ≠ 0 ∧ q e01 = 0 ∧
    Matrix.trace e00 = 1 ∧ Matrix.trace e11 = 1 ∧
    t (q e00) = qZ 1 ∧ t (q e11) = qZ 1 ∧
    qZ 1 ≠ 0 ∧ q e00 ≠ 0 ∧ q e11 ≠ 0 ∧
    -- A nonzero instance of the raw block trace statement and its boundaries.
    Matrix.trace blockSum =
      Matrix.trace singletonBlock + Matrix.trace (0 : Matrix (Fin 1) (Fin 1) IntegerMatrix) ∧
    Matrix.trace blockSum = e00 ∧
    q (Matrix.trace blockSum) = q e00 ∧
    emptyBlockBoundary (Sum.inr 0) (Sum.inr 0) = e00 ∧
    Matrix.trace emptyBlockBoundary = e00 ∧
    zeroBlockStabilization singletonBlock 0 0 = e00 ∧
    (∀ i : Fin 2,
      zeroBlockStabilization singletonBlock (Fin.last 1) i = 0 ∧
      zeroBlockStabilization singletonBlock i (Fin.last 1) = 0) ∧
    Matrix.trace (zeroBlockStabilization singletonBlock) = e00 ∧
    zeroBlockStabilization (0 : Matrix (Fin 0) (Fin 0) IntegerMatrix) = 0 := by
  dsimp only
  let q := QuotientAddGroup.mk' (Ring.additiveCommutators IntegerMatrix)
  let qZ := QuotientAddGroup.mk' (Ring.additiveCommutators ℤ)
  let t := Matrix.traceOnCommutatorQuotient (R := ℤ) (n := Fin 2)
  let s := (swapUnit : IntegerMatrix)
  let si := (↑(swapUnit⁻¹) : IntegerMatrix)
  have h01 : e01 * e10 = e00 := by
    simp [e01, e10, e00]
  have h10 : e10 * e01 = e11 := by
    simp [e10, e01, e11]
  have hdistinct : e00 ≠ e11 := by
    intro h
    have hentry := congrArg (fun A : IntegerMatrix => A 0 0) h
    simp [e00, e11] at hentry
  have hs : s = !![0, 1; 1, 0] := by
    decide
  have hself : s * s = 1 := by
    rw [hs]
    decide
  have hsi : si = !![0, 1; 1, 0] := by
    calc
      si = si * (s * s) := by rw [hself, mul_one]
      _ = s := by simp [si, s, ← mul_assoc]
      _ = !![0, 1; 1, 0] := hs
  have hunit : swapUnit ≠ 1 := by
    intro h
    have hentry := congrArg (fun u : IntegerMatrixˣ => (u : IntegerMatrix) 0 0) h
    have hzero : (swapUnit : IntegerMatrix) 0 0 = 0 := by
      simpa [s] using congrArg (fun A : IntegerMatrix => A 0 0) hs
    simp [hzero] at hentry
  have hnoncentral : s * e00 ≠ e00 * s := by
    rw [hs]
    decide
  have hconj : s * e00 * si = e11 := by
    rw [hs, hsi]
    decide
  have hcyclic : q (e01 * e10) = q (e10 * e01) :=
    Ring.additiveCommutatorQuotient_mk_mul_comm e01 e10
  have hquotConj : q (s * e00 * si) = q e00 :=
    Ring.additiveCommutatorQuotient_mk_units_conj swapUnit e00
  have hqeq : q e00 = q e11 := by
    simpa only [h01, h10] using hcyclic
  have hoff : e01 ≠ 0 := by
    intro h
    have hentry := congrArg (fun A : IntegerMatrix => A 0 1) h
    simp [e01] at hentry
  have hqoff : q e01 = 0 := by
    apply (QuotientAddGroup.eq_zero_iff e01).2
    exact Matrix.offDiagonal_single_mem_additiveCommutators (0 : Fin 2) 1 (by decide) 1
  have htrace00 : Matrix.trace e00 = 1 := by
    simp [e00]
  have htrace11 : Matrix.trace e11 = 1 := by
    simp [e11]
  have hdet00 : t (q e00) = qZ 1 := by
    simp [t, q, qZ, htrace00]
  have hdet11 : t (q e11) = qZ 1 := by
    simp [t, q, qZ, htrace11]
  have hqZne : qZ 1 ≠ 0 := by
    intro h
    have hmem := (QuotientAddGroup.eq_zero_iff (1 : ℤ)).mp h
    simp [integer_additiveCommutators_eq_bot] at hmem
  have hq00ne : q e00 ≠ 0 := by
    intro h
    apply hqZne
    rw [← hdet00, h, map_zero]
  have hq11ne : q e11 ≠ 0 := by
    intro h
    exact hq00ne (hqeq.trans h)
  have hraw : Matrix.trace blockSum =
      Matrix.trace singletonBlock + Matrix.trace (0 : Matrix (Fin 1) (Fin 1) IntegerMatrix) :=
    Matrix.trace_fromBlocks singletonBlock 0 0 0
  have hblock : Matrix.trace blockSum = e00 := by
    rw [hraw, Matrix.trace_zero, add_zero, Matrix.trace_fin_one]
    rfl
  have hblockq : q (Matrix.trace blockSum) = q e00 :=
    congrArg q hblock
  have hemptyentry : emptyBlockBoundary (Sum.inr 0) (Sum.inr 0) = e00 := rfl
  have hemptytrace : Matrix.trace emptyBlockBoundary = e00 := by
    calc
      Matrix.trace emptyBlockBoundary =
          Matrix.trace (0 : Matrix Empty Empty IntegerMatrix) + Matrix.trace singletonBlock :=
        Matrix.trace_fromBlocks 0 0 0 singletonBlock
      _ = e00 := by simp [Matrix.trace_fin_one, singletonBlock]
  -- This equality computes the given reindexing, so its zero coordinate is last.
  have hstabilization :
      zeroBlockStabilization singletonBlock = !![e00, 0; 0, 0] := by
    decide
  have hstabentry : zeroBlockStabilization singletonBlock 0 0 = e00 := by
    rw [hstabilization]
    rfl
  have hstablast : ∀ i : Fin 2,
      zeroBlockStabilization singletonBlock (Fin.last 1) i = 0 ∧
      zeroBlockStabilization singletonBlock i (Fin.last 1) = 0 := by
    rw [hstabilization]
    decide
  have hstabtrace : Matrix.trace (zeroBlockStabilization singletonBlock) = e00 := by
    rw [hstabilization, Matrix.trace_fin_two]
    simp
  have hstab0 :
      zeroBlockStabilization (0 : Matrix (Fin 0) (Fin 0) IntegerMatrix) = 0 := by
    decide
  exact ⟨h01, h10, hdistinct, hs, hsi, hunit, hnoncentral, hconj, hcyclic, hquotConj,
    hqeq, hoff, hqoff, htrace00, htrace11, hdet00, hdet11, hqZne, hq00ne, hq11ne,
    hraw, hblock, hblockq, hemptyentry, hemptytrace, hstabentry, hstablast, hstabtrace,
    hstab0⟩

end MatrixTraceClient
