/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Native finite matrix kernels over dual numbers

This module identifies the identity fibers of the native general and special linear groups
under first-component reduction, together with the analogous scalar units fiber.
-/

@[expose] public section

universe u v w z

namespace DualNumber

/-- The first-component ring homomorphism from dual numbers. -/
abbrev fstRingHom (R : Type u) [CommRing R] : DualNumber R →+* R :=
  (TrivSqZeroExt.fstHom R R R).toRingHom

/-- Coefficient change on dual numbers; unlike `TrivSqZeroExt.map`, the base ring changes. -/
def mapRingHom {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) : DualNumber R →+* DualNumber S where
  toFun x := (f x.fst, f x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · change f (x.fst * y.fst) = f x.fst * f y.fst
      simp
    · change f (x.fst * y.snd + x.snd * y.fst) =
          f x.fst * f y.snd + f x.snd * f y.fst
      simp
  map_zero' := by ext <;> simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · change f (x.fst + y.fst) = f x.fst + f y.fst
      simp
    · change f (x.snd + y.snd) = f x.snd + f y.snd
      simp

@[simp] theorem mapRingHom_fst {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) (x : DualNumber R) : (mapRingHom f x).fst = f x.fst := rfl

@[simp] theorem mapRingHom_snd {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) (x : DualNumber R) : (mapRingHom f x).snd = f x.snd := rfl

@[simp] theorem fstRingHom_comp_mapRingHom {R : Type u} {S : Type w}
    [CommRing R] [CommRing S] (f : R →+* S) :
    (fstRingHom S).comp (mapRingHom f) = f.comp (fstRingHom R) := by
  apply RingHom.ext
  intro x
  rfl

@[simp] theorem mapRingHom_id (R : Type u) [CommRing R] :
    mapRingHom (RingHom.id R) = RingHom.id (DualNumber R) := by
  ext x <;> rfl

@[simp] theorem mapRingHom_comp {R : Type u} {S : Type w} {T : Type v}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f) := by
  ext x <;> rfl

end DualNumber

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

/-- The matrix with first component the identity and second component `X`. -/
def liftMatrix (X : Matrix n n R) : Matrix n n (DualNumber R) :=
  fun i j => ((1 : Matrix n n R) i j, X i j)

omit [Fintype n] in
@[simp] theorem liftMatrix_fst (X : Matrix n n R) (i j : n) :
    (liftMatrix X i j).fst = (1 : Matrix n n R) i j := rfl

omit [Fintype n] in
@[simp] theorem liftMatrix_snd (X : Matrix n n R) (i j : n) :
    (liftMatrix X i j).snd = X i j := rfl

omit [Fintype n] in
@[simp] theorem liftMatrix_zero : liftMatrix (0 : Matrix n n R) = 1 := by
  ext i j <;> by_cases h : i = j <;> simp [liftMatrix, Matrix.one_apply, h]

theorem liftMatrix_add (X Y : Matrix n n R) :
    liftMatrix (X + Y) = liftMatrix X * liftMatrix Y := by
  ext i j
  · simp only [Matrix.mul_apply, TrivSqZeroExt.fst_sum,
      TrivSqZeroExt.fst_mul, liftMatrix_fst]
    simp only [← Matrix.mul_apply, one_mul]
  · simp only [Matrix.mul_apply, TrivSqZeroExt.snd_sum,
      DualNumber.snd_mul, liftMatrix_snd, liftMatrix_fst, Finset.sum_add_distrib]
    simpa only [← Matrix.mul_apply, one_mul, mul_one, Matrix.add_apply] using
      (add_comm (X i j) (Y i j))

/-- The natural unit with first component the identity and second component `X`. -/
def liftGL (X : Matrix n n R) : Matrix.GeneralLinearGroup n (DualNumber R) :=
  ⟨liftMatrix X, liftMatrix (-X),
    by rw [← liftMatrix_add, add_neg_cancel, liftMatrix_zero],
    by rw [← liftMatrix_add, neg_add_cancel, liftMatrix_zero]⟩

@[simp] theorem liftGL_val (X : Matrix n n R) :
    (liftGL X : Matrix n n (DualNumber R)) = liftMatrix X := rfl

/-- Reduction of the native general linear group along the first projection. -/
abbrev glReduce (R : Type u) [CommRing R] (n : Type v) [Fintype n] [DecidableEq n] :
    Matrix.GeneralLinearGroup n (DualNumber R) →* Matrix.GeneralLinearGroup n R :=
  Matrix.GeneralLinearGroup.map (DualNumber.fstRingHom R)

/-- The native GL identity fiber has first component the identity matrix. -/
theorem glKernel_fst (g : (glReduce R n).ker) :
    (g.1 : Matrix n n (DualNumber R)).map (DualNumber.fstRingHom R) = 1 := by
  exact congrArg (fun h : Matrix.GeneralLinearGroup n R => (h : Matrix n n R)) g.property

/-- The second component of an element of the native GL identity fiber. -/
def glReadback (g : (glReduce R n).ker) : Matrix n n R :=
  fun i j => ((g.1 : Matrix n n (DualNumber R)) i j).snd

@[simp] theorem glReadback_apply (g : (glReduce R n).ker) (i j : n) :
    glReadback g i j = ((g.1 : Matrix n n (DualNumber R)) i j).snd := rfl

/-- The first-order GL identity fiber is the additive matrix group, in multiplicative form. -/
def glKerEquiv : Multiplicative (Matrix n n R) ≃* (glReduce R n).ker where
  toFun X := ⟨liftGL (Multiplicative.toAdd X), by
    apply Units.ext
    ext i j
    exact liftMatrix_fst (Multiplicative.toAdd X) i j⟩
  invFun g := Multiplicative.ofAdd (glReadback g)
  left_inv X := rfl
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    · have h := congrArg (fun M : Matrix n n R => M i j) (glKernel_fst g)
      change (1 : Matrix n n R) i j = ((g.1 : Matrix n n (DualNumber R)) i j).fst
      exact h.symm
    · rfl
  map_mul' X Y := by
    apply Subtype.ext
    apply Units.ext
    exact liftMatrix_add (Multiplicative.toAdd X) (Multiplicative.toAdd Y)

@[simp] theorem glKerEquiv_readback (X : Multiplicative (Matrix n n R)) :
    glReadback (glKerEquiv X) = Multiplicative.toAdd X := rfl

/-- All products in the first-order GL identity fiber commute. -/
theorem glKernel_mul_comm (g h : (glReduce R n).ker) : g * h = h * g := by
  obtain ⟨X, rfl⟩ := glKerEquiv.surjective g
  obtain ⟨Y, rfl⟩ := glKerEquiv.surjective h
  rw [← map_mul, ← map_mul, mul_comm]

/-- Native scalar units reduction along the first projection. -/
abbrev unitsReduce (R : Type u) [CommRing R] :
    (DualNumber R)ˣ →* Rˣ := Units.map (DualNumber.fstRingHom R)

/-- The unit `1 + εr`, with inverse `1 - εr`. -/
def liftUnit (r : R) : (DualNumber R)ˣ :=
  ⟨(1, r), (1, -r),
    by
      apply TrivSqZeroExt.ext
      · change (1 : R) * 1 = 1
        simp
      · change (1 : R) * -r + r * 1 = 0
        ring,
    by
      apply TrivSqZeroExt.ext
      · change (1 : R) * 1 = 1
        simp
      · change (1 : R) * r + -r * 1 = 0
        ring⟩

@[simp] theorem liftUnit_fst (r : R) : (liftUnit r : DualNumber R).fst = 1 := rfl
@[simp] theorem liftUnit_snd (r : R) : (liftUnit r : DualNumber R).snd = r := rfl

theorem liftUnit_add (r s : R) : liftUnit (r + s) = liftUnit r * liftUnit s := by
  apply Units.ext
  apply TrivSqZeroExt.ext
  · change (1 : R) = 1 * 1
    simp
  · change r + s = (1 : R) * s + r * 1
    ring

/-- The native scalar units identity fiber is the additive coefficient group. -/
def unitsKerEquiv : Multiplicative R ≃* (unitsReduce R).ker where
  toFun r := ⟨liftUnit (Multiplicative.toAdd r), by apply Units.ext; rfl⟩
  invFun r := Multiplicative.ofAdd (r.1 : DualNumber R).snd
  left_inv r := rfl
  right_inv r := by
    apply Subtype.ext
    apply Units.ext
    apply TrivSqZeroExt.ext
    · have h := congrArg (fun x : Rˣ => (x : R)) r.property
      exact h.symm
    · rfl
  map_mul' r s := by
    apply Subtype.ext
    exact liftUnit_add (Multiplicative.toAdd r) (Multiplicative.toAdd s)

@[simp] theorem unitsKerEquiv_snd (r : Multiplicative R) :
    ((unitsKerEquiv r).1 : DualNumber R).snd = Multiplicative.toAdd r := rfl

/-- The first component of a native units reduction-kernel element. -/
theorem unitsKernel_fst (r : (unitsReduce R).ker) : (r.1 : DualNumber R).fst = 1 := by
  have h := congrArg (fun t : Rˣ => (t : R)) r.property
  exact h

omit [Fintype n] in
/-- Entrywise description in the form required by the quadratic determinant expansion. -/
theorem liftMatrix_eq_one_add_smul (X : Matrix n n R) :
    liftMatrix X = 1 + (DualNumber.eps : DualNumber R) •
      X.map (algebraMap R (DualNumber R)) := by
  ext i j
  · change (1 : Matrix n n R) i j =
        ((1 : Matrix n n (DualNumber R)) i j +
          DualNumber.eps * (algebraMap R (DualNumber R)) (X i j)).fst
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, DualNumber.fst_eps,
      zero_mul, add_zero, Matrix.one_apply, apply_ite, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.fst_zero]
    split_ifs <;> rfl
  · change X i j =
        ((1 : Matrix n n (DualNumber R)) i j +
          DualNumber.eps * (algebraMap R (DualNumber R)) (X i j)).snd
    simp only [TrivSqZeroExt.snd_add, DualNumber.snd_mul, DualNumber.fst_eps,
      DualNumber.snd_eps, zero_mul, one_mul, zero_add,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
      Matrix.one_apply, apply_ite, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_zero]
    simp only [ite_self, zero_add]

/-- The determinant at first order is `1 + ε * trace X`, at every finite rank. -/
theorem det_liftMatrix (X : Matrix n n R) :
    (liftMatrix X).det = (1, X.trace) := by
  rw [liftMatrix_eq_one_add_smul, Matrix.det_one_add_smul,
    DualNumber.eps_pow_two, mul_zero, add_zero]
  rw [← AddMonoidHom.map_trace (algebraMap R (DualNumber R)) X]
  apply TrivSqZeroExt.ext
  · change (1 : R) + ((algebraMap R (DualNumber R)) X.trace).fst * 0 = 1
    ring
  · change (0 : R) + (((algebraMap R (DualNumber R)) X.trace).fst * 1 +
        ((algebraMap R (DualNumber R)) X.trace).snd * 0) = X.trace
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    simp

/-- The determinant restricted to the *native* general-linear reduction kernel. -/
def detKer : (glReduce R n).ker →* (unitsReduce R).ker where
  toFun g := ⟨Matrix.GeneralLinearGroup.det g.1, by
    apply Units.ext
    change (DualNumber.fstRingHom R) (g.1 : Matrix n n (DualNumber R)).det = 1
    rw [RingHom.map_det]
    change ((g.1 : Matrix n n (DualNumber R)).map (DualNumber.fstRingHom R)).det = 1
    rw [glKernel_fst g, Matrix.det_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- Commuting determinant/trace square for the actual native kernels. -/
theorem detKer_glKerEquiv (X : Multiplicative (Matrix n n R)) :
    detKer (glKerEquiv X) = unitsKerEquiv (Multiplicative.ofAdd (Matrix.trace
      (Multiplicative.toAdd X))) := by
  apply Subtype.ext
  apply Units.ext
  exact det_liftMatrix (Multiplicative.toAdd X)

/-- Native special-linear first-component reduction. -/
abbrev slReduce (R : Type u) [CommRing R] (n : Type v) [Fintype n] [DecidableEq n] :
    Matrix.SpecialLinearGroup n (DualNumber R) →* Matrix.SpecialLinearGroup n R :=
  Matrix.SpecialLinearGroup.map (DualNumber.fstRingHom R)

/-- First component of a native SL reduction-kernel element. -/
theorem slKernel_fst (g : (slReduce R n).ker) :
    (g.1 : Matrix n n (DualNumber R)).map (DualNumber.fstRingHom R) = 1 := by
  have h := congrArg (fun k : Matrix.SpecialLinearGroup n R => (k : Matrix n n R))
    g.property
  change (g.1 : Matrix n n (DualNumber R)).map (DualNumber.fstRingHom R) = 1 at h
  exact h

/-- Inclusion of the native SL identity fiber in the native GL identity fiber. -/
def slToGL : (slReduce R n).ker →* (glReduce R n).ker where
  toFun g := ⟨Matrix.SpecialLinearGroup.toGL g.1, by
    apply Units.ext
    exact slKernel_fst g⟩
  map_one' := by apply Subtype.ext; apply Units.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Units.ext; rfl

/-- Trace-zero matrices, using mathlib's existing `SpecialLinear.sl` carrier. -/
def liftSL (X : LieAlgebra.SpecialLinear.sl n R) :
    Matrix.SpecialLinearGroup n (DualNumber R) :=
  ⟨liftMatrix X.1, by
    rw [det_liftMatrix]
    have h : (X.1 : Matrix n n R).trace = 0 := by
      have hx := X.property
      change (X.1 : Matrix n n R).trace = 0 at hx
      exact hx
    rw [h]
    rfl⟩

/-- The second component of an SL kernel element, in the existing trace-zero Lie subalgebra. -/
def slReadback (g : (slReduce R n).ker) : LieAlgebra.SpecialLinear.sl n R :=
  ⟨glReadback (slToGL g), by
    change (glReadback (slToGL g)).trace = 0
    have hm : (g.1 : Matrix n n (DualNumber R)) =
        liftMatrix (glReadback (slToGL g)) := by
      ext i j
      · have h := congrArg (fun M : Matrix n n R => M i j) (slKernel_fst g)
        change ((g.1 : Matrix n n (DualNumber R)) i j).fst =
          (1 : Matrix n n R) i j
        exact h
      · rfl
    have hd : (g.1 : Matrix n n (DualNumber R)).det = 1 := g.1.property
    rw [hm, det_liftMatrix] at hd
    have hz := congrArg TrivSqZeroExt.snd hd
    simpa only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_one] using hz⟩

/-- The native special-linear reduction kernel is the additive group of mathlib's `sl`. -/
def slKerEquiv : Multiplicative (LieAlgebra.SpecialLinear.sl n R) ≃* (slReduce R n).ker where
  toFun X := ⟨liftSL (Multiplicative.toAdd X), by
    apply Subtype.ext
    ext i j
    exact liftMatrix_fst (Multiplicative.toAdd X).1 i j⟩
  invFun g := Multiplicative.ofAdd (slReadback g)
  left_inv X := rfl
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    · have h := congrArg (fun M : Matrix n n R => M i j) (slKernel_fst g)
      change (1 : Matrix n n R) i j = ((g.1 : Matrix n n (DualNumber R)) i j).fst
      exact h.symm
    · rfl
  map_mul' X Y := by
    apply Subtype.ext
    apply Subtype.ext
    exact liftMatrix_add (Multiplicative.toAdd X).1 (Multiplicative.toAdd Y).1

@[simp] theorem slKerEquiv_readback (X : Multiplicative (LieAlgebra.SpecialLinear.sl n R)) :
    slReadback (slKerEquiv X) = Multiplicative.toAdd X := by
  apply Subtype.ext
  rfl

@[simp] theorem slReadback_apply (g : (slReduce R n).ker) (i j : n) :
    (slReadback g).1 i j = ((g.1 : Matrix n n (DualNumber R)) i j).snd := rfl

/-- Products in the native first-order SL identity fiber commute. -/
theorem slKernel_mul_comm (g h : (slReduce R n).ker) : g * h = h * g := by
  obtain ⟨X, rfl⟩ := slKerEquiv.surjective g
  obtain ⟨Y, rfl⟩ := slKerEquiv.surjective h
  rw [← map_mul, ← map_mul, mul_comm]

/-- The inclusion square commutes on the actual native GL and SL kernels. -/
theorem slToGL_slKerEquiv (X : Multiplicative (LieAlgebra.SpecialLinear.sl n R)) :
    slToGL (slKerEquiv X) =
      glKerEquiv (Multiplicative.ofAdd (Multiplicative.toAdd X).1) := by
  apply Subtype.ext
  apply Units.ext
  rfl

section CoefficientChange

variable {S : Type w} [CommRing S] (f : R →+* S)

/-- Coefficient change on the native GL identity fibers. -/
def glKerMap : (glReduce R n).ker →* (glReduce S n).ker where
  toFun g := ⟨Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) g.1, by
    have h : glReduce S n (Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) g.1) =
        Matrix.GeneralLinearGroup.map f (glReduce R n g.1) := by
      apply Units.ext
      rfl
    change glReduce S n (Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) g.1) = 1
    rw [h, g.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- Coefficient change on the native scalar units identity fibers. -/
def unitsKerMap : (unitsReduce R).ker →* (unitsReduce S).ker where
  toFun g := ⟨Units.map (DualNumber.mapRingHom f) g.1, by
    have h : unitsReduce S (Units.map (DualNumber.mapRingHom f) g.1) =
        Units.map f (unitsReduce R g.1) := by
      apply Units.ext
      rfl
    change unitsReduce S (Units.map (DualNumber.mapRingHom f) g.1) = 1
    rw [h, g.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- Coefficient change on the native SL identity fibers. -/
def slKerMap : (slReduce R n).ker →* (slReduce S n).ker where
  toFun g := ⟨Matrix.SpecialLinearGroup.map (DualNumber.mapRingHom f) g.1, by
    have h : slReduce S n (Matrix.SpecialLinearGroup.map (DualNumber.mapRingHom f) g.1) =
        Matrix.SpecialLinearGroup.map f (slReduce R n g.1) := by
      apply Subtype.ext
      rfl
    change slReduce S n (Matrix.SpecialLinearGroup.map (DualNumber.mapRingHom f) g.1) = 1
    rw [h, g.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- The trace-zero subalgebra's underlying additive groups under coefficient change. -/
def slMap : LieAlgebra.SpecialLinear.sl n R →+
    LieAlgebra.SpecialLinear.sl n S where
  toFun X := ⟨(X.1 : Matrix n n R).map f, by
    change ((X.1 : Matrix n n R).map f).trace = 0
    rw [← AddMonoidHom.map_trace f X.1]
    have hx : (X.1 : Matrix n n R).trace = 0 := X.property
    rw [hx, map_zero]⟩
  map_zero' := by apply Subtype.ext; ext i j; simp
  map_add' X Y := by apply Subtype.ext; ext i j; simp

@[simp] theorem slMap_val (X : LieAlgebra.SpecialLinear.sl n R) :
    ((slMap f X).1 : Matrix n n S) = (X.1 : Matrix n n R).map f := rfl

/-- Coefficient change acts entrywise on the GL-kernel second component. -/
@[simp] theorem glReadback_natural (g : (glReduce R n).ker) :
    glReadback (glKerMap f g) = (glReadback g).map f := by
  ext i j
  rfl

/-- Coefficient change acts on the scalar-units second component. -/
@[simp] theorem unitsReadback_natural (r : (unitsReduce R).ker) :
    (((unitsKerMap f r).1 : (DualNumber S)ˣ) : DualNumber S).snd =
      f (r.1 : DualNumber R).snd := rfl

/-- Coefficient change acts entrywise on the SL-kernel second component. -/
@[simp] theorem slReadback_natural (g : (slReduce R n).ker) :
    slReadback (slKerMap f g) = slMap f (slReadback g) := by
  apply Subtype.ext
  ext i j
  rfl

/-- Naturality of the GL fiber equivalence. -/
theorem glKerMap_glKerEquiv (X : Multiplicative (Matrix n n R)) :
    glKerMap f (glKerEquiv X) =
      glKerEquiv (Multiplicative.ofAdd ((Multiplicative.toAdd X).map f)) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  · change f ((1 : Matrix n n R) i j) = (1 : Matrix n n S) i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · rfl

/-- Naturality of the scalar units fiber equivalence. -/
theorem unitsKerMap_unitsKerEquiv (r : Multiplicative R) :
    unitsKerMap f (unitsKerEquiv r) =
      unitsKerEquiv (Multiplicative.ofAdd (f (Multiplicative.toAdd r))) := by
  apply Subtype.ext
  apply Units.ext
  apply TrivSqZeroExt.ext
  · change f (1 : R) = 1
    simp
  · rfl

/-- Naturality of the SL fiber equivalence. -/
theorem slKerMap_slKerEquiv (X : Multiplicative (LieAlgebra.SpecialLinear.sl n R)) :
    slKerMap f (slKerEquiv X) =
      slKerEquiv (Multiplicative.ofAdd (slMap f (Multiplicative.toAdd X))) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  · change f ((1 : Matrix n n R) i j) = (1 : Matrix n n S) i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · rfl

/-- Determinant commutes with coefficient change on the native fibers. -/
theorem detKer_natural (g : (glReduce R n).ker) :
    detKer (glKerMap f g) = unitsKerMap f (detKer g) := by
  apply Subtype.ext
  apply Units.ext
  change ((g.1 : Matrix n n (DualNumber R)).map (DualNumber.mapRingHom f)).det =
    (DualNumber.mapRingHom f) (g.1 : Matrix n n (DualNumber R)).det
  exact (RingHom.map_det (DualNumber.mapRingHom f) (g.1 : Matrix n n (DualNumber R))).symm

/-- Native SL inclusion commutes with coefficient change. -/
theorem slToGL_natural (g : (slReduce R n).ker) :
    slToGL (slKerMap f g) = glKerMap f (slToGL g) := by
  apply Subtype.ext
  apply Units.ext
  rfl

end CoefficientChange

/-- Identity coefficient change on the native GL kernel. -/
@[simp] theorem glKerMap_id :
    glKerMap (n := n) (RingHom.id R) =
      MonoidHom.id (glReduce R n).ker := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply Units.ext
  rfl

/-- Identity coefficient change on the native scalar-units kernel. -/
@[simp] theorem unitsKerMap_id :
    unitsKerMap (RingHom.id R) = MonoidHom.id (unitsReduce R).ker := by
  apply MonoidHom.ext
  intro r
  apply Subtype.ext
  apply Units.ext
  rfl

/-- Identity coefficient change on the native SL kernel. -/
@[simp] theorem slKerMap_id :
    slKerMap (n := n) (RingHom.id R) = MonoidHom.id (slReduce R n).ker := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply Subtype.ext
  rfl

section Composition

variable {S : Type w} [CommRing S] {T : Type z} [CommRing T]
    (f : R →+* S) (g : S →+* T)

/-- Coefficient change composes on native GL identity fibers. -/
@[simp] theorem glKerMap_comp :
    glKerMap (n := n) (g.comp f) = (glKerMap (n := n) g).comp (glKerMap f) := by
  apply MonoidHom.ext
  intro X
  apply Subtype.ext
  apply Units.ext
  rfl

/-- Coefficient change composes on native scalar-units identity fibers. -/
@[simp] theorem unitsKerMap_comp :
    unitsKerMap (g.comp f) = (unitsKerMap g).comp (unitsKerMap f) := by
  apply MonoidHom.ext
  intro r
  apply Subtype.ext
  apply Units.ext
  rfl

/-- Coefficient change composes on native SL identity fibers. -/
@[simp] theorem slKerMap_comp :
    slKerMap (n := n) (g.comp f) = (slKerMap (n := n) g).comp (slKerMap f) := by
  apply MonoidHom.ext
  intro X
  apply Subtype.ext
  apply Subtype.ext
  rfl

end Composition

end Matrix.DualNumberKernels
