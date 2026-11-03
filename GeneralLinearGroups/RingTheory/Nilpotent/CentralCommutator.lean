/-
SPDX-License-Identifier: Apache-2.0
Authors: Corbel, Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Tactic.NoncommRing
import Lean.Elab.Tactic.Omega

/-!
# Central commutator powers and nilpotence

For elements `x` and `y` of a possibly noncommutative ring, write the positive
commutator as `x * y - y * x`. Only its commutation with the indicated generators
is assumed; the ambient ring need not have central commutators.

## Main results

* `CentralCommutator.pow_succ_mul_sub_mul_pow_succ` computes the commutator of a
  successor power when the commutator commutes with `x`.
* `CentralCommutator.factorial_nsmul_commutator_pow_eq_zero` gives factorial
  annihilation over any ring. A supplied rational module action cancels this
  coefficient in `CentralCommutator.commutator_pow_min_eq_zero`.
* `CentralCommutator.add_add_smul_commutator_pow_eq_zero` gives the weighted bound
  `(a - 1) + (b - 1) + 2 * (c - 1) + 1` from explicit vanishing powers of `x`,
  `y`, and their commutator.
* `CentralCommutator.isNilpotent_add_add_smul_commutator` discharges commutator
  nilpotence from nilpotence of `x` and `y`.
* `CentralCommutator.exp_mul_eq_add_commutator_mul_exp` gives first-order
  commutation with the finite exponential when only `x` is nilpotent.
* `CentralCommutator.exp_mul_mul_exp_neg_eq_add_commutator` gives the corresponding
  conjugation formula without requiring the commutator to commute with `y`.

The rational results use the given `[Module ℚ A]` and its stock compatibility
with ring multiplication, not an additional algebra structure. Zero rings and
zero nilpotence witnesses are included. The private weighted filtration is a
span, with no assertion of linear independence or ambient finite dimension.

The span-induction interface is reused from Mathlib, with contributions by
Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
and Heather Macbeth.
The finite nilpotent-exponential API is reused from Mathlib, with contributions by
Janos Wolosz; the exponential identities below use the given rational module action.
-/

@[expose] public section

universe u

namespace CentralCommutator

variable {A : Type u} [Ring A]

/-- The positive inner additive operator: `D(u) = u*y - y*u`. -/
private def inner (y : A) : AddMonoid.End A :=
  AddMonoid.End.mulRight y - AddMonoid.End.mulLeft y

private lemma inner_apply (y u : A) : inner y u = u * y - y * u := rfl

private lemma inner_mul (y u v : A) :
    inner y (u * v) = inner y u * v + u * inner y v := by
  simp only [inner_apply]
  noncomm_ring

/-- A first derivative of a power; no commutative-ring hypothesis is used. -/
private lemma inner_pow_succ {x y z : A}
    (hx : inner y x = z) (hzx : Commute z x) (n : ℕ) :
    inner y (x ^ (n + 1)) = (n + 1) • (x ^ n * z) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have hmove : (x ^ n * z) * x = x ^ (n + 1) * z := by
        calc
          (x ^ n * z) * x = x ^ n * (z * x) := mul_assoc _ _ _
          _ = x ^ n * (x * z) := by rw [hzx.eq]
          _ = x ^ (n + 1) * z := by rw [← mul_assoc, ← pow_succ]
      calc
        inner y (x ^ (n + 1 + 1)) =
            inner y (x ^ (n + 1)) * x + x ^ (n + 1) * inner y x := by
          rw [pow_succ, inner_mul]
        _ = (n + 1) • (x ^ (n + 1) * z) + x ^ (n + 1) * z := by
          rw [ih, hx, smul_mul_assoc, hmove]
        _ = (n + 1 + 1) • (x ^ (n + 1) * z) := (succ_nsmul _ _).symm

/-- The commutator of a successor power with `y`, when `x * y - y * x`
commutes with `x`. No commutation with `y` or scalar hypotheses are needed. -/
theorem pow_succ_mul_sub_mul_pow_succ {x y : A}
    (hzx : Commute (x * y - y * x) x) (n : ℕ) :
    x ^ (n + 1) * y - y * x ^ (n + 1) =
      (n + 1) • (x ^ n * (x * y - y * x)) := by
  simpa only [inner_apply] using
    (inner_pow_succ (x := x) (y := y) (z := x * y - y * x) rfl hzx n)

/-- A `D`-constant right factor remains a right factor after iteration.
Multiplication in `AddMonoid.End` is composition, not pointwise multiplication. -/
private lemma inner_iterate_mul_right {y z : A} (hz : inner y z = 0)
    (n : ℕ) (u : A) :
    (inner y ^ n) (u * z) = (inner y ^ n) u * z := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      calc
        (inner y ^ (n + 1)) (u * z) =
            (inner y ^ n) (inner y (u * z)) := by
          rw [pow_succ]
          rfl
        _ = (inner y ^ n) (inner y u * z) := by
          rw [inner_mul, hz, mul_zero, add_zero]
        _ = (inner y ^ n) (inner y u) * z := ih (inner y u)
        _ = (inner y ^ (n + 1)) u * z := by
          rw [pow_succ]
          rfl

/-- The diagonal iterated differentiation identity over an arbitrary ring. -/
private lemma inner_iterate_pow {x y z : A}
    (hx : inner y x = z) (hzx : Commute z x) (hz : inner y z = 0)
    (n : ℕ) :
    (inner y ^ n) (x ^ n) = n.factorial • z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (inner y ^ (n + 1)) (x ^ (n + 1)) =
            (inner y ^ n) (inner y (x ^ (n + 1))) := by
          rw [pow_succ]
          rfl
        _ = (inner y ^ n) ((n + 1) • (x ^ n * z)) := by
          rw [inner_pow_succ hx hzx n]
        _ = (n + 1) • (inner y ^ n) (x ^ n * z) := map_nsmul _ _ _
        _ = (n + 1) • ((inner y ^ n) (x ^ n) * z) := by
          rw [inner_iterate_mul_right hz]
        _ = (n + 1) • (n.factorial • (z ^ n * z)) := by
          rw [ih, smul_mul_assoc]
        _ = (n + 1).factorial • z ^ (n + 1) := by
          rw [← pow_succ, smul_smul, Nat.factorial_succ]

/-- If the commutator commutes with both generators, a vanishing `n`th power
of the left generator annihilates its `n`th power after `n!`-fold addition.
The ring may be noncommutative or zero, and `n = 0` is included. -/
theorem factorial_nsmul_commutator_pow_eq_zero {x y : A} {n : ℕ}
    (hzx : Commute (x * y - y * x) x)
    (hzy : Commute (x * y - y * x) y)
    (hn : x ^ n = 0) :
    n.factorial • (x * y - y * x) ^ n = 0 := by
  have hz : inner y (x * y - y * x) = 0 := by
    rw [inner_apply]
    exact sub_eq_zero.mpr hzy.eq
  have h := inner_iterate_pow (x := x) (y := y)
    (z := x * y - y * x) rfl hzx hz n
  calc
    n.factorial • (x * y - y * x) ^ n = (inner y ^ n) (x ^ n) := h.symm
    _ = 0 := by rw [hn, map_zero]

/-- The right-generator version, with the sign normalized by using `(y, -x)`.
In particular no parity argument or cancellation of a natural scalar occurs. -/
theorem factorial_nsmul_commutator_pow_eq_zero_right {x y : A} {n : ℕ}
    (hzx : Commute (x * y - y * x) x)
    (hzy : Commute (x * y - y * x) y)
    (hn : y ^ n = 0) :
    n.factorial • (x * y - y * x) ^ n = 0 := by
  have hswap : y * (-x) - (-x) * y = x * y - y * x := by noncomm_ring
  have hleft : Commute (y * (-x) - (-x) * y) y := by
    rw [hswap]
    exact hzy
  have hright : Commute (y * (-x) - (-x) * y) (-x) := by
    rw [hswap]
    exact hzx.neg_right
  have h := factorial_nsmul_commutator_pow_eq_zero hleft hright hn
  simpa only [hswap] using h

section Rat

variable [Module ℚ A]

/-- Factorial cancellation uses only the supplied rational module action;
no `CharZero A`, nontriviality, or faithful-action hypothesis is introduced. -/
private lemma eq_zero_of_factorial_nsmul_eq_zero
    {n : ℕ} {a : A} (h : n.factorial • a = 0) : a = 0 := by
  have hq : (n.factorial : ℚ) • a = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using h
  have hnq : (n.factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  calc
    a = (n.factorial : ℚ)⁻¹ • ((n.factorial : ℚ) • a) :=
      (inv_smul_smul₀ hnq a).symm
    _ = 0 := by rw [hq, smul_zero]

/-- Over a supplied rational module the factorial coefficient can be cancelled. -/
theorem commutator_pow_eq_zero_of_pow_eq_zero
    {x y : A} {n : ℕ}
    (hzx : Commute (x * y - y * x) x)
    (hzy : Commute (x * y - y * x) y)
    (hn : x ^ n = 0) :
    (x * y - y * x) ^ n = 0 := by
  exact eq_zero_of_factorial_nsmul_eq_zero
    (factorial_nsmul_commutator_pow_eq_zero hzx hzy hn)

/-- The right-generator rational commutator bound. -/
theorem commutator_pow_eq_zero_of_pow_eq_zero_right
    {x y : A} {n : ℕ}
    (hzx : Commute (x * y - y * x) x)
    (hzy : Commute (x * y - y * x) y)
    (hn : y ^ n = 0) :
    (x * y - y * x) ^ n = 0 := by
  exact eq_zero_of_factorial_nsmul_eq_zero
    (factorial_nsmul_commutator_pow_eq_zero_right hzx hzy hn)

/-- Either supplied nilpotence exponent is valid, hence so is their minimum. -/
theorem commutator_pow_min_eq_zero
    {x y : A} {a b : ℕ}
    (hzx : Commute (x * y - y * x) x)
    (hzy : Commute (x * y - y * x) y)
    (ha : x ^ a = 0) (hb : y ^ b = 0) :
    (x * y - y * x) ^ min a b = 0 := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact commutator_pow_eq_zero_of_pow_eq_zero hzx hzy ha
  · rw [min_eq_right hba]
    exact commutator_pow_eq_zero_of_pow_eq_zero_right hzx hzy hb

/-- A central commutator is nilpotent if its left generator is nilpotent. -/
theorem isNilpotent_commutator_of_isNilpotent_left
    {x y : A}
    (hzx : Commute (x * y - y * x) x)
    (hzy : Commute (x * y - y * x) y)
    (hx : IsNilpotent x) : IsNilpotent (x * y - y * x) := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, commutator_pow_eq_zero_of_pow_eq_zero hzx hzy hn⟩

/-- A central commutator is nilpotent if its right generator is nilpotent. -/
theorem isNilpotent_commutator_of_isNilpotent_right
    {x y : A}
    (hzx : Commute (x * y - y * x) x)
    (hzy : Commute (x * y - y * x) y)
    (hy : IsNilpotent y) : IsNilpotent (x * y - y * x) := by
  obtain ⟨n, hn⟩ := hy
  exact ⟨n, commutator_pow_eq_zero_of_pow_eq_zero_right hzx hzy hn⟩

/-- Ordered-monomial spanning filtration; no independence is asserted. -/
private def orderedWeightSpan (x y z : A) (d : ℕ) : Submodule ℚ A :=
  Submodule.span ℚ {v | ∃ i j k : ℕ, d ≤ i + j + 2 * k ∧ v = x ^ i * y ^ j * z ^ k}

private theorem ordered_mem (x y z : A) (d i j k : ℕ)
    (h : d ≤ i + j + 2 * k) :
    x ^ i * y ^ j * z ^ k ∈ orderedWeightSpan x y z d :=
  Submodule.subset_span ⟨i, j, k, h, rfl⟩

private theorem orderedWeightSpan_antitone (x y z : A) {d e : ℕ} (h : e ≤ d) :
    orderedWeightSpan x y z d ≤ orderedWeightSpan x y z e := by
  apply Submodule.span_le.mpr
  rintro v ⟨i, j, k, hd, rfl⟩
  exact ordered_mem x y z e i j k (h.trans hd)

/-- Extend a left-multiplication calculation from generators using the GIVEN action. -/
private theorem ordered_mul_mem (x y z t : A) (d e : ℕ)
    (h : ∀ i j k : ℕ, d ≤ i + j + 2 * k →
      t * (x ^ i * y ^ j * z ^ k) ∈ orderedWeightSpan x y z e)
    {v : A} (hv : v ∈ orderedWeightSpan x y z d) :
    t * v ∈ orderedWeightSpan x y z e := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro w ⟨i, j, k, hd, rfl⟩
    exact h i j k hd
  · simpa only [mul_zero] using (orderedWeightSpan x y z e).zero_mem
  · intro v w hv hw ihv ihw
    rw [mul_add]
    exact (orderedWeightSpan x y z e).add_mem ihv ihw
  · intro r v hv ih
    rw [mul_smul_comm]
    exact (orderedWeightSpan x y z e).smul_mem r ih

private theorem x_mul_ordered_mem (x y z : A) {d : ℕ} {v : A}
    (hv : v ∈ orderedWeightSpan x y z d) :
    x * v ∈ orderedWeightSpan x y z (d + 1) := by
  apply ordered_mul_mem x y z x d (d + 1) ?_ hv
  intro i j k hd
  have h := ordered_mem x y z (d + 1) (i + 1) j k (by omega)
  simpa only [pow_succ', mul_assoc] using h

private theorem z_mul_ordered_mem (x y z : A)
    (hzx : Commute z x) (hzy : Commute z y) {d : ℕ} {v : A}
    (hv : v ∈ orderedWeightSpan x y z d) :
    z * v ∈ orderedWeightSpan x y z (d + 2) := by
  apply ordered_mul_mem x y z z d (d + 2) ?_ hv
  intro i j k hd
  have heq : z * (x ^ i * y ^ j * z ^ k) = x ^ i * y ^ j * z ^ (k + 1) := by
    calc
      z * (x ^ i * y ^ j * z ^ k) = ((z * x ^ i) * y ^ j) * z ^ k := by
        simp only [mul_assoc]
      _ = ((x ^ i * z) * y ^ j) * z ^ k := by rw [(hzx.pow_right i).eq]
      _ = x ^ i * (z * y ^ j) * z ^ k := by rw [mul_assoc (x ^ i) z (y ^ j)]
      _ = x ^ i * (y ^ j * z) * z ^ k := by rw [(hzy.pow_right j).eq]
      _ = x ^ i * y ^ j * z ^ (k + 1) := by simp only [pow_succ', mul_assoc]
  rw [heq]
  exact ordered_mem x y z (d + 2) i j (k + 1) (by omega)

/-- Recursive reordering replaces a closed commutator-power formula. -/
private theorem y_mul_monomial_mem (x y z : A)
    (hyx : y * x = x * y - z) (hzx : Commute z x) (hzy : Commute z y)
    (i j k : ℕ) :
    y * (x ^ i * y ^ j * z ^ k) ∈ orderedWeightSpan x y z (i + j + 2 * k + 1) := by
  induction i with
  | zero =>
      have h := ordered_mem x y z (j + 2 * k + 1) 0 (j + 1) k (by omega)
      simpa only [pow_zero, one_mul, pow_succ', mul_assoc, Nat.zero_add] using h
  | succ i ih =>
      have hx := x_mul_ordered_mem x y z ih
      have hz := z_mul_ordered_mem x y z hzx hzy
        (ordered_mem x y z (i + j + 2 * k) i j k (by omega))
      have hx' : x * (y * (x ^ i * y ^ j * z ^ k)) ∈
          orderedWeightSpan x y z ((i + 1) + j + 2 * k + 1) := by
        have he : (i + 1) + j + 2 * k + 1 = (i + j + 2 * k + 1) + 1 := by omega
        rw [he]
        exact hx
      have hz' : z * (x ^ i * y ^ j * z ^ k) ∈
          orderedWeightSpan x y z ((i + 1) + j + 2 * k + 1) := by
        have he : (i + 1) + j + 2 * k + 1 = (i + j + 2 * k) + 2 := by omega
        rw [he]
        exact hz
      have heq : y * (x ^ (i + 1) * y ^ j * z ^ k) =
          x * (y * (x ^ i * y ^ j * z ^ k)) - z * (x ^ i * y ^ j * z ^ k) := by
        calc
          y * (x ^ (i + 1) * y ^ j * z ^ k) =
              (y * x) * (x ^ i * y ^ j * z ^ k) := by simp only [pow_succ', mul_assoc]
          _ = (x * y - z) * (x ^ i * y ^ j * z ^ k) := by rw [hyx]
          _ = x * (y * (x ^ i * y ^ j * z ^ k)) - z * (x ^ i * y ^ j * z ^ k) := by
            rw [sub_mul, mul_assoc]
      change y * (x ^ (i + 1) * y ^ j * z ^ k) ∈ _
      rw [heq]
      exact (orderedWeightSpan x y z _).sub_mem hx' hz'

private theorem y_mul_ordered_mem (x y z : A)
    (hyx : y * x = x * y - z) (hzx : Commute z x) (hzy : Commute z y)
    {d : ℕ} {v : A} (hv : v ∈ orderedWeightSpan x y z d) :
    y * v ∈ orderedWeightSpan x y z (d + 1) := by
  apply ordered_mul_mem x y z y d (d + 1) ?_ hv
  intro i j k hd
  exact orderedWeightSpan_antitone x y z (d := i + j + 2 * k + 1) (e := d + 1)
    (by omega) (y_mul_monomial_mem x y z hyx hzx hzy i j k)

private theorem sum_mul_ordered_mem (x y z : A)
    (hyx : y * x = x * y - z) (hzx : Commute z x) (hzy : Commute z y)
    (q : ℚ) {d : ℕ} {v : A} (hv : v ∈ orderedWeightSpan x y z d) :
    (x + y + q • z) * v ∈ orderedWeightSpan x y z (d + 1) := by
  rw [add_mul, add_mul, smul_mul_assoc]
  apply (orderedWeightSpan x y z (d + 1)).add_mem
  · exact (orderedWeightSpan x y z (d + 1)).add_mem
      (x_mul_ordered_mem x y z hv) (y_mul_ordered_mem x y z hyx hzx hzy hv)
  · apply (orderedWeightSpan x y z (d + 1)).smul_mem q
    exact orderedWeightSpan_antitone x y z (d := d + 2) (e := d + 1)
      (by omega) (z_mul_ordered_mem x y z hzx hzy hv)

/-- At the cutoff every generator is zero; this also covers zero nilpotence witnesses. -/
private theorem high_ordered_eq_zero (x y z : A) (a b c : ℕ)
    (hx : x ^ a = 0) (hy : y ^ b = 0) (hz : z ^ c = 0)
    {v : A}
    (hv : v ∈ orderedWeightSpan x y z ((a - 1) + (b - 1) + 2 * (c - 1) + 1)) :
    v = 0 := by
  have hbot : orderedWeightSpan x y z
      ((a - 1) + (b - 1) + 2 * (c - 1) + 1) ≤ (⊥ : Submodule ℚ A) := by
    apply Submodule.span_le.mpr
    rintro w ⟨i, j, k, hd, rfl⟩
    have hvan : x ^ i * y ^ j * z ^ k = 0 := by
      by_cases hai : a ≤ i
      · rw [pow_eq_zero_of_le hai hx, zero_mul, zero_mul]
      by_cases hbj : b ≤ j
      · rw [pow_eq_zero_of_le hbj hy, mul_zero, zero_mul]
      by_cases hck : c ≤ k
      · rw [pow_eq_zero_of_le hck hz, mul_zero]
      omega
    exact (Submodule.mem_bot ℚ).mpr hvan
  simpa only [Submodule.mem_bot] using hbot hv

private theorem ordered_sum_pow_eq_zero (x y z : A)
    (hyx : y * x = x * y - z) (hzx : Commute z x) (hzy : Commute z y)
    (a b c : ℕ) (hx : x ^ a = 0) (hy : y ^ b = 0) (hz : z ^ c = 0) (q : ℚ) :
    (x + y + q • z) ^ ((a - 1) + (b - 1) + 2 * (c - 1) + 1) = 0 := by
  have hp : ∀ n : ℕ, (x + y + q • z) ^ n ∈ orderedWeightSpan x y z n := by
    intro n
    induction n with
    | zero =>
        have h := ordered_mem x y z 0 0 0 0 (by omega)
        simpa only [pow_zero, one_mul, mul_one] using h
    | succ n ih =>
        rw [pow_succ']
        exact sum_mul_ordered_mem x y z hyx hzx hzy q ih
  exact high_ordered_eq_zero x y z a b c hx hy hz (hp _)

/-- The weighted ordered-monomial nilpotence bound for a central commutator.
The commutator nilpotence bound is an explicit supporting premise, not a
replacement for the separate theorem that derives such a bound from `hx` and `hy`.
No positivity, nontriviality, or ambient commutativity is assumed. -/
theorem add_add_smul_commutator_pow_eq_zero (x y : A)
    (hzx : Commute (x * y - y * x) x) (hzy : Commute (x * y - y * x) y)
    (a b c : ℕ) (hx : x ^ a = 0) (hy : y ^ b = 0)
    (hz : (x * y - y * x) ^ c = 0) (q : ℚ) :
    (x + y + q • (x * y - y * x)) ^
      ((a - 1) + (b - 1) + 2 * (c - 1) + 1) = 0 := by
  apply ordered_sum_pow_eq_zero x y (x * y - y * x) ?_ hzx hzy a b c hx hy hz q
  noncomm_ring

/-- A relatively central commutator of nilpotent generators gives nilpotent
`x + y + q • (x * y - y * x)` for every rational `q`. The commutator's own
nilpotence is derived, not assumed. -/
theorem isNilpotent_add_add_smul_commutator {x y : A}
    (hzx : Commute (x * y - y * x) x)
    (hzy : Commute (x * y - y * x) y)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (q : ℚ) :
    IsNilpotent (x + y + q • (x * y - y * x)) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨(a - 1) + (b - 1) + 2 * (min a b - 1) + 1,
    add_add_smul_commutator_pow_eq_zero x y hzx hzy a b (min a b) ha hb
      (commutator_pow_min_eq_zero hzx hzy ha hb) q⟩

end Rat

/-- Cancel the successor factor against the inverse successor factorial.
This uses only the supplied rational module action. -/
private lemma inv_factorial_smul_succ_nsmul [Module ℚ A] (n : ℕ) (a : A) :
    ((n + 1).factorial : ℚ)⁻¹ • ((n + 1) • a) =
      (n.factorial : ℚ)⁻¹ • a := by
  have hnq : ((n + 1 : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [← Nat.cast_smul_eq_nsmul ℚ (n + 1) a, smul_smul,
    Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hnq, mul_one]

/-- First-order commutation with the stock finite nilpotent exponential.
Only `x` is nilpotent; `y` is arbitrary, and its commutator with `x` need only
commute with `x`. No rational algebra structure or extra scalar compatibility
hypothesis is required. -/
theorem exp_mul_eq_add_commutator_mul_exp [Module ℚ A] {x y : A}
    (hx : IsNilpotent x) (hzx : Commute (x * y - y * x) x) :
    IsNilpotent.exp x * y = (y + (x * y - y * x)) * IsNilpotent.exp x := by
  obtain ⟨n, hn⟩ := hx
  have hn' : x ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  have hsum :
      IsNilpotent.exp x * y - y * IsNilpotent.exp x =
        IsNilpotent.exp x * (x * y - y * x) := by
    calc
      IsNilpotent.exp x * y - y * IsNilpotent.exp x =
          ∑ k ∈ Finset.range (n + 1), (k.factorial : ℚ)⁻¹ •
            (x ^ k * y - y * x ^ k) := by
        simp only [IsNilpotent.exp_eq_sum hn', Finset.sum_mul, Finset.mul_sum,
          Finset.sum_sub_distrib, smul_mul_assoc, mul_smul_comm, smul_sub]
      _ = ∑ j ∈ Finset.range n, ((j + 1).factorial : ℚ)⁻¹ •
            (x ^ (j + 1) * y - y * x ^ (j + 1)) := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, one_mul, mul_one, sub_self, smul_zero, add_zero]
      _ = ∑ j ∈ Finset.range n, (j.factorial : ℚ)⁻¹ •
            (x ^ j * (x * y - y * x)) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [pow_succ_mul_sub_mul_pow_succ hzx, inv_factorial_smul_succ_nsmul]
      _ = IsNilpotent.exp x * (x * y - y * x) := by
        simp only [IsNilpotent.exp_eq_sum hn, Finset.sum_mul, smul_mul_assoc]
  have hcomm :
      IsNilpotent.exp x * (x * y - y * x) =
        (x * y - y * x) * IsNilpotent.exp x := by
    simp only [IsNilpotent.exp_eq_sum hn, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact congrArg (fun a : A => (j.factorial : ℚ)⁻¹ • a)
      (hzx.pow_right j).eq.symm
  calc
    IsNilpotent.exp x * y =
        IsNilpotent.exp x * (x * y - y * x) + y * IsNilpotent.exp x :=
      sub_eq_iff_eq_add.mp hsum
    _ = (y + (x * y - y * x)) * IsNilpotent.exp x := by
      rw [hcomm, add_mul, add_comm]

/-- Conjugation by the stock nilpotent exponential adds the first commutator.
The right inverse is the stock exponential of `-x`; no nilpotence of `y`
or commutation of the commutator with `y` is assumed. -/
theorem exp_mul_mul_exp_neg_eq_add_commutator [Module ℚ A] {x y : A}
    (hx : IsNilpotent x) (hzx : Commute (x * y - y * x) x) :
    (IsNilpotent.exp x * y) * IsNilpotent.exp (-x) = y + (x * y - y * x) := by
  rw [exp_mul_eq_add_commutator_mul_exp hx hzx, mul_assoc,
    IsNilpotent.exp_mul_exp_neg_self hx, mul_one]

end CentralCommutator
