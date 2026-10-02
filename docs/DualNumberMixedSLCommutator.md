<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- Authors: Formal Frontier Agents -->

# Native special-linear mixed dual-number commutator

Import `GeneralLinearGroups.DualNumberMixedSLCommutator` for the native special
linear group over iterated dual numbers. Its public import is
`GeneralLinearGroups.DualNumberMixedCommutator`; the definitions live in
`Matrix.DualNumberMixedSLCommutator` and use the existing native kernel API
in `Matrix.DualNumberKernels`. No separate source-repository construction is
needed by a client.

Let `R : Type u` be any `CommRing`, let `n : Type v` have `Fintype n` and
`DecidableEq n`, and put `S := DualNumber R`, `T := DualNumber S`. The two
universes are independent. For trace-zero matrices
`X Y : LieAlgebra.SpecialLinear.sl n R`, the *actual factors* of
`Matrix.SpecialLinearGroup n T` are

* `epsilonLiftSL X := SpecialLinearGroup.map (algebraMap S T) (liftSL X)`,
  the outer-constant image of the inner special-linear infinitesimal;
* `etaLiftSL Y := liftSL (slMap (algebraMap R S) Y)`, the outer
  infinitesimal with inner-constant coefficient.

`innerPureSL X : LieAlgebra.SpecialLinear.sl n S` has entries `(0, X.1 i j)`.
Its trace is zero by *additivity* of the pure-inner embedding; the map
`r ↦ (0, r)` is not a unital ring homomorphism. The entrywise identities
`epsilonLiftSL_val` and `etaLiftSL_val` describe the actual matrices.
`epsilonLiftSL_toGL` and `etaLiftSL_toGL` identify their images under the
**whole-group** `SpecialLinearGroup.toGL` with `epsilonLiftGL X.1` and
`etaLiftGL Y.1`. The separate `slToGL` map is only for reduction kernels.

## Ordered identity and readback

`epsilon_eta_SL_commutator` proves the equality *in the native SL group*

```text
epsilonLiftSL X * etaLiftSL Y * (epsilonLiftSL X)⁻¹ * (etaLiftSL Y)⁻¹
  = liftSL (innerPureSL ⁅X, Y⁆).
```

The bracket is ordered `XY - YX`: reversing the factors reverses its sign.
The proof uses the native mixed-GL identity and injectivity of whole-group
`SpecialLinearGroup.toGL`, not a new determinant or matrix-unit argument.
Outer reduction sends epsilon to `liftSL X` (generally **not** `1`) and eta
to `1`, by `epsilonLiftSL_reduce` and `etaLiftSL_reduce`.

`mixedSLKernel X Y : (slReduce S n).ker` is an element of the **actual native
SL identity fiber**, packaged by `slKerEquiv`. `mixedSLKernel_val` identifies
its SL-group value with the ordered four-factor commutator, and
`mixedSLKernel_readback` states
`slReadback (mixedSLKernel X Y) = innerPureSL ⁅X, Y⁆`.
For the outer-dual entry `(a, b) : T`, `mixedSLKernel_snd_snd` says the
inner-second coordinate of `b` equals `(⁅X, Y⁆ : sl n R).1 i j`, or
`(X.1 * Y.1 - Y.1 * X.1) i j`.

Trace zero is needed for **each individual factor** to belong to SL. No
field, nontrivial-ring, nonempty-index, characteristic or inverse-rank
assumption is used. This does not assert a determinant theorem about arbitrary
GL commutators.

## Examples and reproducibility

The direct-import client `tests/DualNumberMixedSLCommutatorClient.lean`
checks the generic identity and reductions, `Fin 0`, `Fin 1`, the zero ring
`ZMod 1`, and characteristic two over `ZMod 2`. Over `ℤ`, the trace-zero
elementary matrices `E₀₁`, `E₁₀` yield mixed diagonal `diag(1, -1)`;
reversing their order yields `diag(-1, 1)`. The characteristic-two diagonal
coefficient remains nonzero although the two signs coincide. These checks
use the actual native factors, SL kernel and readback.

Use this repository's [`lean-toolchain`](../lean-toolchain),
[`lakefile.toml`](../lakefile.toml) and
[`lake-manifest.json`](../lake-manifest.json) for Lean `v4.34.0-rc2` and the
resolved mathlib revision. From the repository root:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups.DualNumberMixedSLCommutator
lake env lean -DwarningAsError=true tests/DualNumberMixedSLCommutatorClient.lean
```

## Dependencies and credits

This refinement reuses the native mixed-GL identity and mathlib's special
linear group, trace-zero Lie algebra and whole-group `toGL` injection.
Formal Frontier Agents developed the original mixed-GL and mixed-SL
constructions, retained their genuine source-expression credit and adapted
them into this library. The Apache-2.0/SPDX collective-author notices remain
on the code. No incubator or source research dependency is needed to use it;
its ordered identity does not claim a global scheme tangent functor,
arbitrary-GL determinant-one refinement or source correspondence.
