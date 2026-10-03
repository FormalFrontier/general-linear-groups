# Adjoint action on native dual-number matrix kernels

Import `GeneralLinearGroups.DualNumberKernelAdjoint`. Its public declarations
are in `Matrix.DualNumberKernels`, over an arbitrary commutative ring `R` and a
finite index type `n` with decidable equality (independent universes). No
nonemptiness, nontriviality, characteristic or invertibility-of-rank condition is
needed. This module extends, rather than replaces, the native reduction kernels
of `GeneralLinearGroups.DualNumberKernels`.

The convention throughout is **left conjugation**: `g * X * g⁻¹`, not the
pre-existing left-multiplication action of `GL n R` on matrices. In particular:

* `slAdjoint g` restricts mathlib's matrix `lieConj` to its existing
  `LieAlgebra.SpecialLinear.sl n R` using trace invariance in both directions.
  Its result is a fixed-ring `R`-linear **Lie equivalence**; `slAdjoint_val`
  displays its underlying matrix.
* `glKerEquiv_conj h X` states the commuting square between **actual**
  `MulAut.conjNormal h` on `(glReduce R n).ker` and the adjoint action of
  `glReduce R n h` on `X`. It applies to every native unit
  `h : Matrix.GeneralLinearGroup n (DualNumber R)`, not just a constant lift.
  `glReadback_conj` gives the corresponding formula for every kernel element.
  The proof uses the actual inverse identity `h * h⁻¹ = 1`: the infinitesimal
  coefficients of `h` and `h⁻¹` cancel, leaving only their reduced matrices.
* `slToGL_conj` says native conjugation in `SL n (DualNumber R)` respects
  `slToGL`; `slReadback_conj` identifies its trace-zero readback with
  `slAdjoint` of the reduced conjugator. The acting group on the native SL
  kernel is **SL**, not an implicitly substituted GL group.
* `glKerMap_conj f h k` states a genuine change-of-coefficients square for
  `f : R →+* S` (independent universe): native conjugation commutes with the
  existing `glKerMap f` and `Matrix.GeneralLinearGroup.map
  (DualNumber.mapRingHom f)`. An arbitrary coefficient map is not asserted to
  be `R`-linear. Existing `slKerMap`, `slMap`, `slToGL_natural`, and readback
  naturality remain the corresponding base API.

The ordinary-import client
`tests/GeneralLinearGroupsTests/DualNumberKernelAdjointClient.lean` checks `Fin 0`,
`Fin 1` and the zero ring `ZMod 1`; it also fixes the nonzero, trace-zero
identity at `Fin 2` over `ZMod 2`. Over `ℤ`, conjugating `E₁₀` by the
upper-right shear yields entry `(0,0) = 1` (and so detects conjugation order).
The client constructs an explicitly nonconstant dual-number unit as a constant
shear times `1 + εE₀₁`, verifies its reduction is the shear and checks the
same orientation on its actual native GL kernel. A pure nonconstant kernel
conjugator acts trivially on the first-order kernel; this does **not** extract
the generally nonzero matrix Lie bracket from its abelian group commutators.
No new global matrix action, tangent bridge, scheme statement, or source
correspondence is supplied here.

## Dependencies and credits

This module builds on `GeneralLinearGroups.DualNumberKernels` and mathlib's
`Matrix.lieConj`, trace invariance, `LieEquiv.ofSubalgebras`, unit inverses and
`MulAut.conjNormal`. Its original native-kernel and adjoint developments and
their adaptation into this library were contributed by Formal Frontier Agents;
Lattice coordinated the native-kernel and adjoint integration. The code's
Apache-2.0/SPDX and collective-author notices are retained, and no source
repository is a build dependency. This guide makes no source-coverage or
scheme-tangent assertion.

The project pins Lean `v4.34.0-rc2` and mathlib in its
[`lean-toolchain`](../lean-toolchain), [`lakefile.toml`](../lakefile.toml) and
[`lake-manifest.json`](../lake-manifest.json). The public root imports this
producer and the default test target includes its ordinary-import client.
Fetch the matching mathlib cache before a build:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```
