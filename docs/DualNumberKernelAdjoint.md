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
`tests/DualNumberKernelAdjointClient.lean` checks `Fin 0`,
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

## Dependencies, provenance and acceptance

This module imports the kernel producer and mathlib; neither module depends
on a source repository. The destination project pins Lean `v4.34.0-rc2`
and mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`.
The original six-leaf transfer did not change any pins, roots, metadata,
manifest or shared registration; subsequent PR55 registration added the two
producers to the public root and their two clients to the default build.
Its proofs reuse mathlib's `Matrix.lieConj`, trace invariance,
`LieEquiv.ofSubalgebras`, `MulAut.conjNormal`, unit inversion, and the existing
native kernel equivalences and coefficient maps. All new code is original;
mathlib and this repository use Apache-2.0, with the code's SPDX notices
preserved and no copied source material.

The original kernel producer credits worker-b Task
`hive-request-1df68ed8f5e4bab1a07522b5ee97f5a4e124e028` (UID
`a1cde5e5-a84f-4b15-b86e-c1d59cf1e533`); earlier kernel research credits
worker-b Task `hive-request-fcd501500f0c5ec813d46a71e1ed0b0d7555a0fd`
(UID `028a7064-28e0-4e93-a917-c5ac60a025d1`). The earlier adjoint investigation
credits worker-b Task `hive-request-00bab16826ab0ca04714504bcb66c30d2fa5991a`
(UID `f709819b-92f5-48e1-b5a4-eb184d4c5a6c`). This implementation is by
worker-b Task `hive-request-083e63349244c927c6fd7ddd1ceb7b01a722e06c`
(UID `bec147d0-40ae-43fd-95d5-5b28c2bf2ed6`). The accepted original
implementation was transferred to a then-**UNACCEPTED destination candidate**
by worker-b Task `hive-request-f1f0750c049a6341076625a8c7823dab83dad5d9`,
UID `704cc043-3e91-4fd0-984a-4723758a7cc5`. Its focused author checks did
not replace fresh author-distinct transfer/assembly review, registration on
the accepted base or a complete registered build and private-inclusive
transitive standard-axiom audit. Those gates subsequently completed through
native CI462, independent PR55 review and Lattice's protected integration;
independent release review and verified publication remain separate. It makes
no source-coverage claim.
