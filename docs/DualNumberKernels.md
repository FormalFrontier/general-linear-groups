# Native finite GL/SL dual-number identity fibers

Import `GeneralLinearGroups.DualNumberKernels`. The definitions and theorems below
are in `Matrix.DualNumberKernels`, except `DualNumber.fstRingHom` and
`DualNumber.mapRingHom`. The module imports **mathlib only**. Let `R : Type u` be a
commutative ring and `n : Type v` a finite type with decidable equality; no
`Nonempty n`, `Nontrivial R`, characteristic, or cardinal-invertibility hypothesis
is needed. The same index type is used before and after a change of coefficients;
the coefficient rings may occupy independent universes.

`glReduce R n`, `slReduce R n`, and `unitsReduce R` are the native
`Matrix.GeneralLinearGroup.map`, `Matrix.SpecialLinearGroup.map`, and `Units.map`
under `(TrivSqZeroExt.fstHom R R R).toRingHom`. Their **actual `MonoidHom.ker`**
subgroups are the identity fibers, not the additive kernel ideal of the ring
projection. The multiplicative equivalences

* `glKerEquiv : Multiplicative (Matrix n n R) ≃* (glReduce R n).ker`,
* `unitsKerEquiv : Multiplicative R ≃* (unitsReduce R).ker`, and
* `slKerEquiv : Multiplicative (LieAlgebra.SpecialLinear.sl n R) ≃* (slReduce R n).ker`

send `X` to the native unit/group element with entries `(δᵢⱼ, Xᵢⱼ)`, and
`r` to the unit `(1, r)`. The inverse of this GL unit has second-component
matrix `-X`. The existing `LieAlgebra.SpecialLinear.sl` carrier supplies trace
zero; no replacement Lie subalgebra or Lie-bracket compatibility is asserted.
`liftMatrix_fst`, `liftMatrix_snd`, `glKernel_fst`, `glReadback_apply`,
`unitsKernel_fst`, `unitsKerEquiv_snd`, `slKernel_fst`, `slReadback_apply`,
and the equivalence readback lemmas expose both components.

`detKer : (glReduce R n).ker →* (unitsReduce R).ker` restricts the *native*
GL determinant. `detKer_glKerEquiv` is the commuting square with `Matrix.trace`
and `unitsKerEquiv`; `det_liftMatrix` gives the coefficient identity
`det(1 + εX) = (1, trace X)`. Its proof applies mathlib's
`Matrix.det_one_add_smul` **over the dual numbers** and then `ε² = 0`.
`slToGL : (slReduce R n).ker →* (glReduce R n).ker` and
`slToGL_slKerEquiv` give the inclusion square with the existing trace-zero
carrier. At `n = Fin 0` the GL and SL fibers are trivial but the scalar-units
fiber over `ℤ` is not: no determinant-surjectivity claim is made for rank zero.

For `f : R →+* S`, `DualNumber.mapRingHom f` sends `(a,b)` to `(f a,f b)`;
unlike pinned mathlib's `TrivSqZeroExt.map`, it changes the **base ring**.
Its first and second readbacks and identity/composition laws are explicit.
`glKerMap f`, `unitsKerMap f`, and `slKerMap f` are induced native-kernel maps,
with identity/composition laws. `glKerMap_glKerEquiv`,
`unitsKerMap_unitsKerEquiv`, and `slKerMap_slKerEquiv` give their naturality
squares; `slMap f` maps the existing trace-zero carrier entrywise.
`detKer_natural`, `slToGL_natural`, and the readback-naturality lemmas complete
the commuting diagrams. The determinant/trace maps use mathlib's native
coefficient naturality. An arbitrary ring hom `f` is **not** claimed to be
`R`-linear.

Compile `tests/DualNumberKernelsClient.lean` directly for clients at
`Fin 0`, `Fin 1`, `ZMod 1` (the zero ring), and `Fin 2` over both
`ℤ` and `ZMod 2`, including the `ℤ → ZMod 2` naturality square. The off-diagonal
`E₀₁` yields a nonidentity native SL-kernel element; over `ZMod 2`, the nonzero
identity matrix has trace zero and yields another. `glKernel_mul_comm` and
`slKernel_mul_comm` prove first-order fiber products commute, while the
client proves `⁅E₀₁, E₁₀⁆₀₀ ≠ 0` using mathlib's existing Lie bracket.
Thus the **ordinary group commutator here is not the matrix Lie bracket**.
Scheme-point transport, tangent functors, higher-order infinitesimals,
differentials, global dimension, general Lie theory, and source correspondence
are outside this standalone API.

## Provenance and status

Copyright notice: SPDX-License-Identifier: Apache-2.0, matching the repository
and the imported mathlib modules. Underlying dual numbers/
`TrivSqZeroExt` are from mathlib (notably Eric Wieser's
`Mathlib/Algebra/DualNumber.lean`); this implementation reuses mathlib's native
GL/SL group definitions, trace-zero `sl`, and quadratic determinant remainder.
The original kernel API investigation is credited to worker-b Task
`hive-request-fcd501500f0c5ec813d46a71e1ed0b0d7555a0fd`,
UID `028a7064-28e0-4e93-a917-c5ac60a025d1`. The original kernel
implementation is credited to worker-b Task
`hive-request-1df68ed8f5e4bab1a07522b5ee97f5a4e124e028`,
UID `a1cde5e5-a84f-4b15-b86e-c1d59cf1e533`. The accepted original
implementation was transferred to a then-**UNACCEPTED destination candidate**
by worker-b Task `hive-request-f1f0750c049a6341076625a8c7823dab83dad5d9`,
UID `704cc043-3e91-4fd0-984a-4723758a7cc5`. The source/registration review,
native CI462 registered build and private-inclusive standard-axiom audit, and
Lattice's PR55 code acceptance and integration subsequently completed. This
guide's release-readiness text does not itself accept or publish the new
internal/public release; independent release review and verified publication
remain separate. This guide makes no source coverage or scheme-point claim.
