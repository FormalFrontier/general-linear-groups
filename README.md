# General linear groups

A reusable Lean library for finite general linear groups over rings: elementary
matrices, ordered block factorizations, congruence and quasi-regular ideals,
additive matrix trace, finite stabilization, a Steinberg presentation, and
native dual-number GL/SL kernels and commutators. The core ring results allow
noncommutative coefficients; dual-number and determinant results use
commutative rings. Matrix indices are finite with decidable equality where
required. The [module guide index](docs/README.md) leads to detailed statements,
worked examples and limitations; [mathlib](https://github.com/leanprover-community/mathlib4)
supplies the underlying matrix, group, ideal and dual-number APIs.

## Headline results

- **Whitehead factorization and doubled lifting.** Over any `Ring`, the
  block diagonal `diag(g, g⁻¹)` of a unit is elementary. A surjective ring
  homomorphism lifts this *doubled* block as a unit; it need not lift the
  original same-rank unit. For separately finite block indices, explicitly
  supplied diagonal units also give rectangular upper-triangular units with
  ordered inverse block `-(A⁻¹ * B * D⁻¹)`.
  [Factorization](GeneralLinearGroups/Whitehead.lean),
  [doubled lift](GeneralLinearGroups/Whitehead.lean#L164),
  [elementary membership](GeneralLinearGroups/ElementaryWhitehead.lean#L117),
  [rectangular guide](docs/RectangularBlockUnits.md).

- **Lifting modulo quasi-regular ideals.** For a two-sided ideal, its
  unitization general linear group identifies with the congruence kernel;
  quasi-regularity of *every* ideal element additionally makes the quotient
  GL map surjective. The Jacobson radical is the greatest quasi-regular
  ideal, and pointwise nil ideals provide examples without a shared nilpotence
  exponent.
  [Kernel equivalence](GeneralLinearGroups/CongruenceSubgroup.lean#L292),
  [quotient lifting](GeneralLinearGroups/QuasiregularQuotient.lean#L139),
  [ideal characterization](GeneralLinearGroups/QuasiregularIdeal.lean#L207).

- **Trace modulo additive commutators.** For a chosen index `p : n`,
  trace gives an additive equivalence from square matrices modulo additive
  commutators to the coefficient ring modulo additive commutators; its inverse
  inserts a scalar in the `p,p` corner. The forward map also works at empty
  rank. These are *additive groups*, not quotient rings or a `K₀` descent.
  [Equivalence](GeneralLinearGroups/MatrixTrace.lean#L166),
  [forward map](GeneralLinearGroups/MatrixTrace.lean#L63).

- **Finite elementary and relative structure.** Off-diagonal elementary
  units generate `E`; ordered commutator laws prove that `E` is perfect at
  rank at least three. A two-sided ideal defines the relative normal closure
  *inside `E`*, not a claimed same-rank normal subgroup of ambient `GL`.
  Congruence units become relatively elementary after Whitehead doubling;
  stabilization preserves elementary, relative and congruence inclusions.
  [Perfectness](GeneralLinearGroups/ElementaryCommutator.lean#L80),
  [relative subgroup](GeneralLinearGroups/RelativeElementary.lean#L98),
  [relative Whitehead](GeneralLinearGroups/RelativeWhitehead.lean#L134),
  [guides](docs/README.md).

- **A Steinberg presentation and universal maps.** Over any `Ring`, for an
  arbitrary index type, symbols satisfy precisely the additive, disjoint-root
  and ordered-composable-root relations, and compatible maps extend uniquely.
  Finite decidable indices additionally give a surjection onto `E`, not
  onto all of `GL`. The reverse relation has coefficient `-(b * a)`; no
  opposite-root, central-kernel or `K₂` theorem is claimed.
  [Universal lift](GeneralLinearGroups/Steinberg.lean#L121),
  [onto-`E` map](GeneralLinearGroups/Steinberg.lean#L206),
  [presentation guide](docs/FiniteRankSteinberg.md).

- **First-order dual-number kernels and conjugation.** Over any `CommRing`,
  the *multiplicative* native GL, SL and scalar-unit reduction identity fibers
  identify with additive matrices, trace-zero matrices and scalars. Native
  determinant corresponds to trace; arbitrary ring-hom coefficient maps
  commute with these constructions without being implicitly `R`-linear.
  Actual native-unit **left conjugation** corresponds to `g * X * g⁻¹`,
  even for nonconstant dual-number units; the SL-kernel action uses SL
  conjugators. First-order fiber groups are abelian, so their commutator is
  not the generally nonzero matrix Lie bracket.
  [Kernel equivalences](GeneralLinearGroups/DualNumberKernels.lean#L132),
  [determinant/trace](GeneralLinearGroups/DualNumberKernels.lean#L264),
  [adjoint guide](docs/DualNumberKernelAdjoint.md).

- **Mixed dual-number GL and SL commutators.** For finite matrices over a
  `CommRing`, actual units over iterated dual numbers satisfy the ordered
  identity `[1 + εX, 1 + ηY] = 1 + εη(XY - YX)` with full outer-kernel
  readback. When *each input* is trace zero, actual special-linear factors
  yield the analogous native SL identity and trace-zero readback. The
  ε-factor reduces to the inner lift `liftGL X` (in SL, `liftSL X`), usually
  not `1`: this is not a bracket of two elements of the abelian first-order
  outer kernel, nor a global Lie- or scheme-tangent theorem.
  [GL identity](GeneralLinearGroups/DualNumberMixedCommutator.lean#L155),
  [SL identity](GeneralLinearGroups/DualNumberMixedSLCommutator.lean#L93),
  [GL guide](docs/DualNumberMixedCommutator.md),
  [SL guide](docs/DualNumberMixedSLCommutator.md).

## Modules and scope

Import the [aggregate root](GeneralLinearGroups.lean) to publicly access its
26 subject modules, or import a [specific subject module](GeneralLinearGroups/)
to keep a narrower dependency surface. Its `public import` declarations expose
the corresponding module APIs to downstream ordinary imports. The default
build also checks fourteen client roots under `tests/`, including examples at
empty and singleton index types, over noncommutative rings and the zero ring;
client-only helpers are not promises of the library API.

| Subject | Start here | Important boundary |
| --- | --- | --- |
| Elementary blocks and reindexing | [Elementary matrices](docs/ElementaryMatrices.md), [commutators](docs/ElementaryCommutators.md) | Ring-only units; no `SL = E` |
| Relative groups and doubled identities | [Relative elementary](docs/RelativeElementary.md), [Whitehead](docs/RelativeWhitehead.md), [consequences](docs/RelativeWhiteheadConsequences.md) | Normal closure inside `E`; arbitrary-GL conjugation only after doubling |
| Finite stabilization and rectangular blocks | [Stabilization](docs/ElementaryStabilization.md), [rectangular blocks](docs/RectangularBlockUnits.md) | Semiring stabilization is a *monoid hom on units*, not a matrix-ring hom or a surjectivity theorem |
| Presented elementary group | [Steinberg](docs/FiniteRankSteinberg.md) | Finite rank does not imply finite presentation over an arbitrary ring |
| Nil and quasi-regular ideal quotients | [QuasiregularIdeal](GeneralLinearGroups/QuasiregularIdeal.lean), [QuasiregularQuotient](GeneralLinearGroups/QuasiregularQuotient.lean), [NonUnitalQuasiregular](GeneralLinearGroups/NonUnitalQuasiregular.lean) | Extra ideal hypothesis is needed to lift arbitrary quotient units |
| Additive trace quotient | [MatrixTrace](GeneralLinearGroups/MatrixTrace.lean), [AdditiveCommutator](GeneralLinearGroups/AdditiveCommutator.lean) | An inverse needs a chosen index; no ring quotient or `K₀` theorem |
| Native first-order and mixed dual numbers | [Kernel guide](docs/DualNumberKernels.md), [adjoint guide](docs/DualNumberKernelAdjoint.md), [mixed GL guide](docs/DualNumberMixedCommutator.md), [mixed SL guide](docs/DualNumberMixedSLCommutator.md) | `CommRing`, finite decidable indices; SL requires individual trace-zero factors |

Additional [nonunital](GeneralLinearGroups/NonUnitalNilpotent.lean),
[local quotient](GeneralLinearGroups/LocalQuotient.lean) and
[unital comparison](GeneralLinearGroups/UnitalComparison.lean) modules retain
their own docstrings and statements. Matrix index and coefficient types may
live in independent universes. Empty indices, singleton indices and zero
rings are not silently excluded; theorems requiring a chosen index state it.
There is **no** claimed stable/direct-limit `GL`, stable `K₁`, excision,
`K₂`, source-complete K-theory, ambient relative normality or universal
triangular-invertibility converse.

The [historical API snapshot](docs/API.md) covers only 128 authored public
entries and 16 module records from an earlier library stage, with source links
on thirteen unchanged producer modules. It is **not** an exhaustive reference
for the present 41-module default graph or subsequent results. The current
Lean sources, subject guides and ordinary-import clients describe those
results; the snapshot has not been regenerated for this revision.

## Use and build

For example, a surjective ring map lifts the *doubled* matrix:

```lean
module
import GeneralLinearGroups

open Matrix Matrix.GeneralLinearGroup

example {R S n : Type*} [Ring R] [Ring S] [Fintype n] [DecidableEq n]
    (f : R →+* S) (hf : Function.Surjective f) (g : GL n S) :
    mapRingHom f (liftBlockDiagonal f hf g) = blockDiagonalUnit g :=
  mapRingHom_liftBlockDiagonal f hf g
```

The existing [`PublicAPIClient`](tests/PublicAPIClient.lean) exercises this
law using an ordinary import, and the other clients exercise the advertised
interfaces and edge cases. Install [elan](https://github.com/leanprover/elan)
and use this repository's `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`),
`lakefile.toml` and `lake-manifest.json`. The nine-package dependency graph
pins mathlib to `e37d88a26f3791ed5a93daa1f949af1021b8d103`. From a clean
checkout with normal network access, **fetch the matching precompiled mathlib
cache successfully before building**:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```

The default `lake build` selects both of those maintained targets (the
aggregate library and fourteen client roots). Do not replace the cache-fetch
step with a full mathlib source rebuild. When using the library as a Lake
dependency, pin an actual reviewed official revision under the same compatible
Lean/mathlib dependency graph; a development commit or a source-repository
experiment is not an official published dependency.

### Expected build cost (historical observation)

In a September 27, 2026 Linux run for a 41-module, fourteen-client mixed-SL
snapshot (Lean `4.34.0-rc2`, pinned mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103`), fetching the matching
precompiled mathlib cache took about **41 seconds**, verifying cached Mathlib
without rebuilding it took about **6 seconds**, and building both maintained
targets (`GeneralLinearGroups` and `GeneralLinearGroupsTests`) took about
**49.5 seconds**. These are distinct phases, not a from-source dependency
build. The full setup, build and separate private-inclusive standard-axiom
audit took about **6 minutes 39 seconds**, not just the project build time.

These are historical host-, cache- and network-dependent measurements, not
timings newly measured for this revision or a guarantee on another machine.
Allow for toolchain setup, dependency/cache disk space and network conditions;
memory-limited hosts may need bounded build parallelism. Peak CPU and RAM
were not measured, so no minimum memory requirement follows.

## License and credits

The library is released under [Apache-2.0](LICENSE); source files carry
authentic license and `Authors: Formal Frontier Agents` notices. Formal
Frontier Agents produced and revised the mathematical Lean code, clients and
guides with compiler feedback and independent **agent** review. Prism
contributed the general-linear/ideal and source-probe developments and
adapted the API documentation; Lattice led native-kernel/adjoint integration;
Anchor contributed the Markdown documentation adapter that informed the
historical API reference. Distinct pooled contributors developed trace,
elementary/relative/stabilization, Steinberg and native dual-number results;
the collective author credit includes them without treating one agent as all
authors. The pinned mathlib contributors retain credit and license notices in
the dependency; in particular this repository does not claim mathlib's
presented-group, trace-zero Lie algebra or matrix foundations as original.

Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory* (2013),
motivates selected constructions, but this repository does **not** claim a
complete formalization of that book or copy its PDF, scans or quotations.
Original source-research expression informed some developments; the public
metadata and guides distinguish that contribution from bibliographic
motivation. Source-passage correspondence and incomplete coverage live in
the source repository, not in this reusable library. No source-author
endorsement, human mathematical review, copyright ownership beyond what
can be established, or blanket third-party redistribution permission is
asserted by the collective credit or by AI authorship.
