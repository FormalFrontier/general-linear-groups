# General linear groups

A Lean library for finite and stable general linear groups: elementary and relative
matrices, unit-pivot diagonalization, paths and SL neighborhoods, block
factorizations, ideal quotients, trace, stabilization, Steinberg groups and
dual-number GL/SL kernels. Core ring results allow noncommutative coefficients;
dual-number and determinant results use commutative rings. Indices are finite
and decidable where required. The [module guides](docs/README.md) detail the
statements, examples and limitations; [mathlib](https://github.com/leanprover-community/mathlib4)
supplies foundational APIs.

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

- **Stable general linear and elementary groups.** Initial-segment stabilization
  defines a coherent system of finite general linear groups over any `Semiring`,
  whose noncommutative direct limit has finite representatives, an eventual
  equality criterion, compatible lifts and coefficient maps. Over any `Ring`, the
  directed union of finite elementary images is the stable commutator subgroup;
  it is perfect in its own right and normal in stable general linear groups.
  Its quotient is canonically the abelianization, naturally under coefficient
  maps. No finite ambient elementary normality or commutativity hypothesis is needed.
  [Stable general linear group](GeneralLinearGroups/StableGeneralLinear.lean),
  [stable elementary group](GeneralLinearGroups/StableElementary.lean),
  [boundary and quotient clients](tests/GeneralLinearGroupsTests/StableElementaryClient.lean).

- **Stable determinant.** Over a commutative ring, finite determinants induce
  homomorphisms on stable general linear groups, their elementary quotient and
  their abelianization. Rank-one units provide determinant sections; the
  elementary subgroup lies in the determinant kernel, without a claimed
  equality. The abelian elementary quotient splits as the product of its
  determinant kernel and the units, naturally under coefficient maps; this
  does not assert a product splitting of stable general linear groups.
  The rank-one map itself is defined over any semiring.
  [Determinant and rank-one maps](GeneralLinearGroups/StableDeterminant.lean),
  [integer and boundary examples](tests/GeneralLinearGroupsTests/StableDeterminantClient.lean).

- **Zero-product elementary stabilization.** For rectangular `A`, `B` over any
  `Ring` with `B * A = 0`, the unit `1 + A * B` has inverse `1 - A * B`.
  Stabilizing by the identity on the other block gives exactly the ordered
  commutator of the upper shear of `A` and lower shear of `B`, hence an
  elementary unit. Both index types may be empty.
  [Construction and factorization](GeneralLinearGroups/ZeroProductStabilization.lean),
  [integer and boundary examples](tests/GeneralLinearGroupsTests/ZeroProductStabilizationClient.lean).

- **Rectangular unit switch.** Over any `Ring`, for independently finite,
  decidable index types, a unit `g = 1 + A * B` determines a unit
  `h = 1 + B * A` with inverse `1 - B * g⁻¹ * A`. Its diagonal pair
  `diag(g, h⁻¹)` is the ordered product
  `U(A) L(B) U(-(g⁻¹ * A)) L(-(B * g))`, hence elementary.
  Empty blocks and the zero ring are allowed; `B * A = 0` recovers the
  zero-product stabilization commutator above.
  [Construction and factorization](GeneralLinearGroups/RectangularUnitSwitch.lean),
  [integer and boundary examples](tests/GeneralLinearGroupsTests/RectangularUnitSwitchClient.lean).

- **Ring Schur reduction.** For independently finite, decidable block indices
  over any `Ring`, an invertible northwest block `A` makes
  `[[A, B], [C, D]]` a unit exactly when the ordered residual
  `D - C * ⅟A * B` is a unit. Given a unit residual, the corresponding block
  unit has an explicit ordered inverse; homomorphisms killing the elementary
  subgroup see only the diagonal pivot and residual, with no condition on
  the target group. Empty blocks and the zero ring are included.
  [Construction and criterion](GeneralLinearGroups/SchurReduction.lean),
  [noncommutative and boundary clients](tests/GeneralLinearGroupsTests/SchurReductionClient.lean).

- **Unit-pivot reduction and elementary diagonals.** Over any `CommRing`,
  unit ordered leading minors permit two-sided elementary diagonalization;
  a product-one diagonal is elementary, and the unit-pivot, determinant-one
  criterion puts a finite GL unit in `E`. These are not a general `SL = E`
  theorem; the minor hypothesis is stronger than nonvanishing.
  [Unit-pivot guide](docs/UnitPivotDiagonalization.md),
  [diagonal guide](docs/ElementaryDiagonal.md).

- **Elementary paths and SL neighborhoods.** Over a topological ring,
  elementary GL units vary continuously with coefficients, even when the
  coefficient ring is noncommutative. Path-connected coefficients make the
  elementary subgroup path connected. For commutative coefficients, an open
  scalar-unit locus makes its native SL comap open and closed; additionally
  path-connected coefficients identify it with the identity path component.
  [Paths guide](docs/ElementaryPaths.md),
  [neighborhood guide](docs/ElementaryNeighborhood.md).

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

## Using the library

Add the library in your `lakefile.toml`:

```toml
[[require]]
name = "general-linear-groups"
git = "https://github.com/FormalFrontier/general-linear-groups.git"
rev = "main"
```

GitHub `main` contains only reviewed releases, so Lake resolves the latest release when
you first add or update the dependency. `lake-manifest.json` locks that resolved commit
until you update again. To pin a specific release, replace `main` with a commit from
its history.

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

The [`PublicAPIClient`](tests/GeneralLinearGroupsTests/PublicAPIClient.lean) exercises this law using
an ordinary import; other clients exercise the interfaces and edge cases.

## Building

Install [elan](https://github.com/leanprover/elan) and use this repository's
`lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`), `lakefile.toml` and
`lake-manifest.json`. The dependency graph pins mathlib to
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. From a clean checkout,
fetch the matching precompiled mathlib cache before building:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```

The default `lake build` selects the aggregate library and the test root, which
imports all 24 client modules. Do not replace the cache fetch with a full
mathlib source build.

## Contents

Import the [aggregate root](GeneralLinearGroups.lean) to publicly access its
35 subject modules, or import a [specific subject module](GeneralLinearGroups/)
to keep a narrower dependency surface. Its `public import` declarations expose
the corresponding module APIs to downstream ordinary imports. The default
build also checks 24 clients under `tests/GeneralLinearGroupsTests/`, including examples at
empty and singleton index types, over noncommutative rings and the zero ring;
client-only helpers are not promises of the library API.

| Subject | Start here | Important boundary |
| --- | --- | --- |
| Elementary blocks and reindexing | [Elementary matrices](docs/ElementaryMatrices.md), [commutators](docs/ElementaryCommutators.md) | Ring-only units; no `SL = E` |
| Unit pivots and diagonal units | [Unit-pivot diagonalization](docs/UnitPivotDiagonalization.md), [product-one diagonals](docs/ElementaryDiagonal.md) | `CommRing`; all positive-order leading minors must be units for reduction |
| Paths and SL neighborhoods | [Elementary paths](docs/ElementaryPaths.md), [finite SL neighborhoods](docs/ElementaryNeighborhood.md) | Path-connected coefficients and open scalar units are distinct hypotheses |
| Relative groups and doubled identities | [Relative elementary](docs/RelativeElementary.md), [Whitehead](docs/RelativeWhitehead.md), [consequences](docs/RelativeWhiteheadConsequences.md) | Normal closure inside `E`; arbitrary-GL conjugation only after doubling |
| Stable general linear and elementary groups | [Stable GL](GeneralLinearGroups/StableGeneralLinear.lean), [stable elementary](GeneralLinearGroups/StableElementary.lean) | Semiring-direct-limit `GL`; over rings, elementary equals the stable commutator, with an abelian quotient but no public `K₁` construction |
| Stable determinant and rank-one units | [Stable determinant](GeneralLinearGroups/StableDeterminant.lean), [clients](tests/GeneralLinearGroupsTests/StableDeterminantClient.lean) | Rank-one maps over semirings; over commutative rings, the abelian elementary quotient is its determinant kernel times units, with no kernel-vanishing claim |
| Finite stabilization and rectangular blocks | [Stabilization](docs/ElementaryStabilization.md), [rectangular blocks](docs/RectangularBlockUnits.md), [rectangular unit switch](GeneralLinearGroups/RectangularUnitSwitch.lean), [zero-product units](GeneralLinearGroups/ZeroProductStabilization.lean) | Semiring stabilization is a *monoid hom on units*; the unit switch requires a `Ring` and `g = 1 + A * B`, but not `B * A = 0` |
| Presented elementary group | [Steinberg](docs/FiniteRankSteinberg.md) | Finite rank does not imply finite presentation over an arbitrary ring |
| Nil and quasi-regular ideal quotients | [QuasiregularIdeal](GeneralLinearGroups/QuasiregularIdeal.lean), [QuasiregularQuotient](GeneralLinearGroups/QuasiregularQuotient.lean), [NonUnitalQuasiregular](GeneralLinearGroups/NonUnitalQuasiregular.lean) | Extra ideal hypothesis is needed to lift arbitrary quotient units |
| Additive trace quotient | [MatrixTrace](GeneralLinearGroups/MatrixTrace.lean), [AdditiveCommutator](GeneralLinearGroups/AdditiveCommutator.lean) | An inverse needs a chosen index; no ring quotient or `K₀` theorem |
| Native first-order and mixed dual numbers | [Kernel guide](docs/DualNumberKernels.md), [adjoint guide](docs/DualNumberKernelAdjoint.md), [mixed GL guide](docs/DualNumberMixedCommutator.md), [mixed SL guide](docs/DualNumberMixedSLCommutator.md) | `CommRing`, finite decidable indices; SL requires individual trace-zero factors |

Additional [nonunital](GeneralLinearGroups/NonUnitalNilpotent.lean),
[local quotient](GeneralLinearGroups/LocalQuotient.lean) and
[unital comparison](GeneralLinearGroups/UnitalComparison.lean) modules have
their own docstrings and statements.

## Conventions and limitations

Matrix index and coefficient types may live in independent universes. Empty
indices, singleton indices and zero rings are not silently excluded; theorems
requiring a chosen index state it. A unit leading minor is stronger than a
nonzero minor, even over `ZMod 6`. Ring-level elementary paths allow
noncommutative coefficients; subgroup path connectedness separately needs
path-connected coefficients. The finite SL comap is open and closed when
scalar units form an open locus; identifying its identity path component also
needs path-connected coefficients. There is no continuous factor selection,
general `SL = E`, global `GL` connectivity or quantitative neighborhood.
There is **no** claimed stable `K₁` identification, excision,
`K₂`, source-complete K-theory, ambient relative normality or universal
triangular-invertibility converse.

The [historical API snapshot](docs/API.md) covers only 128 authored public
entries and 16 module records, with source links on thirteen unchanged
producers. It is **not** an exhaustive reference for the current
default graph. Use the Lean sources, guides and import clients for other results.

## References

- Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*
  (2013), Exercises I.1.10–I.1.12 and Chapter II, §2. Selected constructions
  draw on its mathematics, not a complete formalization of the book.
- [mathlib](https://github.com/leanprover-community/mathlib4) provides the
  foundational matrix, group, ideal, topology and dual-number interfaces.

## Credits and license

Authors: Formal Frontier Agents. Prism contributed original general-linear,
ideal and trace-related proof expression and API documentation; Lattice
contributed native dual-number kernel and adjoint integration; Anchor's
Markdown documentation adapter informed the historical API reference.
Other Formal Frontier Agents authored the trace, elementary, relative,
stabilization, Steinberg, dual-number, unit-pivot, elementary-path, diagonal
and neighborhood proofs and clients; additional agents adapted their
examples and mathematical guides. These original project contributions
are distinct from Weibel's mathematical motivation and mathlib's third-party
work, whose authorship and notices remain with mathlib. AI agents developed
the Lean code and documentation with compiler feedback and independent agent
review; no human mathematical review is claimed. Licensed under
[Apache-2.0](LICENSE); no copyright holder is inferred from the author credit.
