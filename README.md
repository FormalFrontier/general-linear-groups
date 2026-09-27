# general-linear-groups

Reusable Lean theory of general linear groups, block factorizations, and stability.

The initial development unit constructs the elementary block units over an
arbitrary ring, proves the Whitehead factorization of
`diag(g, g⁻¹)`, and uses it to lift this block-diagonal unit through a
surjective ring homomorphism without claiming that the original general linear
group map is surjective.

The elementary-matrix layer supplies off-diagonal GL units and their generated
subgroup for arbitrary, possibly noncommutative rings. Its upper/lower/signed-swap
and doubled block-diagonal membership results reuse that existing Whitehead
factorization. See the [elementary-matrix guide](docs/ElementaryMatrices.md) for
imports, hypotheses, signs, products and degenerate cases. No `SL = E`,
normality or stable `K₁` result follows.

The finite commutator/relative layer proves ordered elementary commutator
relations and perfectness at rank at least three; defines the normal closure
of ideal-coefficient generators **inside** the elementary subgroup; and
gives compatible coefficient maps, doubled relative Whitehead factorization,
semiring-unit stabilization and doubled conjugation/commutator membership.
See the five [finite elementary and relative guides](docs/README.md) for
precise hypotheses, signs, imports and private clients. These APIs assert
neither same-rank ambient normality nor stable `K₁` or full source coverage.

The rectangular-block layer builds upper unipotent and upper triangular
general-linear-group units for independent finite indices, including empty
blocks, over potentially noncommutative rings. It reuses finite stabilization
and reindexing, proves elementary membership of the upper off-block factor,
and retains the ordered diagonal factorizations and inverse. Its diagonal
blocks are explicitly supplied as units. See the
[rectangular-block guide](docs/RectangularBlockUnits.md) for the exact APIs,
signs, hypotheses and unequal-rank private client.

The reindexing layer transports general linear groups along equivalences of
finite index types, with identity, composition, inverse and coefficient-map
naturality laws. It keeps fixed-cardinality notation as an external
specialization of the generic API.

The quasi-regular-ideal layer characterizes two-sided ideals whose elements are
all quasi-regular. In particular, it proves that a globally quantified
right-quasi-inverse condition already supplies two-sided quasi-inverses, without
commutativity or direct-finiteness assumptions, and identifies the Jacobson
radical as the greatest quasi-regular two-sided ideal. This is reusable
groundwork for later quotient-lifting results.

The nil-ideal layer uses the pointwise definition: every element is nilpotent,
with no common exponent required for the ideal. It proves monotonicity, the
zero-ideal case, quasi-regularity, and containment in the Jacobson radical for
arbitrary rings.

The matrix quasi-regularity layer proves that entrywise finite matrix ideals
preserve quasi-regularity over arbitrary rings, including for an empty index
type, by reusing the Jacobson radical and matrix-ideal APIs.

The congruence-subgroup layer defines the general linear group of a nonunital
two-sided ideal as the augmentation kernel over its unitization. It identifies
this group canonically with the kernel of reduction from the ambient general
linear group, and proves that its ambient map is injective and multiplicatively
exact for every two-sided ideal.

The nonunital-nilpotent layer defines strictly positive powers without a
multiplicative identity and uses them to express nilpotence over arbitrary
nonunital rings. It proves that unitization preserves these powers, constructs
the relative general-linear-group element represented by `1 + x` with an
explicit finite geometric-series inverse, and proves strictly upper triangular
finite matrices nilpotent without commutativity.

The unital-comparison layer identifies the unitization of any unital algebra
with the product of its scalar ring and the original algebra. It transports
this equivalence to finite general linear groups and canonically identifies the
augmentation-kernel definition with the ordinary general linear group for a
unital ring, without commutativity or nonempty-index assumptions.

The nonunital-quasiregular layer reuses mathlib's nonunital
`IsQuasiregular` predicate and identifies it, for finite square matrices, with
invertibility of `1 + x` after entrywise unitization and with representability
by that matrix in the augmentation-kernel general linear group. The index and
coefficient universes are independent, and empty matrices and trivial rings
are included.

The quasi-regular-quotient layer proves that a specified finite square matrix
is a unit whenever its image modulo a quasi-regular two-sided ideal is a unit.
It uses this reflection theorem to show that the quotient map is surjective on
every finite general linear group. Together with the congruence-subgroup
layer, this gives the three injective, exact, and surjective assertions of the
corresponding short exact sequence. It works over arbitrary, possibly
noncommutative rings and includes the empty-index case.

The local-quotient layer proves that a proper two-sided ideal whose complement
consists of units is maximal after being viewed as a left ideal. It then reuses
mathlib's standard quotient construction to provide a division-ring structure,
without commutativity or a uniqueness hypothesis for maximal ideals.

The additive-commutator layer defines `Ring.additiveCommutators R` as the native
additive subgroup generated by `a * b - b * a` in any unital ring `R`. It does
not claim that this subgroup is an ideal or that its quotient is a ring. The
matrix-trace layer proves that the trace of a rectangular cyclic difference
is a sum of scalar commutators, and descends trace to the additive quotients
for all finite square matrices, including empty index types. For a chosen
`p : n`, its inverse maps a scalar class to the class of `Matrix.single p p r`:

```lean
Matrix.traceQuotientEquiv p :
  (Matrix n n R ⧸ Ring.additiveCommutators (Matrix n n R)) ≃+
    (R ⧸ Ring.additiveCommutators R)
```

This works for noncommutative and zero rings; the inverse requires a specified
index, whereas the forward map does not. The library also gives matrix-unit
decomposition, a trace criterion for commutator-subgroup membership, and
independence of the corner chosen. The standalone `tests/MatrixTraceClient.lean`
imports only the library root and exercises these public APIs. Coefficient
naturality, conjugation, stabilization and projective-module trace are not
asserted here.

This repository is organized around source-independent algebra. Interpretation,
provenance, correspondence, and coverage for motivating sources remain in their
source-metadata repositories. Prism is responsible for the initial integration
on behalf of the Source-maintainers team.

Release status is revision-specific. Use an exact commit together with its
independent acceptance and publication record; a checkout, version string or
schema-valid metadata alone is not an official release. The root
`formalization.yaml` records mathematical scope, expression origins and a dated
author-time snapshot alongside revision-specific agent review status, not a live
release registry. Internal research and discussion systems are not needed to use
the public mathematical interface.
At the elementary-transfer author checkpoint (**2026-09-27 06:11 UTC**), the
added modules were an **unaccepted promotion candidate**. This dated observation
is not a live acceptance or release registry; later decisions bind their exact
revision. Previously published content does not confer release status on additions.

At this **2026-09-27 finite-relative transfer checkpoint**, the five new
producer/client pairs and six previously private block helpers are a fresh,
**unaccepted destination candidate** adapted from accepted incubator PR95
`a7ef4703603c3002e964be6fb289aa9eeb903af9`. The existing GLG main
`589094186158c7ddec5cac40fad08ac9ab42494f` matches previously published
official release `fe3e506fe33635e057c4cc1d8fa40e33d9d1dbd0` by tree;
that publication covers the previous elementary layer, **not** this finite
relative addition. Destination-pin native CI, full private-inclusive axiom
audit, fresh independent review, Prism's acceptance and a separate reviewed
official release remain distinct gates at this dated author checkpoint.

At the **2026-09-27 rectangular transfer-author checkpoint**, the accepted
incubator PR #101 source revision
`1b04c1d15c15b0f7adf7dcfec2861b451a4d1a79` was being promoted to an
**unaccepted** GLG candidate on then-main
`72861c49b8ed620096b4749e171e25405c3652d2`. That main had the same
tree as official published release
`51a4ca8e4a61eef09ce8164a53f4f37c3f520a00`, which did **not** contain
this addition. Incubator source build/review does not establish destination
e37 compatibility; new default-root nine-client build, complete private-inclusive
axiom CI, fresh independent promotion review, Prism's acceptance and separate
reviewed official release were separate outstanding gates at that checkpoint.
This historical note is not live acceptance or release status; later decisions
bind their exact revisions. It does not revise earlier author-time snapshots
or assert source correspondence or coverage.

## Public imports and examples

The [generated API reference](docs/API.md) records a **pre-elementary snapshot**
of 128 authored public declarations, with native signatures, docstrings and
local source links. It does not list the later elementary or relative declarations
or clients; use the [current guide index](docs/README.md) and Lean sources
for those. The [snapshot reproduction contract](docs/README.md) binds its
original source/pins without requiring internal Git history. This historical
reference is distinct from the complete private/generated proof census.

Use `import GeneralLinearGroups` for the complete public interface, or a subject
module such as `GeneralLinearGroups.MatrixTrace` for narrower dependencies.
All library modules opt in to Lean's module system. The aggregate root publicly
re-exports the subject modules. Consumer examples use ordinary imports, without
access to private helpers through `import all`.

For example, the doubled lift has a usable coefficient-map law:

```lean
module
import GeneralLinearGroups

open Matrix Matrix.GeneralLinearGroup

example {R S n : Type*} [Ring R] [Ring S] [Fintype n] [DecidableEq n]
    (f : R →+* S) (hf : Function.Surjective f) (g : GL n S) :
    mapRingHom f (liftBlockDiagonal f hf g) = blockDiagonalUnit g :=
  mapRingHom_liftBlockDiagonal f hf g
```

The same statement is retained as a named private stored-proof declaration in
`tests/PublicAPIClient.lean`. All nine client modules are default build targets;
test declarations are deliberately private and are not additional library API.

| Subject module(s) | Representative public interface | Boundary |
| --- | --- | --- |
| `Whitehead`, `Reindex` | `mapRingHom_liftBlockDiagonal`, `reindexEquiv` | Doubled lift and equal-cardinality reindexing, not stable GL |
| `Elementary`, `ElementaryWhitehead` | `elementaryUnit`, `elementarySubgroup`, `blockDiagonalUnit_mem_elementarySubgroup` | Ring-only elementary membership after doubling; no `SL = E` or normality assertion |
| `ElementaryCommutator` | `elementaryUnit_commutator`, `elementarySubgroup_isPerfect_of_three_le_card` | Ordered products over any Ring; perfectness needs at least three indices |
| `RelativeElementary` | `relativeElementarySubgroup`, `mapElementarySubgroup_relativeElementarySubgroup_le` | Ideal-coefficient normal closure inside E; compatible coefficient images give inclusions, not surjectivity |
| `RelativeWhitehead` | `blockDiagonalUnit_eq_five`, `blockDiagonalUnit_mem_relativeElementarySubgroup` | Signed ordered five-factor identity; relative membership after doubling |
| `ElementaryStabilization` | `stabilize`, `stabilize_relativeElementarySubgroup_le` | Monoid hom on semiring units, not matrix-ring hom; relative image inclusion |
| `RelativeWhiteheadConsequences` | `stabilize_conj_mem_relativeElementarySubgroup`, `stabilize_commutator_mem_relativeElementarySubgroup` | Arbitrary GL conjugation and congruence commutators only after doubling |
| `RectangularBlockUnits` | `diagonalPairUnit`, `rectangularUpperUnit_mem_elementarySubgroup`, `triangularUnit_inv_val` | Explicit diagonal units; ordered off-block factors; no arbitrary triangular-invertibility converse or stable K₁ |
| `QuasiregularIdeal`, `NilIdeal`, `MatrixQuasiregular` | `IsQuasiregular`, `IsNil`, `IsQuasiregular.matrix` in `TwoSidedIdeal` | Global ideal predicates; pointwise nil is not uniform ideal nilpotence |
| `LocalQuotient` | `TwoSidedIdeal.quotientDivisionRing` | Explicit local structure, not a global instance |
| `CongruenceSubgroup`, `QuasiregularQuotient` | `idealGeneralLinearGroupEquivCongruence`, `isUnit_of_mapMatrix_quotient_isUnit` | Exactness for any ideal; unit reflection and quotient surjectivity require quasiregularity |
| `NonUnitalNilpotent`, `NonUnitalQuasiregular` | `NonUnital.positivePow`, `nilpotentMatrixElement_inv`, `exists_nonUnitalGeneralLinearGroup_iff_isQuasiregular` | Positive powers count `k + 1` factors; no unit on the original ring is assumed |
| `UnitalComparison` | `Unitization.ringEquivProd`, `nonUnitalGeneralLinearGroupEquiv` | Unital comparison with ordinary finite GL |
| `AdditiveCommutator`, `MatrixTrace` | `Ring.additiveCommutators`, `Matrix.traceQuotientEquiv` | Additive quotient only; inverse needs a chosen index |

Unless explicitly qualified above, GL interfaces are in
`Matrix.GeneralLinearGroup`. Persistent clients include independent coefficient
and index universes, noncommutative rings, empty matrices, singleton indices and
trivial rings. The explicit nilpotent inverse client invokes its named theorem;
it does not promise that bare `simp` normalizes every representation of the inverse.

## Build and use as a dependency

Install [elan](https://github.com/leanprover/elan) and the toolchain specified by
`lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`). The only direct library dependency
is mathlib, pinned to `e37d88a26f3791ed5a93daa1f949af1021b8d103`; the manifest pins
all nine transitive packages. Git and network access to those declared repositories
are needed for dependency retrieval. No source-research checkout is required.

The exact Lean toolchain is in `lean-toolchain`, and `lake-manifest.json` pins
the complete dependency graph. Run:

```sh
lake exe cache get
lake build
```

The cache fetch must succeed before building. The literal default build includes
all library modules and nine clients. For optional focused direct checks of
the original three clients (the six later clients also build by default):

```sh
lake --wfail -KwarningAsError=true build GeneralLinearGroups GeneralLinearGroupsTests
lake env lean -DwarningAsError=true tests/PublicAPIClient.lean
lake env lean -DwarningAsError=true tests/MatrixTraceClient.lean
lake env lean -DwarningAsError=true tests/ElementaryClient.lean
```

An ordinary replay with `-T0` removes Lean's allocation timeout; it is not a
trust-level-zero check or a separate stored-proof recheck. A build or a selected
axiom listing does not by itself constitute the complete release proof audit.

For another Lake project, declare this repository using the same toolchain and
a chosen exact reviewed commit. The following is a configuration template:

```toml
[[require]]
name = "general-linear-groups"
git = "<actual-repository-clone-url>"
rev = "<full-accepted-commit-id>"
```

Substitute the actual clone URL and full accepted commit from the relevant
release record; private repositories require authorized access. This template
does not assert a published destination or an official release. Official internal
acceptance requires independent review, guarded preparation and a durable record
binding the full commit and tree. Public-lineage review, promotion and publication
are separate. Tags are deferred. No cross-mathlib-pin compatibility is claimed.

Pre-elementary ordinary-readiness baseline (Linux, Lean4.34rc2, `LEAN_NUM_THREADS=2`, matching
dependency cache already fetched): after `lake clean general-linear-groups`,
the warning-fatal literal default build rebuilt all16 project modules, including
both then-existing clients, in16.635 seconds wall time (29.111 seconds user,8.613 seconds system;
1832 Lake jobs including cached dependencies). This is a warm-dependency,
clean-project measurement, not an all-dependency source-build time or a speedup
claim. Cache retrieval took approximately101 seconds in that run. Timings depend
on the machine and network; use bounded parallelism on memory-limited systems.

Headers intentionally give the license and author credit without inventing a
copyright holder. The pinned mathlib header linter requires a copyright-holder
line and therefore reports a format failure on the 13 subject headers. The
independent PR35 review of `9cec4e1ccee427c7f2748524d194cd7c48ac4214`
accepted this specific header-format convention departure, not a linter pass
or copyright clearance. The root header probe passed; both private-only client
modules failed the private-module linter by design, a separately accepted
non-export convention departure. These findings are not blanket lint waivers;
full release and public-history rights checks are separate.

The pre-elementary full-readiness author run (same pinned environment and two Lean
threads) fetched the matching cache before a clean default build: 1832 jobs,
all 16 modules, 18.913 seconds wall time. It then added 58 docstrings without
changing any mathematical/proof text or attributes; the rebuild passed and native
analysis found no missing docstrings among the 128 authored public declarations.
The subsequent explicit-`Nat.rec` implementation of `NonUnital.positivePow`
retains its generic `[Mul A]` API and both definitional equations. Its original
author bound renewed native documentation and proof evidence to source commit
`907124e973dd20f3efdeb8de0cad42e331b9c6d8` and full PR35 commit
`9cec4e1ccee427c7f2748524d194cd7c48ac4214`. A fresh worker-b review of
that exact 28-file tree independently checked the 128 public axiom records, all
276 stored project declaration bodies, native documentation and current-file origins;
it identified no mathematical, proof or current-file rights defect. Its
development-integration verdict was **REQUEST_CHANGES** and its whole-current-
artifact internal-quality verdict was **NONPASS**, because the live lifecycle
prose and active review metadata needed correction. The stock reviewer
`leanchecker` rerun was interrupted and supplies no pass.

Declaration lint still exits 1: the four exact `simpNF` findings and one unused
`[Subsingleton S]` hypothesis in a private trace test received narrow,
reasoned convention dispositions in that review, not a clean lint result or
general release waiver. This documentation/metadata-only correction keeps the
Lean sources, pins, checker and native adapter unchanged. Its new exact tree
requires independent affected-scope review and Prism's owner disposition before
any acceptance; the prior REQUEST_CHANGES/NONPASS do not approve this successor.
No official internal release, public-lineage review, GitHub publication or
source-coverage decision is asserted here.

The preceding paragraph records the **pre-elementary author-time checkpoint**;
its pending decisions and no-publication statement are not live status for the
previously published base. They do not apply as a review or computation pass to
the elementary addition: its exact-candidate CI, independent promotion review,
Prism's acceptance and release decisions are separate revision-specific records.

## License, authors and provenance

Original project contributions are distributed under the
[Apache License, Version 2.0](LICENSE).

Authors: Formal Frontier Agents

Prism developed the block/reindex, ideal, nilpotent, quotient and unitization
layers, including adaptations of earlier internal source-repository diagnostics,
and maintains the initial integration. The `formalization-worker-b`
execution for issue30 developed the additive-commutator/trace layer, adapting
Prism's earlier source-repository proof exposition and Lean research. Independent
development reviews were contributed by the worker identities and Anchor,
Atlas, Beacon and Lattice; exact authors, Task execution identifiers, revisions,
review scopes and findings are retained in the repository history and issues.
Collective author credit does not assert a copyright holder.

The original Ring-only elementary proofs, client and guide were authored for
the incubator by worker-b Task
`hive-request-1d40c1435bdcf9b74e70656bc81b7b2a3179626f` (UID
`8d3f955e-1034-4229-9ec1-6fc750e9771a`). The distinct worker-b Task
`hive-request-d5b170c2c524d08ea237131ac1b634cbefb66165` (UID
`66b8826e-5348-42d2-bf91-7494acf88159`) transfers that unchanged
mathematics into this library, adapting imports, headers and destination
documentation. At that transfer's **2026-09-27 06:11 UTC** checkpoint, the source
review approved only the frozen mathematical/API/provenance content, conditional
on computational acceptance; destination review and full checks were pending.
This is provenance history, not the status of later exact-revision decisions.
Prism authored the reused Whitehead layer and
is the responsible maintainer for the destination decision. Mathlib contributors
retain credit and licensing for the imported foundational APIs.

The five new finite commutator/relative/stabilization producer/client pairs
come from separate accepted incubator author Tasks: respectively
`hive-request-35aa9748fd43bd94b3ec738f1ad463b088d4ae0b`
(UID `2e849319-c5e4-4143-8824-4e604660c6c5`),
`hive-request-fe47d83d9ec7ed0603df9afa59272f91b6c1d25b`
(UID `aa475138-96f3-40c8-9d3e-a2ed8997d269`),
`hive-request-474d5a18341359e66cfefad57a2fe7fce5fd95be`
(UID `201cfd05-92f3-411c-9f16-9927145c58ca`),
`hive-request-c6d28d96c8c6a1c3dc45b276cd199a8cee20e982`
(UID `79046b95-69ff-4154-945a-95b1b410bc7c`) and
`hive-request-f9c9518717f9190ac25e3ad72fc01ab6a8aadee6`
(UID `956a92f7-088d-407d-9ec0-3110d03431c8`). Prism supplied the
original relative proof exposition/planning and is the responsible maintainer.
The separate GLG source-only transfer and six-helper visibility/docstring
change are by worker-b Task
`hive-request-5da2d3a64872f8d02f43a4373691317fea0453de`
(UID `0c79d3fe-3ca4-433d-9f11-152854f183e2`). At that transfer-author
checkpoint, the previous release `fe3e506fe33635e057c4cc1d8fa40e33d9d1dbd0`
did not include those changes. The original authors' source checks alone
do not establish destination e37 compatibility.

The rectangular producer/client and mathematical guide originated with
`formalization-worker-b`, Hive Task
`hive-request-f05b4be9b9263abe877517328bf1ff2eb3ccbe6c` (UID
`f689b30f-0a76-4727-8ec2-68907a224546`); independent original-leaf
review was by worker-a Task
`hive-request-d58bc9fb1f33c1ab04462845819fa599cfd02540` (UID
`21cca7cb-eaa7-4145-89fc-d310aa764158`). The accepted incubator
registration was by worker-b Task
`hive-request-9f77f8c1f4015db6ddf102989bf1d24ae36a6048` (UID
`63beac6e-e93f-4a54-8fb8-650114a41967`). This source-only destination
transfer is by distinct worker-b Task
`hive-request-cf565ac88c8dc0b5274168e7cb2dbfc1abfab323` (UID
`d7ced547-d176-4d48-af8d-ad239d49cff9`); Prism retains mathematical
planning and responsible-maintainer acceptance, integration and release.
Source acceptance does not certify this destination graph or source coverage.

The distinct worker-a fixture Task
`hive-request-301d13e69087461df1d9f6514c98f2515fe43c2f`
(UID `61ae8cb2-3435-4837-a1eb-563145a5793b`) established bounded
core-only recursor viability, not a GLG pass. Worker-a successor Task
`hive-request-96bd881daa0958792df18fd4319ec9f7807ab021`
(UID `124e5555-0f64-44a3-8fee-18fa5dbadb9c`) applied the bounded
GLG source change and refreshed source-bound author evidence from Prism's
unaccepted frozen assembly. Both Task credits remain distinct from Prism's
original mathematical development and documentation adapter.
This lifecycle prose and metadata correction was authored by worker-a Task
`hive-request-c96601c24931622decfa5ba51d85ecc1377deddb`
(UID `ea63f3e8-a310-41c8-89e4-84e9082ca10f`), not by the mathematical author.

The documentation adapter, tests and recipe are adaptations of Anchor's native
Markdown work and Prism's Group/Dedekind portability work; exact origins and AI
credit are recorded in [the documentation recipe](docs/README.md). Generated
output contains this library's docstrings and mathematical signatures, not the
upstream tool's web assets.

The mathematical motivation includes Charles A. Weibel, *The K-book: An
Introduction to Algebraic K-theory*, August 29, 2013 complete-book build, especially
the elementary block/ideal constructions and matrix trace modulo additive
commutators. Native mathlib matrix, unitization, Jacobson radical, ideal quotient,
quasiregularity and additive quotient APIs supply the formal foundations; their
separate licenses and contributor notices remain with those dependencies.
The trace implementation adapts the source research at
`source-weibel-k-book` revision `5e52651fdf8fca2f27362917c1b693b4e4b8788e`,
not an independently authored replacement of that code. Detailed source passage
correspondence and incomplete coverage stay in the source metadata repository.
No book PDF, scan or substantial source quotation is bundled here.

AI agents produced and revised the formalization, tests and documentation, using
Lean checks and independent agent review. That describes the process, not a
guarantee of mathematical correctness or copyright clearance. Applicable
third-party attribution and permissions must be preserved separately; internal
access, citations and AI involvement are not redistribution licenses.
