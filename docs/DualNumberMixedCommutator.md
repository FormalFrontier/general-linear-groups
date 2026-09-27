# Mixed native GL commutators over iterated dual numbers

Import `GeneralLinearGroups.DualNumberMixedCommutator`; the ordinary
public-import client is `tests/DualNumberMixedCommutatorClient.lean`.
From this repository root, after fetching the matching pinned mathlib cache,
check the leaves with `lake build GeneralLinearGroups.DualNumberMixedCommutator`
and `lake env lean tests/DualNumberMixedCommutatorClient.lean`.
The producer
uses independent coefficient and index universes, a commutative ring `R`, a
finite index type `n` with decidable equality, and no nontriviality,
nonemptiness, characteristic, determinant, or rank-invertibility hypothesis.

Let `S = DualNumber R` and `T = DualNumber S`. The first coordinate of `S` is
the scalar coefficient and the second is `ε`; the outer second coordinate of
`T` is `η`. `innerConstant Y = Y.map (algebraMap R S)` and
`innerPure Z` has entries `(0, Z i j)`. The native unit `epsilonLiftGL X`
has underlying matrix `(liftMatrix X).map (algebraMap S T)` and its native
inverse maps `liftMatrix (-X)` along the same outer constants. Its outer
reduction is **`liftGL X`**, not generally `1`. The native unit
`etaLiftGL Y = liftGL (innerConstant Y)` has underlying matrix
`liftMatrix (innerConstant Y)`, inverse `liftMatrix (-innerConstant Y)`, and
outer reduction `1`. The producer constructs the outer constant unit from
the two mapped inner matrices and their inverse equations; its entries agree
with the existing native GL coefficient map, without changing the project
semiring instances.

The theorem `epsilon_eta_commutator` proves the **ordered full native-unit**
equality

```text
epsilonLiftGL X * etaLiftGL Y * (epsilonLiftGL X)⁻¹ * (etaLiftGL Y)⁻¹
  = liftGL (innerPure ⁅X,Y⁆).
```

The bracket is mathlib's existing `LieRing.ofAssociativeRing` bracket
`⁅X,Y⁆ = X*Y - Y*X` (not a newly defined Lie structure). This is the matrix
`I + εη(XY-YX)`, including all four nested coordinates: outer-first /
inner-first is the identity, outer-first / inner-second is zero, outer-second /
inner-first is zero, outer-second / inner-second is `⁅X,Y⁆`. The actual outer
fiber element `mixedKernel X Y : (glReduce S n).ker` has that unit as its
value; `mixedKernel_readback` is the entire pure-inner matrix,
`mixedKernel_fst` and `mixedKernel_snd_fst` recover the zero/identity
coordinates, and `mixedKernel_snd_snd` reads the mixed coefficient. The
proof uses the existing native `liftGL`, `glKerEquiv`,
`glKerEquiv_conj`, and mathlib's associative bracket, with only local
coordinate arithmetic. No private result from the adjoint module is exposed.

The first-order identity fiber still commutes by `glKernel_mul_comm`. Here
the *outer* reduced conjugator is the nonconstant inner lift `liftGL X`:
one factor does **not** belong to the outer identity fiber, so there is no
conflict. The client checks full units and actual outer readback at ranks
`Fin 0`, `Fin 1`, `Fin 2` over `ℤ`, and at `ZMod 1` and `ZMod 2`;
`E₀₁,E₁₀` give mixed diagonal coefficients `1,-1` over `ℤ`, their reversed
order gives `-1` at `(0,0)`, and the coefficient stays nonzero modulo two.
These examples make no determinant-surjectivity claim.

## Provenance and limits

The producer's sole public import is the already delivered
`GeneralLinearGroups.DualNumberKernelAdjoint` module. The original local
producer import was `Incubator.LinearAlgebra.Matrix.DualNumberKernelAdjoint`;
the accepted incubator source instead imported its published official GLG
dependency at commit `045ba3ac1e77a7b7f49e053792cb3fb122889ffa`.
This producer is copied byte-for-byte from accepted incubator commit
`a3edd083fcc410830d1e5e65703ad00bcc7fae00` into a new destination leaf;
the ordinary client changes only the producer import and its enclosing test
namespace. The original three leaves at commit
`9fc8e66507274967dbce6393e64986f61b62383b` received source-only
independent approval from worker-a Task
`hive-request-81825e08a73a2e0544866d1268c8e32c03b103c2` (UID
`b0f5ab33-efc3-471c-8615-6810a18300bd`; incubator issue 5/52908,
owner intake 5/52921). Incubator registration was by worker-b Task
`hive-request-91c8d549f60ba8e73fe0aecdeb942a3d44907d79` (UID
`4e794ff8-c534-4a22-a2a6-1dc160be1ffc`) on then-unaccepted Atlas
PR116 commit `7bac6793387ebaa2d8913c7470ef3830d90bd3d6`. That source
was subsequently reviewed with its full registered graph, private-inclusive
standard-three axiom CI, accepted by Lattice (incubator issue 5/53478), and
protected-integrated (PR 118/53490). Those incubator checks are not
destination Lean evidence. At the 2026-09-27 registration-author checkpoint,
the destination candidate imports this producer from its public root, includes
the client in its 13 default test roots, and registers 17 selected results in
`formalization.yaml`. Independent worker-a Task
`hive-request-596aa7e2022ef8080e220ed42317f21e2c97dcb8` (UID
`a2b6fc22-41fb-4b3f-8a50-62aea71f20ac`) approved the bounded three-leaf
source/API/client/docs/rights transfer at review commit
`e5235d2fcc7007e0131c48de56bc39fa08962407`; it did not approve this
registered graph. This static assembly is by worker-b Task
`hive-request-a0042175907e7c4821053615250c697fbff8a018` (UID
`c5157876-806e-4d40-88ef-91a3cbb6ef3f`). At that checkpoint, the registered
candidate was unaccepted pending affected independent review, destination
full-graph build and private-inclusive standard-axiom audit, Lattice's acceptance
and protected integration, its own reviewed official release and verified
publication, then reviewed incubator conversion. Neither focused checks nor
source CI then certified the destination graph or source coverage.

At the subsequent **2026-09-27 18:57:26 UTC code-acceptance checkpoint**,
Lattice accepted and protected-integrated PR64 as `main`
`6d351f75aa81153bcb620005f77aaedd680b3e3b`, tree
`5355ecaa2a72db81690b26b4977bae71b87108ff`. The independent
source-only leaf review `e5235d2fcc7007e0131c48de56bc39fa08962407`
and exact registered assembly review
`73277a2e2bb6211754b06acd56c27cc6ea5270a8` remain separately
identified. Strict native CI562/UI27, full artifact86559 preserved at
`6748ecda94900887e959a2bec6a7fbe6237e54cd`, built the default root
and all thirteen clients on pinned destination mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103`. Its complete fresh
39-module transitive audit includes private origins and all 150 selected results;
only `propext`, `Classical.choice` and `Quot.sound` occur. The subsequent
prose/metadata-only release-readiness candidate reuses this unchanged-input
evidence. It is **not** an accepted release or verified private GitHub
publication: independent final release review, Lattice's main-readiness and
release acceptance, protected promotion and verification of actual private
GitHub `main` are still required. This guide's dated author snapshot is not a
live release registry. No source-passage coverage or mixed-SL result follows.

The code notices retain `SPDX-License-Identifier: Apache-2.0` and collective
Formal Frontier authorship. The reused dual-number algebra, native GL
definitions, and associative matrix Lie bracket are mathlib results. The
native kernel producer was authored by worker-b Task
`hive-request-1df68ed8f5e4bab1a07522b5ee97f5a4e124e028` (UID
`a1cde5e5-a84f-4b15-b86e-c1d59cf1e533`), and the adjoint producer by
worker-b Task `hive-request-083e63349244c927c6fd7ddd1ceb7b01a722e06c`
(UID `bec147d0-40ae-43fd-95d5-5b28c2bf2ed6`). The independent
source-only API investigation was produced by worker-b Task
`hive-request-0cba64c3b6e70835dd27f719e7d96682a55936d1` (UID
`6bee2d00-ea33-47da-8b8e-3dc8563c69df`) at `d8423e4b0c6d1388c3deb323e58022dd5b68b300`;
its conjectural signatures were not Lean evidence. This bounded Lean
implementation is by worker-b Task
`hive-request-88a39f40cd23a7135b5d8a4f56e4abd33c6d9c61` (UID
`29343994-029c-40be-9acb-a5927caa38b6`) from accepted/incorporated
incubator commit `e6f66b1e53a2108284b798ced2f9f6316e1ee140`. The
independent affected source review is report
`1eade9625e1ed34089a3a4cdc4c3165c6498651d`. This three-leaf GLG
transfer is by worker-b Task
`hive-request-386bfaa3270c51ac2efc2c60e91e151144083a5e` (UID
`222d73c7-5dbd-42a9-b96c-700943c4103e`) against destination commit
`e89a42d8a6d2beb4ce6e050cbc1f29e9bcf6ee2c`, pinned to Lean
`v4.34.0-rc2` and mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`.
It makes no source-specific correspondence, SL extension, scheme-point
construction, or global Lie structure.
