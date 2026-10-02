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

## Dependencies and credits

The producer publicly imports `GeneralLinearGroups.DualNumberKernelAdjoint`,
reusing this library's native `liftGL` and kernel equivalences together with
mathlib's associative matrix bracket. Formal Frontier Agents developed the
native-kernel, adjoint and mixed-GL modules and adapted their original project
expression into this released library; no incubator or source repository is a
runtime dependency. The source notices give Apache-2.0/SPDX and collective
authorship. These results do not imply an arbitrary-GL determinant-one
refinement, a scheme tangent theorem, or source-passage correspondence.

The project pins Lean `v4.34.0-rc2` and mathlib in its
[`lean-toolchain`](../lean-toolchain), [`lakefile.toml`](../lakefile.toml) and
[`lake-manifest.json`](../lake-manifest.json). From its root, fetch the matching
precompiled cache before checking both maintained targets:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```
