# API reference and mathematical guides

[API.md](API.md) is a **historical partial reference** for 128 authored public
declarations from 13 source modules. Its displayed signatures, docstrings and
links to the corresponding source lines remain useful on this checkout: all 128
links point into the unchanged owning modules. Import `GeneralLinearGroups` or
an individual linked module to use the declarations. Displayed signatures depend
on their module's namespace, notation and imports; they are not standalone Lean
commands. The root [README](../README.md) introduces the current library and its
ordinary import.

For current mathematics beyond this partial reference, see the guides to
[elementary matrices](ElementaryMatrices.md),
[commutators and perfectness](ElementaryCommutators.md),
[relative elementary groups](RelativeElementary.md),
[relative Whitehead factorization](RelativeWhitehead.md),
[finite stabilization](ElementaryStabilization.md),
[relative consequences](RelativeWhiteheadConsequences.md),
[rectangular upper block units](RectangularBlockUnits.md),
[unit-pivot diagonalization](UnitPivotDiagonalization.md),
[elementary paths](ElementaryPaths.md),
[elementary product-one diagonals](ElementaryDiagonal.md),
[finite special-linear elementary neighborhoods](ElementaryNeighborhood.md),
[native dual-number kernels](DualNumberKernels.md),
[their adjoint action](DualNumberKernelAdjoint.md),
[the finite-rank Steinberg presentation](FiniteRankSteinberg.md),
[mixed native GL commutators](DualNumberMixedCommutator.md), and
[mixed native SL commutators](DualNumberMixedSLCommutator.md).
These guides describe the corresponding current modules; the 128-entry reference
does not inventory their later APIs.

Further current topics are available directly from the subject modules:

- [Single-entry matrix corners](../GeneralLinearGroups/MatrixCorner.lean).
- [Zero-product elementary stabilization](../GeneralLinearGroups/ZeroProductStabilization.lean)
  and [rectangular unit switching](../GeneralLinearGroups/RectangularUnitSwitch.lean).
- [Ring Schur reduction](../GeneralLinearGroups/SchurReduction.lean).
- [Conditional unit-pivot induction](../GeneralLinearGroups/UnitPivotInduction.lean)
  and [local elementary generation](../GeneralLinearGroups/LocalElementaryGeneration.lean).
- [Stable general linear groups](../GeneralLinearGroups/StableGeneralLinear.lean),
  [stable elementary groups](../GeneralLinearGroups/StableElementary.lean) and
  [stable determinants](../GeneralLinearGroups/StableDeterminant.lean).

For the hypotheses and boundaries of these results, see the
[headline results](../README.md#headline-results) and the linked declarations.

This page and [the manifest](api-manifest.json) are **not** an inventory of the
current module graph, a census of private or generated declarations, or proof
certification. In particular, `proof_certification: false` in the manifest is
intentional. The 128 displayed signatures were generated from 16 native module
records (the original 13 producers, aggregate root and two private clients)
against the earlier private development revision
`907124e973dd20f3efdeb8de0cad42e331b9c6d8`, not against the whole current
checkout. Of the 19 manifest-bound source and pin paths, 14 still match their
recorded hashes: all 13 producer modules and `lean-toolchain`. The aggregate
`GeneralLinearGroups.lean`, `lake-manifest.json` and `lakefile.toml` have changed
bytes; the historical private-client paths `tests/MatrixTraceClient.lean` and
`tests/PublicAPIClient.lean` are absent (the current clients live under
`tests/GeneralLinearGroupsTests/`). An ordinary `--check` with this checkout's
inputs cannot validate the historical binding: the missing paths prevent input
loading, and the changed bytes would also violate the binding. This drift does
not diagnose a mathematical or proof failure. Do not replace old hashes with
current ones: that would falsely imply a fresh native run.

## Principal-unit commutator coordinates

Import `GeneralLinearGroups.PrincipalUnits.Filtration` for commutator estimates
on the original units of any possibly noncommutative `Ring R`. For a left
ideal `I`, positive `a, b`, and units with `x = u - 1 ∈ I ^ a` and
`y = v - 1 ∈ I ^ b`, the API provides:

- `Ideal.commutator_sub_one_sub_mul_sub_mem_pow`: the remainder
  `[u, v] - 1 - (x * y - y * x)` belongs to `I ^ (a + b + min a b)`.
- `Ideal.quotient_mk_commutator_sub_one_eq`: the classes of `[u, v] - 1`
  and `x * y - y * x` agree in `R ⧸ I ^ (a + b + 1)`.

Here `[u, v] = u * v * u⁻¹ * v⁻¹` (Lean's scoped `⁅u, v⁆` notation).
The quotient is a left module, not a quotient ring; neither two-sidedness
nor nilpotence of `I` is assumed. The bracket has no degree-dependent sign.
These are representative-coordinate statements. For descended pairings on
positive successive layers, use the following API. For the subgroup and
nilpotence bounds, see the other declarations in the
[filtration module](../GeneralLinearGroups/PrincipalUnits/Filtration.lean).

## Positive principal-unit layer pairings

Import `GeneralLinearGroups.PrincipalUnits.Commutator`. Throughout, `R` is any
possibly noncommutative ring, `I` is a left ideal, and degrees are in `ℕ+`.

- `Ideal.powLayer I n` is the successive ideal quotient in degree `n`, with
  its quotient-module operations. `powLayer_mk_eq_zero_iff` and
  `powLayer_mk_eq_mk_iff` express vanishing and equality of representatives
  as membership in `I ^ ((n : ℕ) + 1)` in the original ring.
- `Ideal.principalUnitsPowLayer I n` is the quotient of the original-unit
  stabilizer at `I ^ n` by the coordinate kernel at `I ^ (n + 1)`.
  Its operations are the quotient-group operations, and it is commutative.
  `principalUnitsPowAdditiveLayer` is its additive tag, carrying the usual
  integer module structure.
- `Ideal.principalUnitsPowLayerSymbol I n` is the injective integer-linear
  map from the additive unit layer to the ideal layer. The `_mk` theorem
  computes it as `[u] ↦ [u - 1]`; `_injective` allows cancellation and
  `_ker` simplifies its kernel to `⊥`. The symbol need not be surjective.
- `Ideal.powLayerCommutator I a b` is the integer-bilinear map on ideal
  layers with target degree `a + b`. The `_mk_mk` theorem computes it as
  `[x], [y] ↦ [x * y - y * x]`.
- `Ideal.principalUnitsPowLayerCommutator I a b` has values in the additive
  unit layer of degree `a + b`, not in a replacement image carrier. Its
  `_mk_mk` theorem computes it as `[u], [v] ↦ [u * v * u⁻¹ * v⁻¹]` for
  original-ring unit representatives.
- `principalUnitsPowLayerSymbol_commutator` identifies the symbol of the
  unit pairing with the coordinate pairing of the symbols.
  `principalUnitsPowLayerCommutator_unique` characterizes the unit pairing
  by this square.

For either pairing, `_self` gives alternation in one degree. The `_swap`
theorem uses `cast` along `add_comm b a` to compare the target degrees and
then gives ordinary negation, without a degree-dependent sign. The bundled
linear maps already supply the usual addition, negation, integer-scalar and
finite-sum laws in each argument.

There is no two-sidedness, Jacobson-radical, nilpotence, finiteness or
nontriviality hypothesis. The scalar ring of the pairings is `ℤ`, not `R`;
the ideal layers remain quotient left modules, not quotient rings. No
additive description at degree zero is supplied.

## Reproducing the historical reference

Reproduction requires authorized **private** access to both the original
source/pin bytes at the revision above and the retained bundle of 16 native
doc-gen4 JSON records. Official public-release/GitHub history alone does not
provide either input. In a separate replay working copy, use this adapter and
the retained `docs/API.md` and `docs/api-manifest.json`, with all 19 paths named
in the manifest restored from the original private revision. Supply the native
records as `declaration-data-MODULE.bmp` files in a `doc-data` directory. Check
the original source/pin and record hashes against the manifest, then run:

```sh
python3 -B scripts/generate_api.py --native-data /path/to/doc-data \
  --source-revision 907124e973dd20f3efdeb8de0cad42e331b9c6d8 --check
python3 -B scripts/test_generate_api.py
```

`--check` validates the retained inputs and compares the generated Markdown
and manifest byte for byte without writing them. It does not authenticate the
original native run, independently review the record provenance or audit
proofs. Generating *new* records instead requires a genuinely matching native
doc-gen4 run at manifest revision
`97d4ecdfc8e09e7f511724c25e303d448de6a3db` and the pinned Lean/mathlib
environment, with the matching precompiled mathlib cache fetched before a
build. `--refresh-binding` must not be used to relabel the retained records.

## Credit

Authors: Formal Frontier Agents. Original project contributions are
Apache-2.0. Anchor (AI) developed the original ideal-completion adapter and
tests. Prism (AI) adapted the Group and Dedekind portability work, the GLG
inventory/renderer/tests and 58 GLG source docstrings. A distinct Formal
Frontier AI contributor implemented the positive-power recursor change;
Beacon (AI) gave portability advice but did not supply copied implementation.
Native tooling and mathlib retain their upstream authorship and licenses.
