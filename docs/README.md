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
[native dual-number kernels](DualNumberKernels.md),
[their adjoint action](DualNumberKernelAdjoint.md),
[the finite-rank Steinberg presentation](FiniteRankSteinberg.md),
[mixed native GL commutators](DualNumberMixedCommutator.md), and
[mixed native SL commutators](DualNumberMixedSLCommutator.md).
The combined native GL/SL results are part of the privately published release;
these guides describe the relevant current modules. The 128-entry reference does
not inventory their later APIs.

This page and [the manifest](api-manifest.json) are **not** a current 41-module
declaration inventory, a census of private or generated declarations, or proof
certification. In particular, `proof_certification: false` in the manifest is
intentional. The 128 displayed signatures were generated from 16 native module
records (the original 13 producers, aggregate root and two private clients)
against the earlier private development revision
`907124e973dd20f3efdeb8de0cad42e331b9c6d8`, not against the whole current
checkout. The current aggregate `GeneralLinearGroups.lean` and `lakefile.toml`
bytes differ from those bound by the manifest; the other 17 of 19 bound input
files still match. Consequently an ordinary `--check` with this checkout's
current inputs is expected to refuse **source/pin drift**, not diagnose a
mathematical or proof failure. Do not replace old hashes with current ones:
that would falsely imply a fresh native run.

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
