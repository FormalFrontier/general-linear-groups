# Native API reference

[API.md](API.md) is a **pre-elementary generated snapshot** of 128 authored
public declarations: native displayed signatures including implicit parameters,
source docstrings and relative links to unchanged source files. It was bound to
source revision `907124e973dd20f3efdeb8de0cad42e331b9c6d8`, with 13
subject modules and the two then-existing private clients, `MatrixTraceClient`
and `PublicAPIClient` (16 module records). It does **not** cover the later
`Elementary`, `ElementaryWhitehead`, five finite relative producers or six
corresponding private clients, `RectangularBlockUnits` and its ninth private
client, the dual-number kernel/adjoint modules and their two private clients,
or the Steinberg presentation and its private client.
The snapshot also excludes the later mixed dual-number commutator and its
private client; the historical 128-declaration count is not its API count.
For the current finite APIs and examples see
[elementary matrices](ElementaryMatrices.md),
[commutators and perfectness](ElementaryCommutators.md),
[relative elementary groups](RelativeElementary.md),
[relative Whitehead factorization](RelativeWhitehead.md),
[finite stabilization](ElementaryStabilization.md) and
[relative consequences](RelativeWhiteheadConsequences.md),
[rectangular upper block units](RectangularBlockUnits.md),
[native dual-number kernels](DualNumberKernels.md) and
[their adjoint action](DualNumberKernelAdjoint.md),
[the finite-rank Steinberg presentation](FiniteRankSteinberg.md), and
[the mixed native GL commutator](DualNumberMixedCommutator.md). These standalone
guides do not replace the archived inventory with a new native analysis.
Do not treat 128 as the current declaration count or as proof integrity
evidence for this destination candidate.

The root [README](../README.md) gives the current mathematical scope and ordinary-import
example. The generated snapshot is not a census of private or generated declarations,
nor a proof or release certificate. Display signatures use the source module's
namespace, notation and imports; they are not standalone proof-bearing commands.
No dependency website, HTML, JavaScript, fonts or other web assets are shipped.

## Reproduction contract

Use Python 3 and unchanged doc-gen4 at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, with its committed five-dependency
manifest and Lean `v4.34.0-rc2`, in a separate checkout. Build that core-only tool
with `lake build doc-gen4`. If the runtime compiler wrapper is not on PATH, add
the directory containing `elan which lean` to that build's PATH. Do not change
either manifest or the library's mathematical pins to install the tool.

For reproduction of this historical snapshot, use its bound source revision,
not the current elementary candidate: fetch the matching mathlib cache before
`lake build` and run doc-gen4 in that library's `lake env`, not the tool's.
The historical module/source map is `MODULE_PATHS` in
[the adapter](../scripts/generate_api.py); it includes the root, the original
13 subject modules, and two `tests/` source files. Analyze each once
into a fresh shared database. `FULL_SOURCE_COMMIT` below is the 40-character
`analyzed_source_revision` in [api-manifest.json](api-manifest.json).

```sh
lake env /path/to/doc-gen4 single --build /path/to/fresh-analysis GeneralLinearGroups.AdditiveCommutator api.db source-snapshot:FULL_SOURCE_COMMIT/GeneralLinearGroups/AdditiveCommutator.lean
```

Repeat with each exact module/source pair. `source-snapshot:` is a provenance
identifier, not a claimed remote address. It binds the native record to the full
source revision and file; the Markdown links use only local source paths.
No public repository location or remote availability is inferred.
The pinned native source linker leaves such an identifier unchanged, without a
line-range suffix. The adapter therefore checks its exact bytes and the separate
native integer `line` field against the source bounds. It does not claim to
recover an absent end-line field. Both are bound by the native-record hash.

```sh
lake env /path/to/doc-gen4 bibPrepass --build /path/to/fresh-render --none
lake env /path/to/doc-gen4 fromDb --build /path/to/fresh-render --manifest /path/to/fresh-render/manifest.json /path/to/fresh-analysis/api.db
python3 -B scripts/generate_api.py --native-data /path/to/fresh-render/doc-data --source-revision FULL_SOURCE_COMMIT
python3 -B scripts/generate_api.py --native-data /path/to/fresh-render/doc-data --source-revision FULL_SOURCE_COMMIT --check
python3 -B scripts/test_generate_api.py
```

Ordinary generation and `--check` validate the existing manifest before using
the records: exact 19 source/pin hashes, 16 native-record hashes, tool revision,
source revision and public inventory. They require no Git executable or historic
Git objects. Generation reproduces the outputs and records the current adapter
hash; `--check` compares all output bytes without writing. An adapter change
therefore needs deliberate regeneration and independent review, not an ignored
hash difference. Retained native records remain necessary inputs; the distributed
bundle does not contain all dependency documentation.

For a genuinely new native analysis, including first generation, use
`--refresh-binding` instead of `--check`. This explicit authoring mode requires
the selected source commit locally and compares every source/pin blob with it
before writing a new binding. New records must come from a matching native run.
The mode does not authenticate their origin or approve the new artifact, and
cannot be combined with `--check`. Source-only and independent parentless
checkouts reproduce an existing binding without that historical object.

The bounded adapter checks exact names, native and displayed kinds, owning
modules, source identifiers/lines, nonempty docstrings, and all retained implicit binders
and typeclasses. It preserves every visible signature token, normalizing only
whitespace. It refuses malformed/active header markup, duplicate JSON keys,
missing/extra declarations, drift and unsupported Markdown fences. These checks
do not turn supplied JSON into authenticated compiler output. Independent review
must bind the exact native run, complete graph, source/artifact bytes and final
full candidate commit/tree. Jointly forged inputs and hashes are outside the
manifest's guarantee; proof integrity and private/generated census are separate.

All headers and implicit assumptions were inspected against the actual source
statements for this inventory. In particular, trace equivalence requires a
chosen index; its forward map does not. Nonunital powers count `k + 1` factors;
quasi-regularity is not inferred merely from a proper ideal. Native `def` entries
may display `abbrev` or `noncomputable def`; these distinctions are explicit in
the inventory rather than silently erased.

## Provenance and status

Authors: Formal Frontier Agents. Original project contributions are Apache-2.0.
Prism (AI agent) adapted Anchor's (AI agent) ideal-completion adapter/tests/recipe
at `f0c8c34386109116e4912fb425a8ad15d9dc42a4`, through the portable group-rings
version `fe121a046bd40691bba6cf275273a71cd5d7d007` and the Dedekind
adaptation `f2f718d4e38f5b1a6ef1ce683a7ca8a405974bf6`, unreviewed when used
as an input here. The GLG changes supply its
actual inventory, ownership, implicit binders, displayed kinds, source-identifier
contract and tests. Prior approvals and passes do not approve this adaptation.
Beacon's portability advice informed the earlier Group work; it was not copied
implementation. Native tools and mathlib retain their upstream credit/licenses.

Generated Markdown includes this project's docstrings and native mathematical
display signatures, not dependency implementation or docstrings. The 58 added
GLG docstrings are Prism's AI-authored explanations of the existing statements.
The subsequent source change to `NonUnital.positivePow`'s recursive implementation
used an explicit `Nat.rec`, by worker-a Task
`hive-request-96bd881daa0958792df18fd4319ec9f7807ab021`
(UID `124e5555-0f64-44a3-8fee-18fa5dbadb9c`). The precursor core-only
fixture belongs to distinct worker-a Task
`hive-request-301d13e69087461df1d9f6514c98f2515fe43c2f`
(UID `61ae8cb2-3435-4837-a1eb-563145a5793b`), not to this new native
analysis or Prism's original adapter. Original author checks bound the native
records to source commit `907124e973dd20f3efdeb8de0cad42e331b9c6d8`;
the independent worker-b PR35 review of full commit
`9cec4e1ccee427c7f2748524d194cd7c48ac4214` authenticated the native
records and renderer and found no mathematical, proof or current-file rights
defect. It recorded **REQUEST_CHANGES** for ordinary integration and **NONPASS**
for whole-current-artifact internal readiness because the prose and
metadata at that dated checkpoint needed correction. The declaration linter exited 1 on
four `simpNF` findings and one unused private-test hypothesis; that reviewer
accepted only those exact convention departures, the truthful-header format
departure and the two private-only client refusals, not clean lints or a rights
waiver. At that checkpoint, the documentation/metadata correction needed
independent review of its exact tree and Prism's disposition; its later
acceptance/publication must be checked in exact records, not inferred from this
historical paragraph. The elementary addition was separate and unaccepted at
its **2026-09-27 06:11 UTC** transfer-author checkpoint; that dated observation
does not state its later revision-specific status. Neither these older review
findings nor the archived generated
reference certify its release, human review or source coverage.
