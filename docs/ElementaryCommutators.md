# Elementary commutators and finite-rank perfectness

Import `GeneralLinearGroups.ElementaryCommutator` (or `GeneralLinearGroups`).
The producer imports the existing `GeneralLinearGroups.Elementary` and
`Mathlib.GroupTheory.IsPerfect`. Let `ι` be finite with `DecidableEq ι`, and
let `R` be any `Ring`, with an independent universe. The native
`Matrix.GeneralLinearGroup.elementaryUnit i j hij a : GL ι R` has matrix
`1 + Matrix.single i j a`; `elementarySubgroup ι R` is its generated
subgroup. No commutativity, nontriviality or coefficient equality decision is
required.

## Four public theorems

- `elementaryUnit_commute_disjoint i j k l hij hkl hjk hli a b` gives
  `Commute (elementaryUnit i j hij a) (elementaryUnit k l hkl b)` when
  `i ≠ j`, `k ≠ l`, `j ≠ k`, `l ≠ i`.
- `elementaryUnit_commutator i j k hij hjk hik a b` identifies the ordered
  commutator `⁅Eᵢⱼ(a), Eⱼₖ(b)⁆ = Eᵢₖ(a * b)` for three distinct indices.
  The convention is `x * y * x⁻¹ * y⁻¹`, so `a * b` cannot be reversed.
- `elementaryUnit_eq_commutator i j k hij hik hkj a` expresses `Eᵢⱼ(a)` as
  `⁅Eᵢₖ(a), Eₖⱼ(1)⁆` when a third distinct index is available.
- `elementarySubgroup_isPerfect_of_three_le_card hcard` proves
  `Group.IsPerfect (elementarySubgroup ι R)` with
  `hcard : 3 ≤ Fintype.card ι`. This is a theorem with an explicit bound,
  not a global instance or a perfectness statement for all of `GL`.

The proofs use mathlib's matrix-single multiplication rules and subgroup
closure; they never commute noncommuting coefficients. The private client
`tests/ElementaryCommutatorClient.lean` checks genuinely noncommuting
`Matrix (Fin 2) (Fin 2) ℤ` coefficients, unequal reversed commutators,
perfectness for `Fin 3` over `ℤ`, matrix coefficients and `ZMod 1`, plus
empty/singleton index types. No rank-two perfectness, `SL = E`, ambient
normality, stable `K₁` or source correspondence follows.

Use repository `lean-toolchain` (Lean `v4.34.0-rc2`) and the unchanged
nine-package `lake-manifest.json`, including mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103`. Before any build,
fetch the matching mathlib cache; the ordinary default target includes this
module and client:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```

## Provenance and status

The original mathematical producer/client/guide are by worker-b Hive Task
`hive-request-35aa9748fd43bd94b3ec738f1ad463b088d4ae0b`, UID
`2e849319-c5e4-4143-8824-4e604660c6c5`; Prism is responsible
maintainer. This library transfers their accepted incubator PR95 at commit
`a7ef4703603c3002e964be6fb289aa9eeb903af9` (tree
`956ed94cca79087525cd6f07bb944213d9277cf3`) by the distinct worker-b
Task `hive-request-5da2d3a64872f8d02f43a4373691317fea0453de`, UID
`0c79d3fe-3ca4-433d-9f11-152854f183e2`. The earlier guide's
unregistered/UNACCEPTED snapshots described predecessor branches, **not**
this now-accepted incubator source. At this 2026-09-27 destination-transfer
checkpoint, new GLG compilation, complete private-inclusive standard-axiom
CI, independent destination review, maintainer acceptance and official
publication remain separate; the earlier official GLG release does not
publish this candidate. Source research and book text are not required or
redistributed to use these statements.
