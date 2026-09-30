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

## Dependencies and credits

These Ring-only commutator and perfectness statements are original Formal
Frontier Agents' reusable results, adapting their earlier project development
into this library. Mathlib supplies matrix-single identities and
`Group.IsPerfect`; it is not claimed to supply this library's elementary
subgroup proof. The code retains Apache-2.0 and collective-author notices.
No source-repository import, original book text or source-coverage assertion
is needed to use these theorems.
