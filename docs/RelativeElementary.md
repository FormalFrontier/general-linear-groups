# Relative elementary subgroups of finite general linear groups

Import `GeneralLinearGroups.RelativeElementary` (or `GeneralLinearGroups`).
For finite decidable indices `ι` and arbitrary `Ring R` with independent
universes, this module uses the existing native `GL ι R`, its off-diagonal
`elementaryUnit i j hij a` and `elementarySubgroup ι R`; it also imports the
existing `GeneralLinearGroups.CongruenceSubgroup`. No commutativity,
`DecidableEq R`, nonzero-ring or positive-rank assumption is needed.

## Generators, normal closure and congruence

For `I : TwoSidedIdeal R`, `relativeElementaryGenerators I` consists of
ideal-coefficient elementary units bundled in `elementarySubgroup ι R`.
`relativeElementarySubgroup I` is their normal closure **inside** that
elementary group, not a claimed normal subgroup of the whole ambient GL.
`elementaryUnit_mem_relativeElementarySubgroup` supplies generator
membership; `relativeElementarySubgroup_normal` is its normal instance;
`relativeElementarySubgroup_mono` respects ideal inclusion; and
`relativeElementarySubgroup_bot` makes the zero-ideal subgroup trivial.
`relativeElementarySubgroup_le_congruenceSubgroup` places it inside the
elementary restriction of the existing quotient-reduction kernel, while
`relativeElementarySubgroup_map_subtype_le_congruenceSubgroup` does so for
its image in ambient GL.

For `f : R →+* S`, `mapRingHom_elementaryUnit` and
`mapRingHom_elementarySubgroup_le` preserve generators and absolute groups.
`mapElementarySubgroup f` is the restricted monoid homomorphism with
`mapElementarySubgroup_coe`, `mapElementarySubgroup_elementaryUnit`,
`mapElementarySubgroup_id`, and `mapElementarySubgroup_comp` laws.
`mapElementarySubgroup_relativeElementarySubgroup_le` assumes the **explicit**
compatibility `I ≤ J.comap f` for two-sided `I`, `J` and gives an image
inclusion; it asserts neither equality nor surjectivity on GL.

The client `tests/GeneralLinearGroupsTests/RelativeElementaryClient.lean` checks the proper ideal
`ker(ℤ → ZMod 2)`, nonzero `2` reducing to zero, compatible-image inclusion,
the proper kernel for entrywise reduction of noncommutative matrix coefficients,
noncommuting elementary conjugation, empty indices and the zero ring.
No same-rank ambient normality, relative perfectness, quotient GL
surjectivity, excision, stable `K₁` or source-coverage decision follows.

The exact environment uses Lean `v4.34.0-rc2` from
[`lean-toolchain`](../lean-toolchain), with mathlib pinned in
[`lakefile.toml`](../lakefile.toml) and resolved in the nine-package
[`lake-manifest.json`](../lake-manifest.json). To build the root and all
eighteen clients from this repository, first fetch its matching mathlib cache:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```

## Dependencies and expression credit

Prism's source-research design informed the relative subgroup and coefficient
map API; Formal Frontier Agents developed the reusable producer, client and
guide and adapted that original project expression into the standalone
library. The relative normal closure is explicitly **inside** this library's
`elementarySubgroup`; mathlib supplies the subgroup and ideal foundations.
The code retains its Apache-2.0/collective-author notices. No source
repository is a runtime dependency; bibliographic motivation and original
book text are not formalized source-coverage assertions.
