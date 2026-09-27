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

The client `tests/RelativeElementaryClient.lean` checks the proper ideal
`ker(ℤ → ZMod 2)`, nonzero `2` reducing to zero, compatible-image inclusion,
the proper kernel for entrywise reduction of noncommutative matrix coefficients,
noncommuting elementary conjugation, empty indices and the zero ring.
No same-rank ambient normality, relative perfectness, quotient GL
surjectivity, excision, stable `K₁` or source-coverage decision follows.

The exact environment is Lean `v4.34.0-rc2`, mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103`, and the unchanged
nine-package `lake-manifest.json`. To build the root and all eight clients
from this repository, first fetch its matching mathlib cache:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```

## Provenance and status

Prism designed the relative API in source research
`source-weibel-k-book@dc2dc4d8946b0ab83b8ce916d6f68ad87c4ac749`;
the original reusable Lean producer/client and guide are by worker-b Task
`hive-request-fe47d83d9ec7ed0603df9afa59272f91b6c1d25b`, UID
`aa475138-96f3-40c8-9d3e-a2ed8997d269`. Prism accepted the full
incubator source PR95 at `a7ef4703603c3002e964be6fb289aa9eeb903af9`
(tree `956ed94cca79087525cd6f07bb944213d9277cf3`). Distinct GLG
transfer: worker-b Task `hive-request-5da2d3a64872f8d02f43a4373691317fea0453de`,
UID `0c79d3fe-3ca4-433d-9f11-152854f183e2`. Earlier unaccepted PR87/88
snapshots in the incubator guide are history. At this dated 2026-09-27
destination author checkpoint, native e37 graph checks, fresh independent
promotion review, Prism's acceptance and reviewed official publication remain
outstanding. The source research is provenance, not a build/use dependency;
no book text is distributed here.
