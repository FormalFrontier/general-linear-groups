# Finite elementary stabilization

Import `GeneralLinearGroups.ElementaryStabilization` (or
`GeneralLinearGroups`). For finite types `X : Type uX` and `Y : Type uY`
with decidable equality, and `R : Type uR` a `Semiring`, the native
`Matrix.GeneralLinearGroup.stabilize (Y := Y) : GL X R →* GL (X ⊕ Y) R`
adjoins an identity block: `[[g, 0], [0, 1]]`. It imports the preceding
`GeneralLinearGroups.RelativeElementary` and mathlib block matrices.
The three universes are independent; neither block needs to be nonempty.

## Fourteen public declarations

`stabilize_apply_inl_inl`, `stabilize_apply_inl_inr`,
`stabilize_apply_inr_inl`, `stabilize_apply_inr_inr` describe the four
blocks, and `stabilize_injective` recovers the original unit.
`mapRingHom_stabilize f g` commutes stabilization with coefficient mapping
between semirings. The identity block makes `stabilize` a **monoid hom on
units**, never a ring hom on matrices (it does not preserve matrix zero).

For `[Ring R]`, `stabilize_elementaryUnit` maps each existing generator to
the generator at `(Sum.inl i, Sum.inl j)`;
`stabilize_elementarySubgroup_le` includes the absolute elementary image.
`stabilizeElementarySubgroup` restricts the unit hom to elementary groups,
with `stabilizeElementarySubgroup_coe` and
`stabilizeElementarySubgroup_elementaryUnit` exposing its evaluation.
For any two-sided ideal `I`, `stabilize_relativeElementarySubgroup_le I`
includes the image of the **inner-elementary** normal closure in the enlarged
relative subgroup, without an equality or surjectivity claim.
`stabilize_congruenceSubgroup_le I` includes the stabilized existing
congruence kernel in the enlarged congruence kernel.

`tests/ElementaryStabilizationClient.lean` checks genuinely noncommuting
matrix coefficients, a nontrivial elementary conjugate of an ideal-valued
generator, and preservation of relative membership and congruence for the
proper reduction-mod-2 kernel. It also uses different index universes,
empty added/source blocks and the zero ring. There is no colimit, original-
rank GL-normality, image equality, stable `K₁` or source correspondence.

The destination environment is Lean `v4.34.0-rc2` and mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103` with the unchanged
nine-package `lake-manifest.json`. The ordinary build includes this module
and client; fetch the matching mathlib cache first:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```

## Provenance and status

The original incubator Lean producer/client and guide are by worker-b Task
`hive-request-c6d28d96c8c6a1c3dc45b276cd199a8cee20e982`, UID
`79046b95-69ff-4154-945a-95b1b410bc7c`, using Prism's source plan
`source-weibel-k-book@ce3f6c8f1466d9642a6333ea04c20dcd8714eec8`
and reviewed finite exposition
`source-weibel-k-book@8f633bbd2797ec45e03213b3e932776a475d2ba0`.
Prism accepted the incubator source at PR95 commit
`a7ef4703603c3002e964be6fb289aa9eeb903af9` (tree
`956ed94cca79087525cd6f07bb944213d9277cf3`); older PR91
unaccepted snapshots are historical. Distinct destination transfer:
worker-b Task `hive-request-5da2d3a64872f8d02f43a4373691317fea0453de`,
UID `0c79d3fe-3ca4-433d-9f11-152854f183e2`. At this dated
2026-09-27 author checkpoint, destination e37 CI, private-inclusive
standard-axiom audit, independent review, Prism's acceptance and official
publication are not yet established. Source research is not needed to use
or build this API; no original source text is shipped.
