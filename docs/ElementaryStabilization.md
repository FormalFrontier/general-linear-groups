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

## Dependencies and credits

Prism's earlier finite-stabilization proof plan and exposition informed this
implementation; Formal Frontier Agents developed the reusable Lean producer,
client and guide. This is a genuine expression credit rather than a runtime
source-repository dependency. The Semiring unit homomorphism and Ring-level
relative results reuse local elementary groups and mathlib's block matrices.
The repository's Apache-2.0 and collective-author notices apply. No book text
is shipped; no source-passage coverage, stable colimit or stable `K₁` follows.
