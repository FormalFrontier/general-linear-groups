# Elementary paths over topological rings

Import [`GeneralLinearGroups.ElementaryPaths`](../GeneralLinearGroups/ElementaryPaths.lean)
to use `Matrix.GeneralLinearGroup.elementaryUnit` and its algebraic
`elementarySubgroup`. The original elementary definitions come from
[`GeneralLinearGroups.Elementary`](../GeneralLinearGroups/Elementary.lean).

For independent universes of finite index type `ι` and coefficient type `R`,
with `[DecidableEq ι] [Ring R] [TopologicalSpace R] [IsTopologicalRing R]`,
`Matrix.GeneralLinearGroup.continuous_elementaryUnit i j hij` proves continuity
of `c ↦ Eᵢⱼ(c)` in the matrix-unit topology. Its inverse has value
`1 + Matrix.single i j (-c)`; no continuous inversion on coefficients is
needed. `continuous_elementaryUnit_subtype` maps continuously into the
elementary subgroup with its subtype topology.

For `γ : Path (0 : R) c`, `elementaryUnitPath i j hij γ` joins `1 : GL ι R`
to `elementaryUnit i j hij c`, and `elementaryUnitPathSubtype` joins the
corresponding endpoints *inside* `elementarySubgroup ι R`. Under the separate
assumption `[PathConnectedSpace R]`,
`elementarySubgroup_pathConnectedSpace` constructs a path-connected-space
instance for that subgroup by induction on its generators and subgroup
closure; `elementarySubgroup_joined_one` and `elementarySubgroup_joined`
give ambient `Joined` conclusions for subgroup elements.

```lean
import GeneralLinearGroups.ElementaryPaths

open Matrix.GeneralLinearGroup

example : PathConnectedSpace (elementarySubgroup (Fin 2) ℝ) :=
  elementarySubgroup_pathConnectedSpace
```

The [ordinary-import client](../tests/ElementaryPathsClient.lean) also uses
empty and singleton index types, a noncommutative topological matrix
coefficient ring, and a nonconstant real elementary path. This does not make
ambient `GL ι R` path connected, make an arbitrary coefficient ring path
connected, or identify `E` with `SL`, a determinant kernel or an identity
component. Neither coefficient commutativity, nontriviality, completeness,
open scalar units nor local path connectedness is assumed. The connectedness
result itself makes no closedness assertion about `E`.
