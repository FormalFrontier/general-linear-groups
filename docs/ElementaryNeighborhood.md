# Elementary neighborhoods in finite special linear groups

[`GeneralLinearGroups.ElementaryNeighborhood`](../GeneralLinearGroups/ElementaryNeighborhood.lean)
uses mathlib's topology on `Matrix.SpecialLinearGroup (Fin n) R` and
`SpecialLinearGroup.toGL`. Its `Matrix.SpecialLinearGroup.elementarySubgroup`
is the **comap** of the library's existing GL elementary subgroup; it is
distinct from the GL subgroup and introduces no new elementary generators.

For `[CommRing R] [TopologicalSpace R] [IsTopologicalRing R]`,
`isOpen_unitLeadingPrincipalMinors` proves the locus of all-unit ordered
leading minors open **if** `{r : R | IsUnit r}` is open. The identity is in
this locus, and `unitLeadingPrincipalMinors_subset_elementarySubgroup`
places it in the SL comap using the separate determinant-one and
unit-pivot criterion. With scalar units open, topological subgroup arguments
prove
`isOpen_elementarySubgroup` and `isClosed_elementarySubgroup` with no
separation axiom, field, or domain assumption.

**Separately**, `[PathConnectedSpace R]` lets paths in the GL elementary
subgroup lift to SL without assuming scalar units are open: every elementary
element has determinant one.
Together with the open scalar-unit locus, this identifies the comap with
`Subgroup.pathComponentOne (Matrix.SpecialLinearGroup (Fin n) R)` by
`elementarySubgroup_eq_pathComponentOne`. Openness of scalar units by itself
does not imply path-connectedness: the discrete ring `ℤ` separates these
hypotheses. No continuous factor selection, continuous inversion assumption,
quantitative neighborhood or assertion `SL = E` is supplied. Dimensions
`0` and `1`, zero rings and arbitrary coefficient universes are permitted.
The [ordinary-import client](../tests/GeneralLinearGroupsTests/ElementaryNeighborhoodClient.lean)
checks open and closed cases, the path-component result, integer coefficients,
and an empty zero-ring example.
