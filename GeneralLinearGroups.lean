/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.Whitehead
public import GeneralLinearGroups.Elementary
public import GeneralLinearGroups.ElementaryWhitehead
public import GeneralLinearGroups.Reindex
public import GeneralLinearGroups.CongruenceSubgroup
public import GeneralLinearGroups.QuasiregularIdeal
public import GeneralLinearGroups.MatrixQuasiregular
public import GeneralLinearGroups.QuasiregularQuotient
public import GeneralLinearGroups.NilIdeal
public import GeneralLinearGroups.LocalQuotient
public import GeneralLinearGroups.NonUnitalNilpotent
public import GeneralLinearGroups.UnitalComparison
public import GeneralLinearGroups.NonUnitalQuasiregular
public import GeneralLinearGroups.AdditiveCommutator
public import GeneralLinearGroups.MatrixTrace
public import GeneralLinearGroups.ElementaryCommutator
public import GeneralLinearGroups.RelativeElementary
public import GeneralLinearGroups.RelativeWhitehead
public import GeneralLinearGroups.ElementaryStabilization
public import GeneralLinearGroups.RelativeWhiteheadConsequences
public import GeneralLinearGroups.RectangularBlockUnits
public import GeneralLinearGroups.DualNumberKernels
public import GeneralLinearGroups.DualNumberKernelAdjoint
public import GeneralLinearGroups.Steinberg
public import GeneralLinearGroups.DualNumberMixedCommutator
public import GeneralLinearGroups.DualNumberMixedSLCommutator
public import GeneralLinearGroups.UnitPivotDiagonalization
public import GeneralLinearGroups.SchurReduction
public import GeneralLinearGroups.ZeroProductStabilization
public import GeneralLinearGroups.RectangularUnitSwitch
public import GeneralLinearGroups.ElementaryPaths
public import GeneralLinearGroups.ElementaryDiagonal
public import GeneralLinearGroups.UnitPivotInduction
public import GeneralLinearGroups.ElementaryNeighborhood
public import GeneralLinearGroups.StableElementary
public import GeneralLinearGroups.StableDeterminant
public import GeneralLinearGroups.LocalElementaryGeneration

/-!
# General linear groups

Reusable results about general linear groups, ideal congruence subgroups, nil
and quasi-regular ideals, reflection of matrix units through quasi-regular
quotients, local quotients, block factorizations, stability, and matrix trace
modulo additive commutators over arbitrary unital rings.

The elementary layer supplies Ring-only off-diagonal GL units, their generated
subgroup, and membership of Whitehead's upper/lower/signed-swap and doubled
block-diagonal units, including empty index types and trivial rings.
The finite relative layer provides ordered elementary commutators and
rank-at-least-three perfectness, ideal-coefficient normal closure inside the
elementary subgroup, doubled relative Whitehead membership, and stabilization
of elementary and congruence subgroups over arbitrary rings.

The nonunital-nilpotent layer defines positive-power nilpotence without a
multiplicative identity, proves strictly upper triangular matrices nilpotent,
and constructs their canonical `1 + x` elements in the augmentation-kernel
general linear group.

The unital-comparison layer identifies the unitization of a unital algebra
with the product of its scalar ring and the algebra. It consequently proves
that the augmentation-kernel general linear group agrees canonically with the
ordinary finite general linear group for a unital ring.

The nonunital-quasiregular layer identifies matrix quasiregularity with
invertibility after entrywise unitization and with representability by `1 + x`
in the augmentation-kernel general linear group.

The rectangular-block layer assembles explicit diagonal units and ordered
upper triangular units for independent finite index types, including empty
blocks, over arbitrary rings. Its upper off-block factor is elementary.

The elementary diagonalization layer uses unit ordered leading principal
minors over commutative rings to reduce finite matrices to diagonals by
elementary factors. Product-one diagonals are elementary. Elementary units
depend continuously on coefficients over topological rings; under separately
stated path-connectedness and open-unit assumptions, the elementary subgroup
of the native finite special linear group equals its identity path component.

The native dual-number layer identifies the actual GL, SL and scalar-unit
reduction kernels over commutative rings with additive first-order coefficients,
and relates determinant, trace, coefficient maps and left conjugation to their
matrix and trace-zero Lie-algebra counterparts. It includes empty finite ranks
and does not identify abelian kernel commutators with matrix Lie brackets.

The iterated dual-number layer proves an ordered commutator of genuine native GL
units is the mixed coefficient lift of the associative matrix bracket. It
identifies the resulting element in the actual outer reduction kernel and
reads back its full pure-inner matrix over arbitrary commutative rings.

For trace-zero inputs, its native SL refinement identifies the ordered
commutator of actual special-linear factors with the mixed lift of `XY - YX`.
It packages the result in the actual SL outer reduction kernel and reads back
its pure-inner trace-zero coefficient, without an arbitrary-GL determinant claim.

The Steinberg layer gives a native presented group on additive, disjoint and
ordered-composable elementary-symbol relations over any ring, with universal
lifts and, for finite decidable indices, a surjection onto the elementary
subgroup. It imposes no opposite-root relation or central-extension claim.
-/
