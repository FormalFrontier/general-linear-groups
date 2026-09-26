/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.Whitehead
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

/-!
# General linear groups

Reusable results about general linear groups, ideal congruence subgroups, nil
and quasi-regular ideals, reflection of matrix units through quasi-regular
quotients, local quotients, block factorizations, stability, and matrix trace
modulo additive commutators over arbitrary unital rings.

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
-/
