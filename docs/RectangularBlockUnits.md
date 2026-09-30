# Rectangular upper block units

Import `GeneralLinearGroups.RectangularBlockUnits` to work with
invertible block matrices on `X ⊕ Y`. The index types `X` and `Y` are separately
finite and have decidable equality; either or both may be empty, and their
universes need not agree. The coefficient ring may be noncommutative, has no
decidable-equality or nontriviality requirement, and lives in an independent
universe. The diagonal-only definitions and lemmas work even over a semiring.

For a ring `R`, `rectangularUpperUnit C : GL (X ⊕ Y) R` has matrix
`Matrix.fromBlocks 1 C 0 1`, where `C : Matrix X Y R`. Its inverse has upper
block `-C`. The `rectangularUpperUnit_zero`, `_add`, `_inv` and `_single`
lemmas respectively identify the identity, addition as multiplication, the
inverse, and a single entry with the existing `elementaryUnit (Sum.inl i)
(Sum.inr j) ... c`. Thus `rectangularUpperUnit_mem_elementarySubgroup` places
every such unit in the *existing* finite `elementarySubgroup (X ⊕ Y) R`,
including the cases where one block is empty. There is no ambient normality
assumption.

`diagonalPairUnit (A : GL X R) (D : GL Y R)` is defined using *existing* maps:

```lean
stabilize (Y := Y) A *
  reindexEquiv R (Equiv.sumComm Y X) (stabilize (Y := X) D)
```

Its matrix is `Matrix.fromBlocks A 0 0 D`; its inverse is
`diagonalPairUnit A⁻¹ D⁻¹`. With `D = 1` it is exactly `stabilize A`; with
`A = 1` it is the reindexed stabilization of `D`. No competing diagonal
constructor or second stabilization map is introduced.

With **explicit** diagonal units `A : GL X R`, `D : GL Y R` and an arbitrary
`B : Matrix X Y R`, `triangularUnit A B D` has matrix
`Matrix.fromBlocks A B 0 D`. The two ordered factorizations are

```lean
triangularUnit A B D =
  rectangularUpperUnit (B * ↑D⁻¹) * diagonalPairUnit A D

triangularUnit A B D =
  diagonalPairUnit A D * rectangularUpperUnit (↑A⁻¹ * B)
```

and `triangularUnit_inv_val` reads its inverse as
`Matrix.fromBlocks A⁻¹ (-(A⁻¹ * B * D⁻¹)) 0 D⁻¹`. Matrix multiplication
is ordered: neither `B * D⁻¹` nor `A⁻¹ * B` may be reversed. In particular,
the inverse's upper-right block starts with a **minus**, not a positive
product. Existing `lowerUnit C` has lower-left block **`-C`** and remains
unchanged. For equal indices, `rectangularUpperUnit_eq_upperUnit` and
`diagonalPairUnit_inv_pair` identify the existing published `upperUnit C`
and `blockDiagonalUnit g`.

For any group `G` and homomorphism `f : GL (X ⊕ Y) R →* G` with
`elementarySubgroup (X ⊕ Y) R ≤ f.ker`, the theorem
`map_triangularUnit_eq_diagonalPairUnit` gives
`f (triangularUnit A B D) = f (diagonalPairUnit A D)`. It does **not**
assume an abelian target or assert normality of the finite elementary
subgroup; it constructs no quotient or stable K₁. It does not claim that
invertibility of an upper triangular matrix *forces* invertibility of its
individual diagonal blocks for every ring. Supply `A` and `D` as units.

The default-built private client `tests/RectangularBlockUnitsClient.lean`
checks unequal block sizes (`Fin 1` versus `Fin 1 ⊕ Fin 1`) with nonzero `B`
over `Matrix (Fin 2) (Fin 2) ℤ`, a noncommutative coefficient ring. Its
`right_inverse_order_detected` coefficient `(1,0) = -1` detects a reversal
of `B * D⁻¹`; its `left_inverse_order_detected` coefficient `(0,1) = -1`
detects a reversal of `A⁻¹ * B`. The two concrete inverse coefficients
`(0,1) = (1,0) = 1` additionally test the sign and both ordered factors
in `-A⁻¹ B D⁻¹`. Empty left, empty right, both-empty and equal-index clients
are included. No private client declaration extends the public API.

## Dependencies and expression credit

This module reuses the native `stabilize` from
`GeneralLinearGroups.ElementaryStabilization` and the existing elementary
units, reindexing and Whitehead block constructors. Its block arguments
reuse mathlib's `Matrix.fromBlocks_multiply` and `Matrix.induction_on'` with
their original semantics and credit. Formal Frontier Agents developed the
rectangular producer, unequal-block client and guide, adapting earlier
original project expression into this standalone library. The Apache-2.0
collective-author notices remain. No incubator/source repository is a build
dependency, and this module does not establish source passage coverage.

The repository pins Lean `v4.34.0-rc2` and mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103`. Fetch the matching
mathlib cache before building the library and fourteen clients:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```
