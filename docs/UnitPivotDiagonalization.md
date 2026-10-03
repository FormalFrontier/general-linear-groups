# Unit-pivot elementary diagonalization

Import [`GeneralLinearGroups.UnitPivotDiagonalization`](../GeneralLinearGroups/UnitPivotDiagonalization.lean);
see the [ordinary-import client](../tests/GeneralLinearGroupsTests/UnitPivotDiagonalizationClient.lean).
For `M : Matrix (Fin n) (Fin n) R` over a `CommRing R`, including rings with
zero divisors and the zero ring, `Matrix.leadingPrincipalMinor M k hk` is the
determinant of the submatrix indexed in both coordinates by the ordered
inclusion `Fin.castLE hk : Fin k → Fin n`. The minor of size zero is `1` and
the minor of size `n` is `M.det`.

Given a *unit* minor at every positive order,

```lean
h : ∀ (k : ℕ) (hk : k ≤ n), 0 < k →
  IsUnit (Matrix.leadingPrincipalMinor M k hk)
```

`Matrix.exists_elementary_diagonalization_of_unit_leadingPrincipalMinors n M h`
returns `L Q : Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R` and
`d : Fin n → Rˣ` whose underlying matrices satisfy
`L * M * Q = Matrix.diagonal (fun i => (d i : R))`.
`Matrix.det_eq_prod_of_elementary_diagonalization` gives
`M.det = ∏ i, (d i : R)`. Neither determinant one nor `Nontrivial R`, a field,
or a domain is required.

`Matrix.leadingPrincipalMinor_schur` transports every ordered leading minor
through a unit first pivot. The general `Ring`-level APIs
`Matrix.GeneralLinearGroup.reindexEquiv_mem_elementarySubgroup`,
`rectangularLowerUnit_mem_elementarySubgroup`, and `trailingElementary`
handle arbitrary finite decidable index types (also independent universes),
including empty and singleton sizes. The lower shear exchanges the two blocks
of the existing rectangular upper shear. The proof reuses the library's
elementary and stabilization constructions and mathlib's Schur complement.

Nonzero pivots do **not** suffice: over `ZMod 6`, the determinant-one matrix
`!![2, 1; 1, 1]` has nonunit leading entry `2`. The matrix
`!![5, 1; 2, 3]` has unit leading minors and determinant `1`, but a unit
pivot is not a field pivot. Even for determinant one, the induction residual
need not lie in `SL`: `diagonal ![-1, -1]` over `ℤ` has first-pivot residual
determinant `-1`. This module alone asserts neither product-one diagonal
membership in `E`, openness or path-connectedness, continuous factor selection,
nor quantitative norm or factor bounds; see
[elementary diagonals](ElementaryDiagonal.md) for the first of these.

To compile the producer and client in an authorized checkout, use this
repository's pinned Lean/mathlib graph and first fetch its matching precompiled
mathlib cache. A failed cache fetch is not a reason to build mathlib from source.
