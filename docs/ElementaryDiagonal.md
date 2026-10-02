# Elementary product-one diagonals

Import [`GeneralLinearGroups.ElementaryDiagonal`](../GeneralLinearGroups/ElementaryDiagonal.lean)
for elementary diagonal units over an arbitrary commutative ring. If
`d : Fin n → Rˣ` has product one, the GL unit `diagonalUnit d` belongs to
`Matrix.GeneralLinearGroup.elementarySubgroup (Fin n) R`, including empty
matrices and zero rings. No field, domain or nontriviality is required.

```lean
import GeneralLinearGroups.ElementaryDiagonal

open Matrix.GeneralLinearGroup

-- h : (∏ i, d i) = 1
-- diagonalUnit_mem_elementarySubgroup n d h :
--   diagonalUnit d ∈ elementarySubgroup (Fin n) R

-- g : GL (Fin n) R; hg : (g : Matrix (Fin n) (Fin n) R).det = 1
-- hp : ∀ k (hk : k ≤ n), 0 < k →
--   IsUnit (Matrix.leadingPrincipalMinor (g : Matrix (Fin n) (Fin n) R) k hk)
-- mem_elementarySubgroup_of_det_one_of_unit_leadingPrincipalMinors g hg hp :
--   g ∈ elementarySubgroup (Fin n) R
```

`diagonalUnit_val` identifies the underlying matrix of `diagonalUnit d` with
`Matrix.diagonal (fun i => (d i : R))`; `diagonalUnit_one` and
`diagonalUnit_mul` expose its unit laws. The proof factors a product-one
diagonal into existing Whitehead inverse pairs and trailing elementary
diagonals. The determinant-one corollary also uses
[unit-pivot diagonalization](UnitPivotDiagonalization.md) to cancel two
elementary factors, and requires *every positive-order leading minor* to be
a unit, not merely nonzero. This is not `SL = E` over an arbitrary ring.

The [ordinary-import client](../tests/ElementaryDiagonalClient.lean) covers
empty/singleton dimensions, integer product-one diagonals, and unit entries
over `ZMod 6`. Only the established algebraic elementary subgroup is used;
the result imposes no topology or source-specific hypotheses.
