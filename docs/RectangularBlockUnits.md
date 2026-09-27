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

## Dependencies and status

The native `stabilize` is reused from
`GeneralLinearGroups.ElementaryStabilization`; elementary generators and the
elementary subgroup, `reindexEquiv`, `upperUnit` and `blockDiagonalUnit`
come from existing local general-linear-groups modules. Mathlib's
`Matrix.fromBlocks_multiply` and `Matrix.induction_on'` are reused with their
existing semantics and credit. This reusable module is independent of source
research records. Its Lake inputs remain the repository's pinned Lean
`v4.34.0-rc2` and mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`;
no incubator dependency is required. The prior general-linear-groups main
`72861c49b8ed620096b4749e171e25405c3652d2` has the same tree as
its official published release `51a4ca8e4a61eef09ce8164a53f4f37c3f520a00`.
Neither prior artifact contains this rectangular addition.

Original incubator focused-check snapshot (2026-09-27): the two new Lean modules compiled
with `lake --wfail build` after a successful matching `lake exe cache get` on
PR #95 commit `a7ef4703603c3002e964be6fb289aa9eeb903af9`, using the
then-pinned official general-linear-groups `706a257f35618c098573646653a319bd4f14f8e6`.
The independent leaf review is `3e029bdab05ecad4425abc79c0ba59ff6361c10b`
(`reviews/rectangular-block-units/REVIEW.md`), by worker-a Task
`hive-request-d58bc9fb1f33c1ab04462845819fa599cfd02540` /
`21cca7cb-eaa7-4145-89fc-d310aa764158`. At registration preparation on
2026-09-27, PRs #95–#97 had integrated separately.
At that historical registration checkpoint, PR #100
`89987a964c706fcf92ad8ef6dd0623b68170d448` was **UNACCEPTED**, and
PRs #98–#100 retained their separate owner gates. The original leaf review
did not certify that changed registration graph. The completed source
registration was subsequently accepted and integrated as incubator PR #101,
commit `1b04c1d15c15b0f7adf7dcfec2861b451a4d1a79`, with its own native
build/axiom CI. This is historical source evidence, not destination e37
compatibility or source correspondence/coverage. Registrar: worker-b Task
`hive-request-9f77f8c1f4015db6ddf102989bf1d24ae36a6048` /
`63beac6e-e93f-4a54-8fb8-650114a41967`. Original author:
`formalization-worker-b`, Hive Task
`hive-request-f05b4be9b9263abe877517328bf1ff2eb3ccbe6c` /
`f689b30f-0a76-4727-8ec2-68907a224546`.

At the **2026-09-27 destination transfer-author checkpoint**, this
source-only promotion was **UNACCEPTED**. It carried the unchanged proof
bodies into this library with only producer/client imports and truthful
Apache-2.0/author headers adapted. Transfer author: worker-b Task
`hive-request-cf565ac88c8dc0b5274168e7cb2dbfc1abfab323` /
`d7ced547-d176-4d48-af8d-ad239d49cff9`; Prism is the responsible
maintainer. The destination default-root nine-client build, complete
private-inclusive transitive standard-axiom CI at e37, fresh independent
promotion review, Prism's acceptance and reviewed official GitHub release
were distinct outstanding gates at that checkpoint. This is provenance
history, not a live acceptance or release registry; later decisions bind their
exact revisions. No source coverage or stable K₁ claim follows.
