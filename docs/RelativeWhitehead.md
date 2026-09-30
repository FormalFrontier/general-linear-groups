# Finite relative Whitehead block factorization

Import `GeneralLinearGroups.RelativeWhitehead` (or `GeneralLinearGroups`). It
reuses `GeneralLinearGroups.RelativeElementary` and
`GeneralLinearGroups.ElementaryWhitehead`, hence the existing native Whitehead
units and congruence subgroup. In `Matrix.GeneralLinearGroup`, let `ι` be any
finite type with `DecidableEq ι`, `R` any `Ring`, and `I : TwoSidedIdeal R`.
The index and coefficient universes are independent; empty indices, trivial
rings and noncommutative coefficients are allowed. No ideal is needed for
the factorization theorem itself.

## Four public theorems

`upperUnit_mem_relativeElementarySubgroup I a ha` and
`lowerUnit_mem_relativeElementarySubgroup I a ha` assume every entry of
`a : Matrix ι ι R` is in `I` (`ha : ∀ i j, a i j ∈ I`). They bundle the
existing block units in `elementarySubgroup (ι ⊕ ι) R` and prove membership
in the normal closure `relativeElementarySubgroup (ι := ι ⊕ ι) I` **inside**
that elementary group. `upperUnit a` has upper-right block `a`; `lowerUnit a`
has lower-left block `-a`. The six public zero/add/single block lemmas live
in `GeneralLinearGroups.ElementaryWhitehead`; specifically
`lowerUnit_single i j c` has elementary coefficient `-c`.

For any `g : GL ι R`, set `A = (g : Matrix ι ι R) - 1` and
`q = ((g⁻¹ : GL ι R) : Matrix ι ι R)`.
`blockDiagonalUnit_eq_five g` proves the **ordered** identity

```text
blockDiagonalUnit g =
  upperUnit 1 * lowerUnit (-A) * upperUnit (-1) *
    upperUnit (q * A) * lowerUnit ((g : Matrix ι ι R) * A).
```

Because lower units already include a minus sign, the first lower factor
represents `+A`, and the last represents `-(g*A)`. For
`g : congruenceSubgroup (n := ι) I`, the theorem
`blockDiagonalUnit_mem_relativeElementarySubgroup I g` puts this diagonal
in the doubled relative elementary subgroup: the congruence condition makes
the entries of `A` ideal-valued; two-sided absorption handles `q*A` and
`g*A`; normality inside the elementary group handles the conjugated first
three factors. `upperUnit 1` alone is **not** asserted to be relative.

`tests/RelativeWhiteheadClient.lean` exercises the proper even-integer ideal,
including a rank-one congruence unit not in the rank-one elementary group
but whose doubled diagonal is relative, and a proper two-sided ideal of a
noncommutative matrix coefficient ring. It also covers ideal-valued blocks,
empty indices and `ZMod 1`. No original-rank normality, stable `K₁`,
perfectness, excision or full source correspondence is asserted.

The repository pins Lean `v4.34.0-rc2` and mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103` in its unchanged
nine-package manifest. From the destination root:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```

## Dependencies and expression credit

Prism's original finite Whitehead proof exposition informed this five-factor
identity; Formal Frontier Agents authored its reusable producer/client and
the supporting elementary-block helper docstrings. The library adapts that
original project expression without importing source research or shipping
book text. The code retains Apache-2.0/collective-author notices. The
relative membership is a doubled statement, not same-rank ambient normality
or a claim of source-passage coverage.
