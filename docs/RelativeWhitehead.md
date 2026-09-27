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

## Provenance and status

Prism developed the mathematical factorization in source exposition
`source-weibel-k-book@8f633bbd2797ec45e03213b3e932776a475d2ba0`;
the original reusable producer/client and six published-in-incubator helper
docstrings were authored by worker-b Task
`hive-request-474d5a18341359e66cfefad57a2fe7fce5fd95be`, UID
`201cfd05-92f3-411c-9f16-9927145c58ca`. This is a transfer of Prism's
accepted incubator PR95 `a7ef4703603c3002e964be6fb289aa9eeb903af9`
(tree `956ed94cca79087525cd6f07bb944213d9277cf3`) by distinct worker-b
Task `hive-request-5da2d3a64872f8d02f43a4373691317fea0453de`, UID
`0c79d3fe-3ca4-433d-9f11-152854f183e2`. Incubator PR91's old
unaccepted/branch-only status is historical, not source PR95's status. At
this 2026-09-27 **unaccepted destination** checkpoint, new native CI with
private-inclusive axiom audit, independent promotion review, maintainer
acceptance and an official release still require separate decisions. No
original book text or source-repository dependency is included.
