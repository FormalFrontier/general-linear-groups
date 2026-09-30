# Finite relative conjugation and congruence commutators

Import `GeneralLinearGroups.RelativeWhiteheadConsequences` (or
`GeneralLinearGroups`). Let `X` be any finite type with decidable equality,
`R` an arbitrary `Ring` in an independent universe, `I : TwoSidedIdeal R`,
`s = stabilize (Y := X)` and `D = blockDiagonalUnit`. The producer imports
`GeneralLinearGroups.RelativeWhitehead` and
`GeneralLinearGroups.ElementaryStabilization`. No nonempty-index,
commutativity, proper-ideal or nonzero-ring assumption is required.

## Four public theorems

Two identities retain the order of factors even over noncommutative rings:

```text
stabilize_conj_eq_blockDiagonalUnit_conj g h :
  s (g * h * g⁻¹) = D g * s h * (D g)⁻¹
stabilize_commutator_eq_blockDiagonalUnit_mul g h :
  s (g * h * g⁻¹ * h⁻¹) = D g * D h * D ((h * g)⁻¹)
```

The last factor uses `(h * g)⁻¹`, never `(g * h)⁻¹`. Both membership results
land in the image in doubled ambient GL of the existing relative subgroup:

```text
(relativeElementarySubgroup (ι := X ⊕ X) I).map
  (elementarySubgroup (X ⊕ X) R).subtype
```

`stabilize_conj_mem_relativeElementarySubgroup I g h hh` uses **arbitrary**
`g : GL X R`, `h : elementarySubgroup X R` and
`hh : h ∈ relativeElementarySubgroup I`. The Whitehead diagonal of `g`
is absolutely elementary, stabilization of `h` is relatively elementary,
and conjugation uses normality *inside* the doubled elementary group.
`stabilize_commutator_mem_relativeElementarySubgroup I g h` takes
`g h : congruenceSubgroup (n := X) I`. The three diagonals of `g`, `h`
and `(h * g)⁻¹` are relative, so their ordered product is relative after
doubling. Neither theorem asserts original-rank commutator containment.

`tests/RelativeWhiteheadConsequencesClient.lean` uses the proper even ideal,
an arbitrary conjugator provably outside its congruence subgroup, and two
congruence units with unequal ordered products and a nonidentity commutator.
Empty indices and `ZMod 1` remain valid; there is no stable union, ambient
normality, excision, stable K₁ or source-coverage decision.

Pinned Lean `v4.34.0-rc2` and mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103` occur in this repository's
unchanged nine-package manifest. Fetch the matching cache before building
the public root and all fourteen ordinary client roots:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```

## Dependencies and expression credit

Prism's finite proof and plan informed these ordered, doubled relative
identities; Formal Frontier Agents developed the reusable Lean producer,
client and guide. They adapt actual earlier project expression, not book
text, and import only the local Whitehead/stabilization APIs and mathlib.
The source files retain Apache-2.0/collective-author notices. Neither the
arbitrary-GL doubled conjugation nor the congruence commutator gives
same-rank ambient relative normality, stable `K₁` or source coverage.
