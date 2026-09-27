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
the public root and all eight ordinary client roots:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```

## Provenance and status

Prism's finite proof and plan are preserved in
`source-weibel-k-book@8f633bbd2797ec45e03213b3e932776a475d2ba0`
and `source-weibel-k-book@a200e6c19e5678e75ec836e6e5adc9158b400d7f`.
The original reusable producer/client and guide are by worker-b Task
`hive-request-f9c9518717f9190ac25e3ad72fc01ab6a8aadee6`, UID
`956a92f7-088d-407d-9ec0-3110d03431c8`. Prism accepted the
incubator source PR95 `a7ef4703603c3002e964be6fb289aa9eeb903af9`
(tree `956ed94cca79087525cd6f07bb944213d9277cf3`); PR93's
code-unaccepted state in the earlier source guide is a historical snapshot.
Distinct transfer: worker-b Task
`hive-request-5da2d3a64872f8d02f43a4373691317fea0453de`, UID
`0c79d3fe-3ca4-433d-9f11-152854f183e2`. At the 2026-09-27
destination-author checkpoint, native e37 CI, full private-inclusive axiom
audit, fresh independent promotion review, Prism's acceptance and reviewed
official release remain open. Source repositories and original book text
are not runtime dependencies or shipped assets.
