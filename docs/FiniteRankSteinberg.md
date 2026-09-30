# The finite-rank Steinberg presentation

Import `GeneralLinearGroups.Steinberg` to use a presentation over **any ring**
`R` and index type `ι`. Its `Steinberg.Root ι` consists of ordered pairs of
distinct indices, and its symbols `Steinberg.generator p a` are indexed by a
root and a coefficient. `Steinberg.Presented ι R` is mathlib's
`PresentedGroup` on the three explicit relator families in
`Steinberg.relations`:

* `xᵢⱼ(a) xᵢⱼ(b) = xᵢⱼ(a+b)`;
* `[xᵢⱼ(a), xₖₗ(b)] = 1` when `j ≠ k` and `l ≠ i`;
* `[xᵢⱼ(a), xⱼₖ(b)] = xᵢₖ(a*b)` for distinct `i,j,k`.

Here `[x,y] = x*y*x⁻¹*y⁻¹`. The presentation has **no** imposed
opposite-root relation. `Steinberg.generator_zero`, `.generator_neg`,
`.generator_commutator_disjoint` and `.generator_commutator` give the direct
laws. `.generator_commutator_reverse` derives
`[xᵢⱼ(a),xₖᵢ(b)] = xₖⱼ(-(b*a))` from the inverse commutator, not from
commutativity of `R`. The native `Steinberg.lift` extends a family into any
group if it satisfies the same three laws. `.lift_generator`, `.lift_unique`
and `.hom_ext` give its evaluation and universal uniqueness.

Only `Ring R` is required to define the presentation; index and coefficient
types may live in independent universes, without `DecidableEq R`, a nonzero
assumption or any `Fintype` instance. Matrix-valued
`Steinberg.toElementary` additionally needs `[Fintype ι] [DecidableEq ι]`.
It is onto this library's native
`Matrix.GeneralLinearGroup.elementarySubgroup ι R` by
`Steinberg.toElementary_surjective`. Composing with inclusion gives
`Steinberg.toGL`, whose range is **exactly** that elementary subgroup by
`Steinberg.toGL_range`. The implementation imports
`GeneralLinearGroups.ElementaryCommutator` for the native elementary-unit and
commutator results; it does not assert surjectivity onto all of `GL`.

```lean
import GeneralLinearGroups.Steinberg

open scoped commutatorElement

example {R : Type*} [Ring R] (a b : R) :
    ⁅Steinberg.generator (Steinberg.root (0 : Fin 3) 1 (by decide)) a,
      Steinberg.generator (Steinberg.root (1 : Fin 3) 2 (by decide)) b⁆ =
      Steinberg.generator (Steinberg.root (0 : Fin 3) 2 (by decide)) (a * b) :=
  Steinberg.generator_commutator (0 : Fin 3) 1 2 (by decide) (by decide) (by decide) a b
```

Rank at least three is the usual finite-rank Steinberg interpretation.
The same presentation and onto-elementary map are defined at empty, singleton
and rank-two index types, but these low-rank extensions claim only the stated
relations and surjection. Finite index rank does **not** make the coefficient
set finite, the generator set finite, or the resulting group finitely presented.
There is no asserted injection into `GL`, surjection onto all of `GL`, equality
with `SL`, determinant or normality theorem, or K₂/central-extension/stability
claim here. Neither universal central extension nor source correspondence or
source-level coverage follows from this module. In particular, no kernel
centrality, direct-limit or formalized-source-milestone assertion is made.

## Dependencies and expression credit

Mathlib supplies `PresentedGroup` and its universal API (Michael Howes and
Newell Jensen) and the commutator-inverse API (Jordan Brown, Thomas Browning
and Patrick Lutz). The Ring-only elementary symbols, the three chosen
relations, the representation into the native elementary subgroup and their
clients are Formal Frontier Agents' original mathematical development, adapted
from earlier original project expression. These constructions import mathlib,
not copyrighted book passages or a source-repository implementation. The
Apache-2.0/collective-author notices remain on the Lean files.

This module and its ordinary-import client belong to the current public root
and default test target. Lean `v4.34.0-rc2` and mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103` are pinned; first fetch the
matching mathlib cache:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```
