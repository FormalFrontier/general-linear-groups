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

## Expression provenance and status

The generic `PresentedGroup` construction and its universal API are from
mathlib (Michael Howes and Newell Jensen); mathlib's commutator-inverse API
is by Jordan Brown, Thomas Browning and Patrick Lutz. The native
elementary-unit and commutator API and this presentation are by Formal
Frontier Agents under Apache 2.0. They are used by import rather than copied
from other implementations or from copyrighted source text.

The original incubator presentation was authored by worker-b Hive Task
`hive-request-6b39f9a4c79e5938a346f45309940f84d0b16772` (UID
`f2682c03-c1b7-4de5-9a2e-1cd6a3da9c98`), corrected at leaf
`7e6de2fd563d627da0e6b5401f7d7011af26a59e` and bounded-reviewed by
worker-a Task `hive-request-4044a0af00ae05d4ba94be2e4071b3ade07df6bf`
(UID `2a654bf7-7c6d-4f4d-8874-11fe6f542159`). Registration was authored
by worker-b Task `hive-request-d3ca9eb2ba97805844722619e16d8dbe47913c8c`
(UID `df01e742-d861-475d-b350-2b1723c5c368`). The original guide's
**2026-09-27** wording about an unregistered and unaccepted leaf on mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` describes that earlier
snapshot, **not** the subsequently accepted incubator PR109 at
`34c923b615722d4dd50980efa4ae55245a1a4b55`.

This distinct GLG source-only transfer was prepared by worker-b Hive Task
`hive-request-c645ac24da6ddcd181e73c4627845063d58a40ad` (UID
`57209be5-e440-4975-9dac-b74d068db5aa`), with Prism responsible for
planning and later destination acceptance. Its frozen destination base is
`4a85ce8223c87d2bfa47659e702f89c5442e5f56`, Lean is `v4.34.0-rc2`,
and destination mathlib is `e37d88a26f3791ed5a93daa1f949af1021b8d103`.
At this 2026-09-27 leaf-transfer checkpoint, this **new destination leaf**
is not registered in the roots or metadata, built against destination mathlib,
independently reviewed for promotion, accepted or officially released.
The then-official GLG publication at that leaf-transfer checkpoint,
`2509e13448a0ee4229a22204c73fa20faa0f0ba3`, did not contain it.
Source correspondence and coverage decisions belong in
the responsible source repository, not to users of this guide.

At the **2026-09-27 13:25:21 UTC accepted-code checkpoint**, Prism accepted
and protected-merged GLG PR60 at
`5a55a99d5cae2a6c4cd3f7312549fd77b16d40c5`. Its native full build,
private-inclusive transitive standard-three-axiom audit and fresh independent
promotion review preceded code acceptance. The preceding native-kernel release
`045ba3ac1e77a7b7f49e053792cb3fb122889ffa` was verified on private
GitHub at 13:22:10 UTC; unlike the then-official `2509` publication above,
it includes native kernels but not this presentation. Steinberg code acceptance
does **not** accept or publish a Steinberg release. Its separately reviewed
internal/public release and verified publication remain outstanding; this
guide does not decide source correspondence or coverage.
