# General linear groups

A Lean library for finite and stable general linear groups: elementary and relative
matrices, unit-pivot diagonalization, paths and SL neighborhoods, block
factorizations, matrix corners, ideal quotients, trace, stabilization, Steinberg
groups and dual-number GL/SL kernels. Core ring results allow noncommutative coefficients;
dual-number and determinant results use commutative rings. Indices are finite
and decidable where required. The [module guides](docs/README.md) detail the
statements, examples and limitations; [mathlib](https://github.com/leanprover-community/mathlib4)
supplies foundational APIs.

## Headline results

- **Signed swaps and even permutation matrices.** Over any possibly noncommutative
  `Ring R`, the word `e_ij(1) e_ji(-1) e_ij(1)` gives the signed coordinate swap
  with block `[0,1;-1,0]`. Every even permutation of a finite decidable basis gives
  an element of the original finite elementary subgroup, including ranks zero,
  one and two and zero rings. The permutation unit sends `e_i` to `e_(σ i)`;
  no parity converse is asserted in characteristic two. The argument follows
  Weibel, *The K-book*, III.1.2.1, using Mathlib's permutation units and generation
  of the alternating group by three-cycles.
  [Signed coordinate swaps and even permutations](GeneralLinearGroups/ElementaryPermutation.lean).

- **Upper-triangular semiring nilpotence.** For an arbitrary, possibly
  noncommutative `Semiring R` and an independently-universed finite linearly ordered
  index type, an upper triangular matrix is nilpotent if and only if every diagonal
  entry is nilpotent. Given `e : ι → ℕ` killing the corresponding diagonal entries,
  the bound is `A ^ (∑ i, e i) = 0`, including empty indices and zero exponents.
  The strict `Fin n` predicate uses only `Zero`; its support bound holds over
  `NonUnitalNonAssocSemiring` and its nilpotence over `NonUnitalSemiring`.
  Positive-power index `n` means `n + 1` factors, not an exact `n`th-power bound.
  The unitization and relative general linear constructions require
  `NonUnitalRing`.
  [Upper-triangular nilpotence](GeneralLinearGroups/UpperTriangularNilpotent.lean),
  [nonunital powers and strict triangularity](GeneralLinearGroups/NonUnitalNilpotent.lean).

- **Finite block-triangular units.** Over any possibly noncommutative `Ring`,
  a block-triangular matrix on a finite decidable index type is a unit if each
  equality-fiber diagonal block is a unit and its represented labels form a
  strict chain in a `Preorder`. For a `PartialOrder`, a chain for `≤` suffices.
  The index, label and coefficient universes are independent. Labels have
  decidable equality but need not be finite or globally linearly ordered,
  and block sizes may differ. Empty indices, empty fibers and zero rings are
  included. Over a `Semiring`, the converse holds if each original
  diagonal-block matrix monoid is Dedekind-finite: an ambient matrix unit
  then has unit diagonal blocks. Separately, given `[Invertible M]` and unit
  diagonal blocks, the given inverse `⅟M` is block triangular over a semiring,
  with no direct-finiteness assumption. Both directions retain the same
  represented-chain hypotheses; neither asserts semiring sufficiency from
  diagonal units or derives matrix direct finiteness from scalar direct
  finiteness.
  [Block-unit criterion](GeneralLinearGroups/BlockTriangularUnits.lean).

- **Matrix ideal-power bounds and nilpotence.** For a `Semiring R` and a left
  ideal `I : Ideal R`, an ordered list `As` of square matrices with entries in
  `I` has `(As.prod) i j ∈ I ^ As.length`. The finite decidable index type has
  a universe independent of the coefficients. Repeated factors recover
  `(A ^ k) i j ∈ I ^ k`. Any exponent annihilating
  the whole ideal also annihilates the matrix, so `IsNilpotent I` implies
  `IsNilpotent A`. Empty lists, empty indices and zero semirings are included,
  without two-sidedness or commutativity. Right-append induction matches
  `I ^ (k + 1) = I ^ k * I`, without a multiplicative monoid on arbitrary
  left ideals; pointwise nilness of an arbitrary ideal does not give a
  uniform exponent. For a `CommSemiring R`, however, a finite
  square matrix with nilpotent entries is nilpotent: its finitely generated
  entry ideal is contained in the nilradical and is therefore nilpotent.
  This needs no Noetherian hypothesis and includes empty indices and zero semirings.
  [Ordered-product bound and nilpotence](GeneralLinearGroups/MatrixNilpotentIdeal.lean),
  [nilpotent entries](GeneralLinearGroups/MatrixNilpotentEntries.lean),
  [nonzero dual-number diagonal](tests/GeneralLinearGroupsTests/MatrixNilpotentIdeal.lean),
  [nonzero matrix over `ZMod 4`](tests/GeneralLinearGroupsTests/MatrixNilpotentEntriesClient.lean).

- **Kronecker products of matrix units.** Over any `Semiring`, the Kronecker
  product of two unit matrices is a unit, for independently-universed finite
  decidable square indices, including empty indices and zero semirings. The
  ordered factorization `(A ⊗ₖ 1) * (1 ⊗ₖ B)`, for chosen input units with
  stored inverse values `A'` and `B'`, supplies the reversed inverse witness
  `(1 ⊗ₖ B') * (A' ⊗ₖ 1)`; tensoring input inverses is not valid in general
  over noncommutative coefficients. The rectangular mixed identity
  needs only a `NonAssocSemiring` and finite, decidable middle indices. Over
  commutative coefficients, the extracted unit agrees with mathlib's general
  linear Kronecker construction.
  [Unit preservation](GeneralLinearGroups/KroneckerUnits.lean),
  [operational examples](tests/GeneralLinearGroupsTests/KroneckerUnits.lean).

- **Single-entry matrix corners.** For a `Semiring R`, finite decidable indices
  and a chosen index `i`, the corner of `Matrix ι ι R` at the diagonal matrix
  unit `single i i 1` is ring-equivalent to `R` by extracting the `(i,i)` entry;
  its inverse inserts a coefficient there. The corner identity is the matrix
  unit, which need not be the ambient matrix identity. The equivalence also
  covers noncommutative and zero semirings.
  [Corner equivalence](GeneralLinearGroups/MatrixCorner.lean),
  [concrete clients](tests/GeneralLinearGroupsTests/MatrixCornerClient.lean).

- **Whitehead factorization and doubled lifting.** Over any `Ring`, the
  block diagonal `diag(g, g⁻¹)` of a unit is elementary. A surjective ring
  homomorphism lifts this *doubled* block as a unit; it need not lift the
  original same-rank unit. For separately finite block indices, explicitly
  supplied diagonal units also give rectangular upper-triangular units with
  ordered inverse block `-(A⁻¹ * B * D⁻¹)`.
  [Factorization](GeneralLinearGroups/Whitehead.lean),
  [doubled lift](GeneralLinearGroups/Whitehead.lean#L164),
  [elementary membership](GeneralLinearGroups/ElementaryWhitehead.lean#L117),
  [rectangular guide](docs/RectangularBlockUnits.md).

- **Stable general linear and elementary groups.** Initial-segment stabilization
  defines a coherent system of finite general linear groups over any `Semiring`,
  whose noncommutative direct limit has finite representatives, an eventual
  equality criterion, compatible lifts and coefficient maps. Over any `Ring`, the
  directed union of finite elementary images is the stable commutator subgroup;
  it is perfect in its own right and normal in stable general linear groups.
  Its quotient is canonically the abelianization, naturally under coefficient
  maps. No finite ambient elementary normality or commutativity hypothesis is needed.
  [Stable general linear group](GeneralLinearGroups/StableGeneralLinear.lean),
  [stable elementary group](GeneralLinearGroups/StableElementary.lean),
  [boundary and quotient clients](tests/GeneralLinearGroupsTests/StableElementaryClient.lean).

- **Finite coefficient products of stable groups and elementary quotients.**
  For arbitrary `Semiring R` and `Semiring S` in independent universes,
  coefficient projections give `StableGL (R × S) ≃* (StableGL R × StableGL S)`.
  For `[Finite ι]` and a family of semirings `R i`, evaluation gives
  `StableGL (∀ i, R i) ≃* (∀ i, StableGL (R i))`, including the empty family.
  Over arbitrary rings these comparisons carry the stable elementary subgroup
  onto the product of the elementary subgroups and induce equivalences of the
  existing elementary quotients. All comparisons commute with arbitrary
  coefficient maps; inverse-stage computations allow unequal representative
  ranks after passage to any common upper bound. Zero rings and rank zero are
  included; no unrestricted infinite-product stable-group equivalence is asserted.
  These extend the binary ring example in Weibel, *The K-book*, Example III.1.1.3.
  [Finite coefficient products](GeneralLinearGroups/StableProduct.lean).

- **Matrix invariance of stable groups and elementary quotients.** For `0 < n`,
  fixed row-major flattening gives
  `StableGL (Matrix (Fin n) (Fin n) R) ≃* StableGL R` over any `Semiring R`.
  Over a `Ring R`, it induces an equivalence of the existing stable elementary
  quotients. Over a `CommRing R`, the transported quotient determinant on a
  matrix-ring unit is its ordinary finite determinant.
  [Matrix invariance](GeneralLinearGroups/StableMatrix.lean).

- **Stable determinant.** Over a commutative ring, finite determinants induce
  homomorphisms on stable general linear groups, their elementary quotient and
  their abelianization. Rank-one units provide determinant sections; the
  elementary subgroup lies in the determinant kernel. The abelian elementary quotient
  splits as the product of its
  determinant kernel and the units, naturally under coefficient maps; this
  does not assert a product splitting of stable general linear groups.
  For commutative local rings, elementary matrices equal the determinant kernel,
  and the existing quotient determinant is an equivalence with the units.
  The rank-one map itself is defined over any semiring.
  [Determinant and rank-one maps](GeneralLinearGroups/StableDeterminant.lean),
  [integer and boundary examples](tests/GeneralLinearGroupsTests/StableDeterminantClient.lean).

- **Zero-product elementary stabilization.** For rectangular `A`, `B` over any
  `Ring` with `B * A = 0`, the unit `1 + A * B` has inverse `1 - A * B`.
  Stabilizing by the identity on the other block gives exactly the ordered
  commutator of the upper shear of `A` and lower shear of `B`, hence an
  elementary unit. Both index types may be empty.
  [Construction and factorization](GeneralLinearGroups/ZeroProductStabilization.lean),
  [integer and boundary examples](tests/GeneralLinearGroupsTests/ZeroProductStabilizationClient.lean).

- **Rectangular complement isomorphisms.** In any preadditive category
  `C : Type u` with `Category.{v} C`, for arbitrary objects `X`, `Y` and
  morphisms `a : X ⟶ Y`, `b : Y ⟶ X`, the complements are simultaneously
  isomorphisms:
  `IsIso (𝟙 X - a ≫ b) ↔ IsIso (𝟙 Y - b ≫ a)`. Their canonical inverse is
  `inv (𝟙 X - a ≫ b) = 𝟙 X + a ≫ inv (𝟙 Y - b ≫ a) ≫ b` under only
  `IsIso (𝟙 Y - b ≫ a)`. The universes `u`, `v` are independent; no
  finiteness, biproduct or nonzero-object hypothesis is imposed. The
  rectangular unit-switch inverse below is a finite-matrix specialization.
  [Criterion and inverse](GeneralLinearGroups/RectangularIsomorphisms.lean).

- **Rectangular unit switch.** Over any `Ring`, for independently finite,
  decidable index types, a unit `g = 1 + A * B` determines a unit
  `h = 1 + B * A` with inverse `1 - B * g⁻¹ * A`. Its diagonal pair
  `diag(g, h⁻¹)` is the ordered product
  `U(A) L(B) U(-(g⁻¹ * A)) L(-(B * g))`, hence elementary.
  Empty blocks and the zero ring are allowed; `B * A = 0` recovers the
  zero-product stabilization commutator above.
  [Construction and factorization](GeneralLinearGroups/RectangularUnitSwitch.lean),
  [integer and boundary examples](tests/GeneralLinearGroupsTests/RectangularUnitSwitchClient.lean).

- **Ring Schur reduction.** For independently finite, decidable block indices
  over any `Ring`, an invertible northwest block `A` makes
  `[[A, B], [C, D]]` a unit exactly when the ordered residual
  `D - C * ⅟A * B` is a unit. Given a unit residual, the corresponding block
  unit has an explicit ordered inverse; homomorphisms killing the elementary
  subgroup see only the diagonal pivot and residual, with no condition on
  the target group. Empty blocks and the zero ring are included.
  [Construction and criterion](GeneralLinearGroups/SchurReduction.lean),
  [noncommutative and boundary clients](tests/GeneralLinearGroupsTests/SchurReductionClient.lean).

- **Unit-pivot reduction and elementary diagonals.** Over any `CommRing`,
  unit ordered leading minors permit two-sided elementary diagonalization;
  a product-one diagonal is elementary, and the unit-pivot, determinant-one
  criterion puts a finite GL unit in `E`. This is not a general `SL = E`
  theorem; the minor hypothesis is stronger than nonvanishing. More generally,
  if an elementary left factor can produce a unit leading
  entry for every invertible matrix at every successor rank, the same
  two-sided reduction exists at every finite rank. The latter theorem is
  conditional on that all-rank pivot property; it does not assert an
  unconditional elementary generation theorem.
  [Unit-pivot guide](docs/UnitPivotDiagonalization.md),
  [conditional pivot induction](GeneralLinearGroups/UnitPivotInduction.lean),
  [diagonal guide](docs/ElementaryDiagonal.md).

- **Elementary generation over local rings.** Every invertible finite matrix
  over a commutative local ring has elementary left and right factors reducing
  it to a diagonal of units, without a leading-minor hypothesis. At every
  finite rank, determinant one characterizes the elementary subgroup. The
  stable elementary subgroup is the determinant kernel, and the elementary
  quotient is canonically the coefficient units via the existing determinant
  and rank-one section. Over a field, Mathlib transvection lists give an
  invertible diagonal factorization.
  [Local generation](GeneralLinearGroups/LocalElementaryGeneration.lean),
  [nonfield and rank-boundary clients](tests/GeneralLinearGroupsTests/LocalElementaryGenerationClient.lean).

- **Elementary paths and SL neighborhoods.** Over a topological ring,
  elementary GL units vary continuously with coefficients, even when the
  coefficient ring is noncommutative. Path-connected coefficients make the
  elementary subgroup path connected. For commutative coefficients, an open
  scalar-unit locus makes its comap in Mathlib's special linear group open
  and closed; additionally path-connected coefficients identify it with the
  identity path component.
  [Paths guide](docs/ElementaryPaths.md),
  [neighborhood guide](docs/ElementaryNeighborhood.md).

- **Scalar unit reflection and canonical quasi-regular kernels.** For
  `f : R →+* S` from a possibly noncommutative ring to a semiring,
  `IsLocalHom f` (reflection of units) makes the canonical two-sided kernel
  `TwoSidedIdeal.ker f` quasi-regular, **without surjectivity**, by
  [`RingHom.isQuasiregular_ker`](GeneralLinearGroups/QuasiregularQuotient.lean).
  For a **surjective** such map, unit reflection is equivalent to kernel
  quasi-regularity by
  [`RingHom.isLocalHom_iff_isQuasiregular_ker`](GeneralLinearGroups/QuasiregularQuotient.lean);
  its reverse direction is also available through
  [`RingHom.isLocalHom_of_surjective_of_isQuasiregular_ker`](GeneralLinearGroups/QuasiregularQuotient.lean).
  Mathlib supplies `IsUnit (f a) ↔ IsUnit a` via `isUnit_map_iff`; under
  surjectivity it also gives a surjective induced map on units. Source and
  target universes are independent; neither commutativity, local-ring
  structure, nontriviality nor nilness of the kernel is assumed. Nil kernels
  specialize through `TwoSidedIdeal.IsNil.isQuasiregular`.

- **Lifting modulo quasi-regular ideals.** For a two-sided ideal, its
  unitization general linear group identifies with the congruence kernel;
  quasi-regularity of *every* ideal element additionally makes the quotient
  GL map surjective. The Jacobson radical is the greatest quasi-regular
  ideal, and pointwise nil ideals provide examples without a shared nilpotence
  exponent.
  [Kernel equivalence](GeneralLinearGroups/CongruenceSubgroup.lean#L292),
  [quotient lifting](GeneralLinearGroups/QuasiregularQuotient.lean#L139),
  [ideal characterization](GeneralLinearGroups/QuasiregularIdeal.lean#L207).

- **Trace modulo additive commutators.** For a chosen index `p : n`,
  trace gives an additive equivalence from square matrices modulo additive
  commutators to the coefficient ring modulo additive commutators; its inverse
  inserts a scalar in the `p,p` corner. The forward map also works at empty
  rank. These are *additive groups*, not quotient rings or a `K₀` descent.
  [Equivalence and forward map](GeneralLinearGroups/MatrixTrace.lean).
  The following characteristic laws use weaker hypotheses:
  [cyclic representatives and unit conjugation](GeneralLinearGroups/AdditiveCommutator.lean)
  require `AddCommGroup` with `Mul`, respectively `Monoid`, without distributivity;
  [raw block trace](GeneralLinearGroups/MatrixTrace.lean) requires only
  `AddCommMonoid` and two independently-universed finite index types, without
  decidable equality or nonemptiness. The raw `Sum`-indexed block shape
  complements mathlib's dependent `trace_blockDiagonal'` formula.

- **Finite elementary and relative structure.** Off-diagonal elementary
  units generate `E`; ordered commutator laws prove that `E` is perfect at
  rank at least three. A two-sided ideal defines the relative normal closure
  *inside `E`*, not a claimed same-rank normal subgroup of ambient `GL`.
  Congruence units become relatively elementary after Whitehead doubling;
  stabilization preserves elementary, relative and congruence inclusions.
  [Perfectness](GeneralLinearGroups/ElementaryCommutator.lean#L80),
  [relative subgroup](GeneralLinearGroups/RelativeElementary.lean#L98),
  [relative Whitehead](GeneralLinearGroups/RelativeWhitehead.lean#L134),
  [guides](docs/README.md).

- **A Steinberg presentation and universal maps.** Over any `Ring`, for an
  arbitrary index type, symbols satisfy precisely the additive, disjoint-root
  and ordered-composable-root relations, and compatible maps extend uniquely.
  Finite decidable indices additionally give a surjection onto `E`, not
  onto all of `GL`. The reverse relation has coefficient `-(b * a)`; no
  opposite-root, central-kernel or `K₂` theorem is claimed.
  [Universal lift](GeneralLinearGroups/Steinberg.lean#L121),
  [onto-`E` map](GeneralLinearGroups/Steinberg.lean#L206),
  [presentation guide](docs/FiniteRankSteinberg.md).

- **Units over square-zero kernels.** For a homomorphism from any `Ring` to
  any `Semiring`, a square-zero kernel identifies the units mapping to `1`
  with the additive kernel, written multiplicatively. The coordinates are
  `u ↦ u - 1` and `x ↦ 1 + x`, with inverse unit `1 - x`. The hypothesis
  kills every mixed product of kernel elements; no commutativity or
  surjectivity is needed. The scalar dual-number equivalence is a
  specialization with its explicit lift and readback preserved. This is the
  algebraic ingredient of Fesenko–Vostokov, Chapter I (5.4)(3), not a
  unit-lifting or valuation-layer quotient theorem.
  [Equivalence and coordinate API](GeneralLinearGroups/SquareZeroUnits.lean),
  [dual-number comparison](GeneralLinearGroups/DualNumberSquareZeroUnits.lean).

- **Principal-unit ideal layers on original-ring units.** For left ideals
  `I, J` in any `Ring`, with `I ^ 2 ≤ J`, the stock stabilizer of `[1]` in
  the quotient left module `R / I` maps by `u ↦ [u - 1]` to the additive
  layer `I / (I ∩ J)`, written multiplicatively. Its kernel is exactly the
  relative stabilizer modulo `J`, which is therefore normal. If additionally
  `I ≤ Ring.jacobson R`, the map is surjective and its kernel quotient is
  isomorphic to that additive layer, with inverse `[x] ↦ [1 + x]` in the
  original ring. Neither ideal needs to be two-sided, and `J ≤ I` is not
  assumed. For two-sided `I`, the carrier agrees with the kernel of reduction
  on units. The nonzero-denominator model uses `(3)/(9)` in `ZMod 27`;
  the integer boundary explains the original-unit lifting hypothesis.
  [Equivalence and characteristic laws](GeneralLinearGroups/PrincipalUnits.lean),
  [models and boundary](tests/GeneralLinearGroupsTests/PrincipalUnitsClient.lean).
  For a commutative domain `R`, a nonzero principal ideal
  `I = Ideal.span {π}` contained in `Ideal.jacobson ⊥`, and `n ≥ 1`,
  the original-ring unit stabilizer at `I ^ n`, modulo its exact coordinate
  kernel (the relative deeper stabilizer at `I ^ (n + 1)`), is equivalent
  to `Multiplicative (R ⧸ I)`. It sends `[1 + a * π ^ n]` to `[a]`;
  the inverse returns that original-ring unit class. The target is the additive
  coefficient **ring**, not necessarily a field. Replacing `π` by `u * π`
  for `u : Rˣ` with residue unit `ū` multiplies a fixed class's forward coefficient
  by `(ū⁻¹) ^ n`; the inverse at a fixed coefficient uses the old inverse
  with parameter multiplied by `ū ^ n`. Normality and surjectivity are
  conclusions, not assumptions; exponent zero instead gives multiplicative
  reduction.
  [Coefficients and generator-change laws](GeneralLinearGroups/PrincipalUnits/Powers.lean),
  [coefficient clients](tests/GeneralLinearGroupsTests/PrincipalUnitsPowersClient.lean).

- **Principal-unit commutators and nilpotence.** Over any `Ring R`, including
  noncommutative and zero rings, write `U(I)` for the stock `Rˣ`-stabilizer
  of `1` in the quotient left module `R ⧸ I`. For two-sided `I`, this is
  the kernel of reduction on units to the quotient ring. Arbitrary left ideals
  `A, B` satisfy `[U(A), U(B)] ≤ U(A * B + B * A)`. For two-sided `I`,
  `[U(I ^ a), U(I ^ b)] ≤ U(I ^ (a + b))` for all `a, b : ℕ`, including
  zero, without a nilpotence assumption. For any left ideal `I`, the lower
  central series has `LCS(k) ≤ U(I ^ (k + 1))`, with zeroth term `U(I)`.
  If `I ^ N = ⊥`, then `U(I)` is nilpotent of class at most `N - 1`
  (natural subtraction); `N = 0` and `N = 1` give the trivial subgroup.
  This is not a nilpotence claim about the full unit group. Positive additive
  layers use the preceding ideal-layer and power-coordinate API, not an
  additive equivalence at exponent zero.
  [Commutator bounds and nilpotence](GeneralLinearGroups/PrincipalUnits/Filtration.lean).

- **Leading coordinates of principal-unit commutators.** For any left ideal
  `I` in any `Ring R` and positive `a, b`, let `x = u - 1 ∈ I ^ a` and
  `y = v - 1 ∈ I ^ b` for original-ring units `u, v`. Then
  `[u, v] - 1 - (x * y - y * x) ∈ I ^ (a + b + min a b)`.
  In particular, `[u, v] - 1` and `x * y - y * x` have the same class
  in the quotient **left module** `R ⧸ I ^ (a + b + 1)`.
  No two-sidedness, commutativity or nilpotence is needed; the commutator
  is `u * v * u⁻¹ * v⁻¹`, with no degree-dependent sign.
  [Coordinate estimate and quotient equality](GeneralLinearGroups/PrincipalUnits/Filtration.lean),
  [API guide](docs/README.md#principal-unit-commutator-coordinates).

- **Positive principal-unit layer pairings.** For any left ideal `I` in any
  `Ring R` and `a, b : ℕ+`, the bracket `xy - yx` descends to an
  **integer-bilinear** pairing of successive ideal layers in degrees
  `a`, `b` and `a + b`. The additive positive unit layers embed in these
  ideal layers by the injective symbol `[u] ↦ [u - 1]`; their pairing is
  represented by the ordered commutator of original-ring units. Both pairings
  are alternating, with ordinary negation under swapping and the canonical
  degree cast. No two-sidedness, Jacobson condition or symbol surjectivity
  is assumed, and no degree-zero additive layer is asserted.
  [Pairings and characteristic laws](GeneralLinearGroups/PrincipalUnits/Commutator.lean),
  [API guide](docs/README.md#positive-principal-unit-layer-pairings).

- **Functorial symbols and Jacobson equivalences.** A unital ring map
  carrying a left ideal `I` into `J` induces integer-linear maps on their
  positive ideal and unit layers, preserving symbols and both commutator
  pairings. The maps respect identities and composition, without injectivity,
  surjectivity or radical assumptions on the ring map. If
  `I ≤ Ring.jacobson R`, its symbol is an integer-linear equivalence, with
  inverse represented by the original-ring unit `1 + x`. Inverse naturality
  requires the Jacobson condition on **both** source and target ideals.
  Symbols are also surjective when every element of the left ideal is
  nilpotent, or when `I ^ N = ⊥`, including `N = 0, 1`; no two-sidedness
  or common exponent is assumed for the pointwise-nil result.
  [Forward maps and naturality](GeneralLinearGroups/PrincipalUnits/Naturality.lean),
  [Equivalences and nil lifting](GeneralLinearGroups/PrincipalUnits/LayerEquivalence.lean),
  [API guide](docs/README.md#functorial-symbols-and-jacobson-equivalences).

- **Images of principal-unit subgroups.** For a ring homomorphism
  `f : R →+* S` with `Ring R` and `Ring S` in independent universes,
  and a left ideal `I ≤ Ideal.jacobson ⊥`, a unit `u : Sˣ` lies in the image
  under `Units.map f.toMonoidHom` of the original `R`-unit stabilizer of
  `[1]` in the quotient left module `R ⧸ I` exactly when
  `∃ a ∈ I, f a = (u : S) - 1`.
  This uses the set image of ideal elements, not the extended ideal
  `Ideal.map f I`. The map need not be injective, and neither ring needs
  to be commutative; no domain, local-ring or valuation hypothesis is needed.
  [Image membership criterion](GeneralLinearGroups/PrincipalUnits/Images.lean).

- **Finite exponential and logarithm coordinates.** Over a possibly noncommutative
  or zero rational algebra, Mathlib's finite exponential, packaged as a unit,
  and a concrete logarithm give a plain equivalence between nilpotent elements
  and units `u` with nilpotent coordinate `u - 1`. This restricts to the elements
  of any pointwise-nil left ideal `I` and its principal-unit stabilizer of `1`
  in the quotient left module `R ⧸ I`; neither two-sidedness nor a uniform
  nilpotence exponent is required. Addition and product laws require commuting
  inputs; integer multiples correspond to integer powers in the unit group.
  These are equivalences of types, not group equivalences.
  [Exponential units and logarithm](GeneralLinearGroups/NilpotentExpLog.lean),
  [principal-unit restriction](GeneralLinearGroups/PrincipalUnits/ExpLog.lean).

- **First-order dual-number kernels and conjugation.** Over any `CommRing`,
  the *multiplicative* reduction identity fibers of Mathlib's GL and SL groups
  and of scalar units identify with additive matrices, trace-zero matrices
  and scalars. The determinant corresponds to trace; arbitrary ring-hom
  coefficient maps commute with these constructions without being implicitly
  `R`-linear. Unit **left conjugation** corresponds to `g * X * g⁻¹`,
  even for nonconstant dual-number units; the SL-kernel action uses SL
  conjugators. First-order fiber groups are abelian, so their commutator is
  not the generally nonzero matrix Lie bracket.
  [Kernel equivalences](GeneralLinearGroups/DualNumberKernels.lean#L145),
  [determinant/trace](GeneralLinearGroups/DualNumberKernels.lean#L316),
  [adjoint guide](docs/DualNumberKernelAdjoint.md).

- **Mixed dual-number GL and SL commutators.** For finite matrices over a
  `CommRing`, units over iterated dual numbers satisfy the ordered
  identity `[1 + εX, 1 + ηY] = 1 + εη(XY - YX)` with full outer-kernel
  readback. When *each input* is trace zero, special-linear factors
  yield the analogous identity in Mathlib's SL group and trace-zero readback.
  The ε-factor reduces to the inner lift `liftGL X` (in SL, `liftSL X`), usually
  not `1`: this is not a bracket of two elements of the abelian first-order
  outer kernel, nor a global Lie- or scheme-tangent theorem.
  [GL identity](GeneralLinearGroups/DualNumberMixedCommutator.lean#L155),
  [SL identity](GeneralLinearGroups/DualNumberMixedSLCommutator.lean#L93),
  [GL guide](docs/DualNumberMixedCommutator.md),
  [SL guide](docs/DualNumberMixedSLCommutator.md).

## Using the library

Add the library in your `lakefile.toml`:

```toml
[[require]]
name = "general-linear-groups"
git = "https://github.com/FormalFrontier/general-linear-groups.git"
rev = "main"
```

GitHub `main` contains only reviewed releases, so Lake resolves the latest release when
you first add or update the dependency. `lake-manifest.json` locks that resolved commit
until you update again. To pin a specific release, replace `main` with a commit from
its history.

For example, a surjective ring map lifts the *doubled* matrix:

```lean
module
import GeneralLinearGroups

open Matrix Matrix.GeneralLinearGroup

example {R S n : Type*} [Ring R] [Ring S] [Fintype n] [DecidableEq n]
    (f : R →+* S) (hf : Function.Surjective f) (g : GL n S) :
    mapRingHom f (liftBlockDiagonal f hf g) = blockDiagonalUnit g :=
  mapRingHom_liftBlockDiagonal f hf g
```

The [`PublicAPIClient`](tests/GeneralLinearGroupsTests/PublicAPIClient.lean) exercises this law using
an ordinary import; other clients exercise the interfaces and edge cases.

For the principal-unit image criterion alone, use
`import GeneralLinearGroups.PrincipalUnits.Images`. The theorem
`Ideal.mem_map_stabilizer_quotient_one_iff` uses the existing
`MulAction.stabilizer` subgroup and `Units.map`.

## Building

Install [elan](https://github.com/leanprover/elan) and use this repository's
`lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`), `lakefile.toml` and
`lake-manifest.json`. The dependency graph pins mathlib to
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. From a clean checkout,
fetch the matching precompiled mathlib cache before building:

```sh
lake exe cache get
lake --wfail build GeneralLinearGroups GeneralLinearGroupsTests
```

The default `lake build` selects the aggregate library and the test root.
Do not replace the cache fetch with a full mathlib source build.

## Contents

Import the [aggregate root](GeneralLinearGroups.lean) for the public library API,
or import a [specific subject module](GeneralLinearGroups/)
to keep a narrower dependency surface. The generic preadditive statements alone
are available through `import GeneralLinearGroups.RectangularIsomorphisms`, as
`CategoryTheory.isIso_id_sub_comp_iff` and `CategoryTheory.inv_id_sub_comp`.
The aggregate root's `public import` declarations expose
the corresponding module APIs to downstream ordinary imports. The default
build also checks the clients under `tests/GeneralLinearGroupsTests/`, including examples at
empty and singleton index types, over noncommutative rings and the zero ring;
client-only helpers are not promises of the library API.

| Subject | Start here | Important boundary |
| --- | --- | --- |
| Elementary blocks and reindexing | [Elementary matrices](docs/ElementaryMatrices.md), [commutators](docs/ElementaryCommutators.md) | Ring-only units; no arbitrary-ring `SL = E` |
| Unit pivots and diagonal units | [Unit-pivot diagonalization](docs/UnitPivotDiagonalization.md), [conditional pivot induction](GeneralLinearGroups/UnitPivotInduction.lean), [product-one diagonals](docs/ElementaryDiagonal.md) | `CommRing`; either unit ordered leading minors or an elementary pivot producer at every successor rank for the respective reduction |
| Local elementary generation | [Local generation](GeneralLinearGroups/LocalElementaryGeneration.lean), [clients](tests/GeneralLinearGroupsTests/LocalElementaryGenerationClient.lean) | `CommRing` and `IsLocalRing`; no ordered leading-minor condition; finite and stable determinant kernels |
| Paths and SL neighborhoods | [Elementary paths](docs/ElementaryPaths.md), [finite SL neighborhoods](docs/ElementaryNeighborhood.md) | Path-connected coefficients and open scalar units are distinct hypotheses |
| Relative groups and doubled identities | [Relative elementary](docs/RelativeElementary.md), [Whitehead](docs/RelativeWhitehead.md), [consequences](docs/RelativeWhiteheadConsequences.md) | Normal closure inside `E`; arbitrary-GL conjugation only after doubling |
| Stable general linear and elementary groups | [Stable GL](GeneralLinearGroups/StableGeneralLinear.lean), [stable elementary](GeneralLinearGroups/StableElementary.lean) | Semiring-direct-limit `GL`; over rings, elementary equals the stable commutator, with an abelian quotient but no public `K₁` construction |
| Stable determinant and rank-one units | [Stable determinant](GeneralLinearGroups/StableDeterminant.lean), [clients](tests/GeneralLinearGroupsTests/StableDeterminantClient.lean) | Rank-one maps over semirings; the elementary quotient determinant has trivial kernel over commutative local rings, not arbitrary rings |
| Finite stabilization and rectangular blocks | [Stabilization](docs/ElementaryStabilization.md), [rectangular blocks](docs/RectangularBlockUnits.md), [rectangular unit switch](GeneralLinearGroups/RectangularUnitSwitch.lean), [zero-product units](GeneralLinearGroups/ZeroProductStabilization.lean) | Semiring stabilization is a *monoid hom on units*; the unit switch requires a `Ring` and `g = 1 + A * B`, but not `B * A = 0` |
| Finite heterogeneous block units | [Block-triangular criterion](GeneralLinearGroups/BlockTriangularUnits.lean) | Strict range-chain in a `Preorder`, or a `≤` range-chain in a `PartialOrder`; ring sufficiency, semiring necessity under diagonal-matrix DF, and inverse support given invertibility and unit diagonals |
| Presented elementary group | [Steinberg](docs/FiniteRankSteinberg.md) | Finite rank does not imply finite presentation over an arbitrary ring |
| Quasi-regular kernels, scalar unit reflection and ideal quotients | [QuasiregularIdeal](GeneralLinearGroups/QuasiregularIdeal.lean), [QuasiregularQuotient](GeneralLinearGroups/QuasiregularQuotient.lean), [NonUnitalQuasiregular](GeneralLinearGroups/NonUnitalQuasiregular.lean) | For `Ring` → `Semiring`, unit reflection forces a quasi-regular canonical kernel without surjectivity; the converse and iff require surjectivity. Arbitrary quotient-unit lifting still needs quasi-regularity |
| Principal-unit commutators, leading coordinates and nilpotence | [Filtration API](GeneralLinearGroups/PrincipalUnits/Filtration.lean), [coordinate guide](docs/README.md#principal-unit-commutator-coordinates) | Left ideals suffice for mixed commutators, positive-power leading coordinates and nilpotence; the all-index power bound requires two-sidedness; nilpotence concerns the principal-unit subgroup, not all units |
| Positive principal-unit layer pairings | [Pairing API](GeneralLinearGroups/PrincipalUnits/Commutator.lean), [guide](docs/README.md#positive-principal-unit-layer-pairings) | Arbitrary left ideals in a ring; positive degrees and integer bilinearity; injective symbols need not be surjective; ordinary alternation and skew symmetry |
| Principal-unit images | [Image membership criterion](GeneralLinearGroups/PrincipalUnits/Images.lean) | `Ring R`, `Ring S`, Jacobson containment; set image of left-ideal elements, not ideal extension; no injectivity assumption |
| Finite exponential and logarithm | [NilpotentExpLog](GeneralLinearGroups/NilpotentExpLog.lean) | Possibly noncommutative or zero rational algebras; plain equivalence for nilpotent elements and units with nilpotent `u - 1`; commuting-only sum/product laws; integer powers in units |
| Exponential coordinates on principal units | [ExpLog](GeneralLinearGroups/PrincipalUnits/ExpLog.lean) | Rational algebras; pointwise-nil left ideals and their principal-unit stabilizers; no two-sidedness or uniform exponent; not a group equivalence |
| Kronecker products of units | [KroneckerUnits](GeneralLinearGroups/KroneckerUnits.lean), [clients](tests/GeneralLinearGroupsTests/KroneckerUnits.lean) | Semiring coefficients; the inverse witness reverses the identity-factor order, without a generic product-group homomorphism |
| Single-entry matrix corners | [MatrixCorner](GeneralLinearGroups/MatrixCorner.lean), [clients](tests/GeneralLinearGroupsTests/MatrixCornerClient.lean) | A chosen index gives a corner identity that may differ from the ambient identity; no commutativity assumption |
| Additive trace quotient | [MatrixTrace](GeneralLinearGroups/MatrixTrace.lean), [AdditiveCommutator](GeneralLinearGroups/AdditiveCommutator.lean) | An inverse needs a chosen index; no ring quotient or `K₀` theorem |
| First-order and mixed dual numbers | [Kernel guide](docs/DualNumberKernels.md), [adjoint guide](docs/DualNumberKernelAdjoint.md), [mixed GL guide](docs/DualNumberMixedCommutator.md), [mixed SL guide](docs/DualNumberMixedSLCommutator.md) | `CommRing`, finite decidable indices; SL requires individual trace-zero factors |

Additional [nonunital](GeneralLinearGroups/NonUnitalNilpotent.lean),
[local quotient](GeneralLinearGroups/LocalQuotient.lean) and
[unital comparison](GeneralLinearGroups/UnitalComparison.lean) modules have
their own docstrings and statements.

## Conventions and limitations

The supplied-generator principal-unit power coordinates are algebraic and need
no local-ring, DVR, Noetherian, finiteness, characteristic, topology or completeness
hypothesis. They do not supply an adapter from DVR or valuation-field unit
carriers, assert a residue-field isomorphism, or construct a complete
valuation-ring unit filtration, its topology or p-adic powering.

Matrix index and coefficient types may live in independent universes. Empty
indices, singleton indices and zero rings are not silently excluded; theorems
requiring a chosen index state it. A unit leading minor is stronger than a
nonzero minor, even over `ZMod 6`. Ring-level elementary paths allow
noncommutative coefficients; subgroup path connectedness separately needs
path-connected coefficients. The finite SL comap is open and closed when
scalar units form an open locus; identifying its identity path component also
needs path-connected coefficients. There is no continuous factor selection,
arbitrary-ring `SL = E`, global `GL` connectivity or quantitative neighborhood.
There is **no** claimed stable `K₁` identification, excision,
`K₂`, source-complete K-theory, ambient relative normality or universal
triangular-invertibility converse.

Scalar unit reflection means `IsLocalHom f`, not a local-ring assumption
on source or target.
Its kernel consequence has no surjectivity, nilness, finiteness or rank
hypothesis. The converse needs surjectivity: the inclusion `ℤ → ℚ` has
zero (hence quasi-regular) kernel but does not reflect units, since `2`
becomes a unit. Nonsurjective maps can nevertheless reflect units: rational
constants `PowerSeries.C (R := ℚ) : ℚ →+* PowerSeries ℚ` do so via the
ring-homomorphic retraction `PowerSeries.constantCoeff`, while `X` is not
constant. Quasi-regular kernels need not be nil: the constant-coefficient
map on rational formal power series has a quasi-regular kernel containing
the nonnilpotent series `X`.

The [historical API snapshot](docs/API.md) covers only 128 authored public
entries and 16 module records, with source links on thirteen unchanged
producers. It is **not** an exhaustive reference for the current
default graph. Use the Lean sources, guides and import clients for other results.

## References

- Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*
  (2013), Exercises I.1.10–I.1.12 and Chapter II, §2. Selected constructions
  draw on its mathematics, not a complete formalization of the book.
- I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
  second edition (2002), Chapter I, (5.3) and (5.4)(3), for principal-unit
  multiplication and its additive ideal-layer coordinates.
- Formal Frontier Agents' [Algebraic Groups library](https://github.com/FormalFrontier/algebraic-groups),
  `AlgebraicGroups.GroupTheory.UnitriangularExponent`, formalizes the zero-diagonal
  cardinal-power specialization over commutative rings.
- [mathlib](https://github.com/leanprover-community/mathlib4) provides the
  foundational matrix, group, ideal, topology and dual-number interfaces.
  Its `Submodule.fg_span`, `mem_nilradical` and
  `Ideal.FG.isNilpotent_iff_le_nilradical` supply the finite entry-ideal
  argument for matrices with nilpotent entries; the matrix step reuses this
  library's uniform-ideal nilpotence theorem.
- Jacobson's lemma is the standard unit identity relating `1 - ab` and
  `1 - ba`. The rectangular complement theorem gives its two-object
  preadditive form, using Mathlib's preadditive and isomorphism APIs.
  Its matrix inverse-value specialization uses Mathlib's `Mat_` and
  `SingleObj` categories, finite-index reindexing and the `Units`/`Aut`
  correspondence, with the given unit's inverse over a noncommutative ring.
  Mathlib's finite-matrix inverse identities are related formalizations.
- The [Adic Modules library](https://github.com/FormalFrontier/adic-modules), in
  [`AdicModules.RingTheory.Ideal.IsPrincipalPowQuotient`](https://github.com/FormalFrontier/adic-modules/blob/d0ce9c7ea73e0f995d7318e448af3e14f2e473bd/AdicModules/RingTheory/Ideal/IsPrincipalPowQuotient.lean),
  supplies the chosen-generator forward and inverse representative formulas
  for the principal-power quotient equivalence. The underlying equivalence
  is Yakov Pechersky's Mathlib formalization.

## Credits and license

Authors: Formal Frontier Agents. Contributions include original general-linear,
ideal and trace-related proof expression and API documentation; dual-number
kernel and adjoint integration; the Markdown documentation adapter that
informed the historical API reference; trace, elementary, relative,
stabilization, Steinberg, dual-number, unit-pivot, elementary-path, diagonal
and neighborhood proofs and clients; and adaptation of examples and
mathematical guides. These original project contributions
are distinct from Weibel's mathematical motivation and mathlib's third-party
work, whose authorship and notices remain with mathlib. Kronecker unit
preservation generalizes mathlib's commutative-coefficient theorem and follows
its constant-family, block-diagonal, reindexing and `Units` formalizations.
The nilpotent-entry matrix result follows Mathlib's finite-generation and
nilradical formalizations and the existing uniform-ideal matrix theorem; its
`ZMod 4` client adapts the Formal Frontier Agents' entrywise-nilpotence example.
The upper-triangular semiring proofs use ordered row elimination and diagonal
powers, in contrast to the Algebraic Groups cardinal-power formalization of the
commutative-ring specialization.
The block-triangular proofs follow Mathlib's maximal-fiber splitting and
subtype-reindexing approach, using its block multiplication and stock
Dedekind-finiteness transport; the commutative inverse comparison uses its
nonsingular-inverse API.
AI agents developed
the Lean code and documentation with compiler feedback and independent agent
review; no human mathematical review is claimed. Licensed under
[Apache-2.0](LICENSE); no copyright holder is inferred from the author credit.
