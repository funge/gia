# General interval-set extension on a common domain

Source: Tupper §§2.13.1–2.13.2, [printed p.39 / PDF p.55](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=55),
visually checked. The printed inclusion rule lets each operand value belong to
any of its pieces, while all pieces use the same parameter. It also gives a
squared-distance guard for perfect point demotion and quantifies strict
improvement against every model in the chosen base family.

[IntervalSetExtension.lean](IntervalSetExtension.lean) reuses
`IntervalSetDenotation.denote`, `GeneralFamilyDemotion.outputs` and `Sound`.
It imposes no finiteness on piece sets and no finite-coefficient surrogate.
Parameter and description types are arbitrary; operations have finite arity
and an actual real-output relation, which may be partial or multi-valued.

## Exact lifting versus enclosure

`extension_exact` proves that taking actual output images for every admitted tuple
of pieces and then their union is exactly the actual image of the independently
admitted operand sets, at one common parameter. Piece choices can differ across
coordinates; parameter choices cannot. `lift_encloses` transports sound piece
models, while `lift_exact` requires equality of their actual output sets.
`extension_mono` handles refinement. Empty images and empty piece sets are
supported; zero arity still admits the unique empty tuple.

`correlated_sound` retains an additional actual input relation and its exact
possible/definite domain description. Marginal relaxation remains sound but may
be inexact: the fixture admits a difference of 1 independently, whereas equal
coordinates at one witness always have difference zero. No availability,
totality or attainment is inferred from an enclosure premise.

## Source guard, proved rather than assumed

`squared_guard_iff` proves `Σᵢ(pᵢ−qᵢ)² ≤ 0` iff the vectors are equal, including
zero dimensions. `guarded_point_correspondence` shows that this is extensionally
the existing equality-guarded point representation; it changes no semantics.
`guarded_points_exact` proves exact representation of any partial real-valued
function on any supplied common domain by all its defined guarded points.
This includes the unit cube in the source. Undefined outputs and points outside
the domain contribute no values. The representation may be infinite; there is
no finite encoding, computability or machine demotion claim. Exceptional numeric
outputs outside real values still require the separate source-carrier work.

A positive distance tolerance would be a different model, not an equivalent
choice. The fixture gives distinct vectors passing such a tolerance, so the
proof uses precisely the source's zero threshold.

## Quantified strict improvement

`strict_against_every_interval` proves a general gap criterion: if a set contains
a and b but omits c with a ≤ c ≤ b, then it is strictly contained in **every**
closed extended-bound real interval that encloses it. This is stronger than
comparing with a single loose interval.

The fixtures represent the actual image of a jump on [−1,1] by two singleton
pieces, {0} and {1}. Their union is exact and finite. Every constant closed
interval model of that jump must also contain 1/2, proving the source-shaped
strict improvement against all models of that base family. This does not prove
a universal bumpy classification for every possible parameter-dependent family.

[Fixtures](tests/IntervalSetExtension.lean) also cover reciprocal holes,
external-domain exclusion, independent-versus-correlated inputs, empty pieces
and zero arity. Run the existing pinned `./check.sh`; no native or IEEE contract
is added, and no runtime evaluator is replaced.

## Finish-line movement

Checked general real-output obligations: §2.13.1 n-ary set inclusion/exact image
lifting, the numeric equality guard and perfect point denotation, and a quantified
§2.13.2 gap criterion with a finite source-shaped witness. These are general
semantic results, not another finite family approximation. They stay in review
unit 3 alongside existing interval-set denotation.

Still open: source exceptional-value carriers, concrete finite encodings where
claimed, general bumpy classification relative to other base families,
heterogeneous/open-endpoint variants and the remaining symbolic/representation
constructions. No source interpretation or floating-point assumption was chosen
as a premise to close those rows.
