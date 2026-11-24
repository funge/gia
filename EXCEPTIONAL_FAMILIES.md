# Exceptional expressions versus infinite bounds

This proof package separates three meanings that finite-family promotion cannot
identify: an infinite endpoint bounding real witnesses, a literal infinite
coefficient, and the source undefined tag λ.

## Source-supported subset

Original PDF pages were checked visually:

- §2.5.2, printed p.19 / PDF p.35: an operation outside its defined domain returns
  λ; λ is distinct from real payloads. The existing tagged layer is retained.
- §2.7.4, printed p.25 / PDF p.41: returning the universal interval is a valid
  enclosure for a total real function, although usually uninformative.
- §2.9.5, printed p.30 / PDF p.46: ∞−∞α is explicitly undefined at α=1/2 and is
  therefore not a valid everywhere-defined bound on the parameter interval.

Public sources: [p.19](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=35),
[p.25](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=41),
[p.30](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=46).

[ExceptionalFamilies](ExceptionalFamilies.lean) reuses `ExceptionalComparisons.Value`
and `ExtendedImageHull.interval`. Its `differenceScaled` observation is scoped to
one expression, a−b·t. Finite coefficients have ordinary real semantics. The
literal (+∞,+∞,1/2) row is encoded as `some undefined` directly from the source.
This is a formalization of that explicit specification, **not** a deduction from
a complete exceptional multiplication/subtraction table, which we do not have.
The theorem `source_midpoint` checks this model row; the other theorems establish
its consequences and compare it with independently proved real-set semantics.

Other exceptional cases, including t=0 and t=1, return `none` (unmodeled), not λ.
A λ input is likewise unmodeled here; no propagation rule is guessed. The missing
specification is precise: which primitive exceptional multiplication/subtraction
rules determine ∞−∞t at other t, and are those intended rules distinct from
interval-set arithmetic? The one printed midpoint rule cannot answer that.

## Proven separation and noncommuting replacement

For actual real outputs, the existing extended-bound semantics gives:

- interval(−∞,+∞) = all reals;
- interval(0,+∞) = nonnegative reals;
- interval(+∞,+∞) = empty **as a set of real outputs**.

The last statement is not a claim that Tupper's extended-value singleton interval
is empty in his full exceptional carrier. Literal infinities are not real values.
`universal_encloses` proves the source's total-real-function enclosure claim using
this real-output interpretation.

At t=1/2, two independently varying nonnegative real coefficient witnesses give
`{a−b/2 | a≥0, b≥0} = Real`. The proof constructs witnesses for every real z:
(a,b)=(z,0) for z≥0 and (0,−2z) for z<0. With one shared witness instead,
`{a−a/2 | a≥0} = [0,+∞)`, with witness a=2z. These are exact images, not just
bounds, and the two relations are deliberately distinct.

Replacing those unbounded coefficient families by literal +∞ operands does not
commute with evaluation: the source-specified midpoint result is λ and supplies
no real payload, whereas either real family has actual values. This replacement
is an invalid conflation, **not** a promotion operation we claim Tupper specifies.
No correlation is silently discarded, and no real value is manufactured for λ.

`ereal_evaluation_disagrees` checks an additional concrete boundary: pinned
mathlib EReal computes `top − top*(1/2) = bottom`. Tupper's specified expression
instead gives λ, whose existing `bound` translation is `none`. Thus EReal's
arithmetic cannot be reused as the literal exceptional evaluator merely because
its order correctly models interval endpoints.

## Partiality and controls

`realOutputs` records only finite payloads present in an observation. It is not a
sound domain classifier for `none`: unmodeled observations and modeled λ both
have no recorded finite payload but remain distinct before that lossy projection.
No theorem infers actual undefinedness from `none`. The mismatch theorem uses
only the explicitly modeled midpoint result, never an unmodeled row.

[Fixtures](tests/ExceptionalFamilies.lean) retain a finite midpoint result 4,
negative independent values excluded by the shared relation, the shared zero
witness, every real admitted by universal bounds, empty real membership of
[top,top], unmodeled zero/one parameter cases, and the distinction between bound
order and source numerical comparison.

This closes the explicit example and its real-family/bound correspondence. It
does not complete an extended-coefficient polynomial algebra or a generic λ
propagation table. No IEEE, native backend, or new FP assumption is involved.
Keep this package in the existing exceptional-foundations review unit 2.
