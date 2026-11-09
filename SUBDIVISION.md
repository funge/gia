# Bounded subdivision

`Subdivision.lean` adds `refineBox fuel B X Y e`. It first runs the existing
interval exclusion and finite segment classifier. Only an `unknown` box is
split, at its exact rational midpoint, alternating x and y (starting with x).
At depth zero the current classifier result is returned unchanged. The result
remains `empty`, `present`, or `unknown`; exhausting the depth budget never
turns uncertainty into absence.

## Coverage and result invariants

The two closed interval halves are subsets of their parent and cover it
exactly (`lowerHalf_subset`, `upperHalf_subset`, `split_cover`).
`split_boundary` proves that both halves retain the shared midpoint. There is
no disjointness assumption: boundary overlap and degenerate intervals are valid.
`hasRoot_split_x` and `hasRoot_split_y` lift this coverage to existence of a
**defined** zero in a box using the existing partial `Value` semantics.

`mergeResults` returns present if either child is present, empty if both children
are empty, and unknown otherwise. `mergeResults_sound` proves this rule for any
two propositions and sound results. `subdivide_sound` combines it with coverage
by induction on fuel. The public corollaries are:

- `refineBox_empty`: an empty result excludes every defined zero in the parent.
- `refineBox_present`: a present result implies a defined zero in the parent.
- `refineBox_zero`: budget zero is exactly the previous box classifier.

Fuel bounds the depth of recursive splitting, not the number of primitive
arithmetic operations or wall-clock time. Structural recursion terminates even
on degenerate boxes, which may duplicate work. Presence does not imply uniqueness
or return a numerical root coordinate.

## Thesis connection

Tupper's [§4.2.5, Exhaustive Subpixel Testing](https://www.dgp.toronto.edu/~mooncake/thesis/node155.html)
describes using subpixel tests to establish absence, accepting a discovered
solution, and applying further tests after an inconclusive result. This milestone
formalizes the coverage and result-combination obligations for a bounded version
of that approach. The local presence test uses the continuity argument developed
in the earlier milestone, related to
[§4.2.6, Continuity-Based Testing](https://www.dgp.toronto.edu/~mooncake/thesis/node156.html).
Alternating binary midpoint cuts are our explicit policy, not a claim to
transcribe the thesis algorithm or its broader relation language. These proofs
cover equations over the existing rational expression syntax.

## Checked examples and limits

All examples in `SubdivisionExamples.lean` are kernel checked:

- On `[-1,1]²`, `x*x+1` initially returns unknown because of interval dependency;
  one x split proves the whole box empty.
- `(x-1/4)*(x-1/4)` remains unknown with budget one, but budget three finds a
  presence certificate when a generated sample lands on the root. This does
  not establish a general tangency algorithm or completeness.
- `1/x` across zero stays unknown at budget three, as does a degenerate pole box.
  Guarded division is unchanged; subdivision does not turn a pole into a root.
- Failed finite conversions remain unknown; combining empty and unknown remains
  unknown, while unknown and present gives present.

The general soundness theorem assumes only `BackendSound B`, the existing
successful-evaluation enclosure contract. The exact rational backend satisfies
it unconditionally. The existing directed backend satisfies it under the same
explicit downward/upward enclosure inequalities already documented in
[EVALUATOR.md](EVALUATOR.md); no FP assumption is added. IEEE 754 remains the
reference for rounding direction. Rational split points need not be machine
representable. No IEEE implementation, bit-level behavior, renderer, pixel
ownership convention, root-search completeness, or convergence rate is verified.
In particular, unknown implies neither existence nor absence.

Run `lake build` and `lake env lean Audit.lean` from this directory. This work
remains separate from the native build, v1.0 release, and hosted CI.
