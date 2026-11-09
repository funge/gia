# bounded search for presence certificates

This milestone makes the certified-segment method constructive at the candidate
selection level. It searches a finite list and returns a certified segment, not
a numerical root coordinate. It follows the existing separation between sound
absence/presence certificates and unresolved regions. The default candidate
policy below is a small optional policy, not a transcription of a particular
algorithm or completeness claim from Tupper's thesis.

## general finite search

`SegmentCandidate` is a pair of rational points. `searchSegments B X Y e cs`
returns the first candidate accepted by the existing `certifySegment` checker,
or `none` if all candidates fail. It uses Lean's finite `List.find?`.

The proofs establish:

- a returned candidate belongs to the supplied list;
- it passes the segment checker and therefore proves a defined zero in the box
  for a sound backend;
- `none` is equivalent to every candidate in the list failing certification;
- success is equivalent to at least one candidate in the list being certified;
- appending lists preserves priority: search the second list only if the first
  produces no certificate.

Thus the search is complete relative to this finite list of certificates. It is
not complete for mathematical roots, continuous curves, or all possible segments.
An invalid candidate is rejected and search continues.

`classifyWithSearch` combines zero exclusion with finite candidate search.
`empty` and `present` have separate soundness proofs; `unknown` asserts neither
absence nor presence, and says nothing by itself about definedness.

## optional automatic box policy

`boxSegments` constructs exactly eight candidates, from the box center to:

1. each of the four corners;
2. each of the four edge midpoints.

The order is fixed in `boundarySamples`. Midpoints are computed as exact rational
averages. Their interval membership is proved, as is membership of every endpoint
of every generated segment. The list length is proved to be eight, including for
degenerate boxes, which may generate duplicate candidates. No assumption that
midpoints are representable in binary64 is introduced.

`classifyBox` applies this policy automatically. Soundness is independent of this
particular policy: callers can instead supply their own finite list. A sound
backend is the only backend premise; the exact backend discharges it, and the
directed-rounding adapter uses the same existing successful finite-conversion
enclosure inequalities. IEEE 754 remains the rounding reference, without a new
FP model or implementation assertion.

## checked examples and limitations

`SegmentSearchExamples.lean` proves:

- a circle `x*x + y*y - 1/4 = 0` in `[-1,1]²` is certified using its center and
  first corner, even though all four corner values are positive;
- a user list skips an out-of-box candidate and returns a later valid certificate;
- positive constants are classified empty, while an empty candidate list does
  not turn an unresolved circle into an empty result;
- `1/x` across zero and finite-conversion failure remain unknown;
- degenerate and shifted boxes work with exact rational midpoint geometry;
- `(x-1/4)*(x-1/4)` has a proved defined root in the box but this default search
  returns unknown: none of its sampled endpoints certifies the tangency.

The missed-root example formally demonstrates why exhausting the candidate list
must not mean absence. There is no subdivision, adaptive sampling, convergence,
completeness-for-roots, or wall-clock guarantee. Each candidate may repeat whole-
box and endpoint evaluation; caching and cost optimization are not part of this
change. The whole-box domain guard remains conservative even when a selected
segment would avoid an undefined point.

The rational search is executable and the finite examples use `decide +kernel`.
It does not implement screen coordinates, a renderer, FP rounding instructions,
or extraction of numerical root locations. Run `lake build` and
`lake env lean Audit.lean`; observed results are recorded in `VALIDATION.md`.

The subsequent [bounded subdivision milestone](SUBDIVISION.md) adds coverage
and sound aggregation around this local classifier; its budget can still leave
boxes unknown.
