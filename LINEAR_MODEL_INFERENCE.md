# Fixed-weight linear-model inference

This milestone proves prediction bounds for supplied coefficients and a bias:

`prediction(x) = ∑ i, wᵢ xᵢ + b`.

It does not fit coefficients, train a model, or establish any statistical
accuracy. It builds on the separate [exact dot-product](INTERVAL_DOT_PRODUCT.md)
and [directed composition](DIRECTED_DOT_PRODUCT.md) milestones.

## Exact bounds

[LinearModelInference.lean](LinearModelInference.lean) uses fixed rational
weights and bias, and finite nonempty closed rational feature intervals denoting
real values. `bounds` adds the singleton bias to the existing `weightedBounds`.
The dimension can be zero, in which case the exact result is the bias.

- `sound` encloses every prediction from the supplied feature box.
- `extrema` proves both bounds are attained by feature vectors in that box.
- `least` proves minimality among all closed real interval enclosures.
- `above_threshold` proves a strict prediction threshold when it lies strictly
  below the lower bound. Equality at the lower bound is insufficient.

The exactness statements require independent feature choices. Soundness remains
valid if an application further restricts the inputs, but the resulting interval
may no longer be tight. Shared-feature limitations from the dot-product milestone
still apply. This is the least closed hull; no new theorem of interior-value
attainment is claimed.

## Directed-operation program

`run` first executes the existing fixed-order dot-product program, then makes
one final interval addition with the bias bound. Moving the bias into the initial
accumulator would be a different rounded program; no such equivalence is claimed.

`run_encloses` reuses `DirectedDotProduct.run_encloses` and the existing addition
contract. The premises are decoded zero, input bounds containing the same real
weights/features/bias, and the established successful-operation contracts.
Weights and bias may be held in conservative bounds; the theorem does not require
those bounds to be tight or machine singletons. It proves enclosure of the exact
real prediction, not optimal rounding, a rate of roundoff growth, or guaranteed
availability. The established primitive wrappers discharge these contracts, as
shown by the fixtures; no new floating-point premise is introduced.

A failed dot product or final bias addition returns `none`, meaning no bound is
available. It does not imply the mathematical prediction is undefined or the
feature box empty. Even the zero-dimensional program still performs the final
bias addition and can fail there. This pure Lean program is not wired to a
binary64 native adapter in this milestone. No native execution, FP-state
preservation, C/FFI change, or deployment claim is made.

## Checked example

Use weights `[2,−1]`, bias `1/2`, and independent features
`x₀ ∈ [1,2]`, `x₁ ∈ [0,1]`.

The exact range bounds are `[3/2,9/2]`. The fixtures prove:

- every prediction is strictly greater than 1;
- at threshold 2, predictions on both sides actually occur, using the attained
  extrema rather than inferring existence from enclosure alone;
- a strict threshold of `3/2` cannot hold for every input because the lower
  endpoint is attained;
- the actual directed-program API with exact rational mock primitives returns
  `some [3/2,9/2]` and satisfies `run_encloses` for every feature vector in the box;
- an unavailable final bias addition returns `none`.

The mock calls are reference tests, not binary64 observations. For a future loose
hardware enclosure, overlap with a threshold alone would be inconclusive: it
would not prove that predictions on both sides exist.

## Reproduce and next step

The [fixtures](tests/LinearModelInference.lean) exercise the public `bounds` and
`run` entry points, with kernel-checked results and namespace auditing:

```sh
lake build LinearModelInference
lake env lean tests/LinearModelInference.lean
./check.sh
```

The next implementation question remains the actual directed hardware adapter
route for the dot product and final bias addition. A later proof slice can
compose a certified sigmoid for logistic inference. Fitting, optimization,
backpropagation and training are separate work, not commitments of this slice.
