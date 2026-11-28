# Dot products with uncertain inputs

This is the first proof milestone toward certified model inference. Given two
vectors of finite closed intervals, `IntervalDotProduct.bounds` computes the
least closed interval containing every dot product formed by independently
choosing each input coordinate. The dimension is any natural number, including
zero. Endpoints are exact rationals; the values inside the input boxes are real.

This is a mathematical input-uncertainty result and an executable rational
reference, **not a floating-point dot-product implementation**. It is a foundation
for the intended hardware-backed path, not a substitute for that path.

## Interface and guarantees

[IntervalDotProduct.lean](IntervalDotProduct.lean) reuses `QInterval.mul` and
`mul_encloses` from [IntervalOps](IntervalOps.lean). For each coordinate it takes
the minimum and maximum of the four endpoint products, then sums the minima
and maxima separately. `bounds` is executable and `dot` denotes the real sum.
No new expression evaluator or graphing interface is introduced.

- `sound`: every `x` in the first box and `y` in the second has `dot x y` in
  the returned interval.
- `lower_attained` and `upper_attained`: there are actual pairs of vectors in
  those boxes whose dot products equal the returned lower and upper endpoints.
  Coordinate endpoint witnesses can be assembled together because the box
  imposes no relation between coordinates or between the two vectors.
- `least`: any closed **real** interval enclosing all such dot products contains
  both computed endpoints. Thus the result is the exact least interval hull,
  not just a conservative enclosure. We do not separately prove that every
  interior point is attained.
- `weighted_sound` and `weighted_extrema`: fixed rational weights are singleton
  intervals, leaving only the feature vector uncertain. Negative and zero
  weights require no additional assumptions.

The scalar endpoint-attainment lemmas complement the existing multiplication
soundness proof rather than replace it. Endpoint calculations use exact rational
arithmetic; there is no overflow or finite-word rejection in this reference.
Malformed, empty, infinite or NaN input intervals are outside `QInterval`.

## Examples and dependency limits

The [kernel-checked fixtures](tests/IntervalDotProduct.lean) call the public
reference functions and check these results:

| Inputs | Exact independent-box bounds |
| --- | --- |
| `[-1,2] × [-2,1] + [3,4] × [-1,2]` | `[-8,10]`, with explicit endpoint vectors |
| Weights `[-2,3,0]`, features `[-1,2] × [1,4] × [-100,100]` | `[-1,14]` |
| Singleton vectors `[3/2]` and `[-2]` | `[-3,-3]` |
| Dimension zero | `[0,0]` |

Soundness still holds when an application adds relations between inputs, but
attainment and leastness need not hold on that smaller domain. For `x·x` with
one coordinate `x ∈ [-1,1]`, the independent calculation returns `[-1,1]`;
its lower endpoint is impossible when both operands are the same `x`.
Likewise weights `[1,-1]` with the shared feature vector `[t,t]` always give
zero, while treating the two feature coordinates independently gives a lower
bound of −2. The fixtures prove both limitations. We do not silently replace
shared witnesses by independent choices or claim that enclosure implies existence.

## Relationship to prior proofs and hardware

This is a derived application of the exact interval inclusion and independent
image-hull principles covered in Tupper §§2.7–2.8; it is not presented as a
neural-network theorem from the thesis. See the [source concordance](THESIS_CONCORDANCE.md)
and [exact image-hull proofs](ExactImageHull.lean). The `least` theorem does
not assume rounding or optimality of a machine implementation.

A separate next milestone can compose the existing directed multiplication and
addition contracts over the vector, proving a hardware enclosure with explicit
failure propagation. Rounding only the exact final endpoints is another possible
interface, but this milestone neither supplies that converter nor equates it
with rounded accumulation. It makes no claim about FMA, reduction order, BLAS,
GPU execution, bit equality, error size, or performance. No hardware contract,
C/FFI file, relgraph file, or floating-point assumption changes here.

## Short inference-first roadmap

1. **Dot product:** exact box bounds now; separately connect a finite directed
   hardware evaluation path under the existing contracts.
2. **Linear regression inference:** fixed coefficients plus a bias, with sound
   prediction bounds. Fitting coefficients, least squares and optimization are
   separate tasks and are not committed by this roadmap.
3. **Logistic regression inference:** compose the affine predictor with a
   certified sigmoid enclosure, stating its domain and numerical contract.
   This does not prove a training algorithm or statistical calibration.
4. **Small neural-network inference:** compose affine layers and supported
   activation bounds. Track how box abstraction loses dependencies between
   neurons; do not assume independently attainable layer bounds stay exact
   through the network. Backpropagation and training remain separate work.

The immediate reuse path is inference with supplied model parameters. This
milestone proves no learning, robustness, or classification claim by itself.

## Reproduce the checks

With the repository's pinned Lean/mathlib setup:

```sh
lake build IntervalDotProduct
lake env lean tests/IntervalDotProduct.lean
./check.sh
```

The fixture prints `(-8, 10)` and `(-1, 14)` from the executable reference and
proves the corresponding equalities in the kernel. Its namespace is audited,
and the main declarations are registered in [Audit.lean](Audit.lean). No new
axiom, `sorry`, or native-decision trust is used. This is local proof/reference
qualification; no native floating-point dot-product path is tested here.
