# Fixed-weight logistic inference

This proof slice applies the real sigmoid to the fixed-weight linear prediction
from [LinearModelInference](LINEAR_MODEL_INFERENCE.md). It covers inference with
supplied coefficients and bias, not fitting, training, or statistical calibration.

## Exact real guarantees

[LogisticModelInference.lean](LogisticModelInference.lean) defines the sigmoid as
`exp(z)/(1+exp(z))`. Mathlib's real exponential positivity and strict monotonicity
prove `sigmoid_strictMono` and the strict output range `(0,1)`.

For fixed rational weights/bias and independent nonempty closed rational feature
boxes, `sound`, `extrema`, and `least` transport the existing exact linear-model
bounds. Applying sigmoid to the two logit endpoints gives attained extrema and
the least closed real interval enclosing all predictions. This does not prove a
separate interior-value-attainment theorem. Correlated restrictions still admit
the sound enclosure, but may destroy endpoint attainment and tightness.

`half_lt_iff`, `half_le_iff`, `lt_half_iff`, and `le_half_iff` prove both strict and
nonstrict comparisons against one half by comparing the logit with zero. At zero
the probability is exactly one half. For `0 < p < 1`,
`probability_threshold_iff` proves that exceeding probability threshold `p` is
exactly exceeding the real threshold `log(p/(1-p))`. This is a mathematical
identity, not an executable logarithm or certified floating-point threshold.

## Directed logit bounds and executable certificates

`run_encloses` reuses the existing fixed-order directed dot product and final bias
addition. Under the unchanged successful-operation contracts, decoded zero, and
bounds containing the same real parameters and features, a successful logit
result with decoded endpoints `l,u` implies sigmoid bounds `[sigmoid l,sigmoid u]`.
These bounds need not be tight; no automatic success, exact rounding, or absence
of accumulated rounding error is claimed. Failure remains unknown as in the
linear-model program.

The sigmoid, prediction, and transformed endpoints are **noncomputable real
specifications**. There is no native exponential implementation or native
logistic inference path in this change. The reference `classify` function is
executable: it checks a rational logit interval for a strictly positive lower
bound or strictly negative upper bound. Its two soundness theorems apply to any
real logit contained in that interval, whether the interval is exact or loose.
`none` is inconclusive; it is neither undefinedness nor proof of both outcomes.
A future binary64 implementation needs a separately justified endpoint-validation
and comparison route. No such native wiring or new floating-point assumption is
introduced here.

## Checked examples

The [fixtures](tests/LogisticModelInference.lean) use one feature, weight 1 and
bias 0:

- `[1,2]` certifies probability strictly above one half.
- `[-1,1]` has explicit input witnesses strictly below and above one half.
- `[0,1]` certifies probability at least one half; the zero input attains equality
  and the strict reference classifier returns `none`.
- A loose `[-1,1]` enclosure for the actual logit `1/2` is inconclusive even though
  that particular prediction is strictly above one half.
- The actual directed linear-model API with exact rational mock operations
  returns `[1,2]`; its successful result instantiates the sigmoid enclosure proof.

The mock program executes rational arithmetic, not hardware exponential or
binary64 inference. Existing hardware assumptions are only reused through the
conditional operation contracts.

## Verification and roadmap

```sh
lake build LogisticModelInference
lake env lean tests/LogisticModelInference.lean
./check.sh
```

This is a separately reviewable step after the exact dot product, directed dot
product, and fixed-weight linear model. A next inference step can compose layers
or connect the existing directed logit program to an actual adapter. Fitting,
backpropagation and training require separate specifications and are not included.
