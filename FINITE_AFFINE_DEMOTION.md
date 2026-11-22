# Finite affine storage certificates and outward evaluation

[FiniteAffineDemotion.lean](FiniteAffineDemotion.lean) formalizes a restricted
finite instance of Tupper [§2.10](https://www.dgp.toronto.edu/~mooncake/thesis/node45.html),
printed pp. 32–33 / [PDF pp. 48–49](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=48).
The original separates ideal family bounds, demotion to machine coefficients,
and outward evaluation of the stored bounds at the same parameter. Noncollapse
is pointwise throughout the parameter domain. These distinctions are preserved
here. See the [Chapter 2 checklist](CHAPTER2_CHECKLIST.md) for the broader gaps.

## Storage certificate

`certify I H` accepts an ideal `LinearInterval I` and a candidate
`HardwareAffine.Form Binary64.Word H` containing four supplied raw endpoint
words. It performs four optional exact rational decodes and four comparisons:

- stored lower at zero ≤ ideal lower at zero;
- ideal upper at zero ≤ stored upper at zero;
- stored lower at one ≤ ideal lower at one;
- ideal upper at one ≤ stored upper at one.

Decoding failure or an inward endpoint returns `none`. Ideal endpoint order
already belongs to `LinearInterval`; `certified_order` proves the stored
endpoint order without more comparisons. `certified_endpoints` supplies both
ideal endpoint containment obligations at each end. `certified_enclosure`
reuses [HardwareAffine.linear_bridge](HardwareAffine.lean): for every shared
`t ∈ [0,1]` and every `z` in the ideal interval at that `t`, the stored form
contains `z` at that same `t`. `certified_noncollapse` proves that the stored
meaning is nonempty at every such `t`, using the ideal lower value as a witness.
This is not merely a whole-range hull check.

The [existing coefficient/endpoint correspondence](LinearIntervals.lean)
(`affine_endpoints_roundtrip`, `linear_coefficients_contains`) already relates
this basis to finite rational `p+q*t`; it is not reproved. Likewise
`exact_affine_bridge` and `hull_sound` remain available for exact-line and
parameter-forgetting clients. The new checker does not duplicate these bridges.

This is a **cold-path certificate checker**, not an arbitrary rational-to-binary64
converter or rounding routine. Supplied candidates may be loose and no existence
of acceptable candidates is promised for arbitrary ideal endpoints. It neither
implements the source p,q coefficient rounding nor claims exact rounding,
optimality, machine-precision proximity or a ULP bound. The source's extended-real
and multi-parameter family is strictly broader.

## Evaluating at a parameter

`evaluate sub mul add one parameter H` is an executable proof-side Option
program over the existing generic `Form F` and `Bounds F`. It computes:

1. `w = sub one parameter`;
2. `a = mul w H.atZero`;
3. `b = mul parameter H.atOne`;
4. `add a b`.

Any unavailable stage returns `none`. There is no fallback pretending an
unavailable value is zero, no domain-existence conclusion from failure, and no
native caller. `evaluate_sound` assumes the existing three `OpSound` contracts,
a decoded interval containing 1, a decoded parameter interval containing a
single real `t`, and a stored value witness
`z = (1-t)*a + t*b`. Conditional on success, the result encloses that `z`.
It holds for every stored witness at that `t`, including uncertain endpoint
coefficients. This algebraic evaluation theorem itself permits any real `t`;
`certified_evaluation` adds `t ∈ [0,1]` for the ideal-to-stored bridge.

Finite decoding is required by `Contains` for the one/parameter intervals and
stored endpoint witnesses. Success entails finite decoded output bounds under
the contracts. None of these premises guarantees success, sharpness, exact
rounded extrema or preservation of parameter correlation beyond this evaluation.
A wide parameter interval can yield a loose but sound result. Actual external
domain restrictions may only remove witnesses; this module does not manufacture
defined values of an application from enclosure membership.

The [fixture](tests/FiniteAffineDemotion.lean) discharges these operation
contracts through the existing directed addition, subtraction and four-corner
multiplication assembly theorems. Those are conditional on the already approved
call/comparison contracts. Raw-word decoding is kernel-proved; native
`Float`/`ofBits`/`toBits` correspondence, compiler and hardware execution remain
outside this proof. No new FP assumption, native integration or hot-path rational
arithmetic is introduced.

## Checks and examples

The fixture uses the genuinely uncertain ideal interval `[t, 1+t]`. The exact
endpoint words are `[0,1]` at zero and `[1,2]` at one; the strictly outward
candidate uses `[-1,2]` and `[0,3]`. Tests cover acceptance, inward lower/upper
rejection, infinity, NaN, oversized raw words, negative-zero acceptance, both
parameter endpoints and an interior value, and all four interpolation failure
stages. The rational reference evaluator checks `[0,1]`, `[1,2]` and `[1/2,3/2]`
at parameters 0, 1 and 1/2; these are proof-side control-flow examples, not a
hardware execution claim. The existing Binary64 fixture retains the exhaustive
format-edge controls rather than duplicating them here.

With the pinned toolchain, run:

```sh
lake build FiniteAffineDemotion
lake env lean tests/FiniteAffineDemotion.lean
./check.sh
```

For the optional pinned C API comparison, supply `RELGRAPH_CHECKOUT` explicitly
as documented in [operation coverage](OPERATION_COVERAGE.md). The module changes
no C API or implementation. See [validation receipts](VALIDATION.md) for results.
