# Smaller-angle kernels and safe sine refinement

After split-pi reduction, the local Taylor bracket dominates some narrow-input
results. This milestone evaluates the existing proved kernels at a smaller
angle and reconstructs with exact real identities. The native client uses three
halvings inside each quadrant sine/cosine kernel, retaining the same split-pi
constants, quadrant cover and 40-level period search.
There are no new floating-point assumptions or operations.

## Shared program and mathematical proof

[TrigHalvingProgram.lean](TrigHalvingProgram.lean) recursively divides the input
interval by [2,2]. At depth zero it invokes the existing signed sine and cosine
kernels. Returning from each level, it evaluates

```
sin(2u) = 2 sin(u) cos(u)
cos(2u) = 2 cos(u)^2 - 1
```

with directed multiplication and subtraction. Both outputs refer to the same
real input witness. A failed primitive or base kernel fails the refinement.
The native local guard accepts only finite ordered intervals in [-1,1], after the existing quadrant reduction. Three
halvings place ideal arguments in [-1/8,1/8]; success still depends on actual
interval widths and primitive behavior, not an assumed exact-halving theorem.

[TrigHalving.lean](TrigHalving.lean) proves `run_sound` for the pair and
`sine_sound` and `cosine_sound` for its projections. The real double-angle identities are
mathlib theorems, not additional adapter contracts. The interval division
contract is instantiated at the mathematical denominator 2. No exact cancellation,
error-free transform, FMA, or correctly rounded transcendental is assumed.
The existing period, split-reduction and global-fallback theorems compose with
this new sound kernel.

## Preventing interval-width regressions

Repeated identities can amplify dependency error on wide intervals. For example,
the raw new method gives a wider result on [-3/4,3/4] than the previous
monotone-endpoint sine kernel. Therefore the final `sineSplitFine` client evaluates
both the previous split reducer and the new one and intersects their results.
If refinement fails, it retains the previous result; if the previous client
rejects the input, rejection is retained.

`refine_sound` proves this combination sound. The reusable `clip_subset` theorem
in [HardwareCover.lean](HardwareCover.lean) proves that intersection of valid
enclosures cannot introduce a represented real value outside either input.
Together with `clip_point`, this prevents losing a shared sine value while
preventing a wider result. This costs an additional evaluation; no speedup is
claimed. The existing clients remain available and unchanged.

## Measured improvement and remaining limits

At x = 10^12, using the same constants and search depth:

| Client | Observed enclosure width |
|---|---:|
| Previous split-pi client | 1.0556506485737138e-5 |
| Smaller-angle refinement | 3.4237006563131445e-9 |

This is a measured improvement of more than 3,000 times for this input, not a
universal precision theorem. In the final native vectors, 60 of 67 bounded point
inputs improved strictly, and no final output widened. Tests include points and quarter-unit intervals
through ±2^40, both signs, extrema, the wide dependency counterexample, huge
fallbacks and unsupported inputs. Intersection ensures the final valid result
is no wider than the previous result, but it may be identical. Wide/unresolved
inputs can still produce [-1,1].

Twenty-decimal pi bounds, interval dependency, accumulated operation rounding
and the base Taylor errors remain limitations. This does not provide accurate
all-binary64 reduction, correctly rounded sine or a universal refinement-success
claim. The proof remains conditional on existing directed-operation, decoding,
comparison and finite-selection contracts; IO/FFI/compiler/hardware refinement
remains trusted. External domains and holes are unchanged.

## Source correspondence and checks

Tupper §3.1.6, printed pp.48–49
([PDF page 64](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=64)), motivates
certified small-angle approximations combined with reduction. This double-angle
reconstruction is our extension using proved identities, not a claim that the
thesis prints this exact algorithm. The large-argument layer retains the
[§3.1.5 source comparison](HARDWARE_SINE_SPLIT_PI.md). The initial C comparison
is [`gi_trans_sin`](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/transcendental.c#L644);
no equivalence to its MPFR implementation is proved and it is not a build dependency.

Run `./check.sh` and `./hardware/check.sh`. The Lean fixture exercises zero depth,
failure, exact real reconstruction, and wider/tighter/failed refinement. Native
checks simulate every directed operation independently and compare against the
independent high-precision Machin-pi/series oracle at nine samples per bounded
interval. The wide raw-regression control is required, not hidden. Rational
arithmetic occurs only in test oracles, never the runtime. See
[VALIDATION.md](VALIDATION.md) for qualification and local-review limits.
