# Directed dot-product composition

This proof composes the existing directed interval multiplication and addition
contracts into a finite dot-product program. It is a separate step from the
[exact independent-box bounds](INTERVAL_DOT_PRODUCT.md): soundness here does not
require tight bounds or independent inputs.

## Program and theorem

[DirectedDotProduct.lean](DirectedDotProduct.lean) takes vectors indexed by
`Fin n`, so both operands have the same dimension and no unmatched coordinates
are silently dropped. `run` starts with the supplied zero as a singleton bound.
It processes coordinates 0 through n−1, multiplying a coordinate pair and then
adding that product interval to the current accumulator. It does not reassociate
the sum, fuse multiplication with addition, or skip zero weights. Dimension zero
returns the zero bound without arithmetic operations.

`loop_encloses` proves the induction with an arbitrary enclosed real accumulator.
`run_encloses` concludes that every successful result contains the exact real
sum `∑ i, x i * y i`, provided that:

- every supplied input interval contains its corresponding real value;
- the supplied zero decodes to real zero;
- successful multiplication and addition satisfy the existing
  `HardwareIntervalOps.OpSound` contracts.

The same real vectors are used throughout. Correlations between coordinates do
not invalidate enclosure; they may make it loose. No leastness, attainment,
exact rounding, error bound, or guaranteed success follows from these premises.
Roundoff can accumulate at every multiplication and addition.

`primitiveRun` uses the existing two-call addition assembly and four-corner
multiplication assembly. `primitiveRun_encloses` discharges the interval-operation
premises using the existing `HardwareAddition.CallSound`,
`HardwareMultiplication.CallSound` and finite min/max `SelectSound` contracts,
via the already proved wrappers in [HardwareSine](HardwareSine.lean). Those
wrappers are reused; no trigonometric fact is needed by the dot-product proof.

## Failure and trust boundary

Any encountered multiplication or addition returning `none` makes the whole
program return `none`. This means no bound is available, not that the real dot
product is undefined or that its range is empty. It also does not certify an
absence of solutions. `mul_failure` and `add_failure` record the step rules;
fixtures cover a failure after an earlier successful coordinate.

`Bounds` itself does not enforce finite decoding or endpoint order. The theorem's
`Contains` premises supply those obligations for the actual real inputs. This
program is not a new raw-bit validation layer. Nothing here proves that invalid
native input must be rejected or that a failed computation preserves FP flags.

The program is executable pure Lean, parameterized by optional arithmetic calls.
It can be instantiated by observations from the existing binary64 adapter, under
its existing contracts, but **this milestone does not wire it to native IO/FFI**.
The compiler, Float representation, directed-operation behavior and finite
selection remain at the established adapter trust boundary. No new hardware
assumption, C operation, default path, FMA behavior or reassociation guarantee is
introduced. There is no claim about matching output bits between algorithms.

## Entry-point checks

The [fixtures](tests/DirectedDotProduct.lean) call `primitiveRun` itself with
kernel-checked rational mock primitives. For weights `[2,−1]` and features
`[3,4]`, all supplied intervals are singletons:

| Primitive behavior | Program result |
| --- | --- |
| Exact paired observations | `some [2,2]` |
| Sound observations widened by 1 on each side at every call | `some [−2,6]` |
| Multiplication unavailable at the second coordinate | `none`, while the exact real dot product is still 2 |
| Addition unavailable | `none` |
| Dimension zero with all arithmetic unavailable | `some [0,0]` |

The loose observations satisfy the same enclosure contracts. They demonstrate
why soundness alone cannot establish tightness or prevent accumulating width;
they are not a binary64 rounding-error model. Both successful fixtures also
instantiate `primitiveRun_encloses`, rather than only checking output arithmetic.

Run with the pinned setup:

```sh
lake build DirectedDotProduct
lake env lean tests/DirectedDotProduct.lean
./check.sh
```

The build and audits check the mathematical program and the reference fixtures.
No native dot-product execution or performance measurement is claimed. The
next implementation milestone would supply and qualify an actual adapter
route while keeping its execution order, failure behavior and trust limits
explicit. No fitting or training work is included here.
