# Exact decoding of raw binary64 words

[Binary64.lean](Binary64.lean) provides a pure Lean decoder from an unsigned
raw-word input to `Option ℚ`. It is a proof foundation for constants, not a new
arithmetic backend or rational arithmetic on the native hot path. The existing
hardware core, batching, expression semantics and FFI are untouched.

## Representation and scope

`Word` is a natural number. The decoder checks `w < 2^64` rather than wrapping
out-of-range inputs modulo 2^64. For valid words it extracts the sign at bit 63,
the 11-bit exponent at bits 52–62, and the 52-bit fraction at bits 0–51. With
sign σ∈{1,-1}, exponent e and integer fraction f, the exact finite value is:

- e=0: σ f / 2^1074, including both signed zeros;
- 1≤e≤2046: σ (2^52+f) 2^(e-1075).

The implementation splits the latter at e=1075 to use natural powers with
multiplication or division. It does not interpret natural-number subtraction as
a negative exponent. An all-ones exponent returns `none`: both infinities and
all NaN signs/payloads have no rational value. `no_value_iff` proves this rejection
criterion together with the out-of-range guard; `finite` proves all remaining
words decode. Field bounds are proved for arbitrary inputs.

Rational zero deliberately forgets the sign of zero. This decoder does not model
NaN payload propagation, signaling behavior, exceptions, rounding operations,
byte order or hardware state. `none` here means **no finite rational decoding**,
not an interval-domain claim of nowhere-defined arithmetic.

The formulas match IEEE 754 binary64's finite representation. A checked public
reference is Oracle's [double representation table, G.2.3](https://docs.oracle.com/cd/E77782_01/html/E77788/bjbds.html),
which specifies the bias, implicit normal bit and exceptional exponent. This is
a mathematical definition of that representation plus kernel-checked results,
not a formal verification of the whole IEEE standard. Tupper's
[thesis](https://www.dgp.toronto.edu/~mooncake/thesis.pdf) §3.1 motivates the finite
floating-point/rounding setting; this decoder is a supporting foundation, not a
claim that Tupper used these particular pi constants or this encoding API.

## Four proved constants

| Raw word | Exact rational |
|---|---|
| `0x400921fb54442d18` | 7074237752028440 / 2251799813685248 |
| `0x400921fb54442d19` | 7074237752028441 / 2251799813685248 |
| `0x3ca1a60d3bc55bea` | 2483825185828341 / 20282409603651670423947251286016 |
| `0x3ca1a66bae498e34` | 1242014004962189 / 10141204801825835211973625643008 |

`pi_contains` directly instantiates `HardwarePi.decoded_contains` from
[PiBounds.lean](PiBounds.lean) with the two raw pi words. `tail_contains` directly
instantiates the existing [SplitPi.lean](SplitPi.lean) certificate for
`Real.pi - HardwarePi.lower`. Neither theorem has a remaining decoder premise.
The exact rational values are cast to reals in the proof-only `real` decoder.
The existing pi inequalities and split-tail choice are unchanged.

These words match `piBounds`/`piTail` in [hardware/Main.lean](hardware/Main.lean).
**The bridge to native `Float.ofBits`, `Float.toBits` and actual Float values is
still trusted/empirical.** No theorem equates native conversions to this decoder,
and no arbitrary compiled Float expression is now kernel-verified. Existing
[reduction](HARDWARE_SINE_REDUCTION.md) and [split-pi](HARDWARE_SINE_SPLIT_PI.md)
runtime oracles continue to check their native paths. No new FP assumption is
introduced, and the approved arithmetic adapter contract is unchanged.

## Controls and verification

[Semantic fixtures](tests/Binary64.lean) kernel-check both signed zeros and unit
values, signed minimum subnormals, the maximum subnormal, minimum normal and
transition gap, the exponent-scaling branch boundary, both extreme finite values,
both infinities, representative signaling/quiet and signed NaN payloads, and
out-of-range inputs. The general rejection theorem covers all nonfinite payloads,
not just those examples. A client fixture uses both direct enclosure theorems.
No `native_decide`, `sorry`, new axiom or native execution is used in these proofs.

Run `lake build Binary64`, `lake env lean tests/Binary64.lean`, then `./check.sh`
with the pinned toolchain. The module is included in named and namespace-wide
axiom allowlisting and fresh semantic-fixture validation. See
[validation receipts](VALIDATION.md). The native suite need not be rerun for this
proof-only addition; it does not change any native path.
