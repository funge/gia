# Finite guarded hardware division

This extends the compiled Lean hardware path after multiplication (PR #72).
`HardwareDivision.assembleGuarded_encloses` proves that successful assembly encloses
`x / y` **and that `y ≠ 0`**, for every pair of represented input values.
The executable client uses native binary64 division in both directed modes; it does
not evaluate rational arithmetic as a substitute for hardware execution.

## Contract and proof

[HardwareDivision.lean](HardwareDivision.lean) checks `denominator.hi < 0` or
`0 < denominator.lo`. `awayZero_sound` derives this real condition from finite
comparison agreement and the explicit representation equation `decode zero = some 0`.
`guarded_nonzero` proves every represented denominator nonzero. `four_quotients`
uses reciprocal order and the existing four-product bound for either denominator
sign. The shared [four-corner assembly](HardwareMultiplication.lean) then encloses
the result under four directed-division call contracts and finite min/max contracts.
The existing multiplication theorem retains its interface and regression tests.

Finite strict comparison uses the already approved finite IEEE ordering boundary;
`CompareSound` spells out its Boolean form. No ordering claim is made for NaNs.
Both signed zeros decode as real zero under the intended representation, and neither
can pass the strict guard. The decoder, zero interpretation, primitive enclosure,
and finite ordering remain explicit hypotheses: there is no new global axiom or
formal verification of the Float representation, FFI, compiler, processor, or fenv.
No transcendental error budget or extended-infinity semantics is introduced.

The [compiled client](hardware/Main.lean) checks the guard before requesting four
quotients from the [native adapter](hardware/adapter.c), then uses the same pure
assembly checked by Lean. NaNs, nonfinite input/output, FTZ/DAZ and unsupported
conditions return `none`. Intervals touching or crossing zero also return `none`,
even if some represented quotients exist. This means unknown, never nowhere-defined
or empty. Overflow in a single corner rejects the whole result. Gradual underflow
is supported; zero-sign tie choices are not an implementation-equivalence claim.

## Tupper and C correspondence

Use the [repository thesis PDF](https://www.dgp.toronto.edu/~mooncake/thesis.pdf),
not damaged Markdown formulas. Tupper §2.5.3 (printed p.20 / PDF p.36) supplies the
directed arithmetic setting; §3.1.1 (printed p.45 / PDF p.61) lists exact min/max.
§3.2.22 (printed p.64 / PDF p.80) expresses division through reciprocal and
multiplication; §3.2.26 (printed p.68 / PDF p.84) treats partial binary functions.
This is a finite, zero-excluding construction, not all of those generalized charts.

The public [`gi_interval_div` implementation](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/interval.c#L461)
returns whole for a zero-containing denominator, and otherwise constructs a rounded
reciprocal then multiplies. This client instead directly rounds four quotients.
Their real division specification is related; bitwise equality, equal tightness and
C correctness are **not** proved. Empty/unbounded C representation is not modeled.

## Reproduction and controls

Run `./check.sh` and `./hardware/check.sh` from this directory with the pinned Lean
on PATH. [Semantic fixtures](tests/HardwareDivision.lean) independently instantiate
the assembled theorem, cover both signs, reject a false comparator, and show that
zero-guard rejection does not imply undefinedness everywhere. Native tests include
1/3, both signs of underflow, signed zero, crossing/touching zero, overflow, NaN and
infinity. The restoration probe first demonstrates that native 1/3 raises INEXACT,
then checks the wrapper preserves caller flags and each of four ambient modes.
See [validation receipts](VALIDATION.md) for measured results. Passing native tests
is empirical qualification of the trusted adapter, not proof of its contract.
