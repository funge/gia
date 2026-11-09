# Hardware-backed finite four-corner multiplication

This extends the hardware addition/subtraction path with an executable interval
multiplier and a **conditional** enclosure theorem. John approved finite native
min/max ordering as part of the adapter contract on 2026-11-08. The earlier
foundation and pending decision remain recorded truthfully in [validation](VALIDATION.md).
This branch builds on PR #71; it does not verify the C library or hardware itself.

## Executable path and theorem

Run `./check.sh` for proofs/audits/semantic fixtures and `./hardware/check.sh` for
the compiled native checks. The pinned Lean 4.19.0 setup is unchanged. The adapter
is x86_64 binary64, with the same rounding/environment boundary as
[addition and subtraction](HARDWARE_ADDITION.md).

The compiled Lean `multiply` calls `directedMul` for `(lo,lo)`, `(lo,hi)`,
`(hi,lo)` and `(hi,hi)`. Each successful call yields a downward/upward pair.
[assembleFour](HardwareBounds.lean) selects the minimum of the four lower results
and the maximum of the four upper results. Both the executable and theorem use
this exact pure assembly function, parameterized by the selectors. Any missing
corner propagates `none`, meaning unknown, not absence or mathematical undefinedness.
There is no rational arithmetic in this native computation.

[HardwareMultiplication.lean](HardwareMultiplication.lean) reuses the existing real
`four_products` lemma from [IntervalOps](IntervalOps.lean). `rounded_corners_enclose`
proves that four outward corner enclosures bound every input product.
`assembleFour_encloses` connects that result to the actual assembly function:

- Each input point is represented by its interval under `decode : F → Option ℝ`.
- Each of the four observed calls satisfies the explicit multiplication `CallSound`.
- The selectors satisfy `SelectSound` for real `min` and `max`.
- Assembly succeeds with result R.
- Therefore R represents an interval containing the exact real product x*y.

These are theorem hypotheses, not new axioms. The complete compiled IO execution
is not equated with a kernel reduction or verified by an IO/FFI refinement theorem.
The C primitive and the runtime Float-to-real interpretation remain unverified.

## Approved finite selection contract

For finite decoded operands `decode a = some x` and `decode b = some y`, the
approved adapter obligations are:

```text
decode (chooseMin a b) = some (min x y)
decode (chooseMax a b) = some (max x y)
```

The native selectors use Float comparison and return one of their operands.
Selection adds no rounding error: it returns an already represented endpoint.
The successful multiplication-call contract supplies finite decoded corner results.
NaN/infinite comparison behavior is therefore outside the selection contract.
Positive and negative zero both denote mathematical zero; either tie representative
is permitted. No bit-for-bit tie-policy agreement with the C library is claimed.

This makes finite IEEE ordering explicit at the same trusted adapter boundary as
directed arithmetic. It does not prove an IEEE 754 model, a binary64 decoder,
compiler correctness, or physical processor behavior. No extra error budget,
transcendental accuracy, ULP assumption or rounding mode is introduced.

## Tupper and C correspondence

The source inventory was consulted first, then the repository thesis PDF was
visually checked. [§3.1, printed p. 45 / PDF p. 61](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=61)
assumes an IEEE 754 floating-point system. On the same page, **§3.1.1 Exact
Functions** explicitly includes min and max among exact functions and distinguishes
that case from rounded approximations. For the finite inputs used here, selecting
an existing operand matches this abstraction. The source statement is not a proof
that this particular Lean/native selector implementation satisfies its contract.

[Tupper §3.2.25, printed pp. 67–68 / PDF pp. 83–84](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=83)
gives multiplication through sign sections, including `[-2,3] × [5,7] → [-14,21]`.
This implementation uses four original endpoint products. Its intermediate values
(-10, -14, 15, 21) differ from the source's splitting at zero, but the enclosure
agrees. It does not formalize the full sign-chart or section-pruning optimization.

The C [gi_interval_mul](https://github.com/funge/relgraph/blob/ee964e6272bf04b665165d1dc37bddb569f7a48c/src/interval.c#L358)
uses sign-section optimization and retains a four-corner path for zero/nonfinite
endpoints. This separate Lean demo concerns finite inputs/results only. It does
not reproduce or verify the C empty/unbounded representation, zero fast path,
NaN-handling or tie rules. It conservatively returns unknown if any corner is
nonfinite, even where a more sophisticated implementation could retain useful bounds.

## Controls and limits

The [semantic fixture](tests/HardwareMultiplication.lean) applies the full theorem
with selectors and four call contracts, reproduces the thesis example, rejects
an incorrect minimum selector, rejects insufficient corner selection, and checks
unknown for each of the four missing-corner positions. Its real-valued test backend
is only a proof control, not the executable implementation.

Native tests include mixed-sign and negative intervals, the thesis interval,
nonexact products just above one, positive/negative underflow, and an interval
where just one corner overflows. Zero times infinity remains unknown. The object
check requires `mulsd`; environment restoration and FTZ/DAZ rejection cover all
three arithmetic primitives. Tests give empirical evidence on this environment;
they do not discharge the explicit adapter contracts.

Multiplication encloses independent interval arguments. When the same variable
appears twice, this ordinary interval rule may be loose; it is not a square-specific
or dependency-preserving affine extension. Guarded division and square root remain
future hardware-path milestones with separate domain guards.
