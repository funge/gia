# Hardware shared-parameter multiplication

This extends [hardware affine forms](HARDWARE_AFFINE.md) with multiplication of
two finite forms sharing one parameter in [0,1]. The output is a **composable
form**, not just a range hull. The existing `hull` operation can discard its
parameter dependence when a constant interval is needed. No expression evaluator,
new floating-point primitive, or trigonometric work is included.

## Construction and proof

For pointwise endpoint witnesses `a,b` and `c,d`, write

```
x(t) = (1-t)*a + t*b
y(t) = (1-t)*c + t*d
C    = (b-a)*(d-c)
x(t)*y(t) = (1-t)*(a*c) + t*(b*d) - C*t*(1-t).
```

The existing `parameter_bubble_bounds` proves `0 ≤ t*(1-t) ≤ 1/4` on [0,1].
[The executable program](HardwareAffineProductProgram.lean) computes:

1. Interval endpoint products `P0 = I0*J0` and `P1 = I1*J1`.
2. Interval differences `D = I1-I0`, `E = J1-J0` and curvature `C = D*E`.
3. Residual interval `R = C*[0,1/4]`.
4. Output endpoint intervals `P0-R` and `P1-R`.

All eight interval operations use the existing directed binary64 subtraction
and four-corner multiplication. No rational arithmetic runs in this path, and no
exact cancellation, exact multiplication, new rounding mode or FMA is assumed.
The constants 0 and 1/4 are exactly representable binary64 values. As with earlier
constants, their real interpretation is an explicit proof premise, discharged
by the adapter's existing decoding boundary, not a new Lean axiom.

[The proof](HardwareAffineProduct.lean) establishes `product_sound` for the full
`HardwareAffine.Contains` semantics. It chooses the actual pointwise endpoint
witnesses, proves the computed residual contains their curvature times
`t*(1-t)`, and uses that same residual witness at both output endpoints.
Thus the theorem covers uncertain endpoints and mixed signs, not only exact
center lines. Witnesses may vary with `t`; the enclosed function need not itself
be affine. The product retains enclosure but does not retain every correlation
between intermediate rounding errors. `product_hull_sound` combines the result
with existing finite min/max contracts. A fresh Lean fixture composes this result
with another multiplication and with the existing directed primitive contracts.

## Source correspondence

Tupper's [thesis §2.9.3, printed pp.28–30](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=44)
uses one shared parameter and a pointwise inclusion property for linear bounds.
[§2.9.5, printed p.30](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=46)
introduces quadratic bound functions and leaves their demotion for later.
The repository PDF was visually checked, including its warning on p.30 that
there is no universally best linear demotion.

This implementation realizes a **derived finite quadratic chord construction**,
using the polynomial identity and bubble bound already formalized in
[LinearMultiplication](LinearMultiplication.lean). The existing
`quadratic_chord_lower_iff` / `quadratic_chord_upper_iff` concern sharp constant
shifts of a fixed chord; this milestone does not claim globally optimal affine
bounds or reproduce a particular chapter-3 multiplication algorithm.
It is not the thesis's full extended-real quadratic interval system.

The initial implementation comparison remains the pinned relgraph
[`gi_interval_mul`](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/interval.c#L358),
whose ordinary interval behavior is used as a precision baseline. This new
shared-parameter operation is not a corresponding new C API symbol and is not
proved equivalent to relgraph C code. The [primitive multiplication guide](HARDWARE_MULTIPLICATION.md)
and [coverage ledger](OPERATION_COVERAGE.md) retain those separate boundaries.

## Measured gain and counterexamples

For exact input forms `t` and `1-t`, native output endpoint intervals are both
`[0,1/4]`, so the hull is `[0,1/4]`. This is the exact range, with 0 attained at
an endpoint and 1/4 at `t=1/2`. Ordinary hull multiplication gives `[0,1]`:
**four times narrower**, or a **75% width reduction**.

It is not universally tighter. For `t*t`, the fixed-chord construction produces
`[-1/4,0]` at zero and `[3/4,1]` at one; its hull `[-1/4,1]` is wider than the
ordinary `[0,1]`. The parameterized upper bound still carries useful structure.
Across the 64 native pairs, hulls were **32 tighter, 20 wider, 12 equal**.
No selection or intersection policy is silently added to hide wider results.

Treating the operands' parameters independently invalidates the quarter bound:
`t=1` and `s=0` give `t*(1-s)=1`. Extrapolation outside [0,1] also invalidates the
bubble bound. These are explicit Lean controls. The endpoint chord alone misses
the interior maximum; a separate control rejects that shortcut.

## Failure, trust and reproducibility

The native wrapper rejects nonfinite/reversed inputs. Any failed intermediate
returns `none` and short-circuits. Product overflow and slope overflow are tested
separately: multiplying a form with endpoint values `-maxFinite,+maxFinite` by
zero still returns unknown when its slope computation overflows, even though the
mathematical product is zero. Thus success is not guaranteed for every finite
input or every finitely bounded mathematical result. Failure is not absence or
undefinedness. External domain evidence is not inferred or broadened.

The conditional trust boundary is unchanged: directed operations, decoding,
finite comparison/min/max, IO/FFI refinement, compiler and hardware behavior
remain trusted. Lean proves the source-level pure specialization; native tests
exercise the compiled shared program. The adapter C, compiler flags, toolchain,
dependency pins and licenses are unchanged. No hosted CI is added.

Run `./check.sh` and `./hardware/check.sh`. The new
[semantic fixture](tests/HardwareAffineProduct.lean) checks the common parameter,
unit domain, missing-curvature counterexample, uncertain witnesses, directed
contract composition and repeated products. The
[independent test oracle](hardware/check_affine_product.py) validates all 64
observed products and their compositions using exact directed rational simulation.
It additionally checks exact quadratic extrema against both output affine bounds
for all 16 endpoint-witness combinations of each input pair, over the entire unit
interval rather than only a grid. Repeated products are also checked at five
shared parameters. Native tests inject failure at each of eight operations and
check short-circuit counts, malformed values, overflow and subnormal cases.
These tests supplement the universal Lean theorem, not verification of hardware.
See [validation receipts](VALIDATION.md).
