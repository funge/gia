# Hardware-backed shared-parameter affine enclosures

This milestone connects the existing [linear interval model](LinearIntervals.lean)
to the directed binary64 backend. It is general arithmetic, independent of graphing.
It supports finite forms, addition, subtraction, scalar multiplication, and a
conservative interval hull. It does not implement nonlinear affine multiplication
or a general affine expression evaluator.

The subsequent [multiplication milestone](HARDWARE_AFFINE_PRODUCT.md) adds a
composable quadratic-residual enclosure under the same contracts. The limits
below describe this original addition/subtraction/scaling milestone.

## Source correspondence

Tupper's [thesis](https://www.dgp.toronto.edu/~mooncake/thesis.pdf), §2.9.3,
printed pp.28–29 (PDF pp.44–45), defines linear lower and upper bounds with one
shared parameter in [0,1]. Printed p.29 states the pointwise inclusion property
and contrasts `α−α = 0` with ordinary interval subtraction `[-1,1]`.
The existing `affine_ofCoefficients_value` and related endpoint results
establish the finite rational representation correspondence; see
[concordance](THESIS_CONCORDANCE.md). This implementation uses endpoint intervals
rather than directly storing the thesis's coefficients. It is a finite,
conservative implementation of that inclusion principle, not the thesis's full
extended-real interval system or a claim of optimal demotion.

The outward primitive contracts follow the already documented Tupper §3.1 / IEEE
boundary. See [addition/subtraction](HARDWARE_ADDITION.md) and
[multiplication](HARDWARE_MULTIPLICATION.md) for the pinned relgraph C targets and
native adapter details. This milestone composes those operations; it neither
changes nor verifies relgraph's C implementation. The checked public C API ledger
has no new symbol added by this milestone.

## Representation and proved semantics

[HardwareAffineProgram](HardwareAffineProgram.lean) stores four finite binary64
bounds: an interval at parameter zero and another at parameter one. The runtime
contains no rational arithmetic. At a common parameter `t`, the represented
values have the form `(1−t)*a + t*b`, where `a` and `b` belong to those endpoint
intervals. These are pointwise witnesses and may vary with `t`; the represented
real function need not itself be affine, as Tupper explicitly notes on p.28.
Endpoint uncertainty therefore includes rounding error.

[HardwareAffine](HardwareAffine.lean) proves:

- `add_sound` and `sub_sound`: corresponding endpoint operations enclose addition
  and subtraction of values evaluated at the **same parameter**.
- `scale_sound`: multiplication by one common real scalar enclosed by the scalar
  interval is sound, including negative scalars. The native API takes a finite
  binary64 scalar and supplies its singleton interval to both endpoints.
- `linear_bridge`: if hardware endpoint intervals enclose both rational bounds
  at each endpoint of an existing `LinearInterval`, every value it represents on
  [0,1] belongs to the hardware form. This covers nonzero-width linear intervals,
  not only a chosen central affine function. It is an enclosure bridge, not an
  executable rational-to-float conversion or a precision equivalence claim.
- `exact_affine_bridge`: the corresponding statement for an exact `QAffine`.
- `hull_sound`: selecting the minimum lower and maximum upper endpoint encloses
  all represented values on [0,1]. Outside that parameter range this hull need
  not be sound; a Lean counterexample records this restriction.

The arithmetic identities hold for arbitrary common real `t`; the connection to
ordered linear intervals and their hull uses [0,1]. Callers must provide common
parameter witnesses. Reusing the same storage object does not manufacture such
an identity, and unrelated parameters must not be treated as equal. The API does
not track parameter names or correlations between independent rounding errors.

`combine` and `scale` share their source between pure theorem specialization
and IO execution. Failure at either endpoint returns `none`, including when the
first endpoint succeeded. The native wrappers reject nonfinite or reversed
endpoint intervals and nonfinite scalars. Overflow or adapter failure remains
unknown, not an empty set or a proof of undefined real arithmetic.

## Cancellation and limits

The native example subtracts `2+t` and `1+t`: its affine result is exactly `[1,1]`
at both endpoints. Demoting before subtraction produces the wider `[0,2]`.
Another example first rounds `1 + 2^-53`, then subtracts the resulting uncertain
form from itself: the result retains a nonzero error band. Only the shared
parameter dependence is preserved; this is not symbolic cancellation of all
uncertainty. Finite underflowing operations can still return sound rounded bounds.
True overflow is conservatively rejected.

There are no infinities as real endpoints, multiple noise symbols, affine-form
products, domain inference, interval partitioning, or automatic parameter
alignment. A scalar interval's common witness is required even though the two
endpoint operations are evaluated separately.

## Trust boundary and verification

No floating-point assumption is added. `HardwareIntervalOps.OpSound` is the old
successful-operation enclosure contract extracted from `HardwareSine`; the old
name is retained as a compatibility abbreviation. Existing directed-call assembly
proofs discharge it. The fresh Lean fixture explicitly checks subtraction and
scalar composition with those primitive contracts. Finite min/max ordering is
the previously approved assumption, used for multiplication and hull selection.

Lean proves the real enclosure theorem conditional on these contracts. It does
not prove the IO/FFI refinement, IEEE hardware behavior, compiler flags, ABI,
Float decoding/comparison, or floating-environment restoration. Existing native
checks exercise that trusted path; the C adapter, compiler flags and toolchain
are unchanged. No trusted libm operation or new axiom is introduced.

Run `./check.sh` and `./hardware/check.sh` with the pinned Lean toolchain on PATH.
[Semantic controls](tests/HardwareAffine.lean) cover the full linear bridge,
common witnesses, the hull restriction, uncertainty and failure.
[The native client](hardware/Main.lean) exercises existing directed hardware
primitives. [The independent oracle](hardware/check_affine.py) checks 102 results
against exact rational directed rounding and all endpoint witnesses at five
shared parameter samples. Rational arithmetic appears only in tests, never the
hardware runtime. These finite tests supplement the universal Lean proofs; they
do not verify the compiler or hardware. See [validation receipts](VALIDATION.md).
