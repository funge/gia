# First hardware-backed interval addition

This milestone executes interval addition with binary64 hardware arithmetic from
compiled Lean, and proves enclosure **conditional on an explicit contract for the
observed adapter results**. It is not a rational evaluator presented as hardware,
and it does not prove the C adapter or the physical processor correct.

## What runs

Run from this directory with the pinned Lean/Lake on PATH:

```sh
./check.sh             # kernel proofs, axiom allowlist and semantic controls
./hardware/check.sh    # compiled Lean + C hardware adapter and bit-pattern checks
```

The second command is local and opt-in; neither the application build nor hosted
CI calls it. It currently supports x86_64 with binary64 C double, a C compiler,
`objdump`, and the usual fenv facilities. No toolchain change is needed.

[hardware/Main.lean](hardware/Main.lean) calls an IO extern twice: lower endpoints
are added together, then upper endpoints. Each call returns optional downward and
upward results. The same pure [assemble](HardwareBounds.lean) function used in the
proof selects the lower result of the first call and upper result of the second.
There is no rational conversion or software rational arithmetic in this executable.

[adapter.c](hardware/adapter.c) saves the floating-point environment, holds exceptions,
sets FE_DOWNWARD/FE_UPWARD for volatile double additions, and restores the environment
before returning. Its object is checked for an `addsd` instruction. Nonfinite inputs,
nonfinite outputs, failed rounding setup, and FTZ/DAZ modes return `none` (unknown).
If restoring the environment fails, it aborts instead of returning with altered
state. Reversed input bounds are not rejected by assembly; the theorem requires
actual input membership, which rules out reversed finite intervals.

This deliberate finite-result scope sacrifices useful unbounded answers: overflow
is unknown. Signed zeros and subnormals are exercised, not excluded. No ambient
rounding-mode change is made around ordinary Lean `Float.add` calls.

## What Lean proves and what is assumed

[HardwareAddition.lean](HardwareAddition.lean) is generic over endpoint type `F`
and an interpretation `decode : F → Option ℝ`. `Contains` requires both endpoints
to decode to finite reals and bracket the point. `CallSound` states that, for decoded
operands and a successful observed pair, both outputs decode and enclose the exact
real sum. Failure says nothing about definedness or absence.

`assemble_encloses` proves: if both endpoint calls satisfy `CallSound`, assembly
succeeds, and x and y belong to the input intervals, the result contains x+y.
It derives endpoint inequalities from the two call contracts and real addition
monotonicity. `failure_is_unknown` proves propagation of lower-call failure.
No new axiom is declared; contracts are explicit theorem hypotheses.

To apply this theorem to the executable, the adapter contract must interpret
`Float` as its actual binary64 values and hold for its observed results. **This
interpretation and the C/FFI runtime correspondence are not proved here.** There is
no concrete verified `Float` decoder in this milestone. Thus the result is a
conditional correctness theorem for hardware-produced endpoints, not a completed
bit-level IEEE proof or an unconditional theorem about IO execution.

The externs have throwing Lean fallback definitions, so missing linkage cannot
silently emulate successful hardware calls. Their native replacements are not used
inside proof checking. No theorem identifies fallback IO with native execution;
the proof consumes successful observed results under the stated contract. Compiler,
FFI layout, fenv behavior and the processor remain at the explicit trust boundary.
The approved directed-rounding enclosure contract is used, not nearest rounding,
a ULP error assumption or a transcendental-library contract.

## Source and code correspondence

The repository [thesis PDF §2.5.3, printed p. 20 / PDF p. 36](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=36)
was visually checked: downward/upward arithmetic brackets the real value. This
milestone follows that small arithmetic contract. [§2.10, printed pp. 32–33 / PDF
pp. 48–49](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=48)
requires more for generalized machine-coefficient intervals; coefficient demotion
and parameterized bound evaluation remain future work. See the
[Tupper gap map](FLOATING_POINT_ROADMAP.md).

The corresponding public C operation is
[`gi_interval_add`](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/interval.c#L342).
The demonstration is a separate minimal adapter, not a wrapper around that function
and not its implementation verification. [Coverage](OPERATION_COVERAGE.md) keeps
this distinction explicit. Transcendentals, multiplication, division and extended
endpoints are not part of the executable milestone.

## Independent controls

The compiled Lean client asserts exact output bits for sums at ±1 halfway to the
next binary64 neighbor, ordinary interval corners, the two smallest subnormals,
signed cancellation, and unknown on overflow/infinity/NaN. It also checks restoration
of rounding mode and exception flags from all four rounding modes, and rejection
of FTZ/DAZ mode. Tests are
empirical evidence on this configured machine, not universal contract proofs.

The [semantic fixture](tests/HardwareAddition.lean) proves that inward rounding
violates the contract, missing results propagate unknown, and reversed intervals
have no represented member. Its real-valued fixture is a proof control only, never
the executable arithmetic backend. The core and fixture use the unchanged enforced
axiom allowlist. See [validation](VALIDATION.md) for the recorded run.

## Next hardware operation: subtraction

The extension in [HardwareSubtraction.lean](HardwareSubtraction.lean) reuses
`Bounds`, `Contains` and the pure `assemble` function. Its explicit `CallSound`
contract encloses the exact difference for a successful observed hardware call.
`HardwareSubtraction.assemble_encloses` proves the result contains `x-y`, using
calls on `(I.lo,J.hi)` and `(I.hi,J.lo)`. The second operand reverses the endpoint
order; neither new rounding modes nor a ULP/error-budget assumption is needed.
The interpretation/adapter/FFI trust boundary above is unchanged.

The compiled client now invokes `gia_directed_sub`, using the same save/hold/set/
restore environment code as addition. Only the raw arithmetic operation differs.
The object check requires both `addsd` and `subsd`. All earlier addition cases
remain, with nine subtraction cases: crossed corners, positive and negative
midpoints, the midpoint just below one (where binary64 spacing differs from above
one), subnormal difference, cancellation, and overflow/infinity/NaN unknowns.
Environment restoration and FTZ/DAZ rejection exercise both operations.

The [independent semantic fixture](tests/HardwareSubtraction.lean) checks a complete
application of the theorem, rejects inward rounding and demonstrates that the
incorrect same-endpoint rule misses an input pair. It also checks that a failed
call has an inconclusive contract and returns unknown. As before, its real-valued
proof control is not the executable arithmetic backend.

The public C counterpart is
[`gi_interval_sub`](https://github.com/funge/relgraph/blob/ee964e6272bf04b665165d1dc37bddb569f7a48c/src/interval.c#L350),
which uses the same crossed endpoints and a directed subtraction primitive.
The [header](https://github.com/funge/relgraph/blob/7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b/include/graphing/interval.h) declares it. Its empty/unbounded
interval handling is not reproduced or verified by this finite-result demo.
Tupper [§3.2.22, printed p. 64 / PDF p. 80](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=80)
was visually checked: subtraction is a common binary function, with the real
rewrite `x-y=x+(-y)`. This implementation uses direct directed subtraction, already
among §2.5.3's arithmetic primitives; it does not assume or verify a separate native
negation adapter to implement that rewrite. It is a finite endpoint construction,
not a claim to formalize every binary-function chart in the thesis.

## Prioritized remaining C API coverage

The [operation ledger](OPERATION_COVERAGE.md) is the exhaustive public-API inventory.
Most entries still lack an executable hardware path connected to their Lean
mathematics. A proof over rational intervals alone does not fill that gap.

| Priority | C operations | Concrete next obligation and scope |
| --- | --- | --- |
| Current | `gi_interval_add`, `gi_interval_sub` | Native demos plus conditional endpoint enclosure; actual decoder and adapter correspondence remain unproved |
| Current extension | `gi_interval_mul` | [Four-corner native operation and conditional proof](HARDWARE_MULTIPLICATION.md), with the approved finite min/max contract; unknown on exceptional corners. The C sign-section optimization remains separate |
| Current extension | `gi_interval_div` | [Guarded native division](HARDWARE_DIVISION.md): proved zero-exclusion and four-corner enclosure; exceptional results remain unknown |
| Next | `gi_interval_sqrt` | Explicit real square-root domain and clipping semantics; prove guard and endpoint selection |
| Composition | `gi_interval_pow_nonnegative_integer_exponent`, `gi_interval_factorial` | Iterate certified primitives with exact integer/domain checks and overflow policy. Repeated-input dependence must be preserved in the specification |
| Representation track | constructors, emptiness/membership, neg/abs/min/max, hull/intersection, comparisons and Boolean intervals, floor/ceil | Many select endpoints or have exact finite semantics rather than needing new rounding modes. Still require verified value interpretation, comparison/NaN behavior, signed-zero and empty/unbounded representation decisions; do not mistake these for completed hardware proofs |
| Separate domain/error work | remainder/mod, GCD/LCM point APIs, transcendental family including constants and `tan_defined` | Discontinuity and point-domain conditions need explicit treatment. Transcendentals need justified library error and range-reduction contracts; current C uses MPFR in this layer. No new such contract is adopted here |

The ABI descriptor and numeric-contract probe are infrastructure, not substitutes
for mathematical proofs. Passing a startup probe cannot prove every later operation
or future environment state. Likewise, extending the finite path to infinities
would be a representation milestone, not a silent change to `decode`.

Finite four-corner multiplication is now implemented under the approved finite
selection contract. Guarded division now has a proved zero-exclusion guard and
conservative unknown results; square root is the next arithmetic slice. Adding a concrete binary64
interpretation would separately reduce the remaining representation gap; it would
not by itself verify the C compiler or processor. Transcendental contracts and
extended-value behavior should be reviewed before adopting new assumptions.
