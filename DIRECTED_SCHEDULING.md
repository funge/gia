# Same-outcome equivalence for independent directed requests

[DirectedScheduling.lean](DirectedScheduling.lean) is a pure proof model for an
opt-in batching design. It does not install batching, modify C/FFI code, or claim
performance improvements. The transferred experiment is not an input to this
proof and was not executed.

## Exact scheduling statement

A `Request F` contains an arithmetic opcode, explicit Down/Up direction, and two
immutable operands. The opcode reuses the existing four-constructor hardware
operation type (add, subtract, multiply, divide), without changing it. A group is
indexed by stable slots `S`; interval addition uses the finite `AddSlot` type.
The generic theorem also applies to any other slot type.

`phase denote requests direction` is a pure indexed tabulation: a skipped slot
is `none`, while an executed request returning no result is `some none`. This
distinction prevents losing failure information while separating the phases.
`reassemble` routes each stable slot to its explicitly requested direction.
It does not zip phase positions or depend on an ambient rounding mode.

The kernel proves, for every `denote : Request F → Option F` and immutable group:

```lean
scheduled denote requests = fun slot => denote (requests slot)
```

This is equality of all per-request outcomes, including `None`. The abstract
phase semantics is indexed rather than an imperative list traversal. It proves
routing/reassembly for independent requests; it does not verify a mutable buffer,
loop, allocation strategy, C evaluation order or physical processor scheduling.
A finite implementation must establish that its executor realizes these indexed
outcomes. Explicit direction per request is compatible with a static-rounding
backend; grouping into two phases is one implementation strategy, not a required
hardware mechanism or global fenv assumption.

`reassemble_eq_of_outcomes` allows separately supplied phase results. Its premises
are exactly that each active Down/Up slot equals `some (denote request)`; inactive
slots are irrelevant. These premises include failures. They are universally
quantified mathematical hypotheses, **not new hardware assumptions adopted by
the project**. No claim is made that actual scalar and fused native implementations
already satisfy them.

## Interval addition and all four outcomes

`addRequests` retains lower-Down, lower-Up, upper-Down and upper-Up. `pair` requires
both directed outcomes for each endpoint call; `assembleSlots` then invokes the
existing [HardwareAddition.assemble](HardwareBounds.lean). Although only
lower-Down and upper-Up become interval endpoints, failure in **any** of the four
slots yields no bound (`any_failure`). Neither unused outcome is elided.

`batchAdd_eq` proves the same result as `scalarAdd` for the same denotation.
`observed_add_eq` proves the analogous equality under the active-slot outcome
premises for observed phases. `scalarAdd` is reference assembly from the four
outcomes, not a claim to have verified the actual scalar FFI. Any native pair
validation and error paths still need a refinement argument.

`batchAdd_encloses` reuses the existing [CallSound and assemble_encloses](HardwareAddition.lean)
contracts for the two **same paired outcomes**. Thus an assembled result encloses
the real sum under the existing contract. No stronger rounding, uniqueness or
bit-level assumption is introduced.

## Failure and dependency boundaries

`withEnvironment false ... = none` is a separate theorem. It expresses fail-closed
batch-wide failure, not exact equality with every scalar infrastructure failure.
There is no proof here of fenv acquisition/restoration, exception flags, traps,
abort behavior, NaNs or allocation failure. Those remain native obligations; the
model's `None` supplies no bound and does not classify the mathematical domain as
empty.

The fixtures show that environmental failure can coexist with a successful scalar
reference result. They also show two different paired outcomes satisfying the
same `CallSound` contract, and that failure satisfies that contract. Therefore
soundness alone implies neither identical results nor identical availability,
let alone bit equality between independent implementations.

A dependency example constructs a second group only after the first result is
available: `(1+2)+4` yields 7, whereas hoisting the second request with stale zero
would yield 4. Failure of the first group prevents construction of the dependent
request. The generic equality applies within each immutable independent group;
it does not authorize crossing such dependency boundaries.

## Qualification

[Fixtures](tests/DirectedScheduling.lean) cover all four arithmetic opcodes,
phase skipping versus executed failure, all four addition failure slots,
addition assembly, environment failure, dependencies and soundness counterexamples.
Their Nat arithmetic is a scheduling fixture, not a binary64 numerical oracle.
Run `lake build DirectedScheduling`, `lake env lean tests/DirectedScheduling.lean`
and `./check.sh`. Named and namespace audits cover the new proofs. See
[validation receipts](VALIDATION.md). No native path, AST or production algorithm
changes, no additional FP assumptions, and no benchmark or C-equivalence claim.
