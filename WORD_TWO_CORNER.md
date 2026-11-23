# Executable Word reference for guarded two-corner division

[WordTwoCorner.lean](WordTwoCorner.lean) supplies the missing executable input
validator and sign dispatcher for the [two-corner proof](TWO_CORNER_DIVISION.md).
It is an isolated, opt-in **Lean reference**, not a replacement for the native
four-corner implementation or any default path. It is independent of the draft
exact image-hull/Chapter 2 branch. No C arithmetic or FP assumption changes.

## Validate before dispatch

`validate` decodes all four raw words with the existing exact optional rational
[Binary64 decoder](Binary64.lean), then checks both endpoint orders and
`0 < denominator.lower ∨ denominator.upper < 0`. A failed decode, reversed
interval or denominator meeting zero returns `none`. This includes both signed
zeros, zero-only intervals, one-sided zero touches, infinity, NaN and oversized
Nat words. In particular an endpoint is never skipped merely because sign
selection would not use it.

`pick` uses executable rational sign tests in the same priority order as
`TwoCornerDivision.select`: positive/negative denominator, then nonnegative,
nonpositive or mixed numerator. It returns the **original words**, with no zero
normalization. `requests` performs validation before returning the two operand
pairs. `validate_spec`, `pick_decodes`, `pick_select` and `requests_spec` prove
that successful validation supplies the real decoding, order, nonzero guard
and real corner-selection facts. Validation is not an assumed predicate or a
claim about a native `Float` classifier.

`run` is an executable pure reference with an explicit request trace. Invalid
inputs return `([], none)` before either supplied paired-bound call. A failed
first call records one request and skips the second; otherwise both requests
are recorded, and existing `HardwareAddition.assemble` uses the first Down
bound and second Up bound, failing on an unavailable second pair.
`rejected_no_calls` and `invalid_no_calls` quantify over **any** supplied callback.
The trace is a checked reference dispatch trace, not native instructions, actual
fenv events or a statement about compiler evaluation counts. Two paired-bound
calls are not two individual rounding instructions.

This decoder-based validation is a cold/reference path. It does not establish
performance suitability or native Float/ofBits/toBits correspondence. The
callback here has a pure outcome denotation; no claim about equivalence of
stateful/nondeterministic executions follows from that model.

## Standalone soundness and the separate refinement theorem

`run_sound` assumes only the two selected observed division `CallSound`
contracts, successful reference assembly and actual real input membership.
Executable `requests_spec` discharges finite decoding, both orders and real
corner selection. The proof reuses
`TwoCornerDivision.assemble_selected_encloses`; it concludes containment of
`x/y` and `y ≠ 0` for every actual pair. It **does not require old four-corner
success**. Restricting reachable input pairs only removes witnesses; no claim
of actual occurrence follows merely from result membership.

`run_refines` separately reuses
`TwoCornerRefinement.directional_observations_refine`. Its premises retain:

- old four-corner assembly success and existing result/selection contracts;
- selected old operand/outcome associations;
- equality of the decoded retained Down and Up observations with the new calls.

It concludes successful reference assembly and decoded containment in the old
result. These premises include availability of the matched used observations;
they cannot be inferred just because two implementations are individually sound.
The structural refinement does not by itself supply quotient soundness;
`run_sound` handles that separately. Neither result promises equal availability,
raw bits, unused pair sides, exception flags or caller state. No exact rounding
assumption is added.

## Kernel-checked controls

[The fixture](tests/WordTwoCorner.lean) covers all six sign rows, and proves
empty trace/no result for arbitrary callbacks on:

- mixed `[-2,3]/[1,+∞]` and positive `[2,3]/[1,+∞]`;
- corresponding NaN denominator-upper cases, and invalid endpoints in each of
  the four positions;
- reversed numerator/denominator, crossing and touching zero, `[-0,+0]` as
  denominator, and oversized raw words.

For `[1,2]/[1,2]`, a finite observed-call table returns `[1/2,2]` through the two
selected calls while an omitted old observation fails. The selected contracts
are proved from the raw decoder, and standalone soundness is instantiated.
The old four-corner assembly is `none` for **any** selectors because that old
observation is unavailable. This demonstrates failure asymmetry in the model,
not native exception behavior. First- and second-call failure traces are checked.

Raw-tie controls verify the retained operand words:

- `[-0,+0]/[-2,-1]` selects `(+0,-1)` and `(-0,-2)`;
- `[-minsub,+0]/[-4,-2]` selects `(+0,-4)` and `(-minsub,-2)`.

Both are valid reference plans. We do not normalize the zero words or claim
raw quotient-bit agreement with the old path. The existing
[decoded-direction refinement](TWO_CORNER_REFINEMENT.md) explains why decoded
containment permits differing zero tags. No native bit difference was measured
in this milestone.

## Source and remaining experimental gates

This is a derived finite six-case rule, not a transcription of a Tupper chart.
The mathematical source context remains thesis §2.5.3 (directed arithmetic),
§3.2.22 (division via reciprocal/multiplication) and §3.2.26 (partial binary
functions), as documented in [hardware division](HARDWARE_DIVISION.md).
The unchanged [adapter](hardware/adapter.c) remains a separate native boundary;
this new module does not call it or modify the arithmetic core/flags.

**Pending, not run:** an opt-in native two-versus-four experiment validating all
four native endpoints before dispatch; raw quotient-bit comparisons for the two
zero/subnormal controls; caller fenv/status restoration and old failure
comparisons; direct non-singleton and compiled sine/cosine workloads. No timings,
production speed claim or native deployment follows from the reference request
count. The native/Word bridge remains unproved. This milestone deliberately stops
at the coherent kernel-checked selector and standalone/refinement proofs.

Run `lake build WordTwoCorner`, `lake env lean tests/WordTwoCorner.lean`, then
`./check.sh` with the pinned toolchain. Supply the optional pinned C API comparison
checkout explicitly as described in [operation coverage](OPERATION_COVERAGE.md).
See [validation](VALIDATION.md) for the local results.
