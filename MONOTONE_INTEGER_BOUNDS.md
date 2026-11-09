# Monotone endpoint bounds, floor and ceiling

This milestone builds on the finite operations in PR #69. It adds two reusable
endpoint-enclosure theorems and finite rational implementations of floor/ceiling,
with soundness and least-interval proofs. It does not add evaluator constructors.
See [MonotoneIntegerBounds.lean](MonotoneIntegerBounds.lean) and the independent
[client fixture](tests/MonotoneIntegerBounds.lean).

## Exact contracts and limits

`monotone_endpoint_encloses` assumes `MonotoneOn f [I.lo,I.hi]`, a certified lower
bound at the left endpoint and a certified upper bound at the right endpoint.
`antitone_endpoint_encloses` swaps the endpoint roles. Both conclude enclosure
for every real input member. The interval is finite, rational and closed. Endpoint
bounds may be loose; no continuity, global monotonicity or FP behavior is assumed.
Although `f` is a total Lean function, its behavior outside the input interval is
irrelevant. Applying this to partial mathematics requires an independently justified
defined real function on the whole closed interval; totalizing an undefined endpoint
is not justified by these theorems. Open endpoints and limits are not covered.

`QInterval.floor` uses rational endpoints obtained by casting the integer floors
of the input endpoints; `QInterval.ceil` does the same with integer ceilings.
`floor_encloses` and `ceil_encloses` apply the generic monotone theorem to the real
functions using mathlib's monotonicity and rational-to-real floor/ceil compatibility.
The operations are executable on rational inputs; the statements quantify over reals.
`floor_least` and `ceil_least` show that any interval containing every output contains
these computed intervals, because both endpoint outputs are attained.

Least interval enclosure is not exact discrete image. The fixture shows that the
floor enclosure of `[0,1]` contains `1/2`, which no real input can attain under floor.
It also proves that floor is not continuous on `[0,1]`, by the intermediate-value
theorem. No continuity or domain metadata is inferred from successful enclosure.

## Thesis and C correspondence

The starting source inventory is graphing's C04/C05 entries. The repository's
original thesis PDF was visually checked at printed pp. 56–58 (PDF pp. 72–74):
[T §§3.2.10–3.2.13](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=72).
The increasing and decreasing arguments select the domain's attained extreme
endpoint. The subsequent discussion covers limits when an endpoint is absent.
Our ordinary-real, closed finite interval theorems implement the attained-endpoint
case and compute both bounds directly. They do not formalize the extended-real
relation model, section charts or open/unbounded limit extensions.

The source floor example `[1.4,7.2] → [1,7]` on printed p. 58 / PDF p. 74 is
reproduced with exact rational decimal constants. Ceiling is listed there among
similar monotonic functions; its generic proof is instantiated here, not presented
as a separate numbered theorem from the thesis. The Markdown transcription is
not authoritative: in particular, its increasing-function passage incorrectly
renders the upper domain endpoint as an infimum. The PDF's upper-endpoint argument
and the following decreasing-function definition distinguish the two endpoints.

| C API | Implementation at the inventory baseline | Lean counterpart |
| --- | --- | --- |
| `gi_interval_floor` | [interval.c](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/interval.c#L545) | `QInterval.floor`, `floor_encloses`, `floor_least` |
| `gi_interval_ceil` | [interval.c](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/interval.c#L562) | `QInterval.ceil`, `ceil_encloses`, `ceil_least` |

The [public header](https://github.com/funge/relgraph/blob/7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b/include/graphing/interval.h) declares both operations.
C handles empty inputs, infinite endpoints and signed-zero normalization. The Lean
proofs cover finite rational bounds only, and do not verify those C behaviors,
libm execution, binary64 representability or fenv behavior. No new FP assumption
is introduced. [Operation coverage](OPERATION_COVERAGE.md) keeps these gaps explicit.

## Controls and reproduction

Run `./check.sh`. Six named audits and the namespace allowlist cover the core.
The fixture checks the source example, negative fractional inputs (distinguishing
floor/ceiling from truncation), integer singletons, shared closed boundaries,
antitone reflection, unattained intermediate values and discontinuity. It also
composes floor and ceiling with addition and the existing whole-box zero-exclusion
theorem, which needs no continuity. See [validation](VALIDATION.md) for results.
