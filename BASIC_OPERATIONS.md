# Finite basic interval operations

This proof-branch milestone fills six direct mathematical gaps identified by the
[public C operation ledger](OPERATION_COVERAGE.md): negation, absolute value,
minimum, maximum, interval hull and intersection. The implementation is in
[BasicIntervalOps.lean](BasicIntervalOps.lean); independent client controls are in
[tests/BasicIntervalOps.lean](tests/BasicIntervalOps.lean).

## Contracts

All input intervals are existing `QInterval` values: finite, ordered rational
endpoints denoting closed subsets of the reals. There are no empty input values,
infinite endpoints, NaNs or signed zeros in this type.

| Operation | Result | Claim |
| --- | --- | --- |
| `neg` | `[-hi,-lo]` | `neg_contains_iff`: exact reflection of membership |
| `minimum` | `[min(lo₁,lo₂),min(hi₁,hi₂)]` | Encloses `min x y` for every pair of input members |
| `maximum` | `[max(lo₁,lo₂),max(hi₁,hi₂)]` | Encloses `max x y` for every pair of input members |
| `abs` | `[max(0,lo,-hi),max(-lo,hi)]` | Encloses every absolute value; includes zero at a zero crossing |
| `hull` | `[min(lo₁,lo₂),max(hi₁,hi₂)]` | Contains both inputs and is contained in every interval containing both |
| `intersect` | Optional interval `[max(lo₁,lo₂),min(hi₁,hi₂)]` | Successful membership is exactly conjunction; `none` iff there is no shared real member |

`intersect = none` is a proved empty intersection, **not** an unavailable range.
The existing expression evaluator still uses `none` for unknown and is unchanged.
An intersection at a shared boundary returns a singleton, not `none`.
The hull need not equal set union; the negative/positive disjoint-input control
proves that it introduces zero even though neither input contains zero.

These operations do not add `Expr` constructors or generalized-domain wrappers.
They can be consumed directly by existing enclosure clients: the fixture composes
absolute value and maximum with `empty_pixel_sound` to exclude a root for every
point of a whole box. Min/max assume independently chosen members; they do not
assert shared-environment witness compatibility or recover lost dependency.

## Relation to Tupper and the C library

Starting source: graphing repository `docs/tupper-technique-inventory.md`, entry
C05. The repository PDF at commit
`18f2e0e22a4a5a7893a87252bd0722c919d9a546` was visually checked at printed p. 59
(PDF p. 75): §3.2.13 shows negation `[2,4]` to `[-4,-2]`, and §3.2.14 shows
absolute value `[-2.3,3.1]` to `[0,3.1]`. Both endpoint results are Lean controls,
with decimal constants represented as exact rational fractions. These are faithful
finite instances; the full source's extended-real, section and limit machinery
is not claimed. Source PDF:
[thesis p. 59](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=75).
The Markdown transcription is a navigation aid, not the formula authority.

The C API declarations are in [interval.h](https://github.com/funge/relgraph/blob/7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b/include/graphing/interval.h);
the definitions are in [interval.c](https://github.com/funge/relgraph/blob/7fd4b39dc127dec3be1b96a46cf392d4bcd73d2b/src/interval.c). The ledger links each
exact function at the baseline commit: `gi_interval_neg`, `gi_interval_abs`,
`gi_interval_min`, `gi_interval_max`, `gi_interval_hull`, and
`gi_interval_intersect`. These C counterparts select/reflect endpoints and handle
empty and unbounded inputs.
This milestone proves the underlying finite mathematics, not correspondence with
C execution. Absolute value uses an equivalent branch-free rational bound formula;
no theorem asserts that the C branch algorithm refines it. Full range optimality
for min/max/absolute value is not a theorem of this milestone. No continuity
certificate, rounding implementation, MPFR or IEEE refinement is added.

## Verification

Run `./check.sh` from this directory with the pinned toolchain and dependencies.
The module is imported by the default audit, with eight named theorem checks plus
the namespace-wide allowlist. The fixture tests source examples, zero and sign
cases, whole-box composition, a hull/union counterexample, disjointness, and a
shared boundary. The header-ledger test keeps the coverage map exhaustive; it
checks inventory, not the correctness of each prose assessment.

See the appended [validation record](VALIDATION.md) for actual execution results
and any environment limitation. No unchecked proof is described as completed.
