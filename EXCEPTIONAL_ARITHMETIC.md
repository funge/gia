# Explicit exceptional arithmetic cases

This tranche extends the existing [ExceptionalComparisons](ExceptionalComparisons.lean)
carrier and [fixture](tests/ExceptionalComparisons.lean). It creates no parallel
exception representation or hardware assumptions.

## Checked source, deliberately limited table

The original thesis §2.5.1–2 printed p.19 /
[PDF p.35](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=35) was visually
checked. It explicitly displays addition of positive infinity when the left
operand is not negative infinity, and `sqrt(-1)` returning lambda. The surrounding
text treats undefined real operations as lambda. §2.6 introduces extended reals;
its type-conversion/sequence discussion on printed p.22 / PDF p.38 was also
visually checked. Neither page supplies a complete exceptional-arithmetic table.

| Modeled input | Result | Basis and limitation |
| --- | --- | --- |
| finite x + finite y | finite (x+y) | Existing exact REAL core, not the source rounded floating-point addition |
| finite x + positive infinity | positive infinity | Displayed §2.5.1 rule, finite-left case |
| positive infinity + positive infinity | positive infinity | Displayed §2.5.1 rule, same-positive-infinity case |
| sqrt(finite x), x < 0 | lambda | Undefined real root convention and explicit negative-root example |
| sqrt(finite x), 0 ≤ x | finite sqrt(x) | Existing exact partial-real root relation, not a correctly rounded native root |
| Other exceptional inputs | Unmodeled | No automatic IEEE completion, commuted row, lambda propagation or totalized arithmetic |

The addition implementation deliberately claims only the named cases of the
printed guarded formula. It does not settle a lambda-left guard reading or
turn the prose into a full table. The source's equation specifying a result
is distinguished from its numerical equality observation: the result of
positive-infinity plus positive-infinity is positive-infinity, while the
previous numerical equality observation at that pair is false. These are not
contradictory Lean propositions because the two relations are distinct.

`some Value.undefined` is a specified lambda result. `none` is missing coverage
in this partial specification, not a source result or a hardware failure.
In particular negative infinity plus positive infinity is *unmodeled here*,
not proved to return lambda. A lambda input is likewise not given a propagation
rule. A positive-infinity root remains unmodeled rather than filled by analogy.

## Proof and existing-model correspondence

`add_finite_agreement` uses the existing PartialRealArithmetic addition relation.
`sqrt_finite_agreement` agrees exactly with the existing SqrtValues relation;
`sqrt_defined_iff` characterizes actual finite results by nonnegativity.
`negative_root_not_totalized` explicitly separates absent real roots from
mathlib's total `Real.sqrt`, which returns zero at a negative input.

`add_bound_agreement` is limited to successfully observed addition rows with
successful operand bound interpretations. It proves that mapping that result
to ordered EReal bounds agrees with EReal addition for those rows. It is not a
homomorphism theorem for all source arithmetic, comparisons or IEEE values.
No claim equates same-sign source numerical equality with bound equality.

There are no infinite elements of ℝ. The carrier's infinity constructors are
ideal/source tags; EReal top/bottom are separately interpreted bound endpoints.
Neither is a raw binary64 word, a native Float result or a verified implementation
of the source promotion. In particular finite exact addition here does not
replace any rounded addition contract or runtime.

## Regression evidence and scope

The source-backed table is checked alongside finite 2+3, negative/zero/positive
roots, the distinction between modeled lambda and missing coverage, unassumed
lambda propagation, and structural result equations versus numerical equality.
All earlier comparison proofs are preserved. No heterogeneous comparison
completion is needed by these arithmetic rows; finite root guards use ordinary
real ordering only.

This closes the explicitly listed arithmetic obligations, not all §§2.5–2.6.
See the updated [completion ledger](CHAPTER2_COMPLETION.md),
[concordance](THESIS_CONCORDANCE.md), [validation](VALIDATION.md). The signed sequence representation and supported mathematical promotion/demotion
are documented in this unit; remaining comparison directions, full source-carrier
promotion and the source rounding model remain separate obligations. Unprovided arithmetic rows
must not be invented merely to make a total API.

```sh
lake build ExceptionalComparisons
lake env lean tests/ExceptionalComparisons.lean
RELGRAPH_CHECKOUT=/path/to/pinned/relgraph ./check.sh
```
