# Right-positive-infinity addition through family conversion

Source: Tupper §2.5.1, printed p.19 / [PDF p.35](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=35), with the surrounding §2.5.2 discussion. The displayed positive-infinity addition rule is already represented by the finite-left and positive-infinity-left rows of `ExceptionalComparisons.addObservation`. This milestone connects those existing rows to family conversion; it does not add an exceptional arithmetic table.

The precise unresolved source boundary remains the lambda-left reading of the guard, opposite-infinity addition, and any unprinted commuted or propagation rows. They stay `none` in this partial model, not `some undefined`. Finite payloads are the existing ideal real interpretation, not a newly verified finite floating-point operation or IEEE instruction. See [the original arithmetic scope](EXCEPTIONAL_ARITHMETIC.md).

## Exact graph and transfer

[InfiniteAdditionTransfer.lean](InfiniteAdditionTransfer.lean) defines the observation image of an actual tagged input set under right addition by literal positive infinity. `graph` proves the entire image:

- `some posInf` occurs exactly when there is a finite input or a literal positive-infinity input;
- `none` occurs exactly when a negative-infinity or lambda input is admitted by the family;
- no other observation occurs.

All equalities here are structural result/set equalities, not the source numerical equality observation on infinities. The second row reports missing model coverage, not undefinedness of the source operation. An empty input family has no observations, and a mixed family can have both successful and missing observations. The graph keeps actual input witnesses; no Cartesian independence assumption is introduced.

`conversion_exact` proves a sufficient general conversion theorem: a conversion that preserves nonemptiness of the finite part and retains the exceptional tags has exactly the same observation image. This does not assert equality of the individual operand witnesses or preservation of all cross-parameter correlations. It works because every supported finite input has the same result for this particular operation.

`hull_observations` discharges that premise for the existing least extended-bound hull, including empty and unbounded finite sets. `result_hull_fixed` and `hull_commutes` prove exact commutation on the successful result sets: converting inputs then applying the operation equals applying it then converting outputs. The outputs contain no finite payload and at most the literal positive-infinity tag. `family_transfer` supplies this equality at each same parameter and also preserves missing coverage. It is not a homomorphism theorem for arbitrary operations or conversions.

## Three meanings kept distinct

An unbounded set of finite real inputs contains no literal infinity or lambda. Its hull does not insert those tags. The right operand in this theorem is instead an explicitly supplied **literal** positive infinity. The successful output tag comes from the existing operator rule, not from treating an infinite hull endpoint as an input value.

Explicit lambda input remains admitted by conversion, but this operator table gives no result for it (`none`); no propagation rule is assumed. This differs from an operator explicitly returning `some undefined`, such as the modeled negative-root row.

[Kernel controls](tests/InfiniteAdditionTransfer.lean) cover empty, finite, literal-infinite, lambda-only, mixed and unbounded finite families; preservation of missing observations; absence of invented infinite input tags; and a converter that wrongly creates a finite witness from the empty set, which demonstrably changes the observation image. The unmodeled reversed addition row remains unchanged.

## Remaining work

This closes one concrete exceptional-operation/conversion connection using existing source-backed rows. Nonconstant operations such as the existing partial square root need separate image/domain transfer results; a hull may introduce boundary inputs, so exact commutation cannot be assumed. A complete exceptional arithmetic table, lambda-left source interpretation and IEEE implementation are not resolved. Chapter 2 remains incomplete.

Run `./check.sh`; [VALIDATION.md](VALIDATION.md) records actual qualification. No new project axioms, floating-point assumptions, native/default changes or performance claims.
