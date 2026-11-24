# Strict finite-expression convergence

[ExpressionStreams.lean](ExpressionStreams.lean) closes a restricted but
compositional part of Tupper §2.15.5, printed pp.42–43 / PDF pp.58–59
([original source](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=58)).
The source discusses converging rational interval streams, initial delay when a
denominator contains zero, and arbitrary accuracy for defined finite expressions.
This result uses the **existing exact-rational evaluator** as a mathematical
model of that statement. It is not a replacement for the project's hardware
backend, and no native arbitrary-precision claim follows.

## Exact premises and result

The grammar is the existing `Expr`: rational constants, two real variables `x`
and `y`, addition, subtraction, multiplication and division. It is finite because
it is inductive. There is no new AST, evaluator, transcendental operator or
renderer interface. `eval exactBackend` and its existing `guardedDiv` are unchanged.

`Converges X x` means that both rational endpoints of `X : ℕ → QInterval`,
cast to reals, converge to `x`. Every interval is finite, nonempty and ordered by
its type. No nesting, convergence rate or input enclosure is hidden in this
predicate. The two input streams use the same index `n` throughout evaluation;
repeated occurrences use the same input box and real valuation.

Given `Converges X x`, `Converges Y y` and **`Value x y e z`**,
`eval_converges` constructs an output stream `R` with:

- both output endpoints converge to `z`;
- eventually, `eval exactBackend (X n) (Y n) e = some (R n)`.

The existing strict `Value` derivation requires both children defined at every
binary node and an actual nonzero denominator at every division node. It is not
totalized real expression evaluation. The proof is by induction on this existing
derivation: sums/differences by continuity, products by convergence of all four
corners and min/max, division by eventual separation from zero and inverse
continuity. `eventually_away` reuses the previous `ReciprocalStreams` guard theorem.

`reciprocalTail` is only a total bookkeeping stream with a dummy zero interval
before guard success. That prefix is never claimed to be an evaluator success or
an expression value. `eval_converges_encloses` reuses `eval_sound` to enclose
**every defined actual value** at each successful same-index box. It does not
claim all points of the output interval occur, or that unrelated term witnesses
may be combined.

Input containment is deliberately separate. Converging point intervals
`[1/(n+1),1/(n+1)]` converge to zero but never contain zero. To certify error
relative to the limit value `z`, `eventual_accuracy` additionally requires
`∀ n, (X n).Contains x` and `∀ n, (Y n).Contains y`. Under these premises, for
any real ε>0, eventually every point `w` in the successful result satisfies
`|w-z|<ε`, and the result contains `z`.

## Effective corollary: what follows and what does not

`precisionTest q` is an executable exact-rational test: it rejects `none`, and
accepts `some I` exactly when `I.hi-I.lo < q`. `eventually_precision` and
`exists_precision` prove eventual and existential acceptance for positive rational
`q`. `precision_sound` certifies every point of a passed interval against any
actual enclosed value. Equal width is rejected (the inequality is strict).

`firstPrecision` uses mathlib's computable `Nat.find` over this decidable test,
with the proved existence as its termination witness. `firstPrecision_passes`
and `firstPrecision_certificate` prove that the selected stage succeeds and,
with input containment, gives the requested error certificate. It searches the
existing evaluator; no alternate arithmetic or heuristic success condition is
introduced. The theorem supplies termination for the specified input class,
not a rate or a cost bound.

For executable use the caller must supply **total executable interval streams**
and a **positive rational tolerance**. The proofs do not construct such streams
for arbitrary real inputs, and an arbitrary real ε is not automatically a
computable tolerance representation. A supplied rational `0<q≤ε` suffices.
An a priori stage bound would additionally require quantitative input convergence
information and control of intermediate values/denominator separation (or a
verified adaptive discovery procedure); none is assumed here. Fixed-precision
outward rounding may prevent widths from approaching zero, so a merely sound
hardware/backend contract cannot inherit this theorem. No new FP assumption,
C/FFI code, deployed default, timing result or hardware test is included.

## Controls and remaining Chapter 2 gap

[The kernel-checked fixtures](tests/ExpressionStreams.lean) cover all arithmetic
constructors, nested division initially rejected and eventually accurate, shared
`x-x`, strict width boundaries, and the noncontainment example above. Intervals
around zero converge to zero yet `1/x` is rejected at every stage; the limit has
no strict semantic value. There are nevertheless defined nonzero inputs in every
such box, so rejection is not nowhere-definedness. `0*(1/x)` remains undefined
at zero and rejected: zero multiplication does not erase strict partiality.
A constant-expression search is proved to select stage zero.

This closes finite **rational arithmetic** expression convergence, not the
source's entire operator inventory, all representation constructions, stream
nesting preservation, exceptional values or §2.12 property-tracking issue.
[The consolidated source audit](CHAPTER2_SOURCE_AUDIT.md) retains those gaps.
This leaf belongs with the existing partial-function/property review unit; it
requires no extra stacked PR or native integration.

## Executability qualification

The existing `firstPrecision` definition actually compiles: its generated C
contains the specialized `Nat.find`/well-founded search and exported wrapper.
The opt-in [check script](experiments/accuracy_search/check.sh) compiles that
module's generated C and the client C to object files, then runs the actual
wrapper through `lake env lean --run`. These are distinct checks: this is **not**
a claim that a standalone native executable was linked, nor a verification of
the Lean compiler, rational implementation or host machine.

The [audited example](AccuracySearchExample.lean) supplies the computable nested
stream `[0,2]` at stages 0 and 1, then `[1,1]`, for `1/(x/2)` at the real limit
`x=1`. Endpoint containment of 1, convergence, strict value 2, and the returned
stage's error certificate are kernel-proved. The compiled run observes rejection
at stages 0 and 1, selection of stage 2, and bounds `[2,2]` at tolerance `1/100`.
The exact observed index is execution evidence, while termination, successful
acceptance and enclosure follow from the general kernel proofs. The fixture also
proves the rejected prefix from existing evaluator soundness.

`tests/test_accuracy_execution.py` reruns the compiler/execution check in the
full local gate. This qualifies the original wrapper; there is no replacement
search, bounded-success surrogate, extra backend or shipping/default change.
Reproduce with pinned Lean tools on PATH:
`bash experiments/accuracy_search/check.sh`.

The computability obligation is not expressed by `Converges`: an arbitrary
mathematical `ℕ → QInterval` may be noncomputable. Actual execution must supply
compiled total stream programs (as the example does). The semantic obligations
remain convergence, strict definedness at the limit and positive rational query;
endpoint containment of those limit inputs is additionally required to certify
accuracy against their value. These obligations do not give a rate and do not
construct arbitrary real representations.
