# First-digit limitation for plain interval names

Tupper §2.15.5, printed pp.42–43 / [PDF pp.58–59](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=58),
contrasts finite-accuracy computation from converging intervals with extracting
the first decimal digit or the first ordinary continued-fraction term. Both
original page images were checked. This milestone gives a precise, deliberately
narrow finite-query interpretation of that negative claim. It is not a theorem
about all conceivable encodings of real numbers.

## Names and reader

[FiniteQuery](FiniteQuery.lean) reuses `QInterval` and
`ExpressionStreams.Converges`. A valid name is a stream of ordered rational
closed intervals, nested at successive indices, each containing the represented
real, whose lower and upper endpoints both converge to that real. Singleton
suffixes are allowed. No uniform convergence rate is assumed for arbitrary names.

A `Machine S` has a fixed initial state and a deterministic step that either
halts with an integer or requests an index and receives **only** that rational
interval. Requests may be adaptive, repeated or out of order. The step and state
are otherwise unrestricted; the lower bound does not rely on a particular
instruction set. `run` executes a finite number of transitions; `queries` records
the actual trace. `bound_is_trace_max` proves `queriedBound` is its maximum
(with 0 as the empty-trace default). `run_agrees` proves output agreement from
agreement through that maximum, by induction through the actual reply-dependent
states. Thus finite observation equivalence is proved, not imposed as an axiom.
Different names may require different runtimes; no global query bound is used.

The machine cannot inspect a name's program text, identity, rate certificate,
representation tag or represented value. Its fixed initial state does not carry
name-specific extra information. A computation with internal nontermination
is not made total by this model: the obstruction concerns finite halting runs.
The arbitrary abstract transition functions include computable transitions;
no claim of a formal simulation theorem for every external programming language
is made.

## Constructive indistinguishability

For rational boundary `q`, the name `straddle q` has radius
`r(n) = (1/2)^(n+5)` and interval `[q-r(n),q+r(n)]`. For any finite trace maximum
`N`, the second name `splice q N` agrees at **every** index at most `N`, then
becomes the constant singleton `q-r(N)/2`. Both are explicit executable rational
programs. `straddle_valid` and `splice_valid` prove containment, nesting and
endpoint convergence, including the transition from the retained prefix to the
singleton. The second name denotes a strictly smaller rational value.

`splice_indistinguishable` proves identical finite outputs. More strongly,
`boundary_counterexample` shows every finite answer is wrong either on the
boundary name or on one of these explicit splices, whenever the specified target
has different values there. It needs no correctness premise about arbitrary
noncomputable names. The usual no-total-correct-reader result follows as well.

For decimals the boundary is `1/10`; the target is the **existing canonical**
`DigitExtraction.digits 10 x 0`, preferring the zero-tail representation.
It equals 1 at the boundary and 0 at every constructed lower value, all in
`[0,1)`. This does not use the alternative repeating-9 expansion.
`decimal_cannot_halt` and `no_total_decimal_reader` state the obstruction.

For ordinary simple continued fractions the boundary is 1. The actual mathlib
canonical head is the cast of `floor x` (`cf_head`); it is 1 at the boundary and
0 at every constructed positive lower value. `cf_cannot_halt` and
`no_total_cf_reader` use precisely this target, not a claimed extraction of an
arbitrary noncanonical presentation.

## Positive and negative controls

`floor_certificate` proves a sufficient condition: if a containing interval,
after nonnegative scaling, lies wholly in `[z,z+1)`, its represented value has
floor `z`. It is a proof-side certificate, not a new runtime search algorithm.
The strict upper boundary matters; an interval touching the next digit boundary
cannot use this certificate for the preceding digit.

[Fixtures](tests/FiniteQuery.lean) exercise a reply-dependent reader with actual
trace `[4,0,4]`, the maximum 4, both runs returning `some 1`, and the second
name's canonical digit 0. Its exact singleton is `507/5120`. They also check
zero fuel, no-query output, the prefix/suffix boundary, both names' validity,
the continued-fraction head and an interior positive certificate. Executable
observations are checked alongside kernel proofs, not substituted for them.

## Scope and remaining work

This closes the finite-observation obstruction **for plain nested interval
oracles and canonical targets**. It does not exclude successful extraction on
names with extra tags, exact symbolic values or enriched information, or from
particular intervals already within one digit cell. It says nothing negative
about redundant digit output. It does not implement a Turing-machine model,
prove a uniform resource bound, or change the hardware backend.

The [section ledger](SECTION215_LEDGER.md) now records this exact interpretation
instead of leaving the computation model unspecified. Remaining survey work
includes signed continued-fraction coverage/extraction and specified online
algorithms; §2.15.8's qualitative GIA benefits are not a universal rate claim.
The [closeout matrix](CHAPTER2_CLOSEOUT.md) still marks Chapter 2 incomplete.

Run the full `./check.sh`, or the focused `lake build FiniteQuery` followed by
`lake env lean tests/FiniteQuery.lean`. No axioms, floating-point premises,
native code, production defaults or dependencies are added.
