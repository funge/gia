# Exact rational continued-fraction conversion

Source: Tupper §2.15.4, printed p.42 / [PDF p.58](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=58).
The original page image was checked: it displays the nested simple fraction,
nonnegative initial coefficient, positive intermediate coefficients and final
coefficient at least 2 for a nontrivial finite expansion. It states finite iff
rational, Euclidean construction and uniqueness with the final-term convention.
The repository Markdown omits this subsection; it was not used to infer formulas.

## Actual construction and conversion

[ContinuedFractionConversion.lean](ContinuedFractionConversion.lean) imports the
pinned mathlib continued-fraction construction. `GenContFract.of` uses integer
floor, fractional part and reciprocal to compute the stream; `convs` evaluates
its convergents through continuants. We do not introduce a duplicate evaluator.

For a rational q, set N = abs(num(fract(q))) + 1. `stream_stopped` proves the
actual intermediate stream is absent at N. It reuses mathlib's decreasing
fractional numerator bound and its nonnegativity theorem; it does not assume
termination or choose an uncomputable stopping index. `recover q` evaluates the
constructed convergent at N−1. `recover_exact` reuses mathlib's terminating
correctness theorem to prove recover(q)=q. `real_recovery` preserves that result
when cast to the reals. N is conservative, not claimed minimal or efficient.

`finite_iff_rational` specializes the existing pinned mathlib theorem to real
inputs: the constructed expansion terminates iff the value is a rational cast.
`promote` proves that converting the rational head and every coefficient pair
to reals gives exactly the expansion constructed from the real cast, not just
the same final value. `eventually_exact` records stability of convergents after
termination. These are explicit reuse/correspondence results; the underlying
continued-fraction algorithms and proofs are mathlib's, not newly invented here.

The rational `recover` definition is executable: the fixture's Lean `#eval`
returns 43/19. This is proof-side representation work, not a rational substitute
for hardware interval arithmetic. Real expansion is noncomputable through the
real floor instance. No native backend or executable hot path is modified.

## Controls and exact limits

[Fixtures](tests/ContinuedFractionConversion.lean) kernel-check rational recovery,
zero and integer stopping, a signed rational extension, a non-exact early
convergent, and nontermination from an explicit irrationality premise. Lean
runtime evaluation is separate evidence from those proofs; no `native_decide`
or additional axiom is used. A trailing-one arithmetic identity illustrates why
normalization matters, but is not claimed to prove a list normalization theorem.

The source discusses positive reals; the general mathlib conversion also handles
zero and negative rationals, labeled boundary/extension controls. The imported
simple-fraction stream is an actual construction. The continuation below proves
its last-term convention and uniqueness among constructed rational expansions.
The finite integral converse and uniqueness are now proved below. Arbitrary
malformed lists and infinite presentations remain outside that theorem. Nor does termination iff rational assert that a
finite truncation of an irrational expansion is exact. Infinite convergence,
redundant continued fractions (§2.15.7), arithmetic algorithms on presentations,
and performance claims remain outside this package. There is no unspecified
exceptional-value or IEEE operation added to make the conversion work.

Pinned sources (mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b):
`Algebra/ContinuedFractions/Computation/Basic.lean`,
`CorrectnessTerminating.lean`, and `TerminatesIffRat.lean`.
These retain mathlib's own attribution/license in the dependency; no source is
copied into the project. Review this with representation unit 2, not as another
stacked public PR.

## Constructed canonical form and the terminal-1 ambiguity

The same printed p.42 definition requires the LAST non-initial coefficient to
be at least 2, while interior coefficients may be 1. Its uniqueness assertion
quantifies over represented expansions, not only outputs of a chosen algorithm.
We therefore separate the following checked construction properties from that
stronger completeness/uniqueness assertion.

- `terminal_coefficient` proves that a live non-initial integer/fraction stream
  entry followed by termination has integer coefficient at least 2. Termination
  forces its fractional part to zero; the entry came from inverting a previous
  fractional part strictly between zero and one, so its integral value is >1.
- `final_pair_ge_two` transports that fact to the public `GenContFract.of q`
  sequence of coefficient pairs. `one_not_terminal` permits internal 1 but
  forbids a terminating non-initial 1. No restriction is imposed on an integer
  head-only expansion; in particular the value 1 remains admissible.
- `constructed_injective` proves `of q = of r ↔ q = r` for rationals, using
  termination and existing exact-convergent correctness. This is injectivity
  of the actual construction, not uniqueness among all source-admissible lists.
- `finitePresentation` merely packages a finite list into mathlib's existing
  `GenContFract` with unit partial numerators; it has no separate evaluator.
  `terminal_one_contraction` proves `[a;b,1]` and `[a;b+1]` evaluate equally via
  the library's `convs'`. The hypothesis b≥1 records the positive source tail
  domain; the library's totalized algebraic identity itself needs no stronger
  premise. This was initially a local contraction; the arbitrary-prefix extension is now
  proved below.

The end-to-end control compares two distinct actual representations `[1;1,1]`
and `[1;2]`, proves both evaluate to `recover(3/2)`, and separately checks that
the constructed expansion has stored pair (1,2). It also proves that recovering
q and reconstructing preserves the constructed expansion. Earlier zero,
integer, signed and early-truncation controls remain active.

The initial finite-prefix/converse gap is closed by the continuation below for
integral simple presentations. Infinite normalized presentation equality remains
a separate obligation. We do not claim the
local ambiguity is the only possible duplicate among unrestricted generalized
continued fractions, whose partial numerators need not all be one. No arbitrary
exceptional/undefined tail semantics is invented here.

## Finite normalization finished: prefix rewrite, converse, uniqueness

`finiteValue a bs` is just `finitePresentation a bs` evaluated by mathlib's
`convs'` at the full list length. Its nil/cons lemmas expose that same evaluator,
not an independent recursive interpretation. The prefix theorem proves

```
finiteValue a (pre ++ [b,1]) = finiteValue a (pre ++ [b+1]).
```

The algebraic identity holds even for unrestricted rational coefficients under
mathlib's total field operations. Its intended source application is narrower:
positive integral partial quotients. `positive_tail_value` proves every positive
integral tail decodes to at least 1, so all reciprocal denominators in valid
presentations are strictly positive; the proof is reusable at each suffix.
`contracted_normalized` proves that a positive integral prefix ending in b,1
with b≥1 contracts to a normalized tail ending in b+1≥2. No malformed-input
semantics is inferred from the unrestricted algebraic identity.

`Normalized` accepts an empty tail, requires each nonfinal coefficient ≥1, and
requires a nonempty tail's final coefficient ≥2. The head is an arbitrary
integer: imposing a≥0 recovers the source nonnegative-head convention, while
negative heads are an explicitly broader signed case. `normalized_tail_gt_one`
proves every nonempty normalized tail has value >1. Thus in a+b-tail-reciprocal,
the fractional part is strictly between zero and one, and the next floor and
reciprocal recover the supplied coefficient and remaining tail.

`reconstruct_normalized a bs hn` proves equality of the **entire actual library
representation**:

```
GenContFract.of (finiteValue a (bs.map Int.cast))
  = finitePresentation a (bs.map Int.cast).
```

The empty tail uses the integer constructor, not a spurious last-coefficient
restriction. The inductive step uses mathlib's `of_h_eq_floor`, `of_s_head` and
`of_s_succ` and the strict tail bound, so all coefficients and termination are
recovered. `integral_presentation_injective` recovers head/list equality from
representation equality. Consequently `normalized_unique` proves equality of
decoded normalized finite integral presentations iff their heads and lists agree.
This closes finite uniqueness for the stated convention, rather than only
injectivity of the chosen rational constructor.

Controls exercise [0;2,3,4,1]→[0;2,3,5], normalized reconstruction with internal 1,
the integer [1], [1;1,1] recomputing as [1;2], and rejection by the normalization
predicate of zero tails and terminal 1. Normalization rejection does not imply
absence of a rational value: the terminal-1 fixture is a valid but noncanonical
presentation. Infinite equality/convergence, nonunit partial numerators and an
executable malformed-list parser/normalizer are not claimed. This remains
proof-side mathematics with no new FP or runtime contract.

## Infinite canonical expansions and rational-stream conversion

Pinned mathlib `Computation/ApproximationCorollaries.lean` already proves
`GenContFract.of_convergence` and `of_convergence_epsilon` for the actual
canonical constructor. The real specialization uses the existing ordered,
Archimedean real field and topology. `canonical_converges` and
`canonical_accuracy` directly reuse these proofs, with named axiom audits;
there is no duplicate convergence argument or additional premise asserting it.

For an irrational real x, `irrational_infinite` reuses the rational-iff-termination
result. `irrational_entry_present` proves that every stored coefficient entry is
present. `irrational_no_exact_truncation` uses mathlib's theorem that each finite
convergent is rational: convergence is not finite equality. `canonical_injective`
uses uniqueness of real limits to prove `of x = of y ↔ x = y` for ALL real inputs,
not only rationals. This is uniqueness/recovery among canonical constructor
outputs, not completeness or uniqueness for arbitrary infinite coefficient streams.

The separate representation-conversion result reuses the existing §2.15.2
`SequenceRepresentations.Represents`. Each finite canonical convergent has a
rational witness; `rationalConvergent` selects that witness and
`rationalConvergent_cast` proves exact equality after casting to the reals.
`rational_stream_represents` proves this actual sequence represents x, and
`rational_stream_unique` proves it cannot represent a different limit. Rational
inputs are exactly equal to the input eventually. Thus canonical fractions
translate to the existing rational-stream semantics without merely assuming
that the chosen stream converges.

This conversion is deliberately noncomputable for arbitrary real x: classical
selection of rational witnesses is not an effective procedure for extracting
coefficients from an arbitrary real. No rate-computation or executable real
oracle is claimed. The imported epsilon theorem is a mathematical existence
statement. The preceding finite rational `recover` remains executable and is
not replaced. The positive-source convention is a restriction of the real-input
theorems; signed and zero inputs are explicitly supported by the reused mathlib
constructor.

Fixtures use sqrt(2) to check infinite coefficient availability, convergence and
nonexactness of every finite truncation; its converted stream cannot converge
to 2. An epsilon=1/1000 control and the eventually-exact rational zero boundary
are included. No floating-point execution or bit behavior is involved.

Remaining §2.15.4 gap: characterization/reconstruction and uniqueness for
ARBITRARY admissible infinite simple-coefficient streams, rather than those
already known to be constructor outputs. Generalized numerators, redundant
continued fractions (§2.15.7) and algorithms on those presentations remain
separate. Earlier references above to infinite uniqueness being open refer to
this arbitrary-stream claim; canonical-input convergence and injectivity are
now explicitly checked.

Pinned dependency proof references:
[canonical convergence and epsilon recovery](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean#L70),
[rationality of finite convergents and termination](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Algebra/ContinuedFractions/Computation/TerminatesIffRat.lean#L111).
These references match the dependency sources inspected and built locally.
