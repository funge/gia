# Chapter 2: what is proved and what needs qualification

We have finished the scoped Chapter 2 formalization. Lean checks the mathematical
results listed in the [section-by-section checklist](CHAPTER2_CHECKLIST.md),
including the conditions under which they hold. This does **not** mean that every
sentence in the thesis is true as printed, or that every representation has
code that converts it to another representation. Some printed examples disagree
with the definitions;
other claims depend on how they are read. Those limits are part of this closeout.

The checklist was checked against printed pp.13–43, including the formulas in
the PDF. It is the main source-to-Lean map. The older
[source audit](CHAPTER2_SOURCE_AUDIT.md) records earlier checks and is retained
for reference.

## Apparent errors and claims that need qualification

The first two bullets are literal disagreements between printed definitions or
examples. The other three fail under the stated reading; they are not claims
that every possible interpretation of the source is false.

- **The two floating-point format definitions disagree.** In
  [§2.5, pp.18–19](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=34),
  the digit form admits `b^M` at the maximum exponent, but every value in the
  literal coefficient form is smaller. Lean proves this in
  [FormatNormalization.upper_digit_witness](FormatNormalization.lean).
  The [separately labeled repair](FORMAT_DIGITS.md) is not attributed to Tupper.
- **The decimal rounding examples do not all follow the printed format.** In
  [§§2.5.3–2.5.4, pp.20–21](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=36),
  upward rounding of 1001 is printed as 1010; the literal coefficient definition
  gives 1100. The printed downward reassociation result is 10000; the checked
  computation gives 0. See
  [SourceRoundedAlgebra.literal_up_not_printed and printed_reassociation](SourceRoundedAlgebra.lean)
  and the [comparison table](SOURCE_ROUNDED_ALGEBRA.md). Changing to the repaired
  format does not make all the printed rows agree.
- **The affine containment claim fails if containment must hold at the same parameter.**
  In [§2.9.3, p.29](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=45),
  the forward-or-reverse claim misses a family such as `[t/4, 1−t/4]` on `[0,1]`.
  Its total range is `[0,1]`, but it contains neither orientation pointwise.
  [LinearFamilyEquality](LinearFamilyEquality.lean) proves the counterexample
  and a corrected alternative allowing a full endpoint fiber. The
  [scope note](LINEAR_FAMILY_EQUALITY.md) distinguishes pointwise containment
  from containment of total ranges.
- **The weak-tracking implication fails when read as semantic continuity.** In
  [§2.12, pp.36–37](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=52),
  continuity of a composite does not force continuity of its children: squaring
  a jump between −1 and 1 gives the constant 1. The
  [checked counterexamples](tests/PropertyComposition.lean) refute that reading.
  [Sufficient tracking certificates](TRACKING_CERTIFICATES.md) remain sound;
  they are not a claim to have resolved the author's intended meaning.
- **Exact interval subdistributivity does not carry over unchanged to staged rounding.**
  For the floating-interval reading of
  [§2.7.5, p.25](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=41),
  [RoundedIntervalControl.staged](RoundedIntervalControl.lean) gives
  `I·(J+K) = [200,220]` but `I·J+I·K = [200,210]`, with least outward rounding
  at every stage. Here `I=[2,2]`, `J=[100,100]`, `K=[1,1]` in the literal decimal
  format. Both contain the true result 202. The
  [exact rational interval law](IntervalAlgebra.lean) is still valid.

## What conversion code means

A converter is code that changes how a set of values is represented. For example,
closed bounds `[0,1]` plus the condition `0 < x < 1` preserve the original open
interval `(0,1)`; using the closed bounds alone would add its two endpoints.

GIA proves what a conversion must preserve and can supply executable reference
code for supported cases. Not every general theorem needs an implementation for
every case. relgraph needs production code only for conversions its renderer
actually uses; it has no runtime dependency on GIA. Universal conversion is not
required for this Chapter 2 milestone.

## What the proofs cover

| Area | What is checked |
| --- | --- |
| Mathematical foundations | Integer, rational, real, complex and positive-infinitesimal constructions reuse pinned mathlib, with explicit correspondence theorems. |
| Bounds and domains | Least interval hulls of actual output sets; inclusion and demotion with a shared witness; finite comparisons and Boolean composition; strict partial-operation domains; guarded value/domain conversion. General proofs do not automatically supply code for every conversion. |
| Number representations | Finite formats and the repaired binary64 correspondence; finite affine, quadratic and Hansen families; unbounded sets of finite coefficient choices; cuts, rational sequences, radix digits, and simple/signed continued fractions. Each proof states its supported class. |
| Families and sets | Finite family/set representations preserve the stated parameter and coefficient choices. Exact representations are distinguished from enclosures that lose information. |
| Accuracy | Stream arithmetic, convergence and search are proved for the supported strict finite arithmetic grammar. Later operators need their own proofs. |
| Symbolic composition | The [sine/root trace](SYMBOLIC_TRACE.md) proves the printed composition, its partial domain, pointwise singleton bounds and the corresponding projected image. The image remains an unevaluated set, not a computed numerical range. |

The [FloatingDigits proof](FloatingDigits.lean) covers every real and every radix
at least two. Its uniqueness theorem uses canonical fractional digits and an
explicit half-open mantissa convention `[1/b,1)`, with zero handled separately.
The source's zero-tail condition alone does not fix the scale.

## The §2.9.4 follow-up: constant embedding

A later source/Lean review found that the generic constant-embedding theorem
was missing, even though concrete constant operations were already proved.
[ConstantExtension](CONSTANT_EXTENSION.md) now closes that conditional gap.
It derives preservation of constants from sufficient inequalities on demotion,
then proves that constant embedding commutes with interval extension for
partial real operations of any finite arity.

Constructed infimum/supremum demoters satisfy those conditions. Merely rounding
outward does not suffice: a checked counterexample shows why. Each concrete
affine or machine demoter must still prove its own compatibility. The same
review confirms existing finite-real multiparameter denotation and the scoped
positive-infinity addition rule; it does not add missing exceptional cases.

## What the source leaves unsettled

These are specification or interpretation limits, separate from the apparent
errors above:

- **Exceptional values.** [ExceptionalComparisons](ExceptionalComparisons.lean)
  and [TaggedConversion](TaggedConversion.lean) cover the justified tagged cases
  and state conversion conditions. They do not supply a complete arithmetic
  table for infinities and λ. Unspecified rows are not filled in from IEEE.
- **Weak tracking.** [FiniteProperties](FiniteProperties.lean) and
  [TrackingCertificates](TrackingCertificates.lean) prove strict-domain rules
  and sufficient certificates. The alternative readings and counterexamples
  remain explicit; failure of a certificate is not a proof that a property fails.
- **Algorithms not supplied by the chapter.** General nonlinear elimination,
  automatic bumpy-function classification, arbitrary optimal demoters, and
  unspecified online or interval-Euclidean extraction algorithms are not proved
  merely because the chapter describes related representations. Nor does the
  symbolic ellipsis provide an algorithm for every operation.

## Where this leaves Chapter 2

The scoped milestone is complete **with the qualifications above**. We currently
know of no further clearly stated, feasible proof obligation inside that scope.
That assessment is open to correction: the §2.9.4 follow-up shows why the
[checklist and proof links](CHAPTER2_CHECKLIST.md) matter more than a blanket
claim that the chapter is done.

In plain terms: the supported mathematics is checked, apparent printed errors
have counterexamples, and unresolved meanings are labeled rather than guessed.
This is not a complete exceptional-value calculus, a numerical symbolic solver,
or verification of a native implementation. Later-chapter operator proofs and
implementation work remain separate tasks.
