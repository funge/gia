# §2.15 page-and-claim ledger

This ledger separates descriptions, mathematical claims and algorithmic claims.
Original PDF images were rechecked at printed pp.40–43 / PDF pp.56–59. The local
Markdown omits §§2.15.4–8; it is not the authority for those subsections. Links
below use the author's [original thesis](https://www.dgp.toronto.edu/~mooncake/thesis.pdf).
Chapter 2 is not declared complete.

| Source and printed/PDF page | Actual claim and kind | Evidence and residual obligation |
| --- | --- | --- |
| §2.15 introduction, [40/56](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=56) | Survey of discrete representations; some lead to mechanical algorithms. Readers interested only in intervals may skip the survey. | Expository scope, not a theorem that every described representation has an implemented algorithm. |
| §2.15.1, 40–41/56–57 | Nonnegative rational downward cuts represent nonnegative reals by their least upper bound; the improper whole cut represents infinity. Operations are pointwise rational operations. Extending multiplication naively to negative cuts fails. | [CutArithmetic](CutArithmetic.lean) and the existing cut correspondence give decoded order, nonnegative addition/multiplication and representative independence under explicit LUB/nonempty premises. Strict/closed cuts and improper cases remain distinct. A complete signed-cut multiplication construction is **not supplied or asserted** by this passage; it cites other literature. Do not list that optional construction as an unqualified Chapter 2 theorem. The source warning is checked by `negative_product_not_cut` in [CutArithmetic fixtures](tests/CutArithmetic.lean). |
| §2.15.2, [41/57](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=57) | Convergent rational sequences; termwise operations must be independent of representative; no convergence rate is guaranteed. | [SequenceRepresentations](SequenceRepresentations.lean) connects the actual Cauchy quotient and continuous operations, with eventual nonzero division. Delay/zero-limit controls are checked. A generic arbitrary operation does not inherit continuity or definedness. No uniform rate follows. |
| §2.15.3, 41/57 | Base-b digits, infinite sum, floating place/sign for all reals, duplicate terminating/repeating form, uniqueness after preferring zero tails; addition of sums followed by carrying. | [DigitRepresentations](DigitRepresentations.lean) proves sum semantics, truncation and the duplicate identity. [DigitExtraction](DigitExtraction.lean) now constructs and reconstructs every ordinary canonical fractional stream for b≥2, with uniqueness and an all-real integer-part representation. The explicit canonical condition excludes eventually maximal tails. It proves no computable arbitrary-real digit oracle and no online carry algorithm. Arbitrary place/sign encodings need a separate normalization convention for structural uniqueness; integer-part normalization is stated explicitly. |
| §2.15.4, [42/58](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=58) | Positive simple continued fractions, integral head and positive tail terms, last finite term ≥2, unique representation; finite iff rational; Euclidean extraction. | [ContinuedFractionConversion](ContinuedFractionConversion.lean) proves finite rational extraction, arbitrary-prefix terminal-1 rewrite and normalized finite reconstruction, canonical irrational convergence and injectivity using the actual pinned mathlib `of`. [InfiniteSimpleCF](InfiniteSimpleCF.lean) now proves arbitrary admissible infinite-stream existence, canonical recovery, irrationality and uniqueness. It first proves suffix convergence by two-step contraction, then recovers the actual canonical expansion before reusing `of_convergence`. Generalized numerators are not this displayed simple-fraction claim. |
| §2.15.5, 42–43/58–59 | Nested rational interval streams; supported operations converge when the expression defines a real; division may delay until zero is excluded. Finite expressions permit computable accuracy search. Finite computation cannot extract arbitrary first digits/CF terms. | [ExpressionStreams](ExpressionStreams.lean) and [AccuracySearchExample](AccuracySearchExample.lean) prove defined-limit finite arithmetic convergence and certified sequential/bounded search under computable containing streams. Supported grammar is explicit. A formal impossibility theorem for arbitrary digit extraction needs a specified information/computation model and is not yet proved. Continuity failure alone must not be called such a theorem. Chapter 3 operator coverage and infinite-bound online behavior remain separate. |
| §2.15.6, [43/59](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=59) | Signed digit alphabet −b<d<b; hardware motivation; online outputs use only k+1+d input digits, with small-delay circuit references. | [DigitRepresentations](DigitRepresentations.lean) proves signed sum semantics and quantitative truncation. These do not establish an online carry algorithm, finite delay for a specified operation, or circuit performance. Source refers to external implementations; algorithm correspondence remains a separately specified task. |
| §2.15.7, 43/59 | Redundant continued fractions have the displayed absolute-value, adjacent-sign and last-term restrictions; permit negatives; interval Euclidean extraction. | [RedundantCF](RedundantCF.lean) proves convergence and unique value for every printed-admissible infinite signed stream, nonzero finite/limit suffix divisors, recurrence, negation and a derived error bound. Positive overlap recovers the ordinary canonical expansion. Finite nonuniqueness and a terminal-zero syntax limitation are checked. General signed extraction/coverage, signed irrationality and canonical digit recovery are not proved; no algorithm or unspecified finite definedness is guessed. See [scope](REDUNDANT_CF.md). |
| §2.15.8, 43/59 | GIA may improve convergence over constant intervals; symbolic intervals give immediate but unproductive convergence; functional dependence supports later graphing algorithms. | Existing same-witness family/symbolic descriptions and enclosure results support the framework. No uniform strict convergence improvement is asserted by the source or proved here. Concrete quantitative advantage belongs to specified operations; later graphing/runtime claims are not Chapter 2 representation theorems. |

## Selected proof and why

The explicit missing canonical ordinary-digit construction/uniqueness claim is
closed in this milestone, using existing digit sums and mathlib floor/fract.
It is a substantive converse: every admissible canonical stream is recovered
from its value, not merely that the extraction routine is injective. The next [infinite simple-fraction milestone](INFINITE_SIMPLE_CF.md) now closes
the actual arbitrary-stream converse by proving suffix convergence and recovery;
it does not weaken the obligation to another canonical example. Redundant
fractions now have full printed-infinite-class convergence; extraction/coverage and finite definedness remain separate tasks.

## Family claims after this review

§2.13.1 (printed p.39 / PDF p.55) gives mathematical interval-set membership,
inclusion, and perfect demotion descriptions, while explicitly warning that
finite descriptions may be unmanageable. It does not prescribe a terminating
arbitrary nonlinear branch solver. [Finite branch projection](MONOTONE_UNIONS.md)
and [fractional elimination](FRACTIONAL_PROJECTION.md) are useful constructive
subclasses, not a reason to make optional general solver engineering the chapter
finish line. Remaining family work must identify an exact source clause and its
mathematical premises; source ambiguities and unspecified exceptional rules
remain separately marked in the [closeout matrix](CHAPTER2_CLOSEOUT.md).
