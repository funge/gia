# Split quotient semantics across zero

[SplitQuotient.lean](SplitQuotient.lean) fills a proof-side compositional gap:
retain both signs of a denominator instead of rejecting every interval that
crosses zero. It reuses `QuotientValues` and `Expr.Value`; there is no new AST,
evaluator, hardware primitive or floating-point assumption.

## What was already present

[LinearDivision](LINEAR_DIVISION.md) and [hardware quotient composition](HARDWARE_GUARDED_QUOTIENT.md)
require a denominator enclosure strictly separated from zero. The finite cover
reciprocal in [FiniteLinearCovers.lean](FiniteLinearCovers.lean) preserves separated
bounded components, but requires every component to satisfy that same guard.
[NonzeroDomains.lean](NonzeroDomains.lean) provides quotient-domain information,
not a range across a pole. The unboundedness controls in the existing cover work
correctly explain why no finite union of bounded real intervals can cover a
genuine pole. None of those representations or conclusions changes here.

## Exact split and enclosure

`sign_split` decomposes an existing partial quotient into negative and positive
denominator branches, and proves the reverse direction. Every branch retains
both operand witnesses, their same parameter, and the explicit nonzero condition.
Zero-only denominator relations have no quotient values (`zero_only_absent`).
`restrict_iff` preserves any external domain restriction, including holes.

For positive bound magnitudes `c,d`, an actual numerator `x ≥ a ≥ 0` and
denominator `-c ≤ y ≤ d`, `y ≠ 0`,
`quotient_rays` encloses the quotient in the real set

```text
(-∞, -a/c] ∪ [a/d, +∞).
```

The proof uses the negative or positive branch actually witnessed and does not
assume both branches are nonempty. Positive `c,d` keep the numerical ray-tip
divisions defined. The separate one-sided branch bounds cover zero-touching
domains without evaluating an absent side's tip at zero. Touching-zero coverage
is one-sided enclosure plus endpoint witnesses; separate one-sided exact-image
iff theorems are not included. The `rays` set contains
only real numbers; infinity is notation for unboundedness, not an endpoint value
assigned to any expression. For a useful nonempty gap, choose positive `a` as
well. With `a=0`, no central exclusion is promised.
`gap_exclusion` excludes only the strict central gap and retains the closed tips.

`expression_iff` connects the existing division constructor to the existing
partial quotient relation. `expression_rays` applies operand bounds to their
values in the same coordinate environment, including arbitrary nested partial
subexpressions. It never asserts that an enclosed expression has a value or
that every point in the enclosure is attainable. The generic relation theorem preserves the same parameter `p`; it does not
recover correlations already erased by a caller's existential projection.
Callers needing a common uncertain-input witness must include that witness in
`p` before composition. The expression bridge fixes both coordinates explicitly
and therefore supplies that guarantee for `Expr.Value`.

## Exact scalar image is a separate theorem

For the complete input interval with `l < 0 < u`, `reciprocal_image` proves

```text
(∃ x ∈ [l,u], x ≠ 0 and z = 1/x)
  ↔ z ≤ 1/l or 1/u ≤ z.
```

The reverse direction constructs `x=1/z`; neither ray includes zero. This is
an exact image theorem for that complete scalar domain, not for arbitrary
expression ranges or external restrictions.

The [fixtures](tests/SplitQuotient.lean) cover:

- `1/[-2,1]`: exact rays `(-∞,-1/2] ∪ [1,∞)` and both attained tips;
- exclusion of the nonzero closed window `[1/4,3/4]`, whereas every convex
  enclosure of the actual image contains `1/2`;
- negative and positive zero-touching domains, the singleton zero domain,
  external holes and an actual expression pole;
- an enclosure-versus-image falsifier: a denominator taking only `{-1,1}`
  yields only `{-1,1}` under reciprocal. Its ray enclosure contains 2,
  but its actual image does not.

These checks show additional deductive strength without a runtime or speed claim.

## Tupper correspondence and limits

The starting evidence is the existing source inventory's F10/C09 entries.
The original thesis PDF was visually checked at printed pp. 59–60 / PDF pp. 75–76:
[§3.2.14](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=75) splits reciprocal
`[-2,5]` into negative and positive pieces before taking the ordinary interval
hull, and gives a one-sided `[-2,0]` example. This work retains the split as a
union. It is a derived real-set refinement, not a claim that the ordinary hull
algorithm itself returns two intervals, nor a transcription of the thesis's
extended-real/undefined-value model. See also [the concordance](THESIS_CONCORDANCE.md).

The repository copy of the SIGGRAPH 2001 paper was visually checked at PDF p. 6:
[§11 Interval Sets](https://www.dgp.toronto.edu/papers/jtupper_SIGGRAPH2001.pdf#page=6)
and Figure 10(b) motivate retaining disconnected reciprocal results. That page
contains the floor interval-set pseudocode and the general union-cover discussion;
this milestone makes no line-by-line claim about a reciprocal pseudocode listing.
The paper's definedness/continuity flags and branch-cut identity are not formalized
by this module. It does not infer continuity across a pole.

The scope is nonnegative-numerator lower bounds and a semantic reciprocal image.
General signed-numerator range algorithms, normalization of unions, executable
endpoint encoding, propagation through a complete evaluator, and C/IEEE execution
remain outside this milestone. No bounded cover is widened or rewritten, and no
defined value is dropped to make a finite representation succeed.

Run `lake build SplitQuotient`, `lake env lean tests/SplitQuotient.lean` and
`./check.sh`. See [validation receipts](VALIDATION.md). Independent semantic review found no blocking defect. The proof has no
mathematical dependency on residue inference.
