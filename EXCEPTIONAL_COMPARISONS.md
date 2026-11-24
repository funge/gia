# Exceptional comparison observations: explicit source subset

Source: Tupper §§2.5.1–2, printed p.19 /
[PDF p.35](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=35).
The transcription was reread and the original page visually checked. It says
same-sign infinities are incomparable, explicitly makes +infinity < +infinity
and +infinity = +infinity false, and makes comparisons involving lambda false.
The final sentence also identifies both same-sign infinity pairs as exceptions
to trichotomy. This is not Lean's equality or a specification of IEEE instructions.

## What is implemented

[ExceptionalComparisons](ExceptionalComparisons.lean) is a proof-side partial
observation table for the five named predicates `<`, `≤`, `=`, `≥`, `>`. The carrier has
finite real payloads, two infinity tags and a lambda/undefined tag. Real payloads
idealize numeric meanings; this is neither the source's exact finite float set
nor raw binary64. No signed-zero, NaN-payload or signaling-status representation
is added. Real comparisons use classical decisions, not a native executable path.

| Inputs | `<`, `=` | `≤`, `≥`, `>` | Evidence class |
| --- | --- | --- | --- |
| Two finite payloads | Ordinary real meanings | Ordinary real meanings | Standard named predicates; exact finite idealization |
| Either input lambda | false | false | Explicit §2.5.2 rule for all five predicates |
| Same-sign infinity pair | false | false | `<`/`=` explicit/incomparability; others derived below |
| Mixed finite/infinity or opposite infinities | Unmodeled | Unmodeled | Directional completion not supplied by this slice |

### Explicit, derived and still unspecified

The original PDF pp.31, 35 and 37 (printed pp.15, 19 and 21) were rechecked
for this extension. §2.1 names five numerical predicates. §2.5.1 gives the
same-sign incomparability rule and displayed positive-infinity strict/equality
examples; §2.5.2 names both infinity signs as exceptions to trichotomy and makes
comparisons involving lambda false. These are **explicit** source obligations.

The **derived** rows use the ordinary predicate definitions: `a > b` is
`b < a`, `a ≤ b` is `(a < b) ∨ (a = b)`, and `a ≥ b` is `b ≤ a`.
These definitions are not quoted as additional equations printed on p.19.
`gt_converse`, `le_disjunction`, `ge_converse`, `equality_symmetric`, and
`ge_disjunction` prove these identities over every row in the partial table.
`observedOr` combines two available observations and propagates absence; it is
not another source three-valued logic. Thus the same-sign non-strict false rows
follow from the supported primitive observations and those predicate definitions,
not from identifying infinity tags with EReal order. No complement rule is used.
If a different non-strict exceptional predicate were intended, that would be a
different semantic choice, not something established by the printed examples.

**Still unspecified here:** mixed directions, their equality answers, general
exceptional arithmetic, and promotion of lambda. Trichotomy alone does not
choose a direction for a particular mixed pair. The sequence intuition in §2.6.3
and the ordered bound model are not silently substituted for a numerical table.
In particular, no numerical `≠` is added and no IEEE NaN rule is presumed.

`some false` is a specified false answer. `none` means this deliberately partial
table supplies no answer. It is not a lambda value, an empty domain or hardware
failure. The source does say nonexceptional pairs have an ordering; the missing
rows do **not** assert that those pairs are unordered in the source. This slice
leaves their directional completion unimplemented instead of silently importing
the whole EReal or IEEE table. The initial comparison slice had no arithmetic operators. The subsequent
[explicit arithmetic subset](EXCEPTIONAL_ARITHMETIC.md) adds only source-backed
rows and the exact finite real core in this same carrier.

Theorems prove all-five finite agreement, both lambda positions, both same-sign infinity
pairs, all unmodeled shapes, and exact characterization of true observations.
[Fixtures](tests/ExceptionalComparisons.lean) exercise these cases, failure of
ordinary trichotomy at a same-sign infinity, and the distinction between missing
and false observations.

## Precisely limited connection to existing bounds

`bound` is an explicit representation map to optional EReal: finite payloads map
to their embeddings, infinity tags to mathematical top/bottom, and lambda to no
bound. It is **not** claimed to be the source's full promotion or an arithmetic
homomorphism, and has no connection to the native decoder by assumption.

`strict_bound_agreement` requires both mapped bounds and an actual table answer.
Only under those premises does the observed strict comparison agree with the
mathematical strict order. Equality agrees on finite payloads; same-sign infinity
is a proved counterexample to extending equality agreement. Lean equality of
values and EReal equality remain reflexive. A false source equality observation
does not prove structural inequality.

`finite_interval_membership` connects the existing real-member interval to the
two negated finite strict comparisons. The finite restriction matters: lambda
passes both negated tests but has no bound interpretation. Neither this theorem
nor a false comparison is a general exceptional-value containment rule.

## Source refinement: numerical comparisons versus definedness

The original §2.1 printed p.15 / PDF p.31 explicitly lists the five numerical
comparison operators `<`, `≤`, `=`, `≥`, `>`. It omits `≠` even though the
preceding distinct-integers formula uses that symbol. This page was visually
checked after the initial subset milestone. Printed p.14 / PDF p.30 separately
uses `g(x) = lambda` for undefinedness and `g(x) ≠ lambda` for domain membership;
the parent source review also identifies reused definedness on pp.34 and 37.

Accordingly, §2.5.2 does not demonstrably specify a numerical `≠` table. Keep
sentinel/definedness tests distinct from the five named numerical comparisons.
There is no asserted contradiction and no reason to invent a numerical `≠`
operator from the prose. The earlier broad-versus-trichotomy reading was an
investigation question, now narrowed by the explicit five-operator list.

The original `<` and `=` observations remain unchanged. This unit
adds the three remaining named predicates on the same supported
shapes, with the exact explicit/derived distinction above. Mixed finite/infinite
cases stay deferred; no complement-based completion or FP assumption is introduced. The later explicit arithmetic
subset does not settle the remaining comparison rows. The bound
representation map remains separate from source promotion and IEEE behavior.

See the [design note](EXCEPTIONAL_VALUES_DESIGN.md),
[completion ledger](CHAPTER2_COMPLETION.md) and [concordance](THESIS_CONCORDANCE.md).

```sh
lake build ExceptionalComparisons
lake env lean tests/ExceptionalComparisons.lean
./check.sh
```

## Current qualification scope

`observation_available` characterizes exactly which input shapes have a supplied
answer, uniformly over all five operators. The true-result characterizations
for the three new operators retain finite witnesses and do not invent mixed
answers. `finite_nonstrict_bound` gives the finite EReal bridge, while fixtures
refute its extension to infinity and refute complement-based completion at lambda.
`NumberPromotion.rational_comparisons` reuses the exact rational promotion and
proves all five comparisons agree before and after the cast. This is not a claim
about rounding or exceptional promotion. Existing fixtures and observations are
preserved; added controls exercise finite equality boundaries, strict separation,
converse versus complement, every exceptional self-pair, and missing propagation.
