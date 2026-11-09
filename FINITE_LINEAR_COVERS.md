# Finite unions of linear enclosures

A single joined interval loses a useful fact about a discontinuous result:
its values may lie in separated ranges that both exclude zero. This milestone
adds a finite union of existing shared-parameter linear intervals, without
expanding expression syntax or replacing the existing domain contracts.

Tupper's [§2.13, Interval Sets](https://www.dgp.toronto.edu/~mooncake/thesis/node56.html)
uses membership in any constituent interval to describe richer ranges. The
implementation here is a bounded subset of that idea: finite lists, rational
linear bounds, and enclosure over the existing real parameter range [0,1].
Lists may contain duplicates and overlapping members; order has no semantic
significance for the enclosure contract. This is not a complete implementation
of the thesis's interval-set arithmetic or bumpy-function models.

`FiniteLinearCover.Covers R` says that each actual relational value at a unit
parameter is enclosed by some list member. The relation can be partial or
multivalued. This is deliberately only the enclosure part of soundness:
a nonempty list does not imply that any value exists. An empty list excludes
actual values only when its `Covers` proof has been established. There is no
conversion from interpreter failure to an empty list.

`cover_of_domain_sound` forgets only the domain clauses of an existing sound
partial enclosure; callers retain those clauses independently. `cover_guarded`
connects successful arithmetic evaluation and pointwise coordinate enclosure
to a singleton cover of actual `Value` semantics. `cover_select` reuses
`BranchSound` and `PiecewiseValues`: a certified decision keeps the chosen
cover; unknown appends both. Guards in this combinator are total predicates,
not automatically verified partial expression guards. It does not infer
continuity or branch-domain existence.

`cover_excludes_zero` proves absence of actual zero values when every member's
whole hull excludes zero. `recip?` traverses the list using the existing guarded
linear reciprocal; every component must succeed. `cover_recip_sound` encloses
the existing `QuotientValues` relation with numerator 1 and explicit nonzero
denominator. A component whose hull includes zero produces `none` (unknown),
even if a more precise domain could eliminate the offending values. A successful
empty traversal remains merely an empty enclosure, never a defined reciprocal.

The examples integrate arithmetic evaluation, branch selection, zero exclusion,
and reciprocal enclosure. A choice between -2 and 3 succeeds componentwise
where the joined hull's reciprocal fails. The parameter-dependent branches
`t - 2` and `t + 2` preserve linear dependence and exclude zero. Separate
semantic witnesses prove that these branches and their reciprocal actually
have values; enclosure alone is not used for that conclusion. Controls include
a zero-containing component returning unknown, a nonempty cover compatible
with no values, and the exact condition required for an empty cover.

The original finite-union layer introduced no floating-point assumptions,
continuity claims, maximal-domain claims, normalization, cartesian arithmetic,
or general finite-cover interpreter. The existing scalar interpreter and application build are unchanged.
A useful next integration would carry covers through the conditional evaluator,
with explicit resource bounds and the existing lazy definedness conditions;
this change does not silently replace its scalar return type.

## Multiplication of finite covers

CoverArithmetic adds `FiniteLinearCover.mul`: apply the existing LinearInterval.mul
to every pair of components, retaining the shared parameter. The output list has
exactly the product of the input lengths, including duplicate components. Empty
inputs produce empty output; this alone is not a statement about an actual domain.
The existing Covers contract proves enclosure of ProductValues. SoundOn proves
both domain directions with the existing DomainBounds.inter: both operands must
have an actual value at the same parameter. No fresh domain representation or
expression evaluator is introduced.

This is a finite sufficient model motivated by the thesis's
[interval-set inclusion and extension (§2.13.1)](https://www.dgp.toronto.edu/~mooncake/thesis/node57.html).
It composes existing component bounds rather than claiming optimal demotion or
full interval-set arithmetic. Input components may independently supply values;
list positions are not branch identifiers. Pairing only corresponding positions
would miss actual products. Conversely, sharing the parameter does not record
that two operands must choose the *same* relational witness. The full Cartesian
product can therefore overestimate a correlated expression.

The independent core-only CoverPipeline fixture exercises the distinction with
±1: all four pairs retain actual mixed products, while a zipped implementation
would lose -1. A correlated square cannot be negative, yet the product enclosure
contains -1. This is conservative loss of correlation, not a proof of existence
for that square. The parameter-dependent conditional/restriction/reciprocal
pipeline also composes through multiplication, preserves its midpoint domain
hole, excludes zero, exhibits an actual product of one at an endpoint, and
passes its SoundOn contract through the existing coalescing theorem.

Multiplication is total on real values. This step does not add partial binary
operations, new FP assumptions, conditional syntax, branch-domain inference or
continuity claims. The exact list-length formula is an output-size fact, not a
runtime or peak-memory guarantee. Existing coalescing/limit policies can be
applied after multiplication; they do not prevent intermediate Cartesian growth.

## Shared-witness squaring

`SquareValues R p z` chooses one actual x from R and requires z=x*x.
`FiniteLinearCover.square` maps each component I to I.mul I, reusing the existing
linear multiplication enclosure. Covers and SoundOn theorems preserve the input
domain exactly; multiplication of real values is total. A separate theorem
shows SquareValues agrees with ProductValues R R when R is single-valued.
For arbitrary multivalued relations they differ, so square must not replace an
independent product merely because its two cover lists are equal.

Each square component also appears in the Cartesian self-product. The output
has the same length as the input rather than its square. This avoids cross-
component combinations for this particular shared-witness operation, without
introducing a generic correlation algebra, branch identifiers, a new interval
primitive or evaluator rewrite. Component multiplication still overestimates:
this is not an optimal square enclosure or a claim that all represented bounds
are nonnegative. Empty covers and unknown reciprocal results retain their
existing meanings.

The fresh core client retains a hole through conditional interpretation,
restriction, squaring and guarded reciprocal, and proves an actual endpoint
value exists while excluding zero. For the multivalued ±1 relation, exact
squared semantics are proved to be {1} at every unit parameter, and the computed
cover has two exact-one components. The old Cartesian product has four pairs
and still encloses a genuine mixed -1; a regression proves the smaller square
cover is unsound for that independent-product relation.

The resource/precision control uses the existing coalescing operation. Squaring
first and then coalescing permits reciprocal certification. Coalescing the sign
alternatives first and then squaring produces an unknown reciprocal, despite
actual squares being one. The size facts do not bound time, intermediate memory
or rational bit complexity. This bounded unary case is consistent with the
thesis's interval-set extension/representation tradeoff (§2.13.1); it does not
solve general witness correlation or infer shared choices in an expression AST.
No additional FP assumptions or continuity claims are introduced.

## A proved limit of finite affine ranges

`finite_cover_bounded` proves that every finite list of these rational affine
components has uniform finite real lower and upper bounds on unit parameters.
`covered_relation_bounded` transfers that fact to every actual value of a covered
relation. `no_finite_cover_of_unbounded_below` rules out any such cover when actual
values occur below every proposed real lower bound. These are mathematical
limitations of the representation, not runtime limits or undefinedness claims.

The threshold fixture constructs actual values below each bound for
`if t<1/2 then 1/(t-1/2) else 0`. The conditional is defined everywhere, but it has
no finite affine cover either in the original parameter or after reparameterizing
the left cell. All witnesses lie strictly inside the active branch; the proof
never divides by zero at the boundary. Merely making the boundary open cannot
supply the missing bounded range. More finite components cannot do so either.
This makes concrete the distinction between finite practical descriptions and
ideal interval-set extensions discussed in thesis §2.13.1.

Not every inactive-pole failure has this cause. For
`if t<1/2 then (t-1/2)/(t-1/2) else 1`, the same checker returns unknown, but an
independent semantic proof constructs an exact-one finite cover. Cancellation is
justified only with the active branch's nonzero denominator proof. The contrast
separates genuine unbounded-range needs from a possible future guarded
simplification. No simplifier, open-cell representation, extended endpoint type,
infinite family, or additional FP assumption is introduced here.
