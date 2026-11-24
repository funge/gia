# Finite descriptions, guards, and cut conventions

Original pages checked: Tupper §2.13.1 [printed p.39 / PDF p.55](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=55),
and §§2.14–2.15.1 [printed p.40 / PDF p.56](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=56).
The first gives an infinite guarded-point construction and discusses finite
machine-family descriptions. The second varies coefficient types, then describes
nonnegative rational cuts. Neither page supplies a complete grammar/encoding
and construction theorem for every permissible value/domain guard.

## What can be proved about a genuinely finite input

[FinitePointDescriptions.lean](FinitePointDescriptions.lean) makes one explicit,
source-grounded language precise: a finite table of rows, each containing a
`Vector Rat n` of parameter coordinates and one rational value. These are finite
rational data, not arbitrary real functions or predicates. Each row uses the
already proved polynomial zero-distance guard and an equal lower/upper value.
`point_guard` and `table_denotation` prove its correspondence to existing point
and set semantics. This is a finite sublanguage of the source point construction,
not a claim that all source interval pieces must be points.

`representable_iff` proves exact table representability iff the relation's graph
is finite AND every graph point belongs to the decoder's image. The latter means
all parameter coordinates and the value are rational. `function_representable_iff`
replaces finite graph with finite defined domain for an actual partial function.
The converse is a classical mathematical existence proof; it does not extract a
table from an arbitrary oracle function. Supplied tables have explicit finite
data. No native or binary64 encoder is being claimed.

Controls show why both requirements matter:

- even the everywhere-zero function cannot have a finite **point-table** graph;
  one constant interval piece can describe it, so this is not an impossibility
  theorem for general finite interval pieces;
- a singleton with value sqrt(2) is finite but not rationally coded (using the
  pinned mathlib irrationality theorem);
- conflicting rows at one coordinate define a relation, not a partial function;
- an empty table and absent coordinate/value pairs retain empty membership.

`single_arbitrary_guard` contrasts this with an unconstrained semantic guard:
one piece `{z | p∈A and z=0}` can hide ANY set A. Calling that one piece a finite
syntactic description would assume the missing finite description of A. We do
not use arbitrary predicates to close the source's broader finite-description
claim. §2.14's heterogeneous coefficient variants likewise do not specify that
missing general guard grammar.

## Proceeding to a clear §2.15 correspondence

[DedekindBoundary.lean](DedekindBoundary.lean) proves that every nonempty proper
downward-closed nonnegative rational cut has a nonnegative real least upper bound.
Properness supplies a missing rational upper bound; density of rationals proves
that the principal strict and closed cuts of a positive real have exactly that
real as their supremum. These two cuts are different at positive rational
boundaries. They are extensionally equivalent **after decoding**, not equal sets;
we preserve both and do not silently impose a canonical boundary convention.

At zero, the strict nonnegative cut is empty and the closed cut is {0}. The empty
set has no least upper bound in all of Real, despite the library's totalized
`sSup empty = 0`. In a nonnegative ambient order there is a bottom element; this
is an ambient-order distinction, not a claimed contradiction in Tupper. The
fixtures also show that the improper whole nonnegative rational cut is unbounded
and that downward closure is a real obligation, not a consequence of naming a set.
The subsequent [cut arithmetic result](CUT_ARITHMETIC.md) proves nonnegative
addition/multiplication inheritance and the source negative-product warning; a
full signed construction remains outside this model.

## Review and finish-line status

The finite point-table iff belongs to existing review unit 3. The cut
correspondence is a small independent foundational leaf in unit 2. There is no
new branch or additional planned PR. [Point-table fixtures](tests/FinitePointDescriptions.lean)
and [cut fixtures](tests/DedekindBoundary.lean) participate in the full gate.

Now checked: precise finite rational point-code representability and §2.15.1's
proper/nonempty nonnegative-cut supremum correspondence, with boundary controls.
Still open: a source-wide finite guard/piece language and constructive demotion,
heterogeneous/open endpoint variants, full exceptional carriers, signed cut construction,
other §2.15 representations, and the previously documented tracking ambiguity.
This work introduces no new FP assumption, runtime path or source interpretation
as an axiom. Run the pinned `./check.sh` for combined validation.
