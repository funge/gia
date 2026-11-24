# Finite comparison and numeric-description package

This package combines [domain projections](DomainProjections.lean) with
[FiniteEquality](FiniteEquality.lean), building on the merged Boolean composition
and shared-parameter domain constraints (#32 and #33).

## Source and exact scope

Tupper §2.7.2 (printed p.24 / [PDF p.40](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=40))
prints overlapping equality as mixed and equal singleton equality as true.
The original page was visually checked, not inferred only from the transcription.
Our finite ordered rational endpoints are interpreted over real operands. The
comparison represents the exact set of outcomes of **independent** admitted
operands. The prior strict-order proof and projection package, plus reversed
operands, now cover <, >, ≤, ≥, = and ≠ within that scope. There is no new truth
API, empty truth case, exceptional endpoint treatment or correlated evaluator.
Here ≠ is the derived complement of real equality; no exceptional numerical
inequality table is inferred from the source or from lambda sentinel tests.

`eq_true_attainable` characterizes overlap; its witness is the maximum lower
endpoint. `eq_false_attainable` proves a false outcome exists unless both
intervals are the same singleton; unequal opposite endpoint witnesses suffice.
`compareEQ_exact` identifies the executable result with this complete image.
`compareNE_exact` reuses Boolean negation. Identical nonsingleton marginals do
not imply equality of their independently chosen values. A shared x=x remains
a different relation.

The projection/threshold proofs remain documented in
[DOMAIN_PROJECTIONS.md](DOMAIN_PROJECTIONS.md). The source-shaped equality
examples, touching/disjoint intervals, all six comparison directions, and the
shared-witness counterexample are kernel-checked in
[tests/FiniteEquality.lean](tests/FiniteEquality.lean).

## Numeric descriptions under explicit premises

The §2.11.3–4 correspondence concerns classification preservation, not equality
of numeric representations. `reencode_refines` allows source description d and
target description e to use different total real predicates f and g. It requires:

1. The source classifier's admitted Booleans equal the whole interval image of f.
2. The target classifier is sound for every value in its interval under g.
3. For each parameter p and each x in d(p), a y in e(p) exists with g(y)=f(x).

It concludes refinement of the existing domain descriptions at each p. The
source completeness premise accounts for **every** truth admitted by its
classifier, not just one actual input. Target completeness is unnecessary. The
transport witnesses concern the numeric description; they do not authorize
changing an operation's actual valuation or discarding its external domain.
This is a sufficient proof rule, not a solver or a necessary characterization of
all valid source demotions. It adds no rounding assumption.

The positive fixture transports x in [1,3] to y=x−1 in [0,2], preserving the
classification x>0 versus y≥0 on those specific domains. The falsifier replaces
x>0 by x≥0 at singleton zero without witness preservation: false cannot refine
true. Prior endpoint-only and sound-but-nonmonotone counterexamples remain intact.

`nonzero_exact` gives the whole interval image of x≠0; crossing/touching zero is
mixed and singleton zero is false. `reciprocal_constraint_compatible` uses the
existing `PartialRealArithmetic.divRel`, preserving an external input guard.
It gives no bounded reciprocal range near a pole and does not return a value at
zero. It is distinct from successful hardware quotient enclosure and from the
split-ray image work. Tests exercise actual zero/nonzero witnesses, the zero-only
empty domain, a touching interval and a nonzero input removed by an external hole.

## Remaining obligations

General numeric descriptor generation, full family demotion and extended/empty
semantics are outside this finite package. See the
[completion ledger](CHAPTER2_COMPLETION.md) and [checklist](CHAPTER2_CHECKLIST.md).
No native/C/FFI, production-default, FP-contract, renderer or timing changes.
The finite comparison package does not imply completion of Chapter 2.

```sh
lake build FiniteEquality
lake env lean tests/FiniteEquality.lean
./check.sh
```
