# Interval-set denotation and one-interval projection

[IntervalSetDenotation.lean](IntervalSetDenotation.lean) follows Tupper §2.13
and §2.13.1, printed pp.38–39 / PDF pp.54–55. Original page images were checked,
including the existential membership definition and potentially infinite point
descriptions. [Original PDF](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=55).
§2.14, printed p.40 / PDF p.56, distinguishes equal coefficients from
interval-valued coefficients; it does not assert that all variants are singletons.

## Exact meaning first

`denote V J p` means there is a piece j in J containing the real value at the
same parameter p. V can describe closed, open, disconnected or partial sets;
no endpoint convention is silently imposed. Empty and singleton descriptions
and union have exact denotations. `pairwise_inter` gives exact intersection by
pairing pieces at that SAME parameter. This is a derived set-theoretic consequence
of the printed membership rule, not a separately printed intersection algorithm.
Plain intersection of description identifiers only gives inclusion: distinct
pieces can denote the same or overlapping values.

`points_exact` represents the graph of an Option-valued partial real function
by equality-guarded point pieces, with no pieces at an absent output. This is
an abstract equality-guarded specialization of the source's perfect point
representation. It does not implement its squared-distance constraint syntax,
finite enumeration, numeric domain/continuity flags or a practical demotion.

## Least projection when the target is one interval

`real_projection` reuses the exact extended real-output hull to give soundness
and leastness among closed extended-real-bound intervals. `integer_projection`
reuses proved floor/ceiling demotion to give the corresponding result among
extended-integer endpoints. No new rounding contract is assumed. Both handle
empty sets, and neither equates an enclosing value with an attained value.
These are one-interval target results, not optimality among all finite unions.
A union can preserve holes that its hull necessarily loses.

`reencode` preserves denotation under an explicit pointwise equality of piece
meanings. It is only a transport theorem, not proof that arbitrary coefficient
representations are equivalent. `equal_real_bounds` proves the singleton case
of equal scalar real bounds. It does not apply to equal interval-valued
coefficient descriptions in §2.14, or complete Hansen's system correspondence.

[Fixtures](tests/IntervalSetDenotation.lean) check {-1,1} versus its hull,
description-identifier intersection failure, closed versus open touching
intervals, an absent reciprocal value, same-parameter point selection, and an
infinite open point family. These are semantic controls, not native tests.
Run `./check.sh` for the full local gate.

## Deferred source obligations

The inclusion layer preserves values only; domain classifications remain the
separate obligations already proved in GeneralFamilyDemotion. No def/cont flags
are derived from union membership. General multi-parameter coefficient variants,
source bumpy-function quantification over all models, finite representability,
perfect numeric constraint demotion and exceptional arithmetic remain open.
This closes the general existential denotation and its closed-hull projection
bridge, not all of §§2.13–2.14 or Chapter 2. No hardware assumptions changed.
