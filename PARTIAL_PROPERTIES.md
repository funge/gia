# Partial functions, domain extension and property tracking

[PartialProperties](PartialProperties.lean) supplies a small mathematical core
for actual partial real functions and connects it to the existing family theorem.
It does not choose a generic property-recursion interpretation or change an
expression evaluator.

## Original source check

Tupper §2.12, printed pp.36–37 / PDF pp.52–53, was visually rechecked in the
original repository PDF. Page 36 prints weak checkability from the composite
property to the recursive checks, and strong checkability as equivalence.
Page 37 gives definedness, continuity and local constancy, and calls continuity
weakly checkable. The existing [PropertyComposition fixture](tests/PropertyComposition.lean)
already proves a counterexample to that literal ordinary-continuity specialization
using a total jump and a constant outer function. It also proves the sufficient
reverse direction. This milestone reuses that checked evidence without duplicating
it, reversing the source arrow silently, or claiming to know the intended repair.

On printed p.37, §2.12.2 uses three-valued equivalence followed by optimistic
Boolean projection in the property inclusion formula. The Markdown subset
transcription is not the authority. The adopted compatibility interpretation is
the existing `DomainBounds.Compatible`, reused here for property descriptions.
The value inclusion obligation remains independent.

The neighboring square-root examples on p.36 were rechecked as well. The final
printed example has the previously documented `[-1,-1]` input with uncertain
domain and `[0,1]` numeric bounds. It is loose but sound under compatibility when
there are no defined results; it is not evidence that negative square roots
acquire real values. No new square-root implementation is introduced.

## Three distinct notions

* Restricting a partial function removes results outside a specified set.
* Extending a partial function adds possible points of definition while preserving
  every original result. This defines a **different function** at any filled hole.
* An interval extension/enclosure, as in the source, supplies bounds and property
  descriptions. Membership in those bounds does not manufacture a function value.

`PartialReal` is simply `ℝ → Option ℝ`. `none` is absent definedness, not an IEEE
NaN or a chosen exceptional comparison. `Extends f g` preserves each `some` result;
restriction and transitivity are proved. Strict composition is Option bind.
`compose_some` and `compose_defined` exactly characterize its actual result and
domain with the same intermediate value. This is the unary strict definedness
core, not the complete source m-ary recursive calculus.

## Continuity and sound transfer

`ContinuousOnPartial f S` requires a real function continuous on S that agrees
with actual `some` results of f at every point of S. Thus it asserts definedness
on S, uses relative real topology, and does not adopt a topology on Option.
Restriction preserves it; composition preserves it under the explicit image
premise sending defined inner results into the outer continuous domain. This is
only the sufficient direction, not the disputed weak-checkability arrow.

`extension_bounds_original` transfers numeric bounds from an extending function
g to the original f. It deliberately recomputes `exactInputDomain` for f rather
than copying g's possibly larger domain. The theorem reuses the general-family
soundness contract and exact-domain leaf. A result of g at a hole of f is never
returned as a result of f.

`Tracks` is a named predicate using the existing domain compatibility for an
arbitrary semantic property. `tracks_weaken` reuses classification weakening;
`tracked_demotion` combines the existing value/domain demotion theorem with a
separate proved property weakening. It does not infer continuity or constancy
from a numeric range or from syntax. Descriptions are conservative allowed truth
outcomes, not necessarily two attained outcomes.

## Worked example and falsifiers

[Fixtures](tests/PartialProperties.lean) define the genuine partial quotient
`ratio x = none` at zero and `some (x/x)` elsewhere. The constant-one function
extends it and is continuously defined everywhere. Nevertheless:

* `ratio 0` stays `none`, so ratio is not defined/continuous on all ℝ under the
  declared partial continuity predicate;
* strict composition with a constant outer function still has the inner hole;
* the extension's singleton bound `{1}` encloses every original result, while the
  original exact domain remains false at zero;
* copying the extension's total-domain flag is proved unsound;
* an always-true property flag for an actually false property is rejected.

Positive restriction and continuity-composition controls accompany these failures.
The original full continuity tracking obstruction remains in its existing fixture
and is rerun by the complete gate.

## Remaining source issue and scope

The printed continuity implication cannot be asserted for ordinary exact
continuity as specialized in the existing counterexample. A structural sufficient
certificate is valid, but is not automatically the author's intended meaning.
Keep that implication/interpretation open. The finite-arity and selective sufficient rules are documented in
[finite properties](FINITE_PROPERTIES.md) and [tracking](TRACKING_CERTIFICATES.md).
Full property-descriptor construction, exceptional arithmetic and source-wide
interval property extension remain outside this core. No new FP assumption,
native/default/renderer change or runtime claim is involved.

Source: [thesis PDF pp.52–53](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=52).
See [validation](VALIDATION.md), [completion ledger](CHAPTER2_COMPLETION.md),
[concordance](THESIS_CONCORDANCE.md).

```sh
lake build PartialProperties
lake env lean tests/PartialProperties.lean
RELGRAPH_CHECKOUT=/path/to/pinned/relgraph ./check.sh
```
