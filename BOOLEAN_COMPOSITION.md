# Finite Boolean composition

This is a narrow continuation of the [strict comparison](STRICT_COMPARISON.md)
foundation, using its existing `StrictComparison.Truth` and `Truth.values`.
There is no second truth API and no empty/contradiction constructor.

## Source and derived scope

Tupper, *Graphing Equations with Generalized Interval Arithmetic* (1996),
§2.9.2, printed p.27 / [PDF p.43](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=43),
explicitly describes Boolean conjunction and disjunction, their associativity,
commutativity, distributive laws and identities, and the correspondence
F/TF/T ↔ [F,F]/[F,T]/[T,T]. Information refinement is set inclusion, distinct from Boolean truth order.
The logical tables below are not meet/join operations for that information
order, and no information-lattice structure is introduced.
The existing local thesis Markdown was read first, then the original PDF page
was visually checked. The transcription's `IF` glyph is TF in the PDF.
No source copy is included or required by the build.

The new `neg`, `conj`, `disj` are derived finite interval-image tables. Classical
negation and De Morgan laws are useful derived counterparts, not a claim that
this page prints a separate negation algorithm. The exactness proofs instantiate
the Boolean interval interpretation with independent admitted operand values.
The code also proves the listed associative, commutative, identity and
distributive properties for these finite tables. This does not assert exact
range evaluation for arbitrary formulas with repeated/correlated variables.

## Exact independent image versus correlated enclosure

`image₂ op A B = {r | ∃ a ∈ A, ∃ b ∈ B, op a b = r}`.
`neg_exact`, `conj_exact` and `disj_exact` identify each output description's
values with the corresponding independent Boolean image. Both singleton
outcomes and mixed outputs are characterized exactly; the finite case proofs
cover all three unary and nine binary input combinations.

`jointImage op R` instead uses one admitted pair satisfying a joint relation
`R : Bool → Bool → Prop`. `joint_subset` requires each such pair to belong to
the two marginal descriptions, and concludes only subset containment in the
independent image. The conjunction/disjunction wrappers specialize this result.
`shared_witness_sound` additionally exposes the common-domain form for
`D : Set α` and functions `p q : α → Bool`, using the same `x ∈ D` for both.
For partial inputs, a joint relation must include the actual definedness and
external-domain obligations; this module neither constructs those witnesses nor
proves an expression defined. An empty joint relation has an empty image and
can still have a sound nonempty Boolean enclosure.

The `comparison_*_exact` bridges reuse `StrictComparison.compare_exact`.
Each binary composition uses independent copies of the operand comparison
outcomes, with their original real witnesses retained in the outcome definition.
They do not silently identify the witnesses between the two comparisons.

For correlation, let `R p q` mean `q = !p`. Both marginals attain both values,
but the conjunction image is exactly `{false}` and the disjunction image exactly
`{true}`. The independent mixed tables give TF in both cases, with strict subset
loss of precision. The fixture also constructs this relation from `p = (x < y)`
over `[0,1]²` and `q = !p`, invoking the existing exact comparison theorem.
Thus loss of precision is demonstrated even when the marginal images themselves
are exact. A separate constant-input control shows why a merely conservative
mixed description need not have both outcomes attained at all.

## Verification and limits

```sh
lake build BooleanComposition
lake env lean tests/BooleanComposition.lean
./check.sh
```

[Fixtures](tests/BooleanComposition.lean) include correlated complement pairs,
strict subset controls, the real comparison bridge, empty joint domain,
singleton/mixed corner cases and the common-witness soundness entry point.
Enforced audits cover the new declarations and the full project.

This is a proof-side finite foundation, not Boolean AST integration, lazy
partial evaluation, a native comparison implementation, or general recursive
property tracking. The distinct same-parameter domain-constraint conjunction of §2.11.4
(printed p.35 / PDF p.51) remains deferred; this is not its classification-
preservation API. Optimistic/pessimistic projections, broader relations,
exceptional endpoints and the full source logic remain deferred. No full
information lattice, new FP assumptions, hardware/default changes, or runtime
performance claims are made. See [Chapter 2 checklist](CHAPTER2_CHECKLIST.md),
[concordance](THESIS_CONCORDANCE.md) and [validation](VALIDATION.md).
