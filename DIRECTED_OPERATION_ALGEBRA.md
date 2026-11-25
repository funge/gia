# Finite directed-operation algebra

Tupper §2.5.3 (printed p.20 / PDF p.36) describes downward and upward rounding;
§2.5.4 (printed p.21 / PDF p.37) discusses commutativity, identities, additive
cancellation and failure of associativity. The original
[thesis page images](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=36)
were visually checked. This package treats a defined real operation followed by
**least mathematical directed demotion**, using the existing `DiscreteDemotion`
functions. It does not implement floating-point arithmetic or assert the source's
literal and digit formats coincide.

## Precise result

[DirectedOperationAlgebra.lean](DirectedOperationAlgebra.lean) defines `Rounded D
x l u` for a finite rational value family `D`: both finite endpoints belong to
`D` and are the existing downward/upward demotions of `x`. The library proves:

* `rounded_exists_iff`: finite endpoints exist exactly when represented finite
  values bracket `x`. An empty family or out-of-range result has no such pair.
* `rounded_iff_extremal`: exact equivalence with represented endpoint membership,
  enclosure, and greatest-lower/least-upper conditions. Mere outward enclosure
  is insufficient. `rounded_unique` gives uniqueness of the rational endpoints.
* `rounded_sound` and `rounded_least`: the result encloses `x`, and its real
  closed interval is contained in every represented finite enclosing pair.
* `Operation D R a l u` retains a single actual result witness of the partial
  relation `R`. `operation_domain` says success is exactly existence of a defined
  in-range result. `operation_absent` forbids value creation. `operation_sound`
  encloses every result **under explicit functionality of R**; it is not a hull
  theorem for an arbitrary nondeterministic relation.
* `division_domain` specializes this to the existing partial-real quotient:
  denominator nonzero **and** quotient in range. Finite valid inputs alone do
  not ensure finite output success. `add_comm`/`mul_comm` preserve the complete
  rounded relation, including absence; identities and additive cancellation
  are exact when the result is represented. Zero membership is explicit.

This is a reusable finite-value result, not restricted to binary64. Choosing
`FiniteFormat.values F` gives the existing literal-format mathematical family;
choosing the separately proved repaired/binary64 family does not identify those
families. Bounds outside the finite range remain ordered `EReal` bounds in
`DiscreteDemotion`, not a specification of a literal infinity or λ result in
this partial finite-operation layer. No automatic hardware success, faithful
rounding, raw-bit uniqueness, nearest-tie rule or ULP theorem follows.

## Checked controls and source scope

The [fixtures](tests/DirectedOperationAlgebra.lean) use the explicit symmetric
family `{−4,−2,−1,0,1,2,4}`. Downward and upward addition fail associativity on
`2,1,−1`, although all exact intermediate results remain in range. These are
small finite-family controls, **not** the printed decimal-format examples.
Other controls distinguish a zero denominator from a nonzero quotient outside
the finite range, show successful division of 6 by 2, reject a loose but sound
pair as nonoptimal, reject an empty value family, and distinguish interval
membership from attainment of the operation's actual value.

## Discrete remaining numeric obligations

| Printed clause | Current disposition |
| --- | --- |
| §2.5.3 directed finite enclosure | Exact extremal finite result and operation-domain theorem now registered. Existing arbitrary-radix and repaired binary64 representation bridges remain separate. |
| §2.5.4 commutativity, identities, additive inverse | Proved for mathematical directed finite-operation results with explicit representability. Not a total exceptional arithmetic theorem. |
| §2.5.4 nonassociativity | Finite-family witness checked. Printed decimal witnesses and the multiplication witnesses remain to be instantiated in the chosen source convention. |
| §2.5.3 nearest rounding; §2.5.4 all mixed distributive laws | Still separate proof obligations. No nearest tie policy is introduced here; do not infer every law from a single nonassociativity control. |
| §2.5.1 positive-infinity addition | Existing `ExceptionalComparisons.add_positive_infinity_cases` covers finite-plus-positive-infinity and positive-infinity-plus-itself. The reversed finite case follows from the printed commutativity assertion but is not yet added to the deliberately narrow observation API. It is a concrete model-extension task, not a guessed IEEE row. |
| §2.5.2 negative finite root and comparisons with λ | Already modeled by `sqrtObservation` and the five specified comparison predicates. `none` remains unmodeled, not λ; sentinel definedness is not numerical equality. |
| Mixed infinities, infinite-input roots, remaining λ operands | No complete operation table follows from the passages checked. Remain unmodeled pending an explicit source rule; no IEEE completion. |
| §2.6 “homomorphism” | Exact promotion of represented finite values is distinct from preservation of rounded arithmetic. Literal infinities, unbounded real sets and λ remain separate. |

Run `./check.sh` for the full local gate. The new theorem declarations and fixture
namespace use the unchanged axiom audit. See [the closeout matrix](CHAPTER2_CLOSEOUT.md)
for the wider chapter; this does not mark the numeric package or Chapter 2 complete.
