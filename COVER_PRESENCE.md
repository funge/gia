# Domain-certified presence from finite covers

Finite-cover soundness establishes bounds and domain facts. It does not establish
continuity. Conversely, a continuous representative can extend across a hole
where the actual relation has no value. This milestone connects those two
certificates without erasing that distinction.

The connection follows the separation between Tupper's
[interval function domains (§2.11)](https://www.dgp.toronto.edu/~mooncake/thesis/node46.html),
[property tracking (§2.12)](https://www.dgp.toronto.edu/~mooncake/thesis/node52.html),
and [continuity-based testing (§4.2.6)](https://www.dgp.toronto.edu/~mooncake/thesis/node156.html).
It supplies a semantic proof rule, not an automatic continuity or domain analyzer.

`cover_domain_presence` assumes:

- a finite-cover `SoundOn` contract for an actual-value relation;
- a real representative continuous on the whole closed unit interval;
- agreement of every actual value with that representative at unit parameters;
- definite domain membership at every point of the unit interval;
- every cover component's upper affine bound is nonpositive at parameter zero,
  and every component's lower affine bound is nonnegative at parameter one.

The proof extracts actual endpoint values from the definite-domain evidence,
uses their enclosing components to establish endpoint signs, applies the
intermediate value theorem, and extracts an actual value at the resulting
parameter. Agreement then identifies that actual value with zero. Equality in
the endpoint bounds is allowed, so endpoint roots are retained. All retained
components must pass the sign conditions, a conservative sufficient rule.
The agreement assumption restricts this rule to a single-valued representative;
it is not a general root rule for arbitrary multivalued relations.

`conditional_value_unique` proves uniqueness of existing conditional values,
including uniqueness of the guard value. It assumes no existence for undefined
or inactive expressions. This lets a separately proved conditional-continuity
certificate supply the representative agreement needed by the presence rule.
`cover_domain_restrict` reuses the existing domain intersection to restrict both
possible and definite membership while retaining the same finite range cover.
It mirrors the existing partial-enclosure restriction operation without adding
a new domain representation.

The positive example interprets the existing conditional tree
`if t < 1/2 then t - 1/2 else (t - 1/2) + (t - 1/2)`.
The distinct slopes meet at the threshold. The existing threshold-continuity
rule proves continuity and actual conditional values; finite-cover evaluation
proves enclosure and coordinate-domain soundness; rational endpoint signs and
semantic uniqueness complete an actual relational-root certificate.

The negative control removes parameter 1/2 from the relation's domain, retaining
the same range cover and continuous representative. Both endpoints still have
actual values, and the same sign bounds still hold. Nevertheless, the restricted
relation has no zero because the representative's unique zero is the missing
parameter. The definite-domain premise over the whole path is explicitly proved
false. Existing jump controls separately show why continuity cannot be inferred
from definedness or enclosure.

No evaluator, syntax, FP assumptions, application integration, automatic root
search or executable property analyzer changes. Continuity and whole-path
membership remain supplied proofs. Conservative coordinate-domain intersections
from #32 remain in force. A future automatic certificate generator must produce
these obligations; endpoint sampling or a continuous extension alone is not a
substitute.
