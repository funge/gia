# Domain-local interpretation contracts

`DomainEvaluator.lean` addresses the whole-range coordinate premise identified
in the independent review of #17–#18. It leaves the polynomial interpreter and
its existing theorems unchanged and adds two stronger ways to use them.

## Partial coordinate relations

`ExpressionValues A B e t z` means that coordinate values `x` and `y` exist in
relations `A t x` and `B t y`, and the existing partial semantics gives
`Value x y e z`. That pair is chosen once, so repeated variable occurrences
refer to the same values. Coordinate relations need not be total or unique.

`evalLinear_relational_sound` accepts the existing sound partial-enclosure
contracts for both coordinates. Their range clauses require enclosure only for
actual coordinate values. There is no requirement to provide a total coordinate
function or to enclose arbitrary values outside a possible domain. Successful
polynomial interpretation proves the three output obligations:

1. Every expression value is enclosed.
2. Every expression value has possible membership in both coordinate domains.
3. Definite membership in both domains supplies coordinate witnesses and an
   expression value, using the existing `evalLinear_defined` theorem.

Both domain descriptions are intersected and restricted to `[0,1]`, as before.
Unknown domain information is not promoted to definite membership.

This is a **strict coordinate environment** semantics: both bindings must exist,
even when the expression does not mention one of them. It is not a minimal
free-variable domain analysis. Nor does it encode an arbitrary joint constraint
between coordinate values beyond their shared parameter and the supplied unary
relations. These are explicit limits of this interface, not additional assumptions
silently made about the existing `Value` semantics.

## Locally enclosed function representatives

`evalLinear_local_sound` offers a simpler bridge for total real representatives
with an explicit intended domain `D`. Its enclosure premises require membership
only when `t ∈ [0,1]` **and** `D t`. The resulting relation also requires `D t`.
Values assigned to the representatives outside `D` have no semantic effect.

The control representative is 7 at parameter zero and 0 elsewhere, while the
coordinate interval is exactly zero. Lean proves that whole-range enclosure
fails at zero. Nonetheless, the new bridge proves a sound expression contract
on `t ≠ 0` using only the local enclosure. This directly demonstrates the
relaxation relative to #18's stronger sufficient premise.

## Checked domain controls

`DomainEvaluatorExamples.lean` additionally proves:

- An `x-x` expression in a punctured coordinate environment has no environment
  value at the excluded parameter and has a value at `1/2`.
- An empty coordinate relation can have a sound unknown domain description.
  Interpretation preserves possible-but-not-definite membership; it does not
  infer existence, and the example independently proves no environment value.
- All new public theorems are included in the enforced axiom audit.

The new bridges are proofs around the existing executable polynomial evaluator,
not an automatic domain analyser. No division is enabled in that interpreter:
unsupported operations still return `none`. The standalone guarded reciprocal
and quotient operations in [LINEAR_DIVISION.md](LINEAR_DIVISION.md) are unchanged.
No continuity, root-existence, optimality, or machine-correctness claim is added.

## Thesis connection and validation

Tupper [§2.11, Interval Function Domains](https://www.dgp.toronto.edu/~mooncake/thesis/node46.html)
separates value containment from definite, possible, and absent domain membership.
This milestone applies the earlier semantic approximation of that distinction to
coordinate environments and expression interpretation. It does not implement
the thesis's full numerical domain-description encoding or infer maximal domains.

`lake build` and `lake env lean Audit.lean` enforce the fixed axiom allowlist;
see [VALIDATION.md](VALIDATION.md) for counts and results. No FP assumption,
application/release build, toolchain pin, or hosted CI changes. This is a separate
review increment after #19 and does not rewrite the independently reviewed #17–#18.
