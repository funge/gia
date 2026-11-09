# A sufficient conditional continuity certificate

This module supplies a bounded boundary rule for existing ConditionalExpr and
ConditionalValue. It does not add syntax, change evaluation, or implement an
automatic continuity analyzer.

## Exact scope and side conditions

Fix a rational q in [0,1]. The guard must have an actual Value equal to the
parameter t at every certified t in [0,1]. This covers a parameter guard such
as x with x(t)=t, or another arithmetic guard whose equality is proved. It does
not cover arbitrary guard crossings merely because the guard is continuous.
An undefined guard cannot satisfy this premise.

Let f and g be supplied branch-value representatives. The sufficient conditions
are:

- f is continuous on [0,q], including a continuous extension to q;
- g is continuous on [q,1];
- f(q)=g(q);
- the true branch has actual ConditionalValue f(t) for 0 ≤ t < q;
- the false branch has actual ConditionalValue g(t) for q ≤ t ≤ 1.

`thresholdValue` is the real representative selecting f below q and g otherwise.
Equality selects the false branch, consistently with the existing semantics.
`threshold_continuous` proves continuity using #28's finite closed-cover theorem
on [0,q] and [q,1]. `conditional_threshold_certificate` adds actual conditional
values at every unit parameter by selecting the appropriate Value constructor.
No new continuity-certificate structure or independent gluing interface is added.

The true branch need not be defined at q. Its f(q) is part of a supplied
continuous extension, not a fabricated branch value. Matching that extension
to the defined false branch is sufficient. Conversely, a hole inside an active
region or in the false branch at equality cannot meet the value premises.
The rule is sufficient, not necessary; even endpoint thresholds 0 or 1 retain
these stated representative/matching premises.

Coordinate functions are supplied to the branch and guard Value proofs. The
rule does not additionally assume their continuity: the continuous branch-value
representatives provide the required continuity evidence. Nor does it infer
continuity from enclosing affine bounds or from definedness alone.

The certificate concerns ConditionalValue at the supplied coordinates. A separate
partial coordinate environment still requires its own membership evidence; its
holes are not filled by this raw conditional-value certificate.

## Positive and negative controls

The main example is

    if t < 1/2 then (t-1/2)/(t-1/2) else 1.

The true branch has no semantic value at t=1/2. Nevertheless, it has value 1
strictly to the left, its constant extension matches the false branch, and the
certificate proves that the whole conditional is continuous and has actual
value 1 at every unit parameter. A separate theorem proves the true-branch hole;
another proves the false branch supplies the boundary value. The current interval
interpreter still returns unknown on the whole range, so the semantic certificate
is not being misrepresented as an automatic interpreter enhancement.

A nonconstant V-shaped representative tests matching continuous branches. The
existing jump counterexample is reused to reject unmatched constants -1 and 1.
Additional constructor proofs reject an active false-branch pole at the boundary
and an undefined guard even when both branches are identical constants.

## Positive overlap regression requested in the #28 review

The agreement-wrapper regression uses cells [0,3/4] and [1/4,1], which overlap
over an interval rather than only a point. Their local representatives are

    left(s)  = (3/2)s + 1
    right(s) = (3/2)s + 3/2.

They are proved distinct at local parameter zero. Each is separately proved
continuous, and an algebraic identity proves equality to 2*map(s)+1 for every
local parameter, not just selected endpoints. Those full-cell identities feed
`parameter_cover_continuous_of_agreement` to certify the common function 2t+1.
Thus all physical overlap points are covered by the agreement proof, without
weakening #28's premises.

## Thesis relationship and limits

This is a specific property-composition rule in the direction of Tupper
[§2.12](https://www.dgp.toronto.edu/~mooncake/thesis/node52.html), retaining
separate continuity evidence as in
[§3.3.18](https://www.dgp.toronto.edu/~mooncake/thesis/node124.html). It is a
formalization choice built on existing semantics and closed-cover proofs, not
a claim to implement the thesis's full numerical property descriptions.

Guard-to-parameter equality, continuous extensions, branch-value witnesses,
and boundary agreement are supplied proofs. There is no automatic limit
calculation, multiple-crossing analysis, arbitrary-guard theorem, maximal-domain
inference, completeness claim, new FP assumption, or native implementation
correctness claim. Existing evaluators, coverage rules, axiom policy, dependency
pins, application build/release, and hosted CI remain unchanged. See VALIDATION.md
for build, audit, coverage, and regression evidence.
