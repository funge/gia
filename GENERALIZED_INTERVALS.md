# Parameter-dependent bounds and partial domains

This milestone starts the transition from ordinary constant intervals to
Tupper's generalized interval arithmetic. It adds general arithmetic and semantic
interfaces; it does not add another graph classifier or replace the evaluator.

## What is generalized here?

In [§2.9.3, Linear Intervals](https://www.dgp.toronto.edu/~mooncake/thesis/node39.html),
Tupper brings a shared parameter into the number representation. Both bounds
vary linearly with that parameter on `[0,1]`. A value between those bounds need
not itself vary linearly. Keeping parameter dependence allows his `x-x` example
to produce `[0,0]` instead of the ordinary interval result `[-1,1]`.
[§2.9.7, Functional Intervals](https://www.dgp.toronto.edu/~mooncake/thesis/node43.html)
extends the choice of bound functions. Here “generalized” refers to that family
of parameter-dependent representations, not merely to reversed ordinary
interval endpoints or a new name for the existing constant-interval evaluator.

`LinearIntervals.lean` implements a finite, single-parameter fragment:

- `QAffine` stores rational values at parameter endpoints 0 and 1. Its real
  interpretation interpolates between them; this is equivalent to rational
  intercept/slope coefficients.
- `LinearInterval` stores lower/upper affine bounds with two rational ordering
  proofs. `linear_ordered` proves non-collapse throughout `[0,1]`.
- Constant embedding, exact affine embedding, addition and subtraction are
  implemented. Pointwise inclusion is proved for both arithmetic operations.
- `hull` forgets parameter dependence into a rational ordinary interval;
  `linear_hull_encloses` proves its enclosure on `[0,1]`.
- `linear_exact_cancel` proves exact cancellation for an exact affine input.
  It does not assert cancellation of arbitrary independent uncertain values
  simply because they have equal interval descriptions.

All stored coefficients and arithmetic are exact rationals. Real interpretation
is noncomputable Lean mathematics. Multiplication, division, nonlinear-to-linear
bound construction, automatic expression evaluation with these intervals, and
multiple affine parameters are not implemented in this milestone.

## Domain information is separate from bounds

[§2.11, Interval Function Domains](https://www.dgp.toronto.edu/~mooncake/thesis/node46.html)
separates value and domain descriptions, including definite, possible, and absent
definedness, and permits collapsing bounds in the enlarged construction.
`PartialEnclosures.lean` provides a deliberately small semantic interface for
this distinction. It does **not** reproduce Tupper's numerical domain-description
encoding, demotion operators, or full extension construction.

A `PartialEnclosure α` has functional lower/upper value bounds and two predicates
on parameters: `definite` and `possible`, with definite implying possible. For a
partial-value relation `R p z`, its `Sound` contract requires:

1. Every semantic value is within the value bounds.
2. Every semantic value implies possible domain membership.
3. Definite domain membership supplies an actual semantic value.

Thus possible-but-not-definite means unknown. No continuity premise or conclusion
is hidden in this contract. These are arbitrary predicates and real functions,
not an executable domain decision procedure. The relation can be multivalued;
functional uniqueness is not needed by the enclosure proofs.

We prove absence outside the possible domain, existence within the definite
domain, non-collapse at definitely defined parameters, and absence from collapsed
bounds. Restriction by a known predicate and addition of partial relations preserve
all three obligations. Addition intersects both domain descriptions and encloses
every sum of defined operand values. `linear_partial_sound` embeds a supplied
function enclosed by a linear interval into this contract on `[0,1]`; its enclosure
premise is explicit, not a newly asserted axiom.

## Partial functions and discontinuity controls

[§2.12, Property Tracking](https://www.dgp.toronto.edu/~mooncake/thesis/node52.html)
extends domain tracking to other properties;
[§3.2.18, Discontinuous Functions](https://www.dgp.toronto.edu/~mooncake/thesis/node95.html)
tracks a continuity description separately from values. This milestone preserves
that separation but does not implement continuity-property propagation.

`GeneralizedExamples.lean` checks:

- Ordinary subtraction of `[0,1]` from itself gives `[-1,1]`, whereas the shared
  exact affine parameter cancels pointwise and has hull `[0,0]`.
- A reciprocal relation has domain `t ≠ 0`, exact functional bounds, and no value
  at zero. Lean's total inverse is used only to describe bounds and values away
  from zero; its value at zero cannot create a semantic reciprocal value. This
  example is not an algorithm for computing linear reciprocal bounds.
- A jump function takes values -1 and 1. Its total-domain enclosure is sound,
  its endpoint signs are opposite, and it has no zero anywhere. Hence the new
  contract cannot justify a sign-change root theorem. No IVT/presence code is
  changed or given access to this contract as a continuity certificate.
- The same uncertain domain description is sound both for an empty relation
  and for an everywhere-defined zero relation: unknown proves neither case.
- Partial addition and explicit restriction satisfy their composition contracts.

No new floating-point assumptions are introduced. IEEE 754 remains the rounding
reference for the earlier backend; this rational/real milestone makes no IEEE
format, machine-execution, or implementation-correctness claim. The native build,
v1.0 release, and hosted CI remain independent.

A natural bounded follow-on is sound multiplication with an explicit choice of
linear over-approximation, then an expression interpreter retaining shared
parameters. Automatic domain/continuity descriptions require a separate design;
the current semantic interfaces do not pretend that analysis has been implemented.

The subsequent [linear multiplication milestone](LINEAR_MULTIPLICATION.md)
implements one explicit enclosure policy and proves domain-preserving products.
The limitations above describe this earlier foundation milestone.

## Executable queries of certified domains

`DomainQueries.lean` supplies the small query layer missing from `DomainBounds`.
`D.classify p` returns the existing `BranchDecision` values: `yes` precisely when
membership is definite, `no` precisely when membership is not possible, and
`unknown` precisely when membership is possible but not definite. Here these
are **pointwise domain** outcomes, not `BranchSound` certificates across an entire
parameter interval and not present/empty graph-pixel verdicts.

Both membership predicates must have supplied `Decidable` instances. With
executable instances, the query executes; arbitrary real predicates do not
magically become decidable. There is no classical decision oracle in the
implementation. The two semantic wrappers consume only domain existence and
exclusion certificates, without requiring a finite value enclosure. This allows
future use with quotient-domain certificates whose ranges may be unbounded.

The fresh core-only `tests/DomainQueries.lean` uses exact rational decisions for
an intersection of `[0,1]` with exclusions at `1/2` and `1/4`. Kernel-reduced
queries include both endpoints, both holes, and out-of-range parameters. An
independent partial `Value` equivalence for `1/(t-1/2)` connects a sound semantic
enclosure to the query results. The pole and input hole are both excluded, but
the unrestricted expression is proved defined at the latter. The fixture's
functional value bounds are mathematical witnesses, not computed reciprocal
bounds. Two sound relations with opposite existence behavior share an unknown
query, demonstrating why unknown is inconclusive.

This follows the interpretation of unknown as insufficient knowledge in
[Tupper §2.9.2](https://www.dgp.toronto.edu/~mooncake/thesis/node38.html) and is a
query prerequisite for the domain-description work in
[§2.11](https://www.dgp.toronto.edu/~mooncake/thesis/node46.html), not the thesis's
full domain encoding or an automatic domain analyzer. The caller still provides
sound domain evidence and executable predicates. Querying finitely many rational
parameters cannot establish domain coverage or continuity over real intervals.
No evaluator, floating-point assumption, or application integration changes.

## Automatic quotient-domain descriptions

`QuotientDomains.lean` constructs an executable description for the restricted
class `a / b` at rational parameters. It runs the existing `evalGuarded` on both
children. When both succeed, `quotientDomainRat` uses rational affine-bound
values to derive the denominator's nonzero-domain evidence, preserving the
supplied external domain. The two refinement theorems identify these predicates
with the existing semantic quotient certificate from `NonzeroDomains`; this is
an executable refinement, not a separate definition of division semantics.
`QAffine.valueRat` is proved equal, after casting, to real affine evaluation.

If either child fails to enclose, or the outer expression is not a quotient,
`unresolvedDomain` supplies no definite membership and preserves the external
possible domain. Failed analysis does not assert arithmetic undefinedness.
Successful child analysis may also remain unknown when denominator bounds
straddle zero. The result uses the existing `DomainBounds.classify` directly,
with rational membership decision instances; no alternate evaluator is added.

Soundness uses fixed coordinate functions `x(q), y(q)` shared by both operands.
The caller certifies the external domain's definite/possible evidence and that
actual allowed inputs lie in `[0,1]` and the supplied coordinate enclosures.
The proved conclusions are actual-value implies possible membership, and
definite membership implies an actual `Value` for the original quotient.
No independently chosen coordinate environments are mixed. Both coordinates
share one external domain; this is not minimal-free-variable analysis.

The fresh `QuotientDomains` client automatically derives the exact definite
rational domain of `1/(q-1/2)` with an external hole at `1/4`, and independently
proves its semantic definedness set. Queries cover endpoints, both holes and
outside inputs. `u/u` still excludes `u=0`; `1/(x-x)` is certified absent.
For `1/(1/(x-1/2))`, failed child enclosure remains unknown both at an actual pole
and at a separately proved defined point. A loose `[-1,1]` coordinate enclosure
produces unknown with successful child analysis, and admits both defined and
undefined concrete quotient instances. Unsupported polynomial syntax also
remains unknown unless the external domain already excludes the input.

This bridges Tupper's [partial-function domain translation (§3.3.16)](https://www.dgp.toronto.edu/~mooncake/thesis/node122.html)
with the current finite affine representation. It does not construct a quotient
range, infer continuity, solve domains for all expressions, recursively analyze
failed quotient children, or cover real intervals from rational samples. Strict
partial semantics, external holes and the unknown outcome are preserved. No new
floating-point assumptions, dependencies, application code or hosted CI.

## Recursive exact-point domains

`PointDomains.lean` improves executable domain precision without introducing a
second evaluator or extending the expression syntax. `eval_defined` proves that
successful evaluation with a sound backend supplies a partial-semantic value at
each enclosed input. `eval_point_complete` proves the converse **only for the
exact backend and rational singleton inputs**: each defined real value has a
rational witness and evaluation returns its exact singleton interval. Together,
`eval_point_defined_iff` characterizes existence for every constructor of the
existing arithmetic AST, including arbitrarily nested division.

`inferPointDomain` uses that characterization for exact rational coordinate
functions and intersects the computed membership with the caller's definite
and possible external domain. Both semantic directions are proved. The existing
query layer can execute these predicates; no numerical enclosure assumptions
about uncertain coordinates are substituted for exact coordinates. For affine
rational coordinates, the existing `affine_valueRat_cast` supplies agreement
with the real interpretation.

This is a distinct, explicitly restricted precision path. Failed **exact-point**
evaluation certifies arithmetic undefinedness because completeness is proved.
The original evaluator's `none` and its graph classifier remain unchanged for
wide intervals and general sound backends. Such failures still mean unknown.
External possible-but-not-definite membership stays unknown when the arithmetic
has a value; a proved arithmetic pole can still exclude membership.

The fresh core-only `PointDomains` client resolves `1/(1/(q-1/2))` away from the
pole and an external hole at `1/4`, where the earlier interval-based analyzer
remains unknown. Independent direct `Value` inversion and construction prove
that the double reciprocal equals `q-1/2` precisely where its original domain
permits, retaining the hole. A theorem connects the inferred yes-set to that
semantic domain for every rational parameter. Controls retain `u/u` and
`0 * undefined` holes, include polynomial expressions and uncertain external
domains, and show wide-interval and declining-backend failures with defined
values. Therefore neither singleton completeness premise can be dropped.

The thesis motivation remains the separation of domain descriptions from values
in [§2.11](https://www.dgp.toronto.edu/~mooncake/thesis/node46.html) and domain
translation for [partial functions](https://www.dgp.toronto.edu/~mooncake/thesis/node122.html).
This does not supply domain coverage over real intervals, decisions at irrational
coordinates, continuity, finite quotient range bounds, or a runtime/resource
bound. Coordinate functions and external predicates must themselves be executable
for execution. No FP assumptions, application code or hosted CI changes.

## Shared-environment affine guards

`AffineDomainGuards.lean` implements the small guard experiment proposed after
#50 without promoting the optional-range prototype or replacing current APIs.
A `RationalAffineForm` stores coefficients for `a*x+b*y+c`. A finite list denotes
the conjunction that every form is nonzero **at the same complete `(x,y)`
environment**. The list also generates an expression in the existing `Expr` AST:
the sum of the corresponding reciprocals, with zero for the empty list.

`affine_sum_defined_iff` proves exact partial-domain equivalence for every real
environment: a generated sum has an actual `Value` if and only if every guard
holds there. Appending guard lists corresponds to conjoining definedness before
any environment is projected out. Rational guard evaluation is proved equal to
the real interpretation after casting, so its executable Bool check is exact at
rational environments. `affineGuardDomain` intersects that check with existing
external `DomainBounds`; both semantic directions and query instances are proved.

The fresh core-only fixture revisits the disjoint-witness counterexample from
#49. Each child has a permitted real input, but no common permitted input defines
the sum; the joint guard query preserves that absence and excludes the otherwise
arithmetically valid midpoint. A two-coordinate example independently proves the
real domain `x+y ≠ 1 ∧ x ≠ y`, constructs a concrete value, and checks both query
soundness wrappers. Additional controls retain external unknown, reject a zero
denominator, and handle empty and duplicate guard lists.

This is a certified expression family, not extraction from arbitrary expressions,
a new evaluator, a general symbolic solver, or a test for existential feasibility
over an uncertain region. Queries concern one supplied environment; real-set
reasoning in the tests is proved separately. No range is asserted by these
domain-only certificates, so unavailable numerical bounds are not confused with
undefinedness. Continuity, coordinate projection, general constraint simplification
and richer range representations remain separate. The finite conjunction follows
the domain-constraint direction of [Tupper §2.11.4](https://www.dgp.toronto.edu/~mooncake/thesis/node50.html)
without claiming its complete encoding or demotion construction. No FP changes.

## Affine domain certificates along segments

`AffineSegmentDomains` consumes #51's reciprocal-sum family in a useful existing
checker. Strict same-sign values of every affine denominator at both endpoints
prove nonzero values throughout the closed segment. All guards share the same
interpolated x,y environment. The exact domain equivalence then supplies actual
`Value` witnesses; `expr_continuousOn_of_defined` derives continuity, and the
existing endpoint evaluator and `segment_presence` prove a zero. There is no
new expression evaluator, assumed continuity, or finite whole-box range claim.

`classifyAffineWithSegment` first tries this certificate and otherwise delegates
to `classifyWithSegment`. Its presence and empty results are proved sound. Failed
domain/sign/backend checks do not imply absence; the existing fallback can still
prove emptiness or presence. The new certificate accepts nonpositive at the first
endpoint and nonnegative at the second; reverse the supplied segment for the
other orientation. It is incomplete and does not search for segments.

This joins the thesis's [domain conjunctions, §2.11.4](https://www.dgp.toronto.edu/~mooncake/thesis/node50.html)
with [continuity-based testing, §4.2.6](https://www.dgp.toronto.edu/~mooncake/thesis/node156.html).
The general arithmetic result is definedness on the entire segment; graph
presence is its existing consumer. Independent tests show a real improvement
for 1/x + 1/y on [-2,2] × [1,2], along (-1,2) to (-2,1), with an independently
constructed zero at (-3/2,3/2) and an actual off-segment pole. A sign change in
1/x across x=0 remains unknown and has a separate no-zero semantic proof.

Scope: arithmetic partial domains only. This checker has no external-domain
argument and must not be used to claim a zero in an arbitrarily restricted
external domain. A semantic control explicitly shows such a restriction can
remove all arithmetic zeros. No previous external-domain API is changed or
weakened. Endpoint bounds require the existing `BackendSound` contract; exact
rational tests add no floating-point assumptions or IEEE implementation claims.

### Completeness of the restricted segment-domain test

`affine_segment_safe_iff_defined` proves that the existing `affineSegmentSafe`
Boolean succeeds exactly when the generated affine reciprocal sum has an actual
partial value at every real parameter on the supplied closed segment. The reverse
implication uses affine interpolation and the intermediate value theorem: a
continuous nonzero affine denominator cannot change sign. Every denominator is
checked at the same coordinate environment; rational endpoint comparisons are
connected to real semantics by the existing cast theorem.

`affine_segment_unsafe_iff_hole` gives the precise meaning of false: there is at
least one parameter where the expression has no partial value. This is an
existence theorem, not an algorithm returning a hole location. A hole is neither
absence everywhere nor absence of zeros. The independent fixture constructs a
zero of 1/x + 1/y at (-1,1) on a segment that also passes through the undefined
point (0,0). A safe segment can still yield an unknown presence result when the
backend declines. No classifier outcomes or previous APIs change.

The equivalence is limited to this generated family and arithmetic domains.
It neither decides arbitrary external predicates nor generalizes endpoint-sign
reasoning to nonlinear denominators. It is project-authored property-semantics
work built from available source and mathlib proofs, not a claimed exact thesis
proof. The concordance's original-equation access caveats remain in force.

### Presence and absence under external domain restrictions

`certifyAffineSegment_path_sound` retains the real parameter locating the zero,
including its unit-interval membership, box containment, and actual partial
value. The earlier `certifyAffineSegment_sound` statement is unchanged and now
follows by forgetting the parameter. This avoids repeating the continuity and
intermediate-value proof when a caller needs a path property of the zero.

`certifyAffineSegment_domain_sound` accepts an explicit proof that an external
predicate E contains every point of that segment. It concludes an actual zero
inside E and the box. Endpoint membership alone is insufficient: the fixture's
`endpointsOnly` domain contains both endpoints of the successful 1/x + 1/y
certificate but excludes every zero. Its positive `quadrant` example proves
whole-path inclusion and derives restricted presence. No external predicate is
silently inferred, and a classifier's `present` output alone is not a certificate
for an arbitrary external restriction.

The completeness result composes without losing either obligation:
`affine_segment_domain_defined_iff` says restricted partial values exist along
the whole path exactly when E contains the path and `affineSegmentSafe` succeeds.
For absence, `classifyAffineWithSegment_domain_empty` transports a proved empty
result into any E, without a path-inclusion assumption. Restricting a root-free
set cannot introduce a root. These are theorem-level interfaces over existing
checks, not a new executable external-domain analyzer or another classifier.
The existing unknown outcomes and FP contracts are unchanged.

### Executable external regions from affine constraints

`AffineRegions` supplies a bounded constructive case of #55's external-domain
premise. `affineRegion cs x y` is exactly the conjunction `0 ≤ g(x,y)` for every
rational affine form g in a finite list cs. It describes closed half-spaces and
their finite intersections: boxes, strips, convex polygons, and possibly empty
or unbounded regions. This is domain geometry, not an unbounded value enclosure.
All constraints refer to the same actual x,y point.

`classifyAffineRegionSegment` checks rational endpoint values and reuses
`BranchDecision` with the whole-path `BranchSound` meaning:

- `yes`: both endpoints satisfy every constraint. Proved affine convexity gives
  inclusion of every point on the closed segment. This positive test is complete
  for whole-path inclusion in exactly this region class.
- `no`: one constraint is strictly negative at both endpoints, so it excludes
  every point on the segment. This says nothing about other points in the box.
- `unknown`: neither certificate succeeds. This includes mixed-membership paths
  and some infeasible conjunctions; the routine is not a linear feasibility solver.

`certifyAffineSegment_in_region` combines a computed `yes` with the existing
arithmetic presence certificate and its backend enclosure contract. It derives
an actual zero in the region and box without a caller-supplied path proof.
A `yes` region query alone proves no root or arithmetic definedness. Unknowns
are not promoted to absence; a path-level `no` cannot classify a whole box empty.

The independent fixture proves an end-to-end zero under x ≤ -1 and y ≥ 1,
checks closed-boundary contact, degenerate paths, empty/zero constraint lists,
and mixed membership. It separately proves that contradictory constraints can
produce unknown, and that a path excluded from x ≥ 1 can coexist with a genuine
root elsewhere in the same box. Additional external holes must not be dropped:
the query certifies only the explicit constraint list. Nonlinear/disjunctive
restrictions and strict half-spaces are outside this API; no expression recognizer
silently approximates them. No general multidimensional interval representation,
FP changes or exact-thesis formula correspondence is claimed.

### Finite segment search inside affine regions

`AffineRegionSearch` connects the executable region and presence certificates to
finite search. `certifyAffineRegionCandidate` checks whole-path region inclusion
and tries both arithmetic sign orientations. `searchAffineRegionSegments` returns
the first passing supplied `SegmentCandidate`, using `List.find?`; the returned
candidate is proved to belong to that list and to imply an actual restricted
zero. Search succeeds exactly when some supplied candidate passes the certificate.
This is completeness relative to finite certificates, not completeness for roots.

`classifyAffineRegionSearch` reuses the existing whole-box arithmetic zero test
for `empty`. Otherwise a successful search yields `present`, and failure yields
`unknown`. The proof reuses `ResultSound` for the root proposition that includes
the explicit affine region. Region-level no/unknown outcomes never become empty.
`classifyAffineRegionBox` supplies the existing eight center-to-boundary
`boxSegments`; it introduces no new sampling or subdivision machinery. Supplied
candidate lists can extend or replace that policy. This is a fixed finite policy,
not a proved time bound or an exhaustive geometric search.

Independent controls certify an automatic restricted root and the first valid
candidate after rejection, including reversed orientation. They construct a real
root independently of the search proof and show that the automatic policy can
miss it while a supplied segment succeeds. Another control uses the everywhere
zero expression: when the box center lies outside the region, all default paths
fail even though a restricted zero exists. A uniformly excluded candidate still
returns unknown, not box absence. Empty lists and backend failures remain unknown
unless the independent whole-box zero-exclusion proof succeeds.

All earlier domain and source limits remain: only the supplied closed affine
constraints are certified, extra holes need separate evidence, and the work is
an integration of project proofs rather than an asserted exact thesis algorithm.

### Bounded subdivision inside affine regions

`refineAffineRegionBox` in `AffineRegionSubdivision` is a bounded consumer of the
existing constrained box checker. It starts with an x split and alternates axes.
Depth zero still checks the current box; only unknown boxes split. A present
child establishes presence in the parent; both children must be empty to establish
parent absence. All other unresolved combinations stay unknown.

The ordinary `Subdivision` recursion is factored into `refineBoxes`, parameterized
by a box checker. Its soundness theorem requires checker soundness and exact
root-coverage equivalences for each axis. The original `subdivide` interface and
its zero/successor equations are preserved, with kernel-checked compatibility
proofs. There is one recursion, not a second constrained subdivision algorithm.
`HasAffineRegionRoot` includes the same constraint list and actual partial `Value`
semantics in every child. The two split equivalences preserve witnesses in both
directions, including shared boundaries; the region is not rescaled or discarded.

The independent fixture uses `1/x + 1/y` on `[-2,2]²` restricted by `x ≤ -1` and
`y ≥ 1`. Depths zero and one are unknown; depth two certifies presence. The root
`(-1,1)` is also constructed directly from expression semantics. Controls cover
backend failure, an infeasible region that remains unknown, genuine arithmetic
absence, shared-boundary roots, and degenerate boxes with and without a pole.

This improves practical coverage of the existing finite policy without claiming
completeness. Depth limits splitting, not wall time or evaluator operations; the
potential binary tree grows exponentially. There is no proof of eventual success,
constraint clipping or feasibility solver. Empty results still originate from
arithmetic zero exclusion, possibly aggregated over a complete split. Rejected
paths and exhausted depth never imply absence. Arbitrary additional external
holes are not silently covered. No floating-point assumptions change.

### Finite-rational correspondence with thesis coefficient bounds

The graphing inventory entry F06 points to thesis §2.9.3. Its original printed
pp.28–29 (repository PDF pp.44–45) describe coefficient bounds `a+b*t` and
`c+d*t`, require them to be defined and ordered for every `t ∈ [0,1]`, and give
the exact affine `x-x` example. The source allows extended-real coefficients;
this milestone deliberately restricts all four coefficients to finite rationals.
See the pinned PDF provenance in the [concordance](THESIS_CONCORDANCE.md#repository-source-verification-update-2026-11-07).

`QAffine.ofCoefficients a b` uses endpoints `(a,a+b)`. `QAffine.coefficients`
recovers `(atZero,atOne-atZero)`. Both round trips are proved; the interpreted
value equals `a+b*t` for every real t. `affine_order_iff` proves that ordering
at endpoints 0 and 1 is equivalent to ordering throughout the closed unit
interval, reusing the existing convex-combination argument in the forward
direction and evaluating at endpoints in the reverse direction.

`affine_coefficients_order_iff` states the source condition in coefficient form:
`∀ t ∈ [0,1], a+b*t ≤ c+d*t` iff `a ≤ c ∧ a+b ≤ c+d`.
`linear_coefficients_realizable_iff` proves precisely when a coefficient pair
can be represented by the existing LinearInterval structure, and
`linear_coefficients_contains` identifies its containment inequalities. These
are representation/semantic correspondences plus a derived endpoint
characterization, not a transcription of a separately numbered source proof.
There is no new interval representation or evaluator.

The fresh AffineCorrespondence fixture computes `x-x` for the translated exact
input, obtains coefficient bounds `(0,0)` on both sides, and applies evaluator
soundness to actual expression semantics. It also checks the source's ordinary
constant-interval comparison `[-1,1]`. Controls show that one endpoint is
insufficient, affine order may fail outside `[0,1]`, nonlinear bounds can cross
between ordered endpoints, and uncertain non-singleton self-subtraction does
not generally collapse to zero. A negative slope and a nonconstant interval
with distinct bounds exercise the translation independently of cancellation.

No extended-real/infinite coefficient semantics, rounded coefficient conversion,
optimality, new FP assumptions or general thesis-coverage claim is introduced.

### Constant-interval embedding from thesis section 2.9.4

Graphing inventory F06 and its source-review ledger identify §2.9.4, printed
p.30/repository PDF p.46. The source embeds `<a,b>` as `<a+0*t,b+0*t>`, states
injectivity, and describes a homomorphism when the operators are defined by
interval extension. The finite-rational counterpart here reuses the existing
`LinearInterval.constant`; it does not introduce another representation.

`linear_constant_coefficients` identifies both zero slopes through the proved
coefficient conversion. `linear_constant_hull` supplies a left inverse, from
which `linear_constant_injective` follows. Existing `linear_constant_contains`
already proves exact pointwise membership preservation. The new
`linear_constant_add`, `linear_constant_sub` and `linear_constant_mul` prove
literal equality of the embedded ordinary result and the corresponding linear
operation. For multiplication, constant inputs have zero curvature, so the
existing four-corner construction reduces to the ordinary four-corner bounds.
No sign assumptions on the intervals are needed.

`evalLinear_constant_correspondence` composes those equalities: every successful
`evalLinear` result on constant inputs equals the constant embedding of an
ordinary `eval exactBackend` result. This is success-conditioned and one-way;
ordinary evaluation may succeed for division even though `evalLinear` does not
support division. It does not equate the two evaluators on every expression.

These are a restricted injective embedding and operation-preservation result
for the project's finite rational addition, subtraction and multiplication.
The source's universal interval-extension homomorphism, its extended-real
coefficients and the analogous floating-point embedding are not claimed.
No general optimality or interval-extension construction theorem is added.

The independent ConstantEmbedding fixture exercises mixed-sign bounds, distinct
embedded intervals, and a composed `(x+y)*(x-y)` evaluation with a separate
actual-value witness. Controls show that embedding does not repair ordinary
self-subtraction's dependency loss, unsupported division blocks a converse,
and hull does not commute with multiplication on arbitrary nonconstant linear
bounds. The latter is a precision difference, not a containment failure.

## Quadratic bounds and fixed-chord corrections

The next chapter-ordered bridge starts from graphing inventory F07 and thesis
§2.9.5, printed p.30/PDF p.46 (original PDF visually checked). That section
introduces bounds `p + q*α + r*α²` with extended-real coefficients and requires
well-defined bound functions. It defers demotion algorithms. Here we work with
finite real coefficients, so polynomial evaluation is total; this does not
remove holes from arbitrary expression semantics.

[LinearMultiplication.lean](LinearMultiplication.lean) now states the exact
coefficient polynomial for a product of two rational affine functions
(`affine_product_quadratic`). `quadratic_chord_identity` gives the residual
between a quadratic and its endpoint chord. Reusing `parameter_bubble_bounds`,
`quadratic_chord_lower_iff` and `quadratic_chord_upper_iff` prove:

- subtracting δ from the chord bounds the quadratic below throughout [0,1]
  exactly when `max r 0 / 4 ≤ δ`;
- the same shifted chord bounds it above exactly when `δ ≤ min r 0 / 4`.

Necessity uses the endpoint and midpoint; sufficiency uses the existing
`0 ≤ α*(1-α) ≤ 1/4` proof. These constants explain the existing productBounds
construction. This is optimality **only among constant shifts of that fixed
chord**. It neither selects a best arbitrary affine bound nor contradicts the
source's warning on p.30 that affine demotion has no universally best choice.
It is a derived bridge from the source representation, not a numbered source
proof or a complete quadratic-interval implementation. Extended-real validity,
general quadratic range extraction and the later source demotion algorithms
remain unformalized.

[tests/QuadraticChord.lean](tests/QuadraticChord.lean) checks both curvature
signs, zero curvature, insufficient correction, out-of-domain failure and
incomparable affine lower bounds. It also runs x*x through the existing
interpreter and verifies that its lower bound is attained at the midpoint.
The SIGGRAPH paper §5 supplies an ordinary interval enclosure contract, not
this quadratic coefficient construction; no paper algorithm or FP guarantee
is attributed to these exact-real theorems.

## Two independent affine parameters

Thesis §2.9.6 (printed pp.30–31/PDF pp.46–47) introduces bounds
`p + q*α + r*β`, with α and β varying independently throughout [0,1].
Section 2.9.7 on printed p.31 requires lower ≤ upper at every parameter tuple.
The original PDF was checked, starting from graphing inventory F06/F07 and
its source-review ledger. The existing `RationalAffineForm` is exactly the
finite-rational coefficient fragment of this two-parameter affine expression.
This correspondence does not cover extended-real coefficients or arbitrary k.

[AffineDomainGuards.lean](AffineDomainGuards.lean) proves
`affine_form_square_order_iff`: pointwise ordering throughout the unit square
is equivalent to ordering at all four rational corners. The reusable real
lemma `affine_square_nonnegative_iff` proves the criterion by coefficient sign
and endpoint inequalities. `affineSquareOrdered` computes those four comparisons;
`affine_square_ordered_iff` proves its exact specification. This is a derived
finite validity test for the source condition, not a separately numbered
source theorem. It extends neither the expression language nor interval
arithmetic operators.

`affine_square_fibers_iff` connects the test to the existing `FunctionalBounds`:
acceptance is equivalent to a nonempty value fiber at every point of the
square. This introduces no new interval structure. False means some parameter
fails ordering; it does **not** mean every fiber is empty or that a represented
expression is undefined. Restricting to a smaller external domain may retain
valid fibers even when the whole-square test fails. No such domain is silently
removed or enlarged.

The [TwoParameterBounds fixture](tests/TwoParameterBounds.lean) checks a
mixed-sign pair and an actual expression-value witness using both shared
coordinates. Its controls show that checking even an entire diagonal is
insufficient, three corners can miss the fourth, nonlinear functions invalidate
the criterion, and the result cannot be extrapolated beyond the unit square.
A rejected pair still has a valid fiber, preventing failure-as-absence reasoning.
The SIGGRAPH paper's ordinary interval and domain contracts remain separate:
this is not an implementation of its branch-choice correlation tracking.

## Universal input-domain semantics

The chapter-2 domain milestone in [UniversalDomains.lean](UniversalDomains.lean)
addresses the input-quantifier gap recorded in the source concordance. Thesis
§2.11.1 (printed p.34/PDF p.50) quantifies over every represented input tuple.
The original PDF uses optimistic projection of a three-valued **equivalence**;
the Markdown transcription incorrectly displays a one-way implication.
Section 2.11.2 defines domain endpoints by Boolean infimum and supremum over
inputs. Source navigation used inventory F08/F15 and the existing source ledger;
PDF pp.50–51 were visually checked. SIGGRAPH §8 describes the corresponding
three cases: definitely defined, definitely undefined, or uncertain.

The new contract retains an input witness `w` at parameter `p`:

- every actual result `R p w z` is numerically enclosed;
- definite domain implies a result exists for **that** admitted input;
- existence for that input implies possible domain.

`DomainBounds.Compatible` expresses the last two implications. For an actual
true proposition it is equivalent to possible membership; for false it is
equivalent to lack of definite membership. Thus unknown admits either outcome.
This is a propositional interpretation of the inspected domain assertion,
not a formalization of the entire three-valued operator algebra or of λ.
`PartialEnclosure.UniversalSound` quantifies this contract over `A p w`.
Actual values remain relations; totalized division cannot supply a witness.
The caller chooses A and R. Claiming coverage of a particular source model
requires proving that A includes every represented input tuple and R matches
that model; the generic contract does not establish those facts automatically.

`universal_projects` recovers the old existential `Sound` contract only with
an explicit nonempty represented-input premise at definite parameters. The
converse is false. `exactInputDomain` supplies a logical reference envelope:
possible means some admitted input has a result; definite means the input
fiber is nonempty and every admitted input has a result. On nonempty fibers,
`exact_input_domain_precision` proves that this envelope has at least as much
information as every universally sound domain. This captures the Boolean
extremum interpretation without building numeric domain demotions. It is not
an executable inference algorithm. For empty input fibers the chosen envelope
is definitely absent; no equivalence with the source's empty-infimum convention
is claimed.

Composition uses the same `w` on both sides of addition. It must not combine
independently projected input witnesses. External restriction preserves its
predicate exactly. `evalGuarded_universal_sound` integrates the contract with
the existing guarded evaluator: success guarantees a result for every enclosed
coordinate pair at a certified parameter. Enclosure premises are local to the
external domain and [0,1]. Every division still relies on the existing proven
nonzero guard; failure remains unknown.

The [UniversalDomains fixture](tests/UniversalDomains.lean) proves that 1/x
with possible inputs 0 and 1 satisfies the old existential contract but fails
universal definite definedness. Its exact envelope is uncertain. Other controls
cover vacuous empty fibers and incompatible input witnesses. Positive examples
compose the corrected envelope and certify guarded reciprocal evaluation over
all x in [1,2], retaining an external hole and projecting only after proving
nonempty inputs.

This is one integrated semantic layer, not a replacement of existing APIs.
General symbolic intervals (§2.9.8), two-stage floating conversion (§2.10),
extended-real/λ value arithmetic, executable exact domains, representation-specific
domain demotions, and the full property calculus (§2.12) remain open. The
existing conditional FP contracts are unchanged. Universal domain validity
alone does not prove continuity, roots, or compatibility of paper branch labels.

## Square root with domain tracking

[SquareRootDomains.lean](SquareRootDomains.lean) implements an exact-real
counterpart of the three-branch SquareRoot algorithm in SIGGRAPH §8, PDF p.4.
Thesis §2.11.5, printed p.36/PDF p.52, gives related examples. Both original
pages were visually checked via the repository copies, using inventory F08/F15
and the existing source ledger. The paper is the precise branch specification:

- upper < 0: preserve the unused numeric payload and mark the result absent;
- lower ≥ 0 on an ordered range: take square roots of both endpoints and retain
  the incoming domain information;
- lower < 0 ≤ upper: return [0, sqrt(upper)], clear definite membership and retain
  possible membership.

The endpoint operations here are exact `Real.sqrt`, not the paper's directed
floating-point square roots. Bounds and comparisons are real and the definition
is noncomputable. This verifies the domain rule and mathematical enclosure,
not a machine implementation or an executable rational enclosure algorithm.
No square-root syntax is added to Expr and no FP assumptions are introduced.

`SqrtValues` explicitly requires a nonnegative input. Mathlib's total
`sqrt(-1)=0` cannot establish a value of this partial operation.
`sqrt_universal_sound` proves enclosure and domain compatibility for every
admitted input, using the same witness. The branch theorems state the exact
numeric/domain results. `sqrt_negative_absent` rules out actual results on
entirely negative ranges. The nonnegative branch theorem states the endpoint
ordering premise explicitly; soundness itself also permits inactive or
collapsing payloads when there are no corresponding values.

The theorem connects to existing guarded evaluation, repeated square roots,
same-input addition, and external restriction via UniversalSound. External
holes remain absent. Loose mixed-sign bounds may remain uncertain even when
the actual admitted input set is nonnegative; no completeness claim is made.

**Source discrepancy:** the original thesis PDF's final decorated example on
p.36 prints input [-1,-1] but output [0,1] with uncertain domain, whereas the
preceding ordinary example uses [-1,1]. The latter result is loose but sound: uncertain domain permits undefinedness,
and value enclosure is vacuous because no square-root value exists on [-1,-1].
A typo is plausible, but the printed assertion is not refuted. It differs from
the precise paper algorithm, which certifies absence. The mixed-range test uses
[-1,1], justified independently by
the paper's algorithm. The thesis's negative example uses an infinite payload;
the paper preserves the original payload. Our finite-real model follows the
paper; the absent-domain conclusion agrees, but the payload is not identical.

[SquareRootDomains tests](tests/SquareRootDomains.lean) check the negative,
mixed, nonnegative and zero-boundary cases; totalization and conservative
uncertainty controls; nested composition; an external hole; and the guarded
interpreter bridge. Neither continuity nor root existence follows merely from
an uncertain domain flag.

## Property composition: verified direction and source gap

The next chapter-2 property milestone encounters a specification obstruction.
The literal unary continuity specialization of thesis §2.12's printed weak
checkability direction fails: a constant outer function can hide a discontinuous
child. [PropertyComposition.lean](tests/PropertyComposition.lean) independently
proves that obstruction and the valid sufficient composition direction. It uses
total real functions, true leaf flags and the existing intermediate-value
foundation; no partiality or floating-point issue is involved.

The [concordance analysis](THESIS_CONCORDANCE.md#property-tracking-specification-obstruction)
records exact pages, specialization and proof scope. SIGGRAPH §10's conservative
addition continuity flags do not require the false converse. A generic property
API is deferred until the intended specification is resolved; the existing
specific continuity results are not weakened or reinterpreted. This review adds
no production abstraction and makes no claim about the complete local-constancy
calculus or the paper's floor rule.

## Numerical nonzero-domain certificates

`NonzeroDomains.lean` connects functional numerical bounds with the existing
`DomainBounds` predicates. `PartialEnclosure.nonzero` preserves the value bounds
and filters the actual relation by `z ≠ 0`. Definite membership requires both
input definite membership and strict numerical exclusion of zero. Possible
membership requires input possible membership and bounds that are not both zero.
`nonzero_sound` proves the full existing enclosure contract for the filtered
relation, including existence; it does not infer a witness merely from bounds.

`quotientDomain` intersects the numerator domain with this filtered denominator
domain. Its two theorems bound the domain of the existing `QuotientValues`
relation without claiming a finite quotient range. Witnesses remain independent,
as in that relation; this is not a shared-witness cancellation rule.

The fresh client `tests/NonzeroDomains.lean` derives the exact definite domain of
`1 / (t - 1/2)` on `[0,1]`, excludes the pole from possible membership, and checks
an independent equivalence with the existing partial `Value` semantics. The
whole-hull reciprocal remains unknown. Identical `[-1,1]` bounds for zero-only
and one-only relations demonstrate necessary uncertainty. Positive bounds with
an absent input domain cannot create values.

This is a bounded bridge toward Tupper's [domain descriptions (§2.11.3)](https://www.dgp.toronto.edu/~mooncake/thesis/node49.html)
and [partial functions (§3.3.16)](https://www.dgp.toronto.edu/~mooncake/thesis/node122.html):
value information helps describe the domain of a partial operation. It uses our
existing predicate interpretation, not the thesis's full numerical encoding of
domain descriptors. Predicates over arbitrary real parameters are semantic,
not an executable rational query classifier. No new evaluator, finite enclosure
for a pole, continuity certificate, IEEE 754 assumption, or implementation
correctness claim is introduced.
