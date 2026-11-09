# Bounded certificates over parameter cells

The original supplied-cell layer adds a bounded client of the existing evalGuarded interpreter. It does not
copy its arithmetic recursion, change either conditional interpreter, or add a
subdivision algorithm. It addresses the consolidation's missing producer of
local definedness/continuity evidence for a supplied finite cell cover.

`checkCells X Y e fuel cells` returns a CellReport with verdict `certified` or
`unknown` and a checked-call counter. An empty list is certified with zero calls.
For a nonempty list, zero fuel returns unknown without calling the evaluator.
Otherwise it calls evalGuarded on the coordinates reparameterized to the first
cell. A failed enclosure stops immediately with unknown. A successful enclosure
continues with one less fuel and increments the counter once.

The cost model is explicit: one unit is one attempted top-level evalGuarded call.
The instrumented counter is proved at most the supplied fuel for every result.
A certified result has checked exactly the list length, so that length is also
at most the fuel. This is not a bound on elapsed time, peak memory, rational bit
complexity, arithmetic operations, expression depth, or the cost of a single
call. There is no preemption inside evalGuarded. Coordinate reparameterization
and interpreter execution are part of an attempt, not separately metered.

Certification of a list means every listed cell passed. It does not mean the
list covers the intended domain. `checked_cover_defined` separately requires
the existing ParameterCover proof, uses its pointwise pullback to find a checked
cell, and invokes the existing local definedness theorem. Thus every enclosed
actual coordinate pair at a unit parameter has an Expr/Value witness, including
shared cell boundaries and degenerate cells supported by ParameterCell.

`checked_cover_continuous` derives continuity for the existing arithmetic Expr
language from that definedness and supplied continuous coordinate functions.
It also supplies actual canonical Value witnesses over the entire path. It does
not infer continuity for ConditionalExpr. Nor does it establish membership in an
external partial coordinate environment: any such membership remains a separate
obligation. Coverage, coordinate enclosure, and coordinate continuity are still
supplied proofs; automatic search for them is not implemented.

This follows the separation between Tupper's
[interval function domains (§2.11)](https://www.dgp.toronto.edu/~mooncake/thesis/node46.html)
and [continuity-based testing (§4.2.6)](https://www.dgp.toronto.edu/~mooncake/thesis/node156.html).
The checker is a bounded sufficient method for exact rational enclosures, not a
complete decision procedure for domains or continuity.

The independent tests/CellCertificates.lean fixture imports core modules only:

- Whole-interval evaluation of (t-1/3)/(t*t+1/10) is unknown. Two half-cell checks
  certify it with counter 2. Existing split coverage, derived continuity and
  endpoint signs then establish an actual semantic root.
- Fuel one returns unknown with counter 1 even though that actual root exists.
  Fuel zero returns unknown without an evaluator call.
- A pole at the shared midpoint stops the half-cell check after its first call,
  despite a larger budget. A separate theorem rejects a midpoint Value witness.
- Two cells leaving a gap around the pole both pass, but their list is proved
  not to cover the unit interval. Likewise, the empty list passes its vacuous
  local check but cannot supply a coverage proof.

The new fixture is registered for fresh-process elaboration and namespace audit,
and its transitive dependencies are checked to exclude milestone examples.
No FP assumptions, new expression syntax, application dependency, hosted CI,
maximal-domain inference, or whole-program resource guarantee is introduced.

## Automatic coverage front end

`certifyCoveredCells` is the combined entry point when the caller has a cell list
but no coverage proof. It first checks geometry, then delegates unchanged to
checkCells. Geometry failure returns unknown with zero evaluator attempts.
The original checkCells API remains available for callers with a separately
proved ParameterCover, including valid covers rejected by the conservative
geometric checker.

`cellsCoverFrom` scans the supplied list from covered endpoint 0. Each next cell
must start at or before the current endpoint. A cell reaching 1 finishes the
geometric certificate; otherwise the endpoint becomes the maximum of its old
value and the cell's upper endpoint. This handles shared closed boundaries,
overlaps and nested cells without moving the endpoint backwards. An empty list
or a failed connection is unknown. The implementation does not sort the list.
A proof converts successful checking to the existing ParameterCover predicate.

The combined definedness and continuity consumers no longer require a supplied
coverage proof. Continuous coordinate functions, their enclosing bounds, and
any external partial-coordinate-environment membership remain separate as above.
The theorem applies to arithmetic Expr, not arbitrary conditional continuity.

The checker is sufficient, not complete: reversed half-cells are a genuine cover
but are rejected in their supplied order. A geometric success may also ignore a
redundant tail once endpoint 1 is reached; arithmetic checking deliberately still
checks every supplied cell. A redundant cell can therefore exhaust fuel. No
minimal-cover extraction or optimal list policy is claimed.

The evaluator-call bound is preserved by the wrapper. Geometric comparisons are
not charged to that counter and may be performed even with zero evaluator fuel.
This remains an evaluator-attempt budget, not a whole-program work or time cap.

The core-only CellCertificates fixture now derives its actual-root theorem via
the combined checker, without passing a hand-written coverage proof to that
path. New controls reject gapped/empty lists before evaluation, retain pole and
exhaustion failures, accept a nested-overlap chain, and explicitly exhibit a
valid reversed cover whose automatic result is unknown. The earlier supplied-
coverage checks are retained to test both interfaces and their distinct scope.

## Adaptive cell production

`planAdaptiveCells X Y e depth C` attempts the existing single-cell checker.
Success retains C. Failure with positive depth splits C at its rational midpoint
and recursively plans both closed halves, in left-to-right order. Failure at
zero depth retains the unresolved cell. No leaf is discarded. The geometry
reuses Subdivision's midpoint operations and coverage lemmas; there is no second
arithmetic interpreter or new splitting convention.

The producer proves both directions of geometric containment: every parent
point belongs to a produced cell, and every produced cell stays in its parent.
In particular, starting from ParameterCell.unit produces a ParameterCover even
when arithmetic checks fail or depth is exhausted. Closed shared boundaries
are retained. A single-cell attempt is proved to cost exactly one existing
checker call. Planning uses at most B(depth) attempts, where B(0)=1 and
B(d+1)=1+B(d)+B(d).

`certifyAdaptiveCells X Y e depth fuel` plans from the unit cell and passes the
result to certifyCoveredCells. It reports both planning and validation calls,
including rechecks; the total is proved at most B(depth)+fuel. Revalidation
intentionally reuses the existing trusted proof interface instead of introducing
cached certificates. No completeness theorem for the ordered coverage scan on
all generated lists is claimed. Any rejected geometry, arithmetic failure, or
validation exhaustion yields unknown, never an absence certificate.

The fresh client now derives its actual root without supplying cells: for
(t-1/3)/(t*t+1/10), depth one generates two cells using three attempts, then two
validation calls certify definedness and continuity. Endpoint signs establish
an actual Value root. Depth zero keeps the unresolved root cell and returns
unknown; insufficient validation fuel also returns unknown despite that root.
A constant stops at the root even with depth three. The midpoint pole yields
unknown, and a semantic counterexample proves that *no* depth/fuel pair can
certify it. These controls exercise computed reports as well as theorem clients.

This is a bounded sufficient refinement strategy for the domain/continuity
separation described above, not a claim to implement Tupper's complete graphing
algorithm or generalized interval domain representation. Coordinates must still
be enclosed, and continuity of coordinate functions remains supplied. External
partial-environment membership is not inferred. Geometry work, rational bit
complexity, memory and elapsed time remain outside the evaluator-call bound.
There are no additional FP assumptions or application build changes.
