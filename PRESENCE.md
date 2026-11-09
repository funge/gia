# certified presence along a segment

The presence result complements zero exclusion: it proves that a box contains
at least one **defined zero** of an expression. It does not mean that every point
in the box satisfies the equation, and it does not locate or count all roots.

## geometric and mathematical result

`segment a b t = (1-t)*a + t*b` parameterizes each coordinate for `0 ≤ t ≤ 1`.
`segment_mem` proves that two endpoints in a closed interval give an entire
segment in that interval. Applying it in both coordinates keeps the segment
inside a rectangular box.

`certified_curve_zero` uses mathlib's intermediate value theorem. For a continuous
real function `g` on `[0,1]`, if endpoint enclosures `L` and `U` satisfy

```text
L.Contains (g 0)    L.hi ≤ 0
U.Contains (g 1)    0 ≤ U.lo
```

then some parameter `t ∈ [0,1]` satisfies `g t = 0`. The comparisons are deliberately
non-strict: a root at an endpoint also certifies presence. The endpoint bounds
must certify opposite sides, not merely contain zero.

`segment_presence` adds a semantic witness `Value` at every point of the segment
and concludes that the box contains a defined root. At this generic level,
continuity and the semantic witness are explicit premises. Endpoint signs alone
are insufficient for partial functions.

## continuity and domain obligations discharged by evaluation

`eval_curve_continuous` proves that successful interval evaluation over a box
certifies both continuity and definedness of the expression along any continuous
curve contained in that box. It covers all current expression constructors,
including division. In the division case the successful denominator guard,
combined with enclosure, proves a nonzero denominator at every curve point.
That proof is supplied both to continuity of division and to the partial
`Value.div` rule.

`Expr.realValue` is a total mathematical expression function for stating the
continuity theorem. It is paired with a proved `Value` witness; its totalized
division-by-zero behavior is never accepted as a defined semantic value.
`value_eq_realValue` connects defined values with that function.

`evaluator_segment_presence` packages the result with rational endpoints. Its
premises are:

- a sound interval backend;
- both chosen endpoints lie in the input box;
- whole-box evaluation succeeds;
- singleton endpoint evaluations succeed and certify the two signs above.

**It derives continuity and definedness, rather than assuming them.** The exact
backend's soundness is already proved. A directed-rounding backend uses only the
existing explicit successful-conversion enclosure contracts. No extra IEEE 754
assumptions, exceptional-value model, or hardware-correctness claim is added.
Continuity is proved for the underlying real expression, not for the rounded
computational output. Rounding functions need not be continuous; they supply
certified enclosures at the required evaluations.

The whole-box guard is intentionally conservative. It may reject a box even if
the chosen segment itself avoids every undefined point. Such rejection is not
evidence that a root is absent. A narrower box or another certificate may help;
this milestone does not implement subdivision or automatic segment search.

## proof-checked examples

`PresenceExamples.lean` checks:

- `x*x - 2` on `[1,2] × {0}`: whole-box range `[-1,2]`, endpoint values `-1` and
  `2`, and a proved defined root in the box;
- `(x*x - 2)/(x+1)` on the same box: range `[-1/2,1]`, endpoint values `-1/2`
  and `2/3`, and a proved defined root, with denominator safety established;
- `1/x` on `[-1,1] × {0}`: opposite endpoint signs, failed whole-box guard, and
  a proof that no defined point is a root. This is a counterexample to using
  endpoint sign changes without continuity/domain certification.

Finite interval computations use `decide +kernel`. Existence results use the
proved intermediate value theorem, not a native numerical root finder. They do
not assume that zero belongs to the function's image merely because an interval
enclosure contains zero.

## verification and limits

The Lean/mathlib pins are unchanged. Additional topology modules from the pinned
mathlib are built locally. Run `lake build` and `lake env lean Audit.lean` in
the repository root. `Audit.lean` includes all public presence theorems and
examples. Observed command results are recorded in `VALIDATION.md`.

This remains an abstract proof over real values with rational enclosures. No
renderer, screen-coordinate map, parser, bit-level FP operation, or implementation
is verified. The application build and release requirements remain independent.

## executable certificate checker

`PresenceChecker.lean` adds `certifySegment`, a Boolean checker for a supplied
pair of rational endpoints. It checks box membership, whole-box evaluation,
both singleton endpoint evaluations, and certified endpoint signs in either
orientation. Failure of any check means uncertified, not proof of absence.
The proof `certifySegment_sound` derives defined-root existence whenever the
checker returns true, under the same backend soundness contract.

`classifyWithSegment` combines the existing zero-exclusion classifier and this
presence checker into `BoxResult.empty`, `.present`, or `.unknown`:

- `empty` proves there is no defined zero in the box;
- `present` proves at least one defined zero exists in the box;
- `unknown` makes neither claim, including about definedness.

Separate soundness theorems cover the two decisive results.
`empty_disallows_presence` also proves that the independent empty classifier
and presence checker cannot contradict one another for a sound backend.

`PresenceCheckerExamples.lean` contains ten kernel-checked controls: ordinary
and reversed sign certificates, a rational-function presence result, an empty
positive constant, the pole rejection, an out-of-box endpoint rejection,
endpoint and degenerate-segment roots, lack of certified signs, and failed finite
conversion. Non-strict certificates deliberately accept zero at an endpoint.

This checks a supplied segment; it does not discover segments, subdivide boxes,
guarantee detection of every root, or optimize repeated interval evaluation.
The new API adds no FP assumptions. The exact backend is unconditional; a rounded
backend still requires the existing successful-conversion enclosure contracts.

The subsequent [finite-search milestone](SEGMENT_SEARCH.md) supplies a bounded
candidate-selection layer over this checker, with soundness and exact
finite-list success/failure characterizations. The checker itself remains the
same supplied-segment primitive.
