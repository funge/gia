# Finite guarded rational pieces

[FiniteGuardPieces.lean](FiniteGuardPieces.lean) gives an exact finite compiler
for unions and intersections of rational affine constraints at one shared real
parameter. It adds a useful finitely described subclass beyond finite point
tables, without hiding an arbitrary predicate inside a supposedly finite code.

## Source scope

The original thesis §2.13, printed p.39 /
[PDF p.55](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=55), defines
interval-set membership existentially over pieces and states inclusion at a
shared parameter. Its perfect demotion construction uses an infinite point
collection; the subsequent finite descriptions are not supplied with a general
guard grammar. Section 2.13.2 explicitly assumes finitely many returned intervals
for its bumpy-function criterion. Section 2.14, printed p.40 /
[PDF p.56](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=56), makes
coefficient and free-variable types explicit.

These pages were checked visually against the PDF. The syntax below is a
**chosen restricted implementation**, not syntax printed by Tupper. Strict and
closed rational boundaries are explicit choices here, not a claim that §2.14
specifies every open-endpoint variant. No arbitrary-function representability,
perfect finite demotion or general bumpy-function theorem follows.

## Finite code and exact correspondence

An `Atom` has three rational coefficients and a strictness bit. It means
`p*t + q*z + c < 0` or `≤ 0`. A `Piece` is a finite conjunction of atoms;
`pieces` reuses [IntervalSetDenotation](IntervalSetDenotation.lean)'s existential
piece interpretation. `piece_between` proves each output fiber is order-convex,
including empty fibers; an unconstrained piece can be unbounded. Infinite bound
symbols and exceptional arithmetic values are not coefficients.

`Description` contains empty, cell, union and intersection. Its recursive
semantics are independent of compilation. The executable `compile` concatenates
unions and distributes intersections by pairing pieces and concatenating their
constraints. The principal theorem is

```
∀ D t, pieces D.compile t = D.denote t
```

Both sides use exactly the same `t` and output `z`; intersection requires both
constituent witnesses at that pair. No range projection or independent parameter
selection occurs. This is equality of represented sets, not merely enclosure.
Empty descriptions, contradictory pieces and duplicate constraints need no
special normalization to preserve their meaning.

`band` uses existing rational endpoint-basis `QAffine` bounds. Parameter guards
have output coefficient zero by construction. `guard_exact`, `lower_exact`,
`upper_exact` and `band_exact` prove that the generated constraints express
exactly the specified domain guard and open/closed endpoint comparisons.
Reversed endpoints are allowed as descriptions and denote empty fibers where
inconsistent; they are not smuggled into an ordered `LinearInterval` constructor.
Union/intersection can produce piecewise-affine effective endpoint bounds without
forcing them into a single affine form.

`compiled_test_exact` proves the executable rational `test` returns true iff
the promoted rational pair belongs to the original real denotation. This is a
membership decision at a supplied rational pair, not a real satisfiability solver
or quantifier elimination procedure. No real oracle is assumed. `restricted_exact`
preserves an external domain at the same parameter. `empty_fiber` preserves holes.
`tagged_exact` reuses the existing tagged payload-conversion interface: exact
re-encoding changes neither finite denotation nor exceptional tag membership.
It does not define new exceptional arithmetic or claim an arbitrary input payload
is equal to the chosen description.

## Checked controls and limits

[Fixtures](tests/FiniteGuardPieces.lean) cover closed touching bands (singleton
intersection), open touching bands (empty intersection), reversed bounds,
zero-width open bands, a guarded split whose left piece owns the boundary,
nonempty holes, and distributed composition. The shared-witness counterexample
uses `z=t` and `z=1-t`: zero is attained in each projected range at different
parameters, but their compiled intersection rejects `(t,z)=(0,0)` and accepts
`(1/2,1/2)`. Empty outer piece lists are distinguished from unconstrained cells.

All atoms and descriptions contain finite rational data, rather than arbitrary
predicate/function fields. The compiler does not decide piece emptiness, simplify
constraints, minimize piece counts or generate descriptions for arbitrary sets.
Distribution may grow exponentially. No multidimensional, nonlinear, exceptional
value, continuity/definedness flag or universal finite-representability claim is
made. Full Chapter 2 completion remains open.

Use the pinned `./check.sh` gate. Proofs and fixtures participate in the enforced
axiom allowlist. No new project axiom, floating-point premise, native/C/FFI change,
hardware runtime path or performance claim is introduced.
