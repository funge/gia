# Mixed affine endpoints with explicit boundaries

[MixedEndpoints.lean](MixedEndpoints.lean) proves an exact finite conversion from
mixed coefficient carriers to the existing guarded rational affine pieces. It
connects [finite guarded pieces](FINITE_GUARD_PIECES.md) and
[coefficient witnesses](COEFFICIENT_WITNESSES.md) without replacing the latter's
joint witness by independent choices.

## Source scope and explicit model

Tupper §2.13, printed p.39 /
[PDF p.55](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=55), provides
existential piece membership at a shared parameter. Section 2.14, printed p.40 /
[PDF p.56](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=56), permits
explicit coefficient types and equality restrictions, and gives the Hansen
variant. Those source pages were visually checked in the preceding milestones.
They do not define the concrete boundary-flag record or a general convention
for persistent real choices. Both conventions below are **our explicit model**,
not unstated claims about the source.

A `Band` has integer lower intercept and rational lower slope, rational upper
intercept and integer upper slope, two strictness flags and existing finite
rational parameter guards. Thus its endpoints use genuinely different carriers:

```
lower(t) = (integer : Real) + (rational : Real) * t
upper(t) = (rational : Real) + (integer : Real) * t
```

All endpoint values here are finite reals. No extended endpoint, λ, NaN, infinity
or native decoding behavior is introduced. Supplied endpoints need not be ordered:
contradictory or reversed bounds denote an empty fiber, rather than being admitted
to an ordered `LinearInterval` constructor.

## Exact conversion and witnesses

`Band.encode` converts integer coefficients exactly into rationals, uses existing
`QAffine.ofCoefficients`, and retains both flags and all guards. The target is
`FiniteGuardPieces.band`, followed by its already-proved compiler. Independent
source semantics use the displayed mixed real expressions.

`lower_value` and `upper_value` prove endpoint equality. `encode_exact` then
proves equality of the whole represented set at every real parameter:

```
pieces b.encode.compile t = b.denote t
```

`rational_test_exact` connects the actual target membership test to source
semantics on rational inputs. `endpoint_witnesses` instantiates #44's exact
heterogeneous decoding result for each endpoint's fixed coefficient pair, over
any supplied use domain. `family_exact` reuses the existing interval-set
re-encoding theorem for unions of bands.

`joint_exact` additionally proves exact correspondence with **one band witness
outside all parameter uses** on an external set T. The target witness is chosen
from the image of the original admissible band set, preserving any relation
between its lower/upper coefficients, guards and flags. It does not replace
that image by a Cartesian product or reselect a band at each use. Restricting
the use set makes no claim about behavior outside it.

`fiber_nonempty` gives the complete boundary criterion:

```
guards hold AND
  (lower < upper OR
   (lower = upper AND both boundaries are closed))
```

This proves empty-fiber behavior rather than assuming interval order or
nonemptiness. `empty_fiber` preserves emptiness under compilation. No rounding or
lossy enclosure occurs in this conversion.

## Controls and remaining scope

[Fixtures](tests/MixedEndpoints.lean) use lower `t/2` (open) and upper `3/2−t`
(closed). Their fibers are nonempty exactly when `t<1`; equal endpoints at 1
and reversed endpoints at 2 are empty. Closing the lower endpoint at 1 admits
1/2, so dropping the flag would change denotation. Tests also cover a strict
guard boundary, interior membership, and the coefficient-witness bridge.
A two-constant-band example has individually admitted samples 0 and 1 but no
single band for both; source and compiled joint semantics both reject it.

This is a concrete finite mixed conversion, not the general heterogeneous
endpoint calculus. It does not encode irrational coefficients, extended/undefined
endpoint carriers, general symbolic families or the full Hansen variant. The
next high-payoff source correspondence is the printed multi-parameter
interval-coefficient Hansen family, reusing existing shared-vector affine results
while stating its coefficient-choice relation and parameter restrictions exactly.
Source ambiguity about persistent choices remains separate from that proof task.

Use the pinned `./check.sh` gate. All new declarations and fixtures participate
in the enforced axiom allowlist. No new project axiom, floating-point assumption,
trusted contract, native code, runtime default or performance claim is introduced.
Chapter 2 remains incomplete.
