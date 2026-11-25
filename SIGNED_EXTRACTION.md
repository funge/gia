# Signed continued-fraction coverage and extraction

This milestone closes the mathematical representation-coverage gap in Tupper
§2.15.7, printed p.43 / [PDF p.59](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=59).
The original page image was rechecked. It permits signed integral coefficients,
requires tail magnitudes at least 2 before the last term, requires the next term
to have the same sign whenever that magnitude is 2, and excludes a finite last
term of `-2`. It mentions an interval variant of Euclid's algorithm but does not
give its extraction or tie rules on this page.

## Explicit construction, not an inferred source convention

[SignedExtraction](SignedExtraction.lean) chooses
`digit x = ceil(x - 1/2)`. This is nearest-integer selection with half-integer
ties toward the smaller integer, consistently for both signs. It is an explicit
mathematical choice for **this construction**, not an assertion of authorial
intent, canonical uniqueness, or a hardware rounding assumption.

The residual `x - digit x` lies in `(-1/2,1/2]`. A zero residual terminates;
otherwise the next complete quotient is its reciprocal. Consequently every
actual tail quotient is either at least 2 or strictly below -2. In particular,
a terminal integer tail cannot be -2. When a tail digit has magnitude 2,
the next digit has the same sign. These conclusions are proved, not assumed.

`coverage` proves that **every real value** has either:

- a generated finite expansion satisfying the existing `RedundantCF.FiniteTail`
  restrictions and decoding exactly to the original real; or
- a generated infinite stream satisfying `RedundantCF.Admissible` and
  `RedundantCF.Represents` for the original real.

The head is unrestricted, including negative integers and zero. For an integer,
the tail is empty, so head -2 does not violate the last-tail rule.

## Recovery and partial definedness

The same coefficient stream from the same exact orbit is used at every
truncation. The infinite proof reuses #65's single-step contraction and
fractional-tail invariant. `observation_error` bounds the error by `(4/9)^k`
and `infinite_recovers` proves convergence back to the input value, rather than
merely proving convergence to some unspecified real.

For the finite branch, `FirstStop` records a zero residual and nonzero earlier
residuals. `finite_admissible` proves the exact existing finite-tail predicate;
`finite_recovers` uses the existing rational finite decoder. The separate
`finite_divisors_nonzero` proves all actual reciprocal suffix divisors are
nonzero. Thus totalized field division at zero is not being used to establish
partial-operation definedness. Arbitrary finite syntax permitted by the printed
conditions may still need definedness checks; the earlier terminal-zero control
is not erased by proving this well-defined construction.

## Executable rationals and termination

The definitions are shared over ordered fields with a floor operation. Explicit
`digit_cast`, `residual_cast`, `next_cast`, `orbit_cast` and `coeff_cast` lemmas
prove agreement between rational execution and the real interpretation. They
compare actual rational results cast into the reals, not two independently
assumed implementations.

`next_den_lt` proves strict descent of the reduced rational denominator on every
nonterminal step. For `q = p/d`, the integer remainder numerator is
`m = p - digit(q)*d`; the residual bound gives `|m| < d`, while the denominator
of the reciprocal divides down from `|m|`. `rational_stops` supplies a stopping
index strictly below the **original denominator**.

`findStop` is an ordinary fuel-bounded executable search, not a noncomputable
`Nat.find` wrapper. `extract q` uses fuel `q.den`. `rational_extracts` proves it
always succeeds, its finite tail obeys the printed restrictions, and the exact
rational decoder returns `q`. Insufficient user-supplied fuel to `findStop`
returns `none`, not a claim that the value has no expansion.

`stops_iff_rational` and `never_stops_iff_irrational` characterize termination of
**this generated orbit**. These are not uniqueness or canonical-recovery claims
for all arbitrary signed presentations. The finite/infinite case split for an
arbitrary real is mathematical and uses classical logic; it is not a computable
rationality test or an exact-real input oracle.

## Controls

[Fixtures](tests/SignedExtraction.lean) are kernel checked and executable:

| Input | Generated head and tail |
| --- | --- |
| `1/2` | `(0,[2])` |
| `-1/2` | `(-1,[2])` |
| `2/3` | `(1,[-3])` |
| `-2/3` | `(-1,[3])` |
| `5/12` | `(0,[2,2,2])` |
| `-5/12` | `(0,[-2,-3,2])` |
| `-2` | `(-2,[])` |

The opposite half-integer tie choice at `1/2` gives `[1;-2]`: it has the right
rational value but violates the printed terminal restriction. This checks
representation validity separately from numerical equality. Other controls
include zero, insufficient fuel, actual denominator descent, the rational/real
orbit bridge, and an infinite representation of `sqrt 2`.

## Remaining source correspondence and verification

This proves source-compatible coverage and a terminating **exact rational**
constructor. It is not a transcription of the unspecified interval Euclidean
algorithm, an online delay theorem, or a uniqueness proof for redundant syntax.
No arbitrary-real nearest digit is promised computable from plain interval
names; the [finite-query limitation](FINITE_QUERY.md) is compatible with this
mathematical construction. A genuinely interval-driven extraction procedure
would need its own precise operational specification and proof.

The [section ledger](SECTION215_LEDGER.md) and [closeout matrix](CHAPTER2_CLOSEOUT.md)
now separate the closed coverage/termination obligations from that remaining
algorithmic correspondence. Chapter 2 is not declared complete.

Run `./check.sh`; focused checks are `lake build SignedExtraction` followed by
`lake env lean tests/SignedExtraction.lean`. No project axioms, floating-point
premises, native/C/default changes or dependencies are introduced. Rational
execution here is a representation proof tool, not a substitute for the
project's hardware interval-arithmetic path.
