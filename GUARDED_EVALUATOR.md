# Integrated guarded expression interpretation

`GuardedEvaluator.lean` connects the standalone reciprocal/division proofs to a
usable shared-parameter expression interpreter and the domain-local contracts.
The old polynomial interpreter remains unchanged and its successful results are
proved to be preserved exactly by the new interpreter.

## Integration boundaries

| Interface | Arithmetic | Definedness conclusion |
| --- | --- | --- |
| `evalLinear` | Polynomial fragment | Success implies a `Value` at any real coordinates |
| `LinearInterval.div?` | Standalone guarded quotient | Success proves nonzero denominator values inside certified enclosures |
| `evalGuarded` | Compositional arithmetic including guarded division | Success implies a `Value` only at certified parameters and enclosed coordinates |
| `evalGuarded_relational_sound` | Same evaluator with partial coordinate relations | Full output contract under intersected coordinate domains |
| `evalGuarded_local_sound` | Same evaluator with domain-local function representatives | Full output contract restricted to the supplied domain |

This distinction matters: the polynomial definedness theorem is not generalized
by dropping the coordinate/enclosure premises when division becomes available.
A checked counterexample establishes that `1/(1+x)` succeeds for `x(t)=t` on
`[0,1]` but has no partial-semantic value at `x=-1`.

## Proof obligations

`evalGuarded_sound` proves inclusion for every existing `Value` at a shared
parameter in `[0,1]` where the input models enclose the actual coordinates.
`evalGuarded_defined` separately constructs a `Value` from success under those
same local premises. At each division it first constructs the denominator's
semantic value, applies soundness to enclose it, and uses the successful hull
guard to prove it nonzero before applying `Value.div`. Thus definedness is
proved rather than assumed, and Lean's totalized division never supplies a value
at a pole.

`evalGuarded_extends_polynomial` proves equality of output intervals for every
successful `evalLinear` invocation. The two domain bridges then establish all
three obligations of the existing `PartialEnclosure.Sound` contract. They retain
#20's strict complete-coordinate environment semantics: both bindings must
exist, and separate unary coordinate relations do not encode arbitrary joint
constraints. No minimal free-variable domain inference is claimed.

A failed child evaluation or denominator guard returns `none` and propagates
upward. Zero multiplication does not bypass a failed division. `none` still means
unknown, not undefined: a box touching a pole may contain defined interior
values, which an example constructs independently.

## Validation beyond positive examples

`GuardedEvaluatorExamples.lean` checks:

- `1/(1+x)` and a nested reciprocal through the actual new interpreter;
- retention of numerator dependence in `x/(1+x)`;
- safe constant division, boundary poles, an exactly zero `x-x` denominator,
  and zero times a pole;
- a quotient value constructed directly with `Value` constructors, then enclosed
  using soundness (not obtained from the interpreter's existence theorem);
- a defined interior value despite an inconclusive whole-box guard;
- the counterexample to unrestricted/global definedness;
- exact compatibility with the earlier complementary-product example;
- domain-local function contracts and a punctured partial coordinate environment,
  with absence at the excluded parameter and existence inside the domain.

The axiom enforcement's independent-process negative controls are also rerun for
this integration milestone. Concrete coefficient calculations use kernel
reduction, and all public theorems are named audit targets in addition to the
namespace enforcement. See [VALIDATION.md](VALIDATION.md) for exact results.

## Thesis scope and remaining gaps

This composes the shared-parameter representation of Tupper
[§2.9.3](https://www.dgp.toronto.edu/~mooncake/thesis/node39.html), the domain
separation of [§2.11](https://www.dgp.toronto.edu/~mooncake/thesis/node46.html),
and the partial arithmetic theme of
[§3.3.16](https://www.dgp.toronto.edu/~mooncake/thesis/node122.html), using the
previously proved bounded multiplication and reciprocal policies. It is not a
transcription of the full generalized arithmetic or domain-description system.

Reciprocal uses an ordinary hull and forgets denominator dependence. Domain
predicates do not sharpen or bypass that numerical guard, so even an everywhere-
defined expression on a supplied restricted domain may remain unknown. There is
no completeness, optimality, continuity, graph-presence, automatic maximal-domain,
or machine-implementation theorem. FP assumptions and IEEE 754 scope are
unchanged. The native build, v1.0 release, and hosted CI remain independent.
