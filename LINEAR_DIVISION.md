# Guarded linear reciprocal and division

`LinearDivision.lean` adds a conservative exact-rational fallback for partial
arithmetic. `J.recip?` first checks that the ordinary hull of the denominator
excludes zero. On success, it embeds the already-proved ordinary reciprocal
interval as a constant linear interval. `I.div? J` multiplies the numerator by
that enclosure using the existing parameter-dependent multiplication operation.

The denominator's dependence is deliberately forgotten for this fallback; the
numerator's dependence can survive. For `I(t)=t`, `J(t)=1+t`, the computed bounds
are `[t/2,t]`. These are sound, not optimal (the actual range is contained in
`[0,1/2]`). This milestone does not construct affine tangents/secants to inverse,
claim optimal reciprocal bounds, or add division to either expression interpreter.

## What is proved

- `linear_recip_success_iff`: the reciprocal succeeds exactly when its rational
  hull has strictly negative upper bound or strictly positive lower bound.
- Successful reciprocal and division prove nonzero denominator values throughout
  the certified parameter range whenever the denominator enclosure contains them.
- `linear_recip_encloses` and `linear_div_encloses` prove inclusion at each shared
  parameter in `[0,1]`, using the existing real reciprocal and product theorems.
- `QuotientValues` explicitly requires a nonzero denominator; no totalized
  division-by-zero value enters that partial relation.
- `linear_div_domain_sound` proves all three partial-enclosure obligations for
  quotient relations under the intersection of operand domain descriptions.
  Existence from definite membership uses the proved nonzero guard, not an
  assumed definedness conclusion. A successful numerical guard does not erase
  an operand's excluded parameter domain.

Failure returns `none`, meaning unknown. In particular, a hull touching zero,
spanning zero, or equal to zero fails, even with zero numerator. Failure can also
occur for a sound enclosure of the constant function one: `[-1,1]` contains that
function but cannot certify its reciprocal. Domain restrictions are not consulted
to sharpen the hull or bypass the guard. No split-domain reciprocal, infinities,
new rounding mode, or floating-point format behavior is introduced.

## Thesis grounding and controls

Tupper [§2.9.4, Constant Intervals](https://www.dgp.toronto.edu/~mooncake/thesis/node40.html)
places constant bounds within the generalized interval representation.
[§3.3.16, Partial Functions](https://www.dgp.toronto.edu/~mooncake/thesis/node122.html)
keeps domain descriptions distinct from value bounds;
[§3.3.27, Partial Binary Functions](https://www.dgp.toronto.edu/~mooncake/thesis/node133.html)
extends that treatment to binary operations. Our guard plus constant reciprocal
embedding is a deliberately bounded conservative policy compatible with those
principles, not a transcription of the full thesis domain-description machinery.

`DivisionExamples.lean` checks positive and negative reciprocals, a quotient
retaining numerator dependence, exact constant division, poles, boundary zero,
sign crossing, and a zero numerator that cannot bypass the denominator guard.
It also exhibits a defined quotient alongside a failed enclosure guard and
proves that a successfully bounded quotient retains a punctured operand domain.
All concrete coefficient checks use kernel reduction.

The independent review of #17–#18 is unaffected: their statements and policy are
unchanged. `lake build` includes this module and examples and the enforced audit.
See [VALIDATION.md](VALIDATION.md) for results. A separate domain-local interpreter
bridge is the next bounded follow-on; this arithmetic operation itself does not
solve external coordinate-domain inference.

The subsequent [guarded interpreter](GUARDED_EVALUATOR.md) connects these
operations to compositional expression semantics; the standalone APIs above
and the original polynomial interpreter remain unchanged.
