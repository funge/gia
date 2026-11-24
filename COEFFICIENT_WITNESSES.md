# Coefficient witnesses across uses

[CoefficientWitnesses.lean](CoefficientWitnesses.lean) distinguishes a single
admissible coefficient pair reused across evaluations from independently chosen
coefficients in each marginal interval. It supplies an exact heterogeneous-code
conversion and a coefficient-recovery criterion; it does not change the existing
pointwise interval-coefficient semantics.

## Source audit and chosen interpretation

Tupper §2.13, printed p.39 / [PDF p.55](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=55),
uses existential membership of a piece at the same parameter. Section 2.14,
printed p.40 / [PDF p.56](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=56),
explicitly distinguishes coefficient number systems, equality of upper/lower
coefficient descriptions, interval-valued coefficients, and free-variable types.
The latter page was checked visually again for this milestone. Its equality
notation alone does not specify whether repeated interval descriptions share a
particular real choice across all uses. It does not prove a theorem equating
pointwise choice and persistent choice.

[IntervalCoefficientVariants](INTERVAL_COEFFICIENT_VARIANTS.md) already proves
exact *pointwise* correspondence for closed independently chosen coefficient
intervals at nonnegative parameters. We retain that result. The new fixed-witness
interpretation is stated separately, rather than silently attributing a stronger
convention to the source. Its implications and counterexamples are mathematics
independent of that interpretive choice.

## Exact results

`realizes C T f` means there is **one** pair `(p,q) ∈ C` such that, for every
`t ∈ T`, `f t = p+q*t`. It makes no assertion about values outside `T`; it does
not invent outputs of a partial function. `C` can constrain the pair jointly.

`coded` permits distinct types for the two coefficient codes and total real
interpretations of those codes. `coded_exact` proves equivalence with the image
of the original admissible *pair* under decoding. It never replaces that image
by the product of its marginal sets, and does not require code injectivity.
Thus different codes for one real value are allowed. Exceptional or failed
code decoding is not part of these total real-valued maps.

For a parameter set containing 0 and 1, `realizes_iff` proves:

```
realizes C T f ↔
  (f 0, f 1 - f 0) ∈ C ∧
  ∀ t ∈ T, f t = (1-t)*f 0 + t*f 1
```

This recovers the actual coefficients instead of assuming an inclusion premise.
`coded_iff` carries the recovery back to a single admissible code pair.
`integer_rational_iff` instantiates genuinely different carriers: exactness is
precisely an integral intercept, rational slope and the displayed affine identity.
These are mathematical casts, not IEEE conversions or heterogeneous infinite
endpoint arithmetic.

`sample_realization` retains the witness across any indexed collection of uses.
`samples_enclosed` proves inclusion in the existing existential piece marginals;
the reverse inclusion is deliberately absent. `interval_marginal` identifies the
closed interval-coefficient case with the existing definition, and `realized_form`
reuses its proved pointwise `LinearInterval` enclosure. Domain restriction retains
the witness. Empty parameter domains are realizable iff the coefficient set is
nonempty: vacuous observations do not manufacture an admissible coefficient.

## Strict controls

[Fixtures](tests/CoefficientWitnesses.lean) use `p∈[0,1]`, `q=0`. At every
`t∈[0,1]`, the pointwise marginal and existing affine bound admit `f(t)=t`, by
choosing `p=t` anew. No single admissible pair realizes that curve. Likewise the
joint samples `(0,1)` are excluded although each marginal admits its component.
Independent re-choice is therefore a sound overapproximation of fixed-witness
outputs, but an unsound claim of *exact* joint representation.

Other controls cover mixed integral/rational decoding, a rejected fractional
intercept, constrained pairs whose marginal product would admit a forbidden
pair, a one-point domain without the two anchor hypotheses, and both kinds of
empty-domain behavior. No assertion is made that membership in an enclosure
proves attainability with the same coefficient witness.

## Residual scope

This closes a concrete fixed-witness affine correspondence, not the whole §2.14
family calculus. Mixed open/extended endpoint carriers, full Hansen coefficient
families, partial code decoding and arbitrary symbolic/nonlinear coefficient
models remain separate. The source convention concerning persistent real choices
remains explicitly unresolved. See the classified residual tasks in the
[Chapter 2 checklist](CHAPTER2_CHECKLIST.md).

Run pinned `./check.sh`. All new theorems and fixtures are registered in the
existing axiom allowlist. There is no new project axiom, FP assumption, hardware
contract, native code, runtime path or performance claim.
