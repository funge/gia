# Certified endpoints and least directed enclosure

[EndpointOptimality.lean](EndpointOptimality.lean) connects the repaired finite
binary64 value family to existing Word endpoint certificates. Sound outward
endpoints need not be least. The new theorem characterizes exactly the missing
optimality obligation; it does not strengthen the directed hardware contract.

## Source and existing proof chain

Tupper's directed rounding in §2.5.3 (printed p.20 /
[PDF p.36](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=36)), exact
interval extension/demotion in §§2.7.4–2.8 (printed pp.24–26), and stored family
bounds in §2.10 (printed pp.32–33) motivate this derived connection.
The [repaired format bridge](BINARY64_FORMAT.md) identifies the finite values of
the explicitly repaired `(2,53,-1022,1023)` format with `Binary64.decode`.
This is not an identification with the literal printed coefficient display.
[Discrete demotion](DISCRETE_DEMOTION.md) already supplies soundness, leastness
and `word_certificate`: the mathematical hull is contained in every sound
finite Word enclosure. [Finite affine demotion](FINITE_AFFINE_DEMOTION.md)
checks decoding and four outward inequalities, not extremality.

## Exact guarantee

For a nonempty actual real output set `S`, successfully decoded endpoint words
`l,u`, and a certificate enclosing every member of `S`, `certificate_exact_iff`
proves:

```
hull binaryValues S = decoded closed interval [l,u]
  ↔ LowerOptimal (sInf S) l ∧ UpperOptimal (sSup S) u
```

`LowerOptimal x l` states that `l ≤ x` and every repaired-format value below
`x` is at most `l`. `UpperOptimal` is dual. The decoded words already establish
representability. `decoded_down_iff` and `decoded_up_iff` connect these conditions
to the existing mathematical directed rounding operations. A finite sound
certificate for nonempty `S` itself supplies boundedness and finite enclosing
range; no separate representable-range hypothesis is hidden. This neither
constructs such a certificate nor promises one for unbounded outputs.

`interval_exact_iff` specializes to an ordered closed ideal interval.
`certified_zero_exact_iff` and `certified_one_exact_iff` use the actual successful
`FiniteAffineDemotion.certify` result: the checker discharges soundness, while
tightness at each stored parameter endpoint remains precisely the displayed
optimality condition. Existing shared-parameter enclosure and noncollapse proofs
are reused unchanged. Optimal stored endpoint values alone are not a claim of
least affine-family conversion or binary64-tight interior interpolation.

`family_exact` lifts equality to actual parameter-indexed output sets, retaining
the same parameter and its external admissible set. Empty fibers remain empty;
the right-hand side explicitly requires a nonempty fiber. This preserves the
relation defined by mathematical hull demotion, not necessarily the original
attainable values. It neither invents values for absent inputs nor assumes
independent choices across parameters.

## Controls and boundaries

[Kernel fixtures](tests/EndpointOptimality.lean) prove that the existing checker
accepts `[-1,1]` at both endpoints for the constant-zero ideal family, yet this
certificate is not least. Thus existing certificate hypotheses cannot imply
coincidence alone. Exact singleton zero and the open image `(0,1)` have the
expected least closed enclosures; the latter explicitly does not attain zero.
A partial family mixes that open image with an empty fiber.

Run `./check.sh` with the pinned Lean/mathlib setup. The module and fixtures join
the existing enforced axiom audits. There is no executable optimality checker,
new axiom, new floating-point premise, hardware/backend change, or native test.
Native Float/Word transport, raw-bit equality (including signed zeros), correct
rounding by hardware, overflow/NaN behavior, automatic success and performance
remain outside this theorem. Chapter 2 is not declared complete.
