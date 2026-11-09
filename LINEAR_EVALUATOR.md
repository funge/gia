# Shared-parameter expression interpretation

`LinearEvaluator.lean` connects the parameter-dependent arithmetic to the existing
`Expr` syntax and partial real `Value` semantics. It is a new optional interpreter;
the ordinary interval evaluator and all presence/search code remain unchanged.

`evalLinear X Y e` interprets rational constants, `x`, `y`, addition, subtraction,
and multiplication with `LinearInterval` operations. Every variable occurrence
uses the same supplied input model and parameter. Constants are exact affine
constants. Multiplication uses the certified curvature policy from
[LINEAR_MULTIPLICATION.md](LINEAR_MULTIPLICATION.md).

Division returns `none` unconditionally, including `1/1`. Unsupported children
propagate `none` through enclosing operations; for example, zero times an
unsupported division is not simplified into a successful zero result. Here
`none` means unsupported/unknown, not that the expression has no semantic value.
There are no guessed denominator guards or new FP assumptions.

## Proved bridge

- `evalLinear_sound`: at any shared parameter in `[0,1]`, if the input models
  enclose real coordinates and the existing partial semantics supplies a value,
  successful interpretation encloses that value.
- `evalLinear_defined`: successful interpretation supplies an actual `Value`
  witness for any real coordinates. This stronger fact follows because the
  supported fragment is polynomial; it does not claim the unsupported division
  fragment is undefined.
- `evalLinear_partial_sound`: for supplied coordinate functions enclosed on
  `[0,1]`, the resulting interval satisfies all three existing partial-enclosure
  obligations for the expression semantics on that parameter range.
- `evalLinear_restricted_sound`: an explicit caller-supplied parameter domain
  restriction is retained in the resulting contract.
- `evalLinear_div_unknown`: all division nodes return `none`.

Coordinate functions in these statements are total real functions. If they
stand for partial external quantities, the caller must retain their domain
restriction; this interpreter does not infer domains or consume arbitrary
`PartialEnclosure` inputs. No continuity, uniqueness, or root-existence statement
is derived from the new contracts. The existence theorem concerns a function
value, not a zero of the function.

## Kernel-checked examples

With `x(t)=t` and `y(t)=1-t`, the example interpreter computes:

- `x-x` with exact bounds `[0,0]`;
- `x*(1-x)` with bounds `[0,1/4]`;
- `x+y-1` with exact bounds `[0,0]`.

Additional theorems connect the product's successful evaluation to actual
`Value` existence, enclosure, and an explicit restricted-domain contract.
The tests check that `1/1` is unsupported while separately proving its semantic
value is 1, and that zero times a division-by-zero expression stays unsupported.
Coefficient calculations use kernel reduction, not native proof evaluation.

This does not claim exact dependency tracking for arbitrary uncertain input
models: repeated occurrences share the semantic coordinates, but each interval
operation can over-approximate them. Nor does it claim exact polynomial ranges,
optimality, completeness, or an implementation refinement to machine arithmetic.
The operations remain exact rational computations interpreted over reals.

## Thesis scope and review

This bridge makes the shared-parameter representation from Tupper
[§2.9.3](https://www.dgp.toronto.edu/~mooncake/thesis/node39.html) available to
expression evaluation and reuses the proved chapter-3 multiplication policy.
It is a bounded polynomial fragment, not the thesis's full function language,
nonlinear domain/continuity analysis, or a transcription of all optimizations.

The milestone is stacked after the [enforced audit](AUDIT_POLICY.md). `lake build`
checks the new module and examples and enforces the transitive axiom allowlist.
A fresh audit can also be run with `lake env lean Audit.lean`. See
[VALIDATION.md](VALIDATION.md) for exact results. No native build, v1.0 requirement,
hosted CI, or FP assumption changes.

The subsequent [domain-local bridge](DOMAIN_EVALUATOR.md) relaxes the whole-range
coordinate premise with partial relations and domain-local function hypotheses.
The original interpreter and theorems above remain unchanged.
