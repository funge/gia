# Shared proof-side partial real arithmetic

[PartialRealArithmetic.lean](PartialRealArithmetic.lean) is a lightweight semantics
foundation for the two existing operation interfaces. It centralizes real
addition, subtraction, multiplication and division, their value relations, and
the nonzero denominator guard. It imports only mathlib's real-number foundation,
not an evaluator or native implementation.

[ArithmeticOp.Rel](ConditionalArithmetic.lean) selects these shared relations.
[HardwareQuotient.meaning and Defined](HardwareQuotient.lean) select the same
real operations and guards. Division's partial relation is exactly

    y ≠ 0 ∧ z = x / y.

The value function alone remains totalized real division, as before. A caller
must use the relation or pair the value with `Defined`; the refactor does not
make `x/0` a valid expression value. `div_domain_iff` proves existence exactly
when the denominator is nonzero, and `div_zero` excludes zero-denominator values.
This preserves the explicit partiality required by the project's existing Tupper
relational interpretation; it does not add a new thesis theorem or IEEE model.
See [conditional arithmetic](CONDITIONAL_ARITHMETIC.md) and
[guarded hardware quotients](HARDWARE_GUARDED_QUOTIENT.md).

## Compatibility boundary

Both public operation inductives are retained as distinct inductives:
`ArithmeticOp` and `HardwareQuotient.Operation`. Their constructors, generated
recursors and deriving declarations are unchanged. There is no replacement alias,
shared third operation enumeration, or conversion required of callers. Purpose-built
ASTs, evaluator algorithms and native program modules remain unchanged.

Transparent abbreviations in the shared module preserve the original
constructor-wise definitional reductions. Shared simp unfolding attributes preserve existing automation; downstream
proofs need no per-call compatibility rewrites. In particular, addition still reduces directly to an
equality rather than acquiring a redundant `True ∧` in `ArithmeticOp.Rel`.
The hardware interface retains its separate always-true guard for total operations.

[Parity fixtures](tests/PartialRealArithmetic.lean) compare both interfaces with
independent copies of their original definitions, constructor by constructor.
They also prove the cross-interface relation/guard/value correspondence, exercise
dependent pattern matching and both original recursors, and test guarded quotient
values at zero and arbitrary nonzero denominators, including a negative example.
Existing guarded-quotient fixtures and native oracles remain part of qualification.
The test-only correspondence between enums is not a new production conversion API.

## Limits and checks

This is a proof-side consolidation, not an arithmetic algorithm, performance,
batching, startup, layout or AST redesign. No rounding behavior, FP assumptions,
native adapter contract or Float conversion boundary changes. It makes no claim
that the C implementation is verified.

Run `lake build ConditionalArithmetic HardwareQuotient`,
`lake env lean tests/PartialRealArithmetic.lean`, `./check.sh`, and
`./hardware/check.sh` with the pinned toolchain. The module and fixture participate
in the existing named and namespace audits and integration inventory. See
[validation receipts](VALIDATION.md).
