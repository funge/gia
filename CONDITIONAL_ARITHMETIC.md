# Arithmetic composition of conditional trees

This milestone closes a bounded integration gap in #23: conditional trees can
now be operands of addition, subtraction, multiplication, and division. It keeps
the old Expr, ConditionalExpr, and their evaluators unchanged. The public
`arithmeticTree op a b` operation distributes arithmetic through existing trees,
so its result can itself be used in further arithmetic or conditional branches.
Guards still use the old arithmetic Expr; conditional-valued guards and a new
fully recursive surface-language AST are not introduced.

## Exact partial semantics before enclosure

`ConditionalArithmeticValue x y op a b z` requires values from both operands at
the same x and y, and the operation's real relation. Addition, subtraction, and
multiplication use their ordinary equalities. Division additionally requires
a nonzero denominator. There is no semantic value for division by zero and no
simplification of zero times an undefined operand.

`arithmeticTree_value_iff` proves equivalence between this independently stated
relation and ConditionalValue for the transformed tree. This is an exact
value-and-domain correspondence at arbitrary real coordinates, not just one-way
interval soundness or a claim restricted to certified inputs. The existing
active-branch semantics is preserved, including partially defined guards and
undefined inactive branches. Arithmetic remains strict in both operands.

The generic `conditional_map_iff` and `conditional_liftBinary_iff` lemmas take an
explicit semantic correspondence for their supplied leaf transformation.
`arithmeticOp_value_iff` proves that correspondence for all four supported
operations directly from the existing Value constructors. Thus the concrete
arithmetic theorem does not assume an unproved transformation rule or new axiom.

`evalConditionalArithmetic` applies the existing evaluator to the transformed
tree. Its soundness and definedness theorems follow through the exact semantic
correspondence. These interpreter theorems retain the local premises: a parameter
in [0,1] and enclosed coordinates. Success does not imply global definedness.
A relational theorem preserves all three domain-contract obligations for strict
complete-coordinate environments; both coordinate relations must still exist.
Exact compatibility on arithmetic leaves is proved by definitional equality.

## Useful precision and a proved limitation

The examples include the denominator

    jump(x) = if x < 1/2 then -1 else 1

The transformed tree for `1 / jump(x)` successfully encloses the result in
[-1,1]. Each leaf denominator is certified nonzero before the results are joined.
A separate kernel check shows that joining the denominator first and applying
interval division returns unknown because that joined interval contains zero.
An independent semantic proof constructs the reciprocal value for every real x.
This is a concrete integration gain, not a general precision comparison theorem.

Repeated guards expose a different limitation. For

    1 / ((jump(x) - jump(x)) + 2)

we construct the semantic value 1/2 at every real x, but the evaluator returns
unknown. Distribution retains unresolved combinations that cannot occur at the
same coordinates; one such combination produces a zero denominator. There is no
path-condition propagation, coordinate narrowing, or inconsistent-path pruning.
The semantic equivalence theorem keeps the real coordinate correlation intact;
the conservative interpreter loses that information. Failure remains unknown,
not a claim of undefinedness or no solution.

Other controls cover all four arithmetic operations on certified choices with
inactive poles, strict zero multiplication with an undefined operand on either
side, and explicit division-by-zero rejection. Semantic witnesses and absence
proofs are checked separately from the interval computations.

## Thesis coverage and costs

This is a semantic composition step within the richer-syntax direction described
in Tupper [§4.1.4](https://www.dgp.toronto.edu/~mooncake/thesis/node148.html), with
the partial-function distinctions discussed in
[§3.3.16](https://www.dgp.toronto.edu/~mooncake/thesis/node122.html). It reuses the
certified branch-selection foundation related in #23 to
[§4.5](https://www.dgp.toronto.edu/~mooncake/thesis/node166.html). It does not
implement the thesis's caching, generated specialized operators, or rounding-
control optimization. Those references and their scope were established in the
preceding milestones; this module is a bounded formalization choice, not a
claim that the thesis prescribes this exact tree representation.

Distribution copies the right tree into every leaf of the left tree. Repeated
composition can grow the syntax substantially; no sharing, size bound, runtime
cost theorem, compiler correctness, or efficiency claim is supplied. The
transformation terminates structurally on finite trees. A future direct
interpreter or shared representation should be compared against this exact
semantic correspondence before replacing it.

No continuity, root-existence, maximal-domain, completeness, optimality, or
floating-point implementation theorem is added. Existing IEEE 754-related
assumptions, dependency/toolchain pins, native build, release workflow, and hosted
CI remain unchanged. See [VALIDATION.md](VALIDATION.md) for build and enforced
axiom-audit evidence, and [REVIEW_STACK.md](REVIEW_STACK.md) for review order.
