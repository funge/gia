# Nonnegative cut arithmetic: Tupper §2.15.1

The original PDF, printed pp.40–41 / PDF pp.56–57, defines nonnegative cuts as
downward-closed subsets of the nonnegative rationals and interprets their real
value as a least upper bound. The displayed operation on p.41 is
`X ⊕ Y = {x ⊕ y : x∈X, y∈Y}`. The next paragraph warns that redefining cuts as
subsets of all rationals does not make negative multiplication work: the product
of two negative cuts need not be a cut. These statements were checked visually
against the authorized repository PDF. Public source:
[Tupper thesis, §2.15.1](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=56).
No explicit cut-comparison algorithm is printed in this passage.

## Exact mathematical result

[CutArithmetic.lean](CutArithmetic.lean) reuses [DedekindBoundary](DedekindBoundary.lean)
and defines addition and multiplication by precisely that rational `Set.image2`.
For representatives C,D whose rational casts have real least upper bounds r,s:

- `add_lub` proves that the encoded sum has least upper bound r+s.
- `mul_lub` proves that the encoded product has least upper bound r*s, provided
  every admitted rational operand is nonnegative.
- `operations_representation_independent` proves identical decoded results for
  different representatives of the same input reals. It does not assert equality
  of the representative sets.
- `decoded_le_iff` characterizes decoded real order by inclusion of upper-bound
  tests in the reverse direction. This is a derived correspondence, not a
  source-specified executable comparison or equivalence with raw cut inclusion.

No endpoint attainment is required. The lub premises exclude empty and unbounded
sets; they are supplied for the source's proper nonempty downward cuts by the
existing `proper_nonempty_lub`, rather than assumed as a new axiom.
`add_downward`, `mul_downward`, `outputs_nonnegative`, and `proper_of_lub` establish
that these operations again give nonnegative proper downward cuts. Nonemptiness
also follows from the output lub. The proofs use ordinary real-order reasoning
and pinned mathlib's `IsLUB.mul_left` / `IsLUB.mul_right`; there is no new real
construction, quotient implementation, rounding contract or runtime backend.

## Boundary and failure controls

[Kernel-checked fixtures](tests/CutArithmetic.lean) demonstrate:

- strict 1 plus closed 2 decodes to 3, and their product decodes to 2;
- strict 1 plus strict 1 excludes the rational boundary 2, whereas closed 1 plus
  closed 1 includes it; their real values agree;
- closed 1 and strict 1 have equal decoded order despite failure of one raw
  subset relation;
- closed zero `{0}` gives the expected addition and multiplication values;
- strict zero is empty, so its pointwise sum is empty, not the other operand.
  Totalized real `sSup empty = 0` cannot repair this as an additive identity;
- the signed cut `{q | q < -1}` has real lub −1 and is downward closed, but its
  self-product contains 4 and excludes 0, so it is not downward closed.

The existing [boundary fixtures](tests/DedekindBoundary.lean) retain malformed
`{1}` and improper whole-nonnegative-rational controls. Nothing identifies empty
cuts with valid real-lub inputs, or invents a signed-cut arithmetic repair.
The nonnegative ambient order's bottom is distinct from real-lub semantics.

## Coverage and next obligation

This closes the source-supported nonnegative addition/multiplication inheritance
and the printed signed-product warning, with decoded order as a derived result.
It does not license arbitrary discontinuous or partial rational operations under
the generic ⊕ notation. The survey refers further construction to its references;
no full signed quotient or canonical endpoint convention is asserted here.
The related rational-sequence, digit and canonical continued-fraction results
are documented in [representations](SEQUENCE_AND_DIGIT_REPRESENTATIONS.md) and
[continued-fraction conversion](CONTINUED_FRACTION_CONVERSION.md). Their limitations
remain explicit; this unit adds no hardware changes or floating-point assumptions.
