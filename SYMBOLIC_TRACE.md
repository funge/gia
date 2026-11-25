# The symbolic sine/root trace

Tupper §2.9.8, [printed p.32 / PDF p.48](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=48),
uses g(x)=x sin(x)+sqrt(x)/(x+π) on [0,1]. The printed page was visually checked:
the intermediate product and quotient, and the final equal-bound pair, all
retain the same parameter α. This is a description of exact symbolic bounds,
not an algorithm computing a numerical range or simplifying arbitrary syntax.

[SymbolicTrace](SymbolicTrace.lean) instantiates existing real-set and partial
operation semantics, rather than extending a production AST. `product_stage`,
`denominator_stage` and `quotient_stage` identify the printed intermediate
singleton fibers. The root stage uses `RootTransfer.roots`/`SqrtValues`; division
uses `PartialRealArithmetic.divRel`, including its nonzero guard. `trace_iff`
proves the composed graph exactly: z belongs at p iff p≥0 and z=g(p). Positivity
of π discharges the denominator guard on that domain. Negative roots stay
absent even though mathlib's totalized expression has a numerical payload.

`source_trace` identifies the result with the existing `FunctionalBounds`
whose lower and upper functions both equal g. `pointwise_least` proves that any
sound pair contains that singleton. `source_projection` identifies the union
of fibers with g '' [0,1]; it does not compute the endpoints of this image.
`projection` additionally retains an arbitrary external domain by intersection
with [0,∞). `model_sound` supplies exact definite/possible domain flags in the
existing `PartialEnclosure` interface. No expression value is created at a hole.

[Fixtures](tests/SymbolicTrace.lean) check 0, 1, an interior parameter, negative
root rejection, a zero denominator, and an external domain hole. They also
prove that pointwise singleton bounds do not make the projected range the
singleton {0}: g(0)=0 while g(1)>0. This distinguishes containment at one
parameter from occurrence over the whole domain.

This closes the concrete trace identified by the [chapter audit](CHAPTER2_CHECKLIST.md).
The infinite coefficient-function ellipsis in the source remains a description,
not an invented universal grammar. There is no new floating-point assumption,
native execution, exact-real oracle, optimizer, or performance claim.
