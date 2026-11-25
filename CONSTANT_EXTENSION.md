# Constant embedding and interval-extension compatibility

## Source and existing coverage

Tupper §2.9.4 ([printed p.30 / PDF p.46](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=46))
embeds constant endpoint pairs as zero-slope functions and states a homomorphism
when operators are defined via interval extension. The printed page was visually
checked, including its preceding discussion of nonunique function demotion.
The external review was a lead; it had not checked the PDF or Lean.

The existing `linear_constant_add`, `linear_constant_sub`,
`linear_constant_mul` and `evalLinear_constant_correspondence` prove concrete
finite rational instances. `GeneralFamilyDemotion.model_demotion` proves
inclusion, not equality of operations. The general conditional commuting theorem
was a **genuine reusable gap**, despite the prior scoped closeout verdict.
[ConstantExtension](ConstantExtension.lean) now fills its real-output semantic
form. It does not claim an unconditional theorem for arbitrary demoters.

## What the new theorem assumes and proves

`LowerCompatible down` requires outward lower soundness and domination of every
constant lower competitor. `UpperCompatible up` is the dual. These are
**sufficient demotion premises**, not assumed operation equality and not claimed
necessary for every constant-preserving implementation. In particular, they do
not require a globally optimal affine demoter.

`lower_fixes_constants` and `upper_fixes_constants` derive exact preservation
of constant bound functions from those inequalities. `constant_extension` then
proves that taking the actual output set of any fixed partial real relation,
forming its least extended bounds, and applying the two compatible family
demoters commutes with constant embedding. `interval_homomorphism` gives the
explicit diagram for any finite arity and constant endpoint-pair operands.
The same tuple is retained in the operation graph; correlations can also be
represented directly by the more general witness relation. Empty or unbounded
real images are allowed, using the existing canonical extended hull bounds.
Infinite bounds are not literal infinite output values.

The theorem concerns **represented bound functions**, not equality of potentially
redundant coefficient syntax. `constant_injective` requires a nonempty parameter
type. A restricted external parameter domain can be encoded by its subtype;
the operation relation must remain fixed on that domain. No output bound claims
total definedness, and no parameter-dependent guard is silently discarded.

`projectDown_compatible` and `projectUp_compatible` construct real witnesses to
the premises: constant infimum/supremum projections of the bound functions.
These are mathematical, not executable endpoint algorithms. Arbitrary chosen
affine or machine demoters still need their own compatibility proofs. Finite
floating rounding that changes a real constant is not covered by this exact
real constant-fixing theorem; it needs a separate scalar/family rounding
compatibility statement. No existing hardware contract is strengthened.

[Fixtures](tests/ConstantExtension.lean) show a merely outward demoter mapping
zero bounds to [-1,1] breaks the commuting equation and fails compatibility.
They also cover empty/unbounded images and guarded x/x: its image is {1} on
[-1,1] with zero excluded by the operation graph, but x=0 remains absent.

## Secondary source leads, checked without widening the implementation

- **§2.9.6, pp.30–31 / PDF pp.46–47:** the printed family is real-valued,
  with p+Σqᵢαᵢ and independently varying parameters in [0,1].
  `MultiAffineFamilies.Form` is specifically rational-coefficient. However,
  `HansenCoefficients.Choice` already uses arbitrary finite real coefficients,
  and `HansenRealSets.values` admits arbitrary real coefficient sets.
  `real_coefficients_existing` checks the singleton-coefficient specialization
  exactly, with one coefficient vector and one parameter vector. Thus finite-real
  **denotation is covered**, while the specialized rational affine API/extrema
  theorems have not become a general real-coefficient API. Literal extended-real
  coefficients and their undefined evaluations remain separate. The printed
  representation definition is not an additional universal optimization algorithm.
- **§2.5.1, p.19 / PDF p.35:** the guard is x≠−∞ for right addition by +∞.
  On the pre-lambda carrier of finite values and two infinity tags, excluding
  −∞ leaves exactly the already modeled finite and +∞ rows.
  `scoped_positive_infinity` checks the quantified structural-tag formulation
  using `addObservation`; [InfiniteAdditionTransfer](InfiniteAdditionTransfer.lean)
  already proves the full observation graph and conversion transfer for these rows.
  This is **covered in that justified scope**. Section 2.5.2 subsequently includes
  lambda in F, without settling the guard's scope or defining a numerical `≠`
  predicate. `lambda_guard_not_covered` records that the existing model leaves
  this case unmodeled (`none`), not that the source result must be lambda or false.
  No new exceptional row or IEEE interpretation is introduced.

The [§2.9.8 trace](SYMBOLIC_TRACE.md) remains an exact symbolic/pointwise result,
not numerical range computation. Neither this compatibility theorem nor these
source checks add a solver or begin Chapter 3 work.
