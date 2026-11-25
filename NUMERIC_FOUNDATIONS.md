# Scalar numeric-foundations correspondence

This proof-only package maps the explicit scalar claims in Tupper's Chapter 2
onto the pinned mathlib types and the project's existing partial arithmetic.
It does not construct new number systems, change a hardware contract, or finish
Chapter 2. The original [thesis PDF](https://www.dgp.toronto.edu/~mooncake/thesis.pdf)
is the source; its printed pp. 15–22 (PDF pp. 31–38) were visually checked,
including the surrounding rounding and exceptional-value conventions.
The repository Markdown transcription is an index, not authority for equations.

## Exact correspondence

The declarations below are in [NumericFoundations.lean](NumericFoundations.lean).

| Printed source | Formal result | Qualification |
| --- | --- | --- |
| §2.2, p.16: integer promotion preserves addition, multiplication and `>` | `integer_rational_embedding`, `integer_rational_injective` | Uses the actual casts, not a parallel carrier. Integer field division is not truncated `Int.ediv`; `integer_division_not_closed` witnesses the distinction. |
| §2.1 algebra, recalled in §2.2 | `integer_alternative_distributivity_fails` | Checks that addition does not distribute over multiplication; ordinary ring laws come from mathlib. |
| §2.2: inverse partial at zero | `rational_division_graph` | Exact equivalence with the existing nonzero-guarded real relation. Totalized Lean division is not used as a definedness test. |
| §2.2: square root cannot be total over rationals; examples 2 and −1 | `no_rational_root_two`, `no_rational_root_negative_one`, `no_total_rational_root` | Some rationals do have roots. Tests retain a perfect-square control. |
| §2.3, p.17: real values represented by convergent rational sequences, rational constant embedding | `rational_sequence_exists`, `rational_constant_representation` | Reuses mathlib's rational approximation theorem and the existing stream semantics. Existence does not give an executable approximation oracle, rate, or stopping algorithm. |
| §2.3: rational-to-real embedding | `rational_real_embedding`, `rational_real_injective` | Preserves the same three operations/order assertions. |
| §2.3: real square root on nonnegative inputs only | `real_root_graph`, `real_root_domain`, `root_observation_graph` | Nonnegative root with square equal to input, in the actual partial relation and finite tagged observation. Negative input does not acquire a value from totalized `Real.sqrt`. |
| §2.4, pp.17–18: real-to-complex embedding and complex square-root closure | `real_complex_embedding`, `real_complex_injective`, `promotion_chain`, `complex_division_graph`, `complex_root_total` | The root choice uses mathlib complex powers. This asserts algebraic existence, not continuity, branch-cut behavior, or an interval implementation. |
| §2.4, p.18: “no natural ordering relation” | `no_complex_ordered_ring` | Precise narrower reading: no linear order compatible with the existing complex ordered-ring laws, since `I² = −1`. This does not deny lexicographic or partial orders. |

These are kernel-checked correspondences, using existing classical mathlib
foundations. They do not prove C, native Float transport, IEEE arithmetic, or
new exceptional rows. The [fixtures](tests/NumericFoundations.lean) deliberately
combine promotion and domain change: a negative real has no real square root,
but its complex image has one. Thus embedding cannot preserve every operation's
domain across different codomains. Guarded division does preserve its domain.
Likewise square followed by the nonnegative real root yields absolute value,
not an unrestricted inverse of squaring.

## Numeric-package residuals

* **Imported background:** scalar field/ring constructions and ordinary algebra
  use pinned mathlib. No new quotient construction or complete reproof of the
  surrounding elementary exposition is claimed. Quaternion/Cayley narrative
  remains a survey mapping, not a theorem of this module.
* **Already proved elsewhere:** mathematical finite-format directed least
  bounds, repaired radix/binary64 correspondence, endpoint certificates,
  signed-divergence representation and the positive infinitesimal example.
* **Inconsistent as unconditional equality:** the printed coefficient and digit
  format displays. The checked maximum-exponent counterexample and separately
  repaired convention remain unchanged; no authorial intent is inferred.
* **Unspecified/interpretive:** remaining exceptional operand/comparison rows,
  infinite-input square roots, and the scope of the source's extended-real
  “homomorphism.” Literal infinities, unbounded sets of finite reals, and λ
  must remain distinct. Five named numerical comparisons do not specify a
  numerical `≠` table; sentinel/definedness tests are separate.
* **Still mathematical proof work:** source-required rounded-operation algebra
  and rounding conventions beyond the established directed, in-range result;
  exceptional interval algebra only once its operations are specified.
  Neither this package nor existing certificates imply exact hardware rounding.

The [closeout matrix](CHAPTER2_CLOSEOUT.md) keeps these residuals separate from
family/operator closure and the §2.15 representation survey. Standard local
qualification is `./check.sh`; every theorem in this module is named in
[Audit.lean](Audit.lean), and the fixture namespace is also audited. The audit
allowlist is unchanged.
