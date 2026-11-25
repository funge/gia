# Source-rounded decimal algebra and the specified infinity extension

This proof-only package checks Tupper §§2.5.3–2.5.4, printed pp.20–21 / PDF
pp.36–37, against the actual mathematical formats. The
[original PDF](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=36) was
visually inspected at high resolution, including the exponents in the three
reassociation rows. It does not silently repair the source or infer authorial
intent. No IEEE or native arithmetic contract changes.

## Two formats, not one

[SourceRoundedAlgebra.lean](SourceRoundedAlgebra.lean) uses `literal` for the
printed coefficient format `F[10,3,-9…9]`. Its strict coefficient bound is 100,
not 1000. The separately labeled signed three-digit repair has coefficient
bound 1000 and the same exponent shift/range. `repaired_correspondence` proves
that `values repairedIndex` is exactly the existing `FormatDigits.Repaired
literal` value set; `repairedIndex` is only a finite-set reindexing device.
It is not a new interpretation of the literal source formula.

Adjacent-value proofs inspect all admitted exponents and integer coefficient
bounds. They do not assume a gap from numerical testing or enumerate native
floats. `gap_round` feeds these proofs into the existing least-directed result.

| Exact input / computation | Literal coefficient model | Signed three-digit repair | Printed text |
| --- | --- | --- | --- |
| nearest of 1001 | 1000, uniquely nearest | 1000, uniquely nearest | 1000 |
| downward of 1001 | 1000 | 1000 | 1000 |
| upward of 1001 | 1100 | 1010 | 1010 |
| directed enclosure of −99999 | [−100000,−99000] | [−100000,−99900] | implicit inner reassociation |
| `100000 + (−100000 + 1)`, rounding each addition upward | 1000 | 100 | 1000 |
| same expression, rounding downward | 0 | 0 | 10000 |
| same expression, rounding nearest | 0 (uniquely determined inner nearest) | not needed for the repair comparison | 0 |

Thus the upward examples cannot both be reproduced by these two definitions
under one unchanged convention. `literal_up_not_printed` checks the first
mismatch; `printed_reassociation` and the regression fixture check the literal
rows, including the contradiction with the printed downward result. The repair
has separate directed inner and outer certificates. The left-associated
expression equals 1 in all three literal modes. These are statements about
intermediate rounding, not a claim about rounding the exact whole expression.

## Multiplication and mixed distributivity

The source says multiplication is likewise nonassociative but prints no
numerical multiplication witness. Our derived witness uses represented operands
`3, 34, 1/2`: first multiplying 3 by 34 rounds 102 to 100 (down/nearest) or 110
(up), producing 50 or 55 after multiplication by 1/2. Multiplying 34 by 1/2
first gives 17, and then 51. All intermediate outputs are finite and in range.

`mixed_distributivity` quantifies over all five independently chosen modes in

```
round₂(2 * round₁(51 + (-50)))
round₅(round₃(2 * 51) + round₄(2 * (-50)))
```

The left side is 2; the right side is 0 or 10. This supplies one counterexample
for every one of the 3^5 site assignments in this multiplication-over-addition
formula. It does not enumerate other notions of distributivity. The local
hypotheses require only the specified rounding observations, not a total
operation outside the finite range. `small_forces`, `exact_forces` and the
strict-nearest certificates make each used observation unique.

`Nearest` is a distance specification; **no tie selection is defined**. A fixture
shows both candidates at an actual midpoint satisfy it. `probe` in the tests
is an explicitly limited rational observation table, not a general rounding
algorithm. Its certified local observations instantiate the multiplication and
all-five-mode theorems, so the conditional results are not vacuous. This is not
an implementation, performance, or native-hardware correctness claim.

## Exceptional addition: one justified extension

Printed §2.5.1, p.19 / PDF p.35 gives finite-plus-positive-infinity; §2.5.4 says
addition is commutative. `sourceAddObservation` adds the reversed
positive-infinity-plus-finite row to the existing observation model. It proves
extension of every old successful observation and symmetry. The old API and
its tests are unchanged. Its finite branch still describes **ideal real addition
before demotion**, not a rounded finite operation.

The new observation yields the literal positive-infinity tag, not an unbounded
set of real members. Structural equality of its returned tag is separate from
the source numerical equality predicate (which reports false for two positive
infinities). Mixed infinities and λ operands remain `none` (unmodeled), not λ
or a guessed IEEE result. No unspecified exceptional arithmetic was added.

## Remaining obligations

The decimal comparisons, derived multiplication nonassociativity and the stated
five-site mixed-distributivity refutations are now checked, with explicit source
mismatches. This does **not** settle the author's intended format or fix the
printed downward row. The later [nearest-minimizer package](NEAREST_MINIMIZERS.md) closes global finite
existence, uniqueness and ties, and qualifies the inverse-law scope with checked
examples. Implementation tie selection and broad ULP assertions remain separate. Exceptional rows without sufficient source rules
remain specification gaps. Family/operator closure and §2.15 survey obligations
remain on the [Chapter 2 closeout matrix](CHAPTER2_CLOSEOUT.md).

Validation uses `./check.sh`, the unchanged axiom allowlist, and
[SourceRoundedAlgebra fixtures](tests/SourceRoundedAlgebra.lean). No native,
C, default-path, or floating-point-premise change is part of this package.
