# Nearest minimizers without a tie convention

Tupper §2.5.3, printed p.20 / PDF p.36, describes rounding to a nearest member;
§2.5.4, printed p.21 / PDF p.37, states the inverse-law claims. The
[original page images](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=36)
were checked. This package supplies the finite-value mathematical minimization
facts and makes the inverse-law scope explicit. It does not choose a nearest
tie rule, assign exceptional or overflow results, or implement a native rounder.

## Global finite minimization

[NearestMinimizers.lean](NearestMinimizers.lean) defines `NearestReal D x q` by
membership of rational `q` in the finite family `D` and minimal real distance
to the real input `x`. The same relation agrees exactly with the preceding
rational `SourceRoundedAlgebra.Nearest` specification (`rational_agreement`).

* `exists_iff`: a minimizer exists exactly when `D` is nonempty. This includes
  arbitrary real inputs, not merely rationals. It reuses mathlib's finite minimum.
* `in_range_exists`: in particular, represented finite bracketing suffices.
  `bracketed` and `bracket_candidates` connect minimizers to the **least** finite
  downward/upward results: every minimizer is one of those endpoints. They do
  not apply to arbitrary loose hardware enclosure certificates.
* `unique_iff_strict`: a given minimizer is unique iff every different represented
  value has strictly greater distance.
* `tie_iff`: two ordered distinct represented values are both nearest iff the
  input is their midpoint and no represented value lies strictly between them.
  Equal distances alone are insufficient.
* `tied_only_two` and `nonunique_iff_midpoint_gap`: there are exactly those two
  candidates in a tie; for a nonempty family, nonuniqueness is equivalent to
  such an adjacent midpoint. No third nearest value can occur.
* `exact_unique`: a represented input has itself as its unique minimizer.

The finite optimization theorem also has a mathematical answer outside the
represented range. That is **not** a source or IEEE overflow rule. The fixture
`outside_range` makes this distinction explicit: a finite closest candidate can
exist even though `DirectedOperationAlgebra.InRange` fails. No literal infinity,
λ, signed-zero encoding or native Float behavior is inferred. The relation does
not select either member at a tie and supplies no executable conversion API.

## Inverse scope: three distinct claims

1. **Zero has no multiplicative inverse.** `zero_no_inverse` proves that no
   represented partner can make zero multiply and round to one, in any of the
   three specified modes, whenever zero is represented.
2. **The source decimal formats also have a nonzero failure.** `tiny_members`
   places `10^-11` in both the literal coefficient format and the separately
   labeled signed three-digit repair. `literal_no_inverse` and
   `repaired_no_inverse` quantify over every represented partner and every mode:
   none can round the product to one. The finite upper bounds make every product
   smaller than the represented `1/10`; downward/upward extremality and the
   strictly closer zero candidate for nearest prove the result. No overflow or
   underflow policy is needed. This uses finite exponent bounds, not a claim
   about every arbitrary-radix system based solely on its radix.
3. **Nonzero inverse failure is not universal over all admitted formats.**
   `unitFormat` is the valid literal format with radix 2, precision 2 and both
   exponent bounds 1. `unit_format_values` proves its exact set is `{−1,0,1}`.
   Every nonzero member has itself as a rounded inverse in all modes
   (`unit_format_nonzero_inverses`), although zero still does not.

Thus a claim about a total inverse including zero, a claim about nonzero
members of the displayed decimal system, and a claim about all nonzero members
of every allowable format are different propositions. The first two failures
are proved; the third universal-failure reading has a checked counterexample.
This qualifies the source's wording rather than guessing its intended scope.
The ordinary decimal control `2 * (1/2)` also succeeds in all modes: the failure
witness does not mean every nonzero decimal value lacks an inverse.

## Qualification and remaining scope

The [fixtures](tests/NearestMinimizers.lean) cover irrational real input,
empty/singleton families, actual ties, equal-distance non-minimizers, rational
agreement, out-of-range finite minimization, both decimal inverse failures,
and positive inverse controls including the small admitted format.
All new theorems are registered in [Audit.lean](Audit.lean); run `./check.sh`.
No new project axioms, FP assumptions, native/C/default changes or runtime
performance claim are involved.

The global finite nearest existence/uniqueness/tie proof obligation is now
closed. Choosing a tie policy or exceptional overflow behavior would require
additional specification, not another finite-minimum lemma. The printed format
and decimal discrepancies remain recorded in [source-rounded algebra](SOURCE_ROUNDED_ALGEBRA.md).
Broader exceptional semantics, family/operator closure and representation-survey
obligations remain in the [Chapter 2 closeout matrix](CHAPTER2_CLOSEOUT.md);
Chapter 2 is not declared complete.
