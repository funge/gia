# Interval-valued coefficients in §2.14

Source checked: Tupper §2.14, printed p.40 / PDF p.56,
[original PDF](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=56).
It states that equal upper/lower scalar coefficients are restrictive, but the
variant `p± ∈ I, q± ∈ I` for `p+qα` is not impotent and is similar to L.
It does NOT assert equality of all such families with all linear intervals.

[IntervalCoefficientVariants.lean](IntervalCoefficientVariants.lean) makes a
finite, closed, real-meaning specialization precise. `values P Q t` instantiates
existing IntervalSetDenotation with scalar affine point pieces, over independent
real choices p∈P and q∈Q. P and Q have rational endpoints. No duplicate set
representation or runtime evaluator is introduced.

`exact_form` proves, for t≥0 and every real z:

```
z ∈ values P Q t ↔ (form P Q).Contains t z
```

Here the existing LinearInterval lower bound is P.lo+Q.lo*t and its upper is
P.hi+Q.hi*t. The reverse implication is proved by the intermediate value theorem
along a diagonal interpolation of coefficient choices, including degenerate
intervals and t=0. It is not an assumed enclosure contract. The source parameter
domain [0,1] satisfies the hypothesis. No exactness is claimed for negative t
with these same endpoint choices.

Literal equality of interval-valued upper/lower coefficient descriptions does
not collapse their real denotation to one value. With P=Q=[0,1] at t=1, both 0
and 2 occur. Singleton coefficients instead give exactly p+qt. This supports
the concrete source distinction; no source contradiction was found.

## Correlation and scope

The theorem is pointwise in one t. Existence of a coefficient choice at every t
does not supply one fixed choice for all t, or preserve correlations between
multiple evaluations. The product premise explicitly allows independent p,q.
If they must satisfy p+q=1, the output at t=1 is only 1, while independent
marginals admit 2. Open coefficient endpoints do not attain the upper value 2.
Both falsifiers are kernel-checked in [fixtures](tests/IntervalCoefficientVariants.lean).

This is neither the whole §2.14 family calculus nor Hansen's multidimensional
system, arbitrary mixed endpoint types, a bumpy-function classification, or a
native implementation. No new floating-point assumptions. Run `./check.sh`.
