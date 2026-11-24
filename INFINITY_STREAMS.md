# Rational sequence representations of signed infinity

Tupper §2.6.3, printed p.22 / [PDF p.38](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=38),
was checked first in the local transcription and then visually in the original
PDF. The displayed positive criterion is
`∀ l ∈ ℚ, ∃ j, ∀ k > j, l < x_k`; the negative criterion reverses the last
inequality. The text explicitly says j and k are integers. Its informal phrase
“ever growing, unbounded” must be read with these eventual-tail quantifiers,
not as mere unboundedness or as a demand for monotonicity. The positive sentence
uses “if”; the negative display uses an iff. We prove that each displayed
criterion is equivalent to the standard corresponding limit in our mathematical
model, not that the prose constructs a quotient system of sequences.

## Exact signed limit correspondence

[InfinityStreams.lean](InfinityStreams.lean) uses total sequences `x : ℤ → ℚ`
and preserves the strict `k > j` condition in `Up` and `Down`. Negative indices
are allowed as printed; their values do not affect a limit toward positive
index infinity. No theorem here assumes that merely taking a supremum of the
whole range represents the limit. The eventual-tail lemmas explicitly account
for the difference between `k > j` and filter tails `k ≥ j`.

The principal statements are:

- `up_iff_rational_limit`: `Up x ↔ Tendsto x atTop atTop`.
- `down_iff_rational_limit`: `Down x ↔ Tendsto x atTop atBot`.
- `up_iff_extended_limit`: `Up x ↔ Tendsto (fun k => ((x k : ℝ) : EReal)) atTop (𝓝 ⊤)`.
- `down_iff_extended_limit`: the corresponding statement with `Down` and `⊥`.

The extended-limit proofs use rational density to pass from rational thresholds
to arbitrary real thresholds and pinned mathlib's neighborhood bases at top and
bottom. No convergence conclusion is assumed. Negation interchanges the two
criteria; no sequence satisfies both. Eventual equality preserves both criteria,
so an arbitrary prefix can be replaced without changing them. No rate or
computable stopping bound is claimed.

## Precise but limited promotion correspondence

`Represents x v` uses the existing `ExceptionalComparisons.Value` carrier:
finite tags mean ordinary real convergence of the rational casts; positive and
negative infinity tags mean the two source criteria; lambda is not represented.
`represents_iff_limit` proves exact agreement with the already existing optional
`bound` map and convergence to its value. `positive_promotion` and
`negative_promotion` expose the two exceptional cases; `undefined_not_promoted`
explicitly leaves lambda unmapped. `representation_unique` follows from uniqueness
of limits and injectivity of that representation map.

This realizes the mathematical common carrier ℝ ∪ {−∞,+∞} from §2.6 with
standard EReal bounds/topology. It does **not** construct the source floating-point
carrier or a total F→R* homomorphism: lambda is absent from the displayed R*
carrier, and rounded arithmetic and numerical exceptional comparison are separate.
In particular, both integer sequences and their sign-reversed versions have
unique mathematical limit tags, while the existing source numerical comparison
of +infinity with itself is still false. Representation identity is not that
numerical predicate. No native Float, Word, NaN payload, signed zero, exception
status or IEEE conversion is involved.

## Sharp controls and limits

[Fixtures](tests/InfinityStreams.lean) prove:

- `k` tends to positive infinity and `−k` to negative infinity;
- a constant rational represents its finite real value, not positive infinity;
- a changed initial segment retains positive divergence;
- `k + 2*(k mod 2)` diverges despite a decrease from 3 to 2;
- `spikes k = k` for even k and zero for odd k is unbounded above on **every
  tail**, yet satisfies neither signed criterion and tends to neither infinity;
- the strict cutoff cannot simply include its boundary, and lambda has no tag
  interpretation or bound promotion.

The spike control is stronger than a global-range unboundedness example: the
quantifier order `∀ l, ∀ j, ∃ k > j` is insufficient for the source's
`∀ l, ∃ j, ∀ k > j`. Thus oscillation and arbitrarily large values do not alone
establish infinity representation. The nonmonotone diverger independently shows
that monotonicity is not a required premise.

This is a source criterion/limit correspondence with representation examples and
uniqueness, **not a full quotient/transfer theorem**. We do not construct all
real representatives, prove quotient operation independence, promote arbitrary
exceptional arithmetic, or complete mixed numerical comparisons. These remain
separate items in the [completion ledger](CHAPTER2_COMPLETION.md). The milestone
stays in review unit 2; native behavior and FP assumptions are unchanged.

```sh
lake build InfinityStreams
lake env lean tests/InfinityStreams.lean
./check.sh
```
