# Finite exact interval algebra

[IntervalAlgebra.lean](IntervalAlgebra.lean) proves the finite exact rational
instance of the subdistributive law displayed in Tupper **§2.7.5**, printed p.25 /
PDF p.41 ([source](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=41)).
The source image was checked: §2.7.4 is interval extension; the algebra heading
and equation are in §2.7.5. §2.8 supplies the real-interval setting.

For ordered finite rational intervals `I,J,K`, interpreted over reals:

```
(I * (J + K)).Contains z → ((I * J) + (I * K)).Contains z
```

The operations are the unchanged `QInterval.add` and four-corner
`QInterval.mul`. `product_corners_least` first shows that a closed interval
containing all four corner products contains the entire product interval. Each
corner of `I*(J+K)` lies in the right side by the existing multiplication and
addition enclosure theorems and real distributivity. This proves containment of
all enclosed values, not merely a pointwise arithmetic identity or an assertion
that arbitrary interval members are attained expression values.

The source's actual-value associative trail is also proved:
`a∈I`, `b∈J`, `c∈K` imply `(a+b)+c∈I+(J+K)`. This reuses addition enclosure
and real associativity; it does not assert associativity for rounded intervals.

[Controls](tests/IntervalAlgebra.lean) include strict containment:
`I=[-1,1], J=[1,1], K=[-1,-1]` gives left `[0,0]` and right `[-2,2]`.
Thus reverse containment and equality do not follow. Zero-singleton and attained
endpoint controls are included. No operation implementation is replaced.

This exact rational result does **not** prove the source's broader machine
interval law under an arbitrary widening backend. Mere soundness permits unequal
extra widening on either side, so it cannot by itself establish subdistributivity.
Exceptional/infinite endpoint arithmetic and machine-rounding correspondence
remain separate obligations; no floating-point assumption is added.
