# Hansen coefficient sets of finite real values

This is a derived mathematical extension of the finite [Hansen coefficient correspondence](HANSEN_COEFFICIENTS.md), motivated by Tupper §2.14, printed p.40 / [PDF p.56](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=56), together with the set representations and demotion discussion in §§2.13–2.14. The printed Hansen formula is the source anchor, not a claim that Tupper explicitly states this coefficient-set theorem or prescribes our persistent-choice convention. The displayed two-point parameter restriction is unchanged; the theorem works at any fixed vector and hence at those points.

[HansenRealSets.lean](HansenRealSets.lean) uses arbitrary sets of **finite real values** for an offset and finitely many slope coefficients. They can be empty, unbounded, open, closed, or disconnected. The actual output uses one complete admissible coefficient tuple at one parameter vector. Literal infinite coefficients and λ are not elements of these sets, and no arithmetic for them is introduced.

## Exact results and assumptions

- `nonempty_iff`: the output exists exactly when the offset and every slope coefficient set are nonempty. This is a strict tuple interpretation: `empty_coefficient` yields the empty image even at zero weight. It is not an expression simplifier allowed to drop undefined operands.
- `zero_weights`: with all slope sets nonempty, the zero-vector image is exactly the offset set, even when slopes are unbounded. This never computes zero times an infinite value.
- `finite_agreement` reuses #46 directly for finite closed rational coefficient intervals; it does not reprove that endpoint formula.
- `between` and `interior_attained`: if all coefficient sets are convex, every finite point strictly between the extended infimum and supremum of the actual output is attained. No boundedness, closedness or endpoint attainment is assumed. The proof constructs a common coefficient tuple by interpolating two attained tuples.
- `exact_membership`: the image consists of that open extended interior plus exactly the finite boundary values with actual admissible coefficient witnesses. `hull_exact_iff` characterizes when the least closed extended-bound hull equals the image: every finite boundary point in the hull must be attained. Empty images and infinite bounds are included.

The bounds are those of the actual image, computed mathematically by the existing [extended image hull](EXTENDED_IMAGE_HULL.md). Its soundness and endpoint minimality apply to all these sets, even without convexity; this is not a new endpoint-evaluation algorithm. Disconnected coefficient sets can leave interior holes, so the stronger exact interval membership theorem requires convexity. Bounds need not be values. The empty image has reversed bounds top/bottom.

## Demotion and tags

`hull_sound` instantiates the existing general family demotion theorem at each **same parameter**, retaining the coefficient witness and exact input-domain obligations. It does not assert that every point in the hull is a value, or that separate coefficient choices across uses form a single family member. A whole tuple can still be retained across uses as in #46; hull conversion does not manufacture a new shared witness.

`tagged_hull` composes with the existing tagged conversion interface: if the finite part of a tagged family is this image, its converted finite part is exactly this hull, and membership of each literal −∞, +∞ and λ tag is unchanged. This is a conditional correspondence for an already specified tagged family, not an evaluation rule for infinite coefficients or undefined arithmetic.

## Controls and limits

[Kernel fixtures](tests/HansenRealSets.lean) cover an open (0,1) image with finite unattained bounds, a one-sided (0,∞) image, all-real outputs from a genuinely free slope at positive and negative nonzero weights, zero-weight annihilation only for nonempty slope sets, an empty slope at zero weight, a disconnected image, and the distinction between infinite bounds and exceptional tags. Explicit λ membership is retained rather than created or discarded.

Run `./check.sh` with the pinned tools; see [VALIDATION.md](VALIDATION.md) for the qualification receipt. This is proof-only: no new axioms, FP assumptions, native arithmetic or defaults. Remaining work includes source-specified arithmetic/demotion for the whole Hansen system, literal exceptional coefficient evaluation where justified, and executable representation algorithms. It does not close Chapter 2 or prove a global multivariate optimization or correlation-preserving hull algorithm.
