# Exact projection of finite branch unions

Tupper §2.13.1, printed p.39 / [PDF p.55](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=55), defines interval-set membership existentially and inclusion at one shared parameter. Its reciprocal example motivates retaining disconnected outputs. The page also contrasts perfect demotion using infinitely many singleton pieces with manageable finite descriptions. It does not supply an executable arbitrary closure or quantifier-elimination algorithm. This is a derived, explicitly restricted construction, not a transcription of a general algorithm.

## Exact theorems and premises

[MonotoneUnions.lean](MonotoneUnions.lean) reuses existing mixed-endpoint predicates, finite guarded pieces and [fractional-linear elimination](FRACTIONAL_PROJECTION.md).

`increasing_image` and `decreasing_image` give exact images of finite real windows with explicit open/closed flags, assuming continuity on the closed support and strict monotonicity there. Decreasing branches reverse both endpoints and flags. Reversed windows remain empty; equal endpoints admit a value only when both flags are closed. Strictness is essential for copying open flags; continuity is essential for filling all intermediate values.

`finite_projection` combines exact branch relations without inventing an input: every output retains an admitted branch and that branch's original witness. `finite_monotone_image` specializes this to a finite union of monotone windows. It does not assume that the common function is globally injective. Guards and endpoints may depend on an unchanged external parameter; the theorem applies at that parameter. This is an exact union, not its convex hull.

`finite_fractional_projection` instead combines the existing certified inverse descriptions. It preserves every original input piece and expression guard, including cancellation holes and poles. A pole at an open endpoint does **not** satisfy the closed-support continuity premise of the finite endpoint theorem. The fractional descriptor is the appropriate separate route; no finite output endpoint is invented there.

## Effective noninjective instance

`squarePieces` takes rational input endpoints and two boundary flags. It rejects reversed endpoints, reverses a nonpositive window, preserves a nonnegative window, or emits two pieces after splitting a crossing window at zero. `square_pieces_exact` proves that these existing compiled pieces describe precisely the real square image. `square_piece_expression` connects this to `Value x y (.mul .x .x) z`, with the same `x` in both occurrences. `guardedSquares` retains an explicit external parameter guard; `guarded_square_exact` proves its exact guarded image.

This is executable proof-side rational piece generation and membership, not a hardware path. No monotonicity discovery, arbitrary root decomposition or native caller is added. Arbitrary interior input guards cannot be dropped: split them into justified windows or retain them in the existing inverse descriptor. Genuine infinity and λ are not output members of these real images.

## Controls and remaining scope

[Kernel fixtures](tests/MonotoneUnions.lean) check:

- square of `[-2,2]`, including two distinct inputs attaining the same output;
- square of `(-2,-1]` equals `[1,4)`, preserving the reversed flags;
- the union of squares of `[-3,-2]` and `[0,1]` excludes `2`, while a single hull would admit it;
- reversed/empty and open/closed singleton inputs, and a retained external guard;
- constant and jump counterexamples to omitting strictness or continuity;
- an open pole counterexample to naive finite endpoint substitution, plus exact union projection using the existing reciprocal certificate;
- actual reference membership execution, checked separately by kernel theorems.

The remaining general output-conversion gap is certified discovery of branches and output descriptions for broader nonlinear/parameterized expressions, together with domain/property generation. The generic exact union theorem does not itself discover a decomposition. It neither proves exact image intersection for noninjective maps nor claims arbitrary functions have finite descriptions. No FP assumption, native code, dependency pin, default evaluator or exceptional arithmetic rule changes.
