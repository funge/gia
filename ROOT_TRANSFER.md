# Partial square root through hull conversion

Source: Tupper §2.5.2, printed p.19 / [PDF p.35](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=35), explicitly gives the negative-root λ example and describes returning λ for operations outside their real domain. This milestone reuses the existing ideal partial-real `SqrtValues` relation and `ExceptionalComparisons.sqrtObservation`, already scoped in [exceptional arithmetic](EXCEPTIONAL_ARITHMETIC.md). It connects those semantics to the Chapter 2 image-hull/demotion framework. The transfer theorem is a derived mathematical result, not a printed assertion that arbitrary hull conversion commutes with square root.

No source observation row changes. Finite real payloads have a root only for nonnegative input; negative inputs yield the modeled λ result. Literal positive/negative infinity and λ inputs remain unmodeled (`none`). This does not specify IEEE behavior, correctly rounded root evaluation or a root of a literal infinity.

## Exact graph and sound transfer

[RootTransfer.lean](RootTransfer.lean) defines `roots S` by the existing partial relation, not mathlib's totalized square root on negative inputs. `root_iff` characterizes its actual image: `z` occurs exactly when `z ≥ 0` and `z² ∈ S`. This retains an attainable input, rather than treating enclosure membership as existence.

`roots_mono` and `hull_sound` give sound transfer through input hull conversion and an output hull. `witness_transfer` carries the original partial-expression input witness at the same parameter into that enclosure; it does not create values on an absent domain. The theorem promises neither exactness nor optimal bounds for the original image after widening.

`exact_iff` gives a necessary and sufficient condition for `roots(hull S) = roots S`: every nonnegative real admitted by `hull S` already belongs to `S`. Negative holes can be irrelevant to the real root image; new nonnegative inputs cannot be ignored because square root is injective there. Closed extended-bound real intervals satisfy the condition via the existing hull fixed-point theorem (`interval_exact`), including empty/reversed and unbounded real intervals.

For tagged families, `finite_graph`, `lambda_graph`, `missing_graph` and `no_infinite_results` characterize the existing observation table. `observations_sound` preserves every original observation. `negative_iff` proves that hull conversion has a negative witness exactly when the original real set did; therefore `statuses_exact` preserves λ-result existence and missing exceptional-input coverage. `observations_exact_iff` proves that the same no-new-nonnegative-input condition is necessary and sufficient for equality of the **complete observation images**, not only finite results.

## Checked failures of unconditional equality

The [kernel fixtures](tests/RootTransfer.lean) use `S=(-1,0)`. It has no finite roots, but its closed hull is `[-1,0]`, which admits input zero and hence root zero. Thus `roots(hull S)` is not `hull(roots S)`. The original λ-result remains present after conversion; the added zero is a new finite result, not evidence of an original defined input.

A second fixture uses `S={0,4}`. Hull conversion admits input 1 and root 1, although root 1 was absent originally. This changes the image even though the original family already had defined roots. Other controls prove the closed mixed interval image `sqrt([-1,4])=[0,2]`, all-real-input root image `[0,∞)`, empty-image behavior, preserved λ observations, and unmodeled literal exceptional inputs without invented infinite roots.

## Scope and remaining gaps

Unbounded sets of finite reals remain separate from literal infinite inputs. Extended infinities are hull endpoints only; no arithmetic on them is introduced here. λ outputs and `none` observations remain distinct. Observation/set equality is structural, not Tupper's exceptional numerical equality predicate.

This closes exact input-hull transfer criteria for the existing nonconstant partial root model. It does not provide an automatic test of those criteria, a complete exceptional root table, a general conversion homomorphism, or numerical rounded implementation. Other partial operations need their own boundary and image conditions. The source's unresolved exceptional rows and broader Chapter 2 representation claims remain open; Chapter 2 is not declared complete.

Run `./check.sh`; [VALIDATION.md](VALIDATION.md) records qualification. No new project axioms, FP assumptions, native/default changes or performance claims.
