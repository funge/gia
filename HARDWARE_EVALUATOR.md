# One-variable hardware evaluator with ordinary and affine tracks

This is a small, graphing-independent polynomial evaluator: finite binary64
constants, one variable, addition, subtraction and multiplication. It evaluates
the same expression independently using ordinary intervals and shared-parameter
affine forms, then intersects the resulting bounds at the root. It does not add
division, transcendental syntax, a graphing classifier or a resource budget.

## Reuse and representation

[HardwareEvaluatorProgram](HardwareEvaluatorProgram.lean) defines a constant-
parameterized `Polynomial C` and **one** monadic `eval` traversal. Both backends
reuse it. Existing `Expr`/`eval` and `evalLinear` use rational constants, two
coordinates and division; adapting those would require changing their public
semantics or adding a rational-to-hardware conversion. This intentionally smaller
syntax accepts hardware constants directly and leaves the older APIs unchanged.
It is not a second copy of either arithmetic implementation.
The traversal is marked `@[nospecialize]`: Lean 4.19 otherwise emits an opaque
compiler-specialization declaration rejected by the namespace audit. Disabling
that optimization keeps the existing audit policy intact; measurements below
use this final compiled path.

Ordinary evaluation uses the existing directed interval add/subtract/multiply.
`affineEval` supplies the existing hardware affine add/subtract and
[quadratic-residual product](HARDWARE_AFFINE_PRODUCT.md) to the same traversal.
For an input interval `[l,u]`, `seed` constructs exact endpoint forms `[l,l]` and
`[u,u]`: every variable occurrence denotes `(1-t)*l+t*u` for the same `t∈[0,1]`.
`seed_sound` proves agreement between representations; `seed_covers` proves that
every real value in the supplied interval has such a parameter witness, including
singleton intervals without dividing by their width; and
`constant_form_sound` proves constant lifting. Native constants denote their
actual binary64 real values, not the exact decimal or rational number a user
might have intended before conversion. Finite literal parsing/refinement is not
newly verified here.

Each track may fail independently. There is no cross-track substitution inside
the tree: affine structure is retained until the final hull. No common-subexpression
elimination, adaptive subdivision, simplification or special `x*x` primitive is
introduced. Native adapters are demonstrated in [hardware/Main.lean](hardware/Main.lean);
the shared traversal and arithmetic program are reusable library modules.

## Result policy and proved claims

`Result` distinguishes three outcomes:

| Ordinary track | Affine hull | Result |
|---|---|---|
| success | success, overlapping | intersection |
| success | failure | ordinary bound |
| failure | success | affine hull |
| failure | failure | unknown |
| success | success, disjoint | **conflict**; neither bound is returned |

Intersection reuses the existing `HardwareQuadrants.clip` implementation and
`HardwareCover` proofs. Their historical module names do not make this operation
graphing- or trigonometry-specific. A module relocation was not needed for this
bounded integration. Touching intervals intersect at a singleton. A conflict is
not an empty real domain and must not silently become a successful fallback.

[HardwareEvaluator](HardwareEvaluator.lean) proves:

- `eval_sound`: compositional enclosure for the generic traversal and relational
  real semantics `Value`. Constants require successful interpretation; every
  occurrence of the variable has the same real value.
- `ordinary_eval_sound` and `affine_eval_sound`: instantiate the traversal with
  the established operation contracts and shared-parameter proofs.
- `run_sound`: a returned combined bound encloses that same real value.
- `ordinary_survives` and `run_ordinary_survives`: under common-value soundness,
  ordinary success yields a successful combined bound containing the value,
  and **every value in the combined bound belongs to the ordinary bound**.
  This proves non-widening by set inclusion, not just sampled numeric widths.
- `merge_no_conflict`: valid contracts enclosing a common value cannot produce
  a conflict. The executable nevertheless exposes conflict for inconsistent
  outputs, rather than masking an adapter or caller error.

The [integration fixture](tests/HardwareEvaluator.lean) composes the AST semantics,
both concrete backends and intersection in one theorem, and then applies it to
every real input in the original interval using `seed_covers`. It also checks both
fallback directions, both failures, deliberate contradiction and a shared
boundary. The native suite independently supplies contradictory intervals to the
combiner; no theorem pretends these satisfy a common-value premise.

## Widths and measured runtime

Observed widths on input `[0,1]`:

| Expression | Ordinary | Affine hull | Combined |
|---|---:|---:|---:|
| `x*(1-x)` | 1 | 0.25 | 0.25 |
| `x*x` | 1 | 1.25 | 1 |
| `x-x` | 2 | 0 | 0 |
| `x*(1-x)*(1+x)` | 2 | 0.625 | 0.5625 |
| `(x+1)*(x-1)` | 2 | 1.25 | 1.25 |
| `(x*x)-(x*x)` | 2 | 0.5 | 0.5 |

No exact symbolic cancellation of rounded products is assumed. Intersecting can
also improve upon both input widths, as the nested cubic example shows.

The isolated native qualification run on the cloud x86_64 Intel Xeon Platinum
8573C executor measured these medians:

| Expression | Ordinary ns/evaluation | Combined ns/evaluation | Ratio |
|---|---:|---:|---:|
| `x*(1-x)` | 5280.8 | 24662.4 | 4.670 |
| `x*x` | 3415.6 | 18925.6 | 5.541 |
| `x*(1-x)*(1+x)` | 8755.9 | 48378.7 | 5.525 |

Method: same AST/input and compiled adapter, 100 untimed warmups per path, then
five paired trials of 1,000 evaluations each. Order alternates between paths.
`IO.monoNanosNow` measures elapsed time around loops without printing; successful
results are checked. Medians are computed separately per path and their ratio is
reported. The final timing run had no concurrent Lean compilation. Host scheduling
and shared-cloud noise remain uncontrolled; no affinity, statistical confidence,
performance threshold or cross-platform speed claim is asserted. The measured
combined path pays for two traversals and additional affine arithmetic. This is
a precision improvement, not a speedup. Exact compiler commands remain in
[hardware/check.sh](hardware/check.sh), with the established adapter flags.

## Failure, scope and trust

Across 66 native cases, 44 had both tracks succeed, one only ordinary, three only
affine, and 18 returned unknown. Inputs include signed/rounded intervals,
subnormals and maximum finite magnitudes; constants include a deliberately
unsupported NaN. At `[-maxFinite,maxFinite]`, `x*0` survives via the ordinary track
when affine slope computation overflows. Conversely, `x-x` survives via affine
endpoint cancellation when ordinary subtraction overflows. `maxFinite*maxFinite`
fails both tracks. All successful results match the exact directed-operation
oracle and contain nine independent rational real-semantics samples.

Malformed/nonfinite variable intervals yield a failed variable leaf; a constant
expression that never uses the variable may still succeed. Nonfinite constants
fail their leaf. Unknown means no available finite enclosure, not undefined real
polynomial arithmetic or absence. This syntax introduces no external domain
predicates; no claims about division poles or broader partial functions follow.
Deep expressions have no certified execution-resource bound in this milestone.

No new floating-point assumptions are introduced. Directed arithmetic, finite
comparison/min/max, decoding, IO/FFI, compiler behavior and hardware remain at the
existing explicit boundary. Lean proves the pure specialization of the shared
program; it does not verify the native adapter or compiler. The adapter C,
toolchain, dependency pins, licenses and compiler flags are unchanged.

## Tupper and initial C target

Tupper's [§2.9.3, printed pp.28–30](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=44)
provides the shared-parameter pointwise inclusion principle, and §2.9.4 on p.30
relates ordinary constant intervals to linear bounds. §2.9.5 motivates richer
quadratic intermediates; the existing product is a derived finite chord
construction. This dual traversal, root intersection, fallback and conflict
protocol are **project integration**, not a transcription of a thesis algorithm
or a claimed optimal generalized-interval evaluator. See the
[concordance](THESIS_CONCORDANCE.md) and [affine product guide](HARDWARE_AFFINE_PRODUCT.md).

Initial C comparisons remain pinned relgraph
[`gi_interval_add`](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/interval.c),
`gi_interval_sub` and `gi_interval_mul`, listed in the
[operation coverage ledger](OPERATION_COVERAGE.md). This adds no C API symbol,
verifies no C evaluator and introduces no dependency on relgraph or graphing.

Run `./check.sh` and `./hardware/check.sh`. The
[independent oracle](hardware/check_evaluator.py) checks both tracks and the
combiner separately, tracks all fallback classes, verifies non-widening, evaluates
real semantics independently at nine samples and summarizes timing without a
pass/fail speed threshold. Test-only rational arithmetic is never the native
runtime. See [validation receipts](VALIDATION.md).
