# Hardware cosine and sine quadrant coverage on [-4,4]

This milestone adds a cosine kernel on [-1,1] and a closed-cell sine cover on
[-4,4]. It fills the gaps near extrema left by the [finite whole-period
search](HARDWARE_SINE_REDUCTION.md), while retaining that earlier interface.
The runtime composes existing directed binary64 primitives. It uses neither
libm sine/cosine nor rational arithmetic, dynamic integer conversion or a
new floating-point contract.

## Cosine construction

[CosineTaylor.lean](CosineTaylor.lean) proves, for -1 ≤ x ≤ 1,

```
C6(x) = 1 - x²/2 + x⁴/24 - x⁶/720
C6(x) ≤ cos(x) ≤ C6(x) + x⁸/40320
0 ≤ x⁸/40320 ≤ 1/40320.
```

The proof uses mathlib's cosine series, alternating-sum bounds and even symmetry.
The analytic point width is at most 1/40320 (about 0.0000248016), before hardware
rounding. This is not a final interval-width bound or a correct-rounding claim.
The [shared program](CosineProgram.lean) evaluates the polynomial with natural
interval operations and adds [0, upper(error)]. It then caps the upper endpoint
at exactly 1, justified by cos x ≤ 1. It does not assume cosine is monotone on an
interval crossing zero: the maximum can lie in the interior. Natural interval
dependency overestimation remains, especially for wide intervals.

[HardwareCosine.lean](HardwareCosine.lean) proves the program's pure specialization
sound under the existing primitive and finite-minimum contracts. `unit_run_sound`
discharges the actual [-1,1] guard. The native IO client instantiates the same
program with the existing hardware adapters. Constants 2, 24, 720 and 40320 are
exactly representable; their decoding is explicit in the proof interface.

## Closed cover and quadrant identities

The [shared quadrant program](QuadrantProgram.lean) uses this fixed table. Here
r = x - cπ and the last column is the function evaluated at r.

| Input cell | c | Local function |
|---|---:|---|
| [-4, -15/4] | -3/2 | cos r |
| [-15/4, -9/4] | -1 | -sin r |
| [-9/4, -3/4] | -1/2 | -cos r |
| [-3/4, 3/4] | 0 | sin r |
| [3/4, 9/4] | 1/2 | cos r |
| [9/4, 15/4] | 1 | -sin r |
| [15/4, 4] | 3/2 | -cos r |

The input is clipped against every cell with finite max/min. Empty intersections
are skipped, but every intersecting cell must evaluate successfully. A failed
cell aborts the computation as unknown; it is never discarded as if empty.
Successful results are combined by the interval hull, using min of lower bounds
and max of upper bounds. Shared boundaries belong to both adjacent cells.
Negative output uses existing directed subtraction from zero, not an exact
native-negation hypothesis. Pi uncertainty is preserved during every shift.

[HardwareCover.lean](HardwareCover.lean) proves clipping does not lose a covered
point, successful clips have a real witness, successful pieces have decoded
endpoints, and hulling encloses every piece. This is a hardware-interval client
of the cover principle, not a replacement for the existing parameter-cover APIs.
[SineQuadrants.lean](SineQuadrants.lean) proves the seven exact phase identities,
complete geometric coverage, the ideal residual bound for every pi inside its
certified dyadic bracket, and the end-to-end `quadrants_enclose` theorem.
The sine and cosine kernel obligations are discharged by their existing program
proofs; no transcendental-accuracy axiom is added.

## Source correspondence

Tupper §3.1.6, printed p.48
([PDF page 64](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=64)), explicitly
describes combining sine, a similar cosine construction and argument reduction.
Our sixth-degree cosine bracket is an implementation of that basic-methods
approach, not an equation or proof copied verbatim from the thesis. The domain
is deliberately narrower than the source's full finite-argument ambition.

The cover/intersection/hull mechanism is related to §3.2.6, printed p.54
([PDF page 70](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=70)), visually
checked against the original repository PDF. We prove a sound finite cover and
hull construction; we do not claim the source's minimal/proper-cover property or
membership of every cell in its monotonicity classes. In particular our cosine
cells can cross an extremum because their natural interval evaluator is sound
there. The existing [pi and periodicity source comparison](HARDWARE_SINE_REDUCTION.md)
remains applicable. Markdown transcriptions are not the authority for formulas.

The initial C comparison targets are relgraph's
[`gi_trans_cos`](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/transcendental.c#L737)
and [`gi_trans_sin`](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/transcendental.c#L644).
Those private-repository references may require access. No correspondence to their
MPFR algorithms or C implementation is proved; GIA builds independently.

## Trust, partiality and limits

No FP contract changes: finite decoding, exact finite min/max and comparison,
directed arithmetic, and IO/FFI/compiler/hardware refinement retain their
existing trusted status. The finite table instantiates constant-decoding
obligations for dyadic cell boundaries and half-integer phase coefficients.
The pi enclosure is proved mathematically; its bit decoding remains trusted.
The adapter C, compiler flags, dependency pins and licenses are unchanged.

Geometric coverage of [-4,4] and successful-result soundness are kernel-checked.
The enclosure-only adapter contracts deliberately permit failure and loose
bounds. Consequently, the ideal residual-fit theorem is not a universal theorem
that every native call succeeds: rounding may widen, or a primitive may fail.
The concrete hardware path is tested over full cells, boundaries and samples,
including the whole [-4,4] input, but tests do not prove FFI totality or refinement.

Unsupported/nonfinite/reversed inputs and any cell failure remain unknown. Real
sine/cosine are total; this failure does not assert undefinedness. The existing
same-witness `SinValues` lifting preserves arbitrary external domains and holes;
numeric enclosure does not establish an admissible input exists. There are no
raster, pixel or graphing assumptions in these arithmetic results.

Full-range argument reduction, dynamic quadrant selection, precision guarantees
for very large inputs, tighter cosine interval evaluation and correct rounding
remain future work. Inputs beyond [-4,4] are not silently mapped into this cover.

## Verification

Run `./check.sh` and `./hardware/check.sh`. The [Lean fixture](tests/CosineQuadrants.lean)
uses independent exact-real operations to exercise clipping, all phase branches,
reflection and hulling. It also checks a counterexample to endpoint-only cosine,
late-cell failure, analytic bounds and external holes.

The [native oracle](hardware/check_quadrants.py) checks exact simulated directed
arithmetic and 17 independent analytic samples for each of 68 cosine and 149
quadrant vectors. The sine oracle evaluates a higher-degree series at the original
input, independently of pi reduction. Cases include signed zero, subnormal inputs,
full-range intervals, extrema, every cell boundary and adjacent binary64 values.
The native whole [-4,4] result is exactly [-1,1]. Rational arithmetic appears only
in these test oracles, never the runtime. See [VALIDATION.md](VALIDATION.md) for
qualification and the distinction between local source review and implementation
verification.
