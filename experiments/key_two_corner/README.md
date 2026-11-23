# Opt-in proved-key selector experiment

This experiment uses the actual `KeyTwoCorner.requests` proved equal to
`WordTwoCorner.requests`; see [the proof](../../KEY_TWO_CORNER.md). It does not
substitute an unchecked sign dispatcher. The previous rational-reference
experiment remains untouched on its own branch.

Modes are 0 = unchanged four-corner baseline, 1 = rational Word reference,
2 = proved UInt64-key selector. Both selected routes share one IO executor and
the unchanged paired-bound native scalar division. Original raw operands are
retained. All default targets, hardware C/FFI sources and arithmetic build flags
are unchanged. The only experimental C file probes caller environment; it
implements no arithmetic. `keyCornerExperiment` is an explicit opt-in Lake target.

## Reproduce

With pinned Lean 4.19.0 and Python mpmath:

```sh
bash experiments/key_two_corner/build.sh
./check.sh
./hardware/check.sh
# After all proof/native gates pass and background checks finish:
.lake/build/bin/keyCornerExperiment bench > experiments/key_two_corner/out/benchmark.txt
python3 experiments/key_two_corner/summarize.py experiments/key_two_corner/out/benchmark.txt
```

The build script runs unchanged instruction, core-oracle and fault checks. The
Python Fraction oracle independently checks ordered raw requests, all four exact
corner quotients, decoded containment, observed raw differences and call counts.
All direct cases run in four caller rounding modes × two exception-flag seeds.
New and rational routes must agree on actual requests, results and dispatched
paired calls in this test; this is empirical qualification, not a new universal
native equivalence theorem. Invalid inputs must dispatch zero selected calls.
Kernel controls run the actual SineProgram/CosineProgram functions with only their
division argument varied; 100-digit sampled values supplement existing proofs.

The Float bridge is unproved. Supplied and observed input words are recorded;
only NaN-to-NaN canonicalization is allowed, never finite/zero changes. Actual
signaling-NaN transport and payload preservation remain unqualified. Word/Nat
oversized-input rejection is kernel-checked, not simulated by narrowing into a
native Float. Omitted-corner failure asymmetry is covered by separate existing
logical fixtures, not selectively injected native failures.

## Measurement

End-to-end workloads: positive singleton denominator; negative non-singleton
denominator; actual sine and cosine kernels; positive non-singleton denominator.
Identical input sequences and output checksums are used across all three modes.
Warmup: 200 outputs per mode/workload. Measurements: 9 repetitions × 2,000 outputs,
rotating mode order so each mode occupies each position equally. Each output is
materialized with `toBits` and consumed into a printed checksum. Actual paired
scalar-call dispatches are counted with the same IO.Ref wrapper; these are not
counts of individual directed instructions.

Selector-only runs compare modes 1 and 2 with the same input construction,
Float-to-Word conversions and consumed raw request words. One quarter of inputs
have a zero-touching denominator and must reject. After 200 warmups, 10 alternating
repetitions × 2,000 inputs are measured, recording valid/rejected counts.

Absolute elapsed nanoseconds use `IO.monoNanosNow`; summaries give per-output/input
medians and full ranges. Conversion, range guards, allocation, exact rational
validation (mode 1), UInt64 key computation (mode 2), common counters and checksum
work are included as applicable. No rational arithmetic runs in mode 2 selection.
Printing, compilation, startup and qualification are outside timed loops. Native
compilation uses the unchanged optimized project flags and Lean release compiler.
No CPU affinity/frequency policy is imposed. Results concern only this sampled
Linux path, not shipping performance, other architectures or a future direct
UInt64 API that omits the measured Word wrapper.

Generated raw evidence is in ignored `out/`; checksums and observed results are
recorded with the final local validation. No production route is changed.

See [the qualified results](RESULTS.md) for counts, timings, spread and limitations.
