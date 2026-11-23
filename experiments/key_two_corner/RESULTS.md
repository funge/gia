# Proved key selector: local results

Base checkpoint: `5f898703d3d79b21133bee3dfbee48c9cdf9dfa1` (retained unchanged).
Reference selector: `b122f657caceafbfeaa2c0eeafc2dc01bdb769d6`.
This continuation completes decoded-order and exact raw-request equivalence;
see [proof scope](../../KEY_TWO_CORNER.md). Nothing is deployed or published.

## Qualification

- Full `./check.sh`: 29 tests passed in 319.580 seconds, no skips; 979 named axiom
  audits, 1,900 namespace declarations, 124 libraries, 57 semantic fixtures.
  Pinned C API comparison passed against an explicitly supplied read-only checkout.
- 1,544 direct native runs: 193 distinct cases × four incoming rounding modes ×
  two exception-flag seeds. All 184 invalid runs rejected with zero selected calls.
  Both selected routes returned 1,352 successful enclosures and eight valid-input
  overflow failures. Every successful result encloses the exact four-corner
  rational image and refines every successful old enclosure.
- Key and rational routes agreed on actual ordered requests, output words and
  dispatched-call counts in all runs. An independent Fraction oracle checked the
  requested raw pairs, not merely equality of quotient results.
- 16 raw-output differences versus four-corner assembly (two signed-zero cases ×
  eight states), zero observed availability differences. Signed zeros were not
  normalized. These observations do not prove operational equivalence in general.
- 45 actual compiled kernel comparisons passed; all three outputs matched in
  these cases. Sine/cosine also passed 33 independently evaluated 100-digit samples
  per interval. Sampling supplements, rather than replaces, the existing proofs.
- Whole-route rounding-mode and exception-flag preservation passed for all direct
  runs. The unchanged core separately passed instruction checks, control-bit
  rejection/restoration, 7,440 exact-oracle vectors / 59,520 native calls and
  environment-failure controls. The existing complete `hardware/check.sh` passed.

The two observed raw differences were:

| Quotient | Both selected routes | Four-corner route |
|---|---|---|
| `[-0,+0]/[-2,-1]` | `[-0,+0]` | `[+0,-0]` |
| `[-minsub,+0]/[-4,-2]` | `[-0,+minsub]` | `[+0,+minsub]` |

The native Float bridge canonicalized 64 NaN inputs. All finite, infinity and
zero input words round-tripped exactly in this dataset; NaN-to-NaN changes were
recorded. **Actual signaling-NaN transport and payload preservation remain
unqualified.** Raw Word signaling-NaN rejection is proved separately. Existing
omitted-call-failure fixtures remain proof-side controls, not injected native
failures. Neither C execution nor the Float bridge has become formally verified.

## Matched timing

Linux x86_64, Intel Xeon Platinum 8573C; Lean 4.19.0; core/adapter compiled with
Debian GCC 14.2.0 and unchanged `-O2 -frounding-math -fno-fast-math -ffp-contract=off
-fno-math-errno` controls. Lake's default release build uses Clang 15.0.1 via
leanc (`-O3 -DNDEBUG` for generated Lean C). No affinity/governor policy was set.
All gate/qualification jobs finished before timing. See the [measurement method](README.md).

End-to-end medians and full observed ranges in **microseconds/output**:

| Workload | Four corners | Rational selector | Proved key selector |
|---|---|---|---|
| positive singleton | 1.793 (1.734–2.923) | 14.449 (13.937–17.715) | 1.086 (1.060–1.351) |
| negative non-singleton | 1.738 (1.633–2.578) | 18.627 (15.116–21.432) | 1.655 (1.574–1.819) |
| SineProgram | 14.438 (12.774–18.836) | 61.263 (52.842–85.493) | 13.140 (11.105–14.924) |
| CosineProgram | 18.644 (15.759–25.283) | 78.060 (69.458–105.821) | 15.608 (13.952–17.217) |
| positive non-singleton | 1.919 (1.697–3.015) | 17.743 (15.282–19.533) | 1.373 (1.197–1.949) |
All 270,000 measured outputs succeeded, 90,000 per mode; warmups add 3,000 outputs.
Actual paired-bound division calls: 720,000 four-corner, 360,000 rational-reference,
360,000 key. Per output: direct 4→2, sine 12→6, cosine 16→8. These are paired calls,
not individual directed instructions.

Selector-only measurements (including identical input construction/conversion and
consumed raw request words) were 14.849 µs/input median (14.117–16.423) for rational
selection and 0.769 µs/input (0.735–1.632) for the proved key. Each processed 20,000
measured inputs: 15,000 valid and 5,000 rejected, with no hardware division calls.

The proved route removed the large rational-validation cost in this sample.
End-to-end medians were lower than the sampled four-corner baseline, but ranges
overlap for several workloads, particularly the negative non-singleton case.
These are noisy local measurements, not a production/other-platform guarantee.
No unchecked Float sign selector, altered default, new rounding assumption or
round-to-nearest widening was used.

## Evidence

Reproducible commands are in [README.md](README.md). Generated local files in
`out/` include `qualification.json`, `route-stdout.txt`, `route-stderr.txt`,
`kernels.txt`, `benchmark.txt`, `timing-summary.jsonl` and native-core reports.
Their hashes are recorded in `EVIDENCE.sha256`. The complete project/native logs
are also retained locally outside the repository; no private source was published.
