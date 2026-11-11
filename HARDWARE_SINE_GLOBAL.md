# Global sine fallback and composed period reduction

The native `sineGlobal` client accepts ordered intervals with finite binary64
endpoints. It first tries the existing whole-period coefficients 0, ±2, ±4,
now using the certified [-4,4] quadrant kernel instead of only the [-1,1]
local kernel. It returns the first successful refinement. If every attempt
fails, it returns the mathematically proved global sine enclosure [-1,1].

This provides a conservative result for all finite input magnitudes, including
maximum-finite binary64 values. It does **not** provide accurate full-range
argument reduction. The fallback is intentionally uninformative about phase;
its width is 2. NaNs, infinite endpoints and reversed intervals remain unknown.
The existing restricted kernels and search APIs keep their previous behavior.

## What is proved

- [SineQuadrants.lean](SineQuadrants.lean), `period_quadrants_sound`, composes
  the actual quadrant program with the existing certified period search. The
  same real input witness is retained through both reduction levels, and pi
  uncertainty is propagated at each level.
- [SineReduction.lean](SineReduction.lean), `global_enclosure`, proves
  -1 ≤ sin x ≤ 1 for every real x from mathlib. This is not a libm contract.
- `globalFallback_sound` proves that either a sound refinement or the global
  fallback encloses every input value. `globalFallback_defined` proves the pure
  wrapper returns a result when its guard accepts, even if refinement fails.
- [SineReductionProgram.lean](SineReductionProgram.lean) supplies the shared
  monadic wrapper instantiated by both proofs and native IO execution.

The pure success theorem assumes the supplied pure search has returned its
Option result. It does not prove native IO termination, Float decoding, FFI
refinement or hardware behavior. No new floating-point assumptions are added.
The constants -1 and 1 instantiate existing exact decoding obligations; all
other primitive, comparison and min/max contracts are unchanged.

A failed attempt is never mistaken for a successful tight enclosure. The wrapper
uses a separate proved bound after exhaustion. Numeric success does not fill
external domain holes or establish that an admissible input exists: the existing
same-witness `SinValues` relation and its domain restriction remain applicable.

## Coverage and source correspondence

Tupper §3.1.5, printed pp.47–48
([PDF page 63](https://www.dgp.toronto.edu/~mooncake/thesis.pdf#page=63)), motivates
interval argument reduction before invoking a local approximation. The original
PDF p.47 was checked again for this milestone; its fractional-part formula uses
one half, unlike the damaged Markdown transcription. This implementation reuses
certified integer shifts and does not implement that fractional-part formula.
The cosine/quadrant kernels follow §3.1.6 and the cover construction discussed
in [their source comparison](HARDWARE_COSINE_QUADRANTS.md).

The new integration gives useful bounds near shifted extrema: [7.5,8] and
[-8,-7.5], for example, now have strictly positive/negative enclosures. A wide
interval such as [-20,20], or an isolated input 100, falls back to [-1,1]. Even
small intervals can fall back if their reduction does not fit one supported
window. There is no universal precision or native success theorem for the
refinement path. Dynamic period selection, accurate large-argument reduction
and tighter pi representations remain open work, not hidden assumptions.

The initial C comparison remains
[`gi_trans_sin`](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/transcendental.c#L644).
That implementation uses a different algorithm; no C correspondence is proved.
Its private link may require access; GIA has no build dependency on relgraph.

## Checks

`./check.sh` exercises the Lean proofs, enforced axiom allowlist and semantic
controls. `./hardware/check.sh` includes 267 new finite vectors, independently
simulates the directed period/quadrant pipeline, and checks nine original-input
series samples per interval within [-16,16]. The huge-input controls check the
exact global fallback, not an unreliable huge-angle series. The oracle handles
nonfinite intermediate rounding as a rejected refinement, matching the adapter.
It also checks shifted extrema, invalid input rejection and injected failure.
All previous native checks remain enabled. See [VALIDATION.md](VALIDATION.md).
