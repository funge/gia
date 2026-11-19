# Native directed-arithmetic platform qualification

## Contract and implementation

The existing [conditional directed-binary64 contract](HARDWARE_ADDITION.md) is
unchanged. There are no new Lean axioms, rounding-error assumptions, alternate
widening algorithms, toolchain upgrades, or mathematical evaluator changes.
Successful scalar calls enclose the exact result; nonfinite inputs/results,
unsupported execution state, or rounding setup failures return unknown, never
absence. A failed restoration aborts rather than returning into Lean with a
changed floating-point environment.

`hardware/directed_core.c` is now the single scalar implementation. Both the Lean
FFI in `hardware/adapter.c` and the standalone qualification executable link the
same compiled object. The standalone path is not a replacement or mock Lean FFI.
Input bit classification happens before FP arithmetic, so rejecting a signaling
NaN does not itself change exception flags. A separate `fegetenv` snapshot permits
restoration even if `feholdexcept` reports failure after changing state.

On x86_64, the existing MXCSR FTZ/DAZ rejection remains. On AArch64, the core reads
FPCR and admits only its four rounding-mode encodings; every other set bit fails
closed. This conservatively rejects FZ, FZ16, DN, AHP, AFP alternate/flush controls,
trap enables and unknown controls. FZ16 affects half precision, not our binary64
arithmetic; rejecting it is a conservative environment policy, not a claim that
it changes double arithmetic. Supported state is checked before entering the held
environment and immediately before each directed operation. Rounding and exception
handling remain contained within each call; ordinary Lean Float arithmetic is not
run under a changed global environment.

## Compiler and architecture references

- [Arm Cortex-A720 technical reference, FPCR](https://documentation-service.arm.com/static/64a3e7fcdf6cd61d528c478f):
  RMode, flush controls and optional alternate handling are distinct architectural
  controls. Optional bits must be observed by readback, not assumed implemented.
- [Apple XNU register definitions](https://github.com/apple-oss-distributions/xnu/blob/main/osfmk/arm64/proc_reg.h)
  and [FPCR feature probing](https://github.com/apple-oss-distributions/xnu/blob/main/osfmk/arm/commpage/commpage.c):
  Apple also probes control support rather than assuming all exception controls.
  The installed Apple SDK `fenv.h` identifies separate FPCR/FPSR fields and warns
  that its flush-to-zero environment is not IEEE-compliant.
- [Clang floating-point environment](https://clang.llvm.org/docs/UsersManual.html#accessing-the-floating-point-environment):
  `FENV_ACCESS ON` covers exception state as well as dynamic rounding. Both core
  and native-test translation units keep that pragma. The shared compile recipe
  retains `-frounding-math -fno-fast-math -ffp-contract=off -fno-math-errno`.

The instruction gate checks the actual object's native architecture and scalar
**double** operands: `addsd/subsd/mulsd/divsd/sqrtsd` on x86_64 or
`fadd/fsub/fmul/fdiv/fsqrt d…` on AArch64. A single-precision/vector opcode does not
qualify. A library `sqrt` reference is rejected. This is compiler-output evidence,
not a compiler-correctness theorem or proof that every possible build is safe.

## Repeatable checks

```sh
./hardware/check_native.sh              # existing C/Python tools; no Lean needed
./hardware/check_native.sh /new/path    # retain output; path must not already exist
./hardware/check.sh                     # pinned Lean FFI + all existing native suites
./check.sh                              # kernel proofs, audit, integration tests
```

`check.sh` in `hardware/` links the same object after running the standalone gate.
No hosted workflow is added or dispatched. The ordinary root test discovery adds
negative controls for the native oracle and instruction gate. Qualification refuses
Python optimization mode, which otherwise disables its assertions.

The standalone oracle decodes binary64 bits into exact rational values, then checks
all four arithmetic operations without host floating-point arithmetic as the oracle.
Square-root bounds are checked by exact squaring. It requires tight outward bounds,
not merely plausible output, and expects unknown for nonfinite results and poles.
Coverage comprises a signed boundary cross-product plus a fixed-seed raw-bit corpus:
7,440 vectors, each from four incoming rounding modes with clear and seeded flags
(59,520 calls). Eight exact bit anchors include signed zero, half-min-subnormal
multiplication/division, `sqrt(minsub)` and cancellation.

Every call checks architectural state restoration (FPCR/FPSR on AArch64;
MXCSR and x87 control/status on x86_64), including NaN rejection, negative square
roots, division by zero and both-sign overflow. Incoming mode/flag setup is itself
checked. AArch64 also tests unrelated FPSR.QC preservation across success and
failure. Nonstandard controls are tested individually, with readback; mandatory
FZ (or FTZ and DAZ) must be available, while unavailable optional controls are
reported as untested. Fault-injected fenv calls separately test a partially failed
hold, failed downward/upward setup, and mandatory abort on restore failure.

## Recorded evidence and limits (2026-11-19)

Baseline: post-PR-15 `afb77070f210275b349d8d64f2c693ef6b6e53bc`.
Qualification target: native arm64 macOS with Apple Clang 21.0.0. The old full
hardware entry point stopped because Lake was absent, and its x86 intrinsic
header independently failed native compilation.
No toolchain was installed to work around that blocker.

After this change, the standalone gate passes all 59,520 calls, exact bit anchors,
scalar-double instruction checks, and injected failure controls on that host.
All 13 probed FPCR controls (0, 1, 2, 8–12, 15, 19, 24–26) read back and were
rejected without mutation. Ten focused Python tests pass, including eight new
negative controls and the two existing square-root vector tests. Strict warning
compilation and shell syntax checks pass. The initial attempt to use `objdump -f`
was unsupported by Apple's Mach-O tool; the gate now reads the format header of
its actual disassembly output instead.

**Not yet qualified on this Mac:** the compiled Lean-to-C FFI or complete Lean
project suite, because the pinned Lean/Lake toolchain is absent. This record does
not extend historical x86 results to the changed shared-core build, claim other
AArch64 OS/compiler targets, or turn empirical checks into a runtime refinement
proof. Cross-platform regression and independent review results must be recorded
separately against the final patch. Private review material and local run logs are
not committed.
