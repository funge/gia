# Proposed hardware floating-point architecture

Historical assessment, 2026-11-08. John subsequently authorized the small
[conditional hardware addition milestone](HARDWARE_ADDITION.md) with an explicit
directed-operation contract. The broader options below remain proposals.

Status at assessment time: for John's decision. No implementation choice,
toolchain upgrade, FFI override or new assumption has been adopted.

The goal is provably correct interval arithmetic executing with hardware floating
point. Exact rational implementations are supporting mathematics and test oracles,
not the intended runtime or a substitute for this goal. The [Tupper gap map](FLOATING_POINT_ROADMAP.md)
records source coverage; this note supersedes its earlier suggested next work item.

## Evidence from the installed environment and upstream

The project is pinned to Lean 4.19.0. Its installed `Init/Data/Float.lean` defines
`Float` through an opaque specification; add/subtract/multiply/divide and bit
conversions are opaque externs. Its installed `include/lean/lean.h` implements
`lean_float_add`, `lean_float_mul` and `lean_float_div` using C double operators.
Thus hardware execution exists, but those definitions do not give the kernel a
usable real-valued arithmetic specification. The pinned mathlib tree contains no
Float module found by the filename inventory. This is not a claim that no suitable
external library exists.

Upstream changed this: the [Lean 4.33 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.33.0/)
introduce a logical float model, with empirical TestFloat validation, while keeping
native execution. It is expressly a foundation for downstream proofs, not a complete
floating-point theorem library. The [versioned source](https://raw.githubusercontent.com/leanprover/lean4/v4.33.0/src/Init/Data/Float/Float.lean)
defines arithmetic through `Float.Model` with native extern replacements. The
[4.33 reference](https://lean-lang.org/doc/reference/4.33.0/Basic-Types/Floating-Point-Numbers/)
conditions runtime/model agreement on an unchanged floating-point environment;
trigonometric operations remain opaque. These sources were inspected, but 4.33
has not been installed or its mathlib compatibility tested here.

In this repository, [interval.c](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/interval.c#L110)
uses architecture-dependent rounding control (including x86 MXCSR and fenv) and
raw arithmetic wrappers. [transcendental.c](https://github.com/funge/relgraph/blob/3975a5e1696e59c337093435ffce0748f074a057/src/transcendental.c#L24)
uses MPFR directed sine/cosine calculations and directed conversion to double.
That existing transcendental implementation is software multiprecision, not a
hardware-only elementary-function implementation. Neither file has been verified
by the current Lean proofs.

## Candidate architecture and alternatives

Recommended structure: a binary64 endpoint representation and its real/extended
interpretation; primitive arithmetic specification; executable interval algorithms
using those primitives; enclosure/domain theorems; and a separately documented
runtime refinement boundary. Generalized shared-parameter semantics sit above
these layers. Real/rational reasoning can occur in proofs without running rational
arithmetic in the deployed evaluator.

| Route | Benefit | Proof and trust obligation |
| --- | --- | --- |
| Newer Lean native model, ordinary hardware arithmetic plus proved outward adjustment | Reuses upstream representation and native execution without changing global rounding mode | Prove real semantics and neighbor/rounding enclosure, including overflow, subnormal values, zeros and NaNs. A one-neighbor adjustment is a candidate requiring proof, not an adopted guarantee. Expect wider results than tight directed rounding |
| Dedicated directed primitive interface with hardware wrappers | Closest to Tupper's directed operations and the existing C basic arithmetic | Prove interval algorithms against primitive contracts; explicitly trust or later verify wrapper/compiler/hardware correspondence. Do not redefine ordinary Lean `Float.add` to behave under a changed environment. State changes must be contained and restored |
| Fully proved implementation-to-machine refinement | Strongest end-to-end assurance | Requires substantially more compiler/runtime/platform work than the current mathematical proofs; not necessary to start the first two routes |

For the first route, an isolated toolchain feasibility branch is preferable to
upgrading the entire proof stack immediately. For the second, the existing approved
outward-enclosure assumptions can state the mathematical obligation, but identifying
an actual hardware wrapper as satisfying them introduces a new runtime trust claim.
It must be explicit and approved; a Lean axiom or extern override would not prove it.

## Directed rounding and transcendental scope

Tupper §2.5.3 (printed p. 20 / PDF p. 36) uses outward rounding and permits loose
transcendental brackets. §2.10 (pp. 32–33 / PDF pp. 48–49) separately requires
coefficient demotion and outward evaluation of bound functions. See the linked gap
map for precise source references. Existence of rounding modes alone does not
certify a particular libm function or its range reduction.

A bounded first executable milestone should be binary64 interval addition, then
multiplication and guarded division, with edge cases tested independently and
proved at the chosen model boundary. Transcendentals should initially remain
unsupported/unknown in that new backend unless their separate enclosure contract
is justified. Later choices include proved approximations executed with hardware
basic operations, or explicitly trusted certified-library contracts. Merely widening
a stock sine result by one representable value is not an established enclosure.

## Decisions requested through the parent

1. Permit an isolated feasibility study using Lean's newer native logical model,
   without changing the existing project pin until compatibility is established?
2. Prefer native default-mode arithmetic with proved outward adjustment, or tight
   directed primitives with an explicit, initially trusted hardware-wrapper boundary?
3. Is software-assisted certified transcendental evaluation acceptable, or should
   the eventual runtime use hardware basic operations throughout?

My recommendation is to investigate the newer native model first, retain directed
wrappers as the alternative, and defer the transcendental backend choice. No such
assumption or architecture has been silently adopted. Successful model proofs still
leave compiler/runtime/hardware trust; empirical execution tests do not remove it.
