# Enforced axiom audit

`AuditPolicy.lean` implements build-time commands that use the pinned Lean
4.19.0 transitive axiom collector. The exact allowlist is `propext`,
`Classical.choice`, and `Quot.sound`. Any other dependency, including `sorryAx`
or a newly declared axiom, raises a Lean elaboration error and produces a nonzero
process exit. No parsing of human-readable audit output decides acceptance.

`#audit_axioms declaration` checks each named landmark and reports its dependency
set. `#audit_namespace GeneralizedIntervalArithmetic` also checks every imported
theorem and axiom declaration under that namespace. An empty selection is an
error. This catches imported public theorems and axioms omitted from the named
list. Definitions and private/internal dependencies used by those proofs are
traversed by Lean's collector too. Compiler-generated executable specializations
are not independently scanned: some have implementation-only axioms that are
absent from the mathematical proof dependencies. The allowlist is not widened
to admit those artifacts.

`Audit` is a default Lake target, so `lake build` enforces this policy. Lake's
ordinary dependency tracking reruns it when imported proofs or policy change.
For a fresh audit invocation independent of Lake's cached target, run:

```
lake env lean Audit.lean
```

The audit covers the imported environment, not arbitrary unimported source files,
other namespaces, unused definitions, or unreachable private declarations. New proof modules must be
imported by the audit (directly or transitively) and use the project namespace.
It does not prevent someone deliberately editing/removing the policy or build
target. Review those changes like any other trust-boundary change. This is
validation tooling based on Lean's collector and trusted toolchain, not a new
logical assumption or a formal verification of Lean itself.

## Failure-path integration controls

From this directory after building `AuditPolicy`:

```
python3 -m unittest discover -s tests -v
```

The Python standard-library test runner launches independent Lean processes on
temporary fixtures. It checks axiom-free and allowlisted declarations succeed,
while direct placeholder proofs, transitive custom axioms, omitted namespace
axioms/placeholder proofs, unknown names, and empty namespaces fail. Each
rejection check requires the relevant diagnostic as well as a nonzero exit,
except the unknown-name control, which tests Lean's name resolution failure.
The intentionally invalid fixtures are never imported into the project.

These local controls are not hosted CI and add no Python dependency to the native
application build. Historical validation records describe the earlier printed
reports truthfully; this milestone adds enforcement rather than retroactively
claiming the old command enforced an allowlist.

## Project coverage control

`./check.sh` also runs `test_project_integration.py`. Using Lean's own `--deps`
output, it verifies that all current root modules are registered in Lake,
reachable from the default targets, and imported transitively by Audit. Audit
must remain a default target. This guards against accidentally leaving a future
module unimported; it does not change the namespace or dependency allowlist.
The flat source-layout convention is checked explicitly. Test fixtures live
under tests and are excluded from library inventory. Every persistent Lean fixture
must appear in the test runner's explicit fixture registry. Each is elaborated in
a fresh Lean process and must report its own namespace audit without warnings.
Currently these are Integration.lean, CoverPipeline.lean, and CellCertificates.lean. Compiler dependency
output also verifies their transitive project imports exclude milestone modules
named `*Examples`, following the current module naming convention. Temporary
negative audit fixtures remain outside this persistent registry. These controls
do not constitute an independent proof checker or a second implementation. See
[INTEGRATION_ASSESSMENT.md](INTEGRATION_ASSESSMENT.md) for remaining trust limits.

## Hardware executable client

`hardware/Main.lean` is explicitly inventoried as an opt-in executable client,
not a proof library. Its extern IO adapter has a throwing logical fallback; it
is never loaded into the theorem audit. `HardwareBounds` and `HardwareAddition`
remain ordinary library roots in the audit import closure. The inventory check
still rejects any other unregistered nested Lean source. Run
`./hardware/check.sh` separately to compile and exercise the native adapter;
execution tests do not discharge its explicit semantic contract.
