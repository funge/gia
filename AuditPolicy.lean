import Lean

/-! Build-time axiom enforcement. This checks transitive dependencies using Lean's
own collector, not parsed log output. It is validation tooling, not a new logical
axiom or a proof of the Lean implementation. -/
namespace AxiomAudit
open Lean Elab Command

private def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private def check (name : Name) : CommandElabM (Array Name) := do
  unless (← getEnv).contains name do
    throwError "axiom audit: unknown declaration {name}"
  let axioms ← collectAxioms name
  let rejected := axioms.filter fun ax => !allowed.contains ax
  unless rejected.isEmpty do
    throwError "axiom audit rejected {name}: forbidden axioms {rejected.toList}"
  return axioms

/-- Check the named declaration and retain a readable dependency report. -/
elab "#audit_axioms " id:ident : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  for name in names do
    let axioms ← check name
    logInfo m!"axiom audit passed {name}: {axioms.qsort Name.lt |>.toList}"

/-- Check imported theorems and axiom declarations in a namespace. Definitions
used by their proofs are traversed transitively; compiler implementation artifacts
are not independently audited. An empty selection is an error. -/
elab "#audit_namespace " id:ident : command => do
  let namespaceName := id.getId
  let names := (← getEnv).constants.toList.filterMap fun (name, info) =>
    if namespaceName.isPrefixOf name then
      match info with
      | .thmInfo _ | .axiomInfo _ => some name
      | _ => none
    else none
  if names.isEmpty then
    throwError "axiom audit: namespace {namespaceName} has no theorem or axiom declarations"
  -- Reuse the collector's visited set across roots; each dependency is visited
  -- once. Any forbidden dependency still fails immediately at its first root.
  let env ← getEnv
  let mut state : CollectAxioms.State := {}
  for name in names do
    let (_, next) := ((CollectAxioms.collect name).run env).run state
    state := next
    let rejected := state.axioms.filter fun ax => !allowed.contains ax
    unless rejected.isEmpty do
      throwError "axiom audit rejected {name}: forbidden axioms {rejected.toList}"
  logInfo m!"axiom audit passed namespace {namespaceName}: {names.length} theorem/axiom declarations"

end AxiomAudit
