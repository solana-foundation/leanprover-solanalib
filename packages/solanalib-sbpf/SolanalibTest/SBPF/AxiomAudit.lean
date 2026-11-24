/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Lean
import Solanalib.SBPF
import SolanalibTest.SBPF

/-!
# Axiom audit for the sBPF package

Every declaration of the `Solanalib.SBPF` and `SolanalibTest.SBPF` modules may
depend only on `propext`, `Classical.choice` and `Quot.sound`, the axioms the
model audits allow. This rejects a declared `axiom`, `sorry` and `native_decide`,
which trusts the Lean compiler through an auxiliary axiom it adds. The audit runs when
`just test-sbpf` builds this file, and fails the build on any other axiom.

An `example` leaves no declaration behind, so the audit cannot see its axioms.
`just lint` rejects `example` in this package, as CONTRIBUTING.md asks of tests.

`sbpf-oracle` runs the compiled interpreter against a reference VM, and the
theorems are about the kernel definitions. The audit also rejects any model
declaration whose compiled code can differ from its definition: one marked
`implemented_by` or `extern`, an `opaque` constant (which `partial` produces), or
an `unsafe` one. Then the differential tests and the proofs are about one
interpreter.
-/

namespace SolanalibTest.SBPF.AxiomAudit

open Lean Elab Command

/-- The axioms of `name` outside the allowed three. -/
def forbidden (name : Name) : CommandElabM (Array Name) := do
  return (← collectAxioms name).filter
    (!#[``propext, ``Classical.choice, ``Quot.sound].contains ·)

/-- Why `name` runs differently compiled than its definition says, if it does. -/
def compiledApart (env : Environment) (name : Name) : Option String :=
  if (Compiler.implementedByAttr.getParam? env name).isSome then some "implemented_by"
  else if isExtern env name then some "extern"
  else match env.find? name with
    | some (.opaqueInfo _) => some "opaque"
    | some info => if info.isUnsafe then some "unsafe" else none
    | none => none

/-- The compiled-code control: what `controlSpec` runs is `controlImpl`. -/
def controlImpl : Nat := 0
@[implemented_by controlImpl]
def controlSpec : Nat := 1

/-- The control: `native_decide` must be rejected, or the audit proves nothing.
It is a `native_decide` on purpose: the axiom that tactic adds has changed form
across Lean releases, and the monthly toolchain update must not blind the audit.
The declarations of this file are outside the imported modules the audit walks. -/
theorem control : 2 + 2 = 4 := by native_decide

run_cmd do
  if (← forbidden ``control).isEmpty then
    throwError "the audit accepts native_decide"
  let env ← getEnv
  if (compiledApart env ``controlSpec).isNone then
    throwError "the audit accepts implemented_by"
  let mut modules : Nat := 0
  let mut errors : Array String := #[]
  for mod in env.header.moduleNames, data in env.header.moduleData do
    unless (`Solanalib.SBPF).isPrefixOf mod || (`SolanalibTest.SBPF).isPrefixOf mod do
      continue
    modules := modules + 1
    for name in data.constNames do
      let bad ← forbidden name
      unless bad.isEmpty do errors := errors.push s!"{name} ({mod}) depends on {bad}"
      if (`Solanalib.SBPF).isPrefixOf mod then
        if let some why := compiledApart env name then
          errors := errors.push s!"{name} ({mod}) is {why}: compiled code can differ"
  if modules == 0 then throwError "no sBPF module was audited"
  unless errors.isEmpty do throwError "sBPF axiom audit failed:\n{"\n".intercalate errors.toList}"
  logInfo m!"sBPF axiom audit: {modules} modules, standard axioms, compiled as defined"

end SolanalibTest.SBPF.AxiomAudit
