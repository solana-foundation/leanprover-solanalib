/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.Requires

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

open Lean (Json)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTokenOperations

/-- Both the registered reference and its complete registered precondition are
checked. The graph comes from the actual wrapper and all its primitive graphs. -/
def check (binding : Binding)
    (selected : FamilyRun (family binding)) (selectedExact : selected = reference binding)
    (contracts : Contracts binding) (contractsExact : contracts = (family binding).contract)
    (record : Case) : Result Verdict := do
  let prepared ← prepare binding record
  let index := Reference.types binding prepared.script
  have requirement : (contracts index).requires prepared.before prepared.args ↔
      Reference.requestsReadable binding prepared.script prepared.before prepared.args = true := by
    rw [contractsExact]
    exact Reference.ready_iff_requests binding prepared.script prepared.before prepared.args
  let allowed := decideRequirement binding contracts index prepared.before prepared.args _
    requirement.symm
  let graph : PGraph (selected index prepared.before prepared.args)
      (Execution.runFn (Reference.functions binding prepared.script) prepared.before prepared.args)
        := by
    rw [selectedExact]
    exact Reference.run_iff binding prepared.script prepared.before prepared.args
  let verdict := Anchor.decideProjected (selected index prepared.before prepared.args) _ graph
    (fun final => (outcomeJson prepared final).compress) (some record.outcome.compress)
    (fun value => (value.bind fun text => (Json.parse text).toOption).getD .null)
  pure ⟨allowed && verdict.admitted, verdict.expected⟩

def checker (binding : Binding) (function referenceName : String)
    (selected : FamilyRun (family binding)) (selectedExact : selected = reference binding)
    (contracts : Contracts binding) (contractsExact : contracts = (family binding).contract) :
      Checker where
  function
  generics := []
  reference := referenceName
  decides := [referenceName]
  decidesRequires := [referenceName]
  check := check binding selected selectedExact contracts contractsExact

end SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations
