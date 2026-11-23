/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenStateVersions.Values
import Solanalib.Specs.SplToken2022.Extensions

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.TokenStateVersions.KeyCleanup

open Lean (Json)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface
open SolanalibTest.Conformance.Library.Families.Anchor (PGraph decideProjected)

/-- Counts measured around the real typed-getter override and its caller.
Unlike auxiliary observations, these fields are part of the state of this replay. -/
structure State where
  allocations : Nat
  deallocations : Nat
  reallocations : Nat
  getterCalls : Nat

def allocated (state : State) : State :=
  { state with allocations := state.allocations + 1, getterCalls := state.getterCalls + 1 }

def dropped (state : State) : State :=
  { state with deallocations := state.deallocations + 1 }

/-- The override of the fixture constructs one nonempty error String. The separate
destructor consumes that owner. This interpretation is not an SDK body proof. -/
def getter : ExtensionKeyGetter where
  State := State
  Reference := Unit
  Unwind := Empty
  Terminal := Empty
  getExtension := fun before outcome =>
    outcome = .returned (.error .BorshIoError) (allocated before)
  dropError := fun before error outcome =>
    error = .BorshIoError ∧ outcome = .returned () (dropped before)
  key := fun _ _ => .zero

theorem graph (before : State) :
    PGraph (Legacy.keyRun getter before ())
      (some (.returned none (dropped (allocated before)))) := by
  intro final
  constructor
  · rintro ⟨_, rfl, _, ⟨_, rfl⟩, rfl⟩
    rfl
  · intro equality
    have final_eq := (Option.some.inj equality).symm
    subst final
    exact ⟨.returned (.error .BorshIoError) (allocated before), rfl,
      .returned () (dropped (allocated before)), ⟨rfl, rfl⟩, rfl⟩

def decode (j : Json) : Result State := do
  pure ⟨← natField j "allocations", ← natField j "deallocations",
    ← natField j "reallocations", ← natField j "getter_calls"⟩

def encode (state : State) : Json := Json.mkObj [
  ("allocations", Lean.toJson state.allocations),
  ("deallocations", Lean.toJson state.deallocations),
  ("reallocations", Lean.toJson state.reallocations),
  ("getter_calls", Lean.toJson state.getterCalls)]

def args : Json := Json.mkObj [("getter", Json.str "owning_error")]

def check (hook : Bool) (c : Case) : Result Verdict := do
  unless c.args == args do throw "expected the owning-error typed-getter fixture"
  let before ← decode c.state
  let run := if hook then
    Solanalib.Specs.SplToken2022.extension.transfer_hook.get_program_id_run getter before () else
    Solanalib.Specs.SplToken2022.extension.permanent_delegate.get_permanent_delegate_run getter
      before ()
  let computed : Option (Outcome State (Option Solanalib.Runtime.Pubkey) Empty Empty) :=
    some (.returned none (dropped (allocated before)))
  have actual : PGraph run computed := by cases hook <;> exact graph before
  let observe : Outcome State (Option Solanalib.Runtime.Pubkey) Empty Empty → Json := fun outcome =>
    match outcome with
    | .returned value after => returnedJson (optionJson pubkeyJson value) (encode after)
    | .unwound reason _ => reason.elim
    | .terminated reason => reason.elim
  pure (decideProjected run computed actual (fun outcome => observe outcome == c.outcome)
    (some true) (fun _ => (computed.map observe).getD Json.null))

end SolanalibTest.Conformance.Library.Families.TokenStateVersions.KeyCleanup
