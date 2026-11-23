/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.ConstructCheck
import Solanalib.Specs.AnchorLang.account_loader

/-! Reference identity and Rc counts are observed independently: derived
Clone copies a borrowed record, while AsRef returns that very record. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorLoader.Identity

open Lean (Json toJson)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor

abbrev State := Anchor.Construct.StateObs × List (List Nat)

def counts (json : Json) : Result (List (List Nat)) :=
  asList (asList Json.getNat?) json

def state (json : Json) : Result State := do
  return (← Anchor.Construct.asStateObs json, ← counts (← field json "ref_counts"))

def stateJson (value : State) : Json := Json.mkObj [
  ("world", Anchor.Construct.stateObsJson value.1), ("ref_counts", toJson value.2)]

def reference (input : LoaderInput) (json : Json) : Result AnchorLoader.Reference := do
  let id ← natField json "record"
  return ⟨id, ← infoAt input id⟩

def referenceJson (value : AnchorLoader.Reference) : Json := Json.mkObj [("record", toJson
  value.id)]

def index : ProjectionIndex := ⟨State, Unit⟩

def inputs (record : Case) : Result (LoaderInput × State × AnchorLoader.Value Unit) := do
  let (input, world) ← asWorld record.state
  let id ← natField record.args "account"
  let info ← infoAt input id
  let log ← asList Anchor.Construct.asEvent (← field record.state "log")
  return (input, (⟨observeWorld input (inputOwners input) world, log⟩,
    ← counts (← field record.state "ref_counts")), ⟨⟨id, info⟩⟩)

def asRefChecker : Checker :=
  withFrame [("no syscalls", noSyscalls)] <|
  ofModel
    "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as \
      core::convert::AsRef<solana_account_info::AccountInfo<'info>>>::as_ref"
    [("T", "conformance_anchor_loader::script::Zc")]
    "Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.as_ref_run" fun record => do
      let (input, before, args) ← inputs record
      decideReturns (State := State) (Value := AnchorLoader.Reference)
        (Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.as_ref_run index)
        (fun before args => (AnchorLoader.asRef args, before)) rfl before args
        (reference input) state referenceJson stateJson record.outcome

end SolanalibTest.Conformance.Library.Families.AnchorLoader.Identity

namespace SolanalibTest.Conformance.Library.Families.AnchorLoader.Identity

open Lean (Json toJson)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor

def cloneChecker : Checker :=
  withFrame [("no syscalls", noSyscalls)] <|
  ofModel
    "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as \
      core::clone::Clone>::clone"
    [("T", "conformance_anchor_loader::script::Zc")]
    "Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.clone_run" fun record => do
      let (input, before, args) ← inputs record
      decideReturns (State := State) (Value := AnchorLoader.Value Unit)
        (Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.clone_run index)
        (fun before args => (AnchorLoader.clone args, before)) rfl before args
        (fun json => return (⟨← reference input json⟩ : AnchorLoader.Value Unit)) state
        (fun value => referenceJson value.account) stateJson record.outcome

end SolanalibTest.Conformance.Library.Families.AnchorLoader.Identity
