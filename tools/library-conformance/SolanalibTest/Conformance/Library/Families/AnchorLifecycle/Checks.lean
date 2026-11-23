/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Projection
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Ready
import SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck

/-! Factories accept the actual versioned run constant and a checked equality
to its shared family. Each input selects one concrete script interpretation;
the registered precondition and its finite observed execution are decided
separately. Versioned registrations below supply these equalities by rfl. -/

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor
open SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck (decideBy)

abbrev ValidationAt (kind : ValidationKind) (ownership : InfoStorage) (storage :
  AnchorErrorOperations.Storage) :=
  familyAtStorage (validationFamily kind ownership) (fun types => types.errorStorage) storage
abbrev ValidationAccountsAt (kind : ValidationKind) (ownership : InfoStorage) (storage :
  AnchorErrorOperations.Storage) :=
  familyAtStorage (validationAccountsFamily kind ownership) (fun types => types.errorStorage)
    storage
abbrev PayloadAt (kind : PayloadKind) (ownership : InfoStorage) (storage :
  AnchorErrorOperations.Storage) :=
  familyAtStorage (payloadFamily kind ownership) (fun types => types.errorStorage) storage
abbrev PayloadAccountsAt (kind : PayloadKind) (ownership : InfoStorage) (storage :
  AnchorErrorOperations.Storage) :=
  familyAtStorage (payloadAccountsFamily kind ownership) (fun types => types.errorStorage) storage
abbrev ReloadAt (mode : ReloadMode) (storage : AnchorErrorOperations.Storage) :=
  familyAtStorage (reloadFamily mode) (fun types => types.errorStorage) storage
abbrev ExitAt (kind : PayloadKind) (cloneLocal : Bool) (storage : AnchorErrorOperations.Storage) :=
  familyAtStorage (exitFamily kind cloneLocal) (fun types => types.errorStorage) storage
abbrev CloseAt (cloneSource : Bool) (mode : CloseMode) (storage : AnchorErrorOperations.Storage) :=
  familyAtStorage (closeFamily cloneSource mode) (fun types => types.errorStorage) storage

/-- The complete instantiated contract type; version registrations pass their
actual `Family.contract` projection, together with its checked shared definition. -/
abbrev FamilyContracts (family : Family) := (index : family.Index) →
  Solanalib.Contracts.Model (family.State index) (family.Args index) (family.Value index)
    (family.Unwind index) (family.Terminal index)

/-- Keep the exact source contract in the decided proposition. The equality
transports the executable shared admission proof without replacing that contract. -/
def decideRequires {family : Family} (contracts : FamilyContracts family)
    (contracts_eq : contracts = family.contract) (index : family.Index)
    (state : family.State index) (args : family.Args index) (b : Bool)
    (equivalent : b = true ↔ (family.contract index).requires state args) : Bool :=
  decideBy (p := (contracts index).requires state args) b (by rw [contracts_eq]; exact equivalent)

def checker (function : String) (generics : List (String × String)) (name : String)
    (admission : Case → Result Bool) (run : Case → Result Verdict) : Checker :=
  withRequires [(name, admission)] <| ofModel function generics name run

def validationCheck (kind : ValidationKind) (ownership : InfoStorage) (storage :
  AnchorErrorOperations.Storage)
    (legacy : Bool) (object : String) (source : FamilyRun (ValidationAt kind ownership storage))
    (source_eq : source = familyAtStorageRun _ _ storage (validationRun kind ownership))
    (contracts : FamilyContracts (ValidationAt kind ownership storage))
    (contracts_eq : contracts = (ValidationAt kind ownership storage).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy (ownership == .owned) object "try_from" record
    return decideRequires contracts contracts_eq
      ⟨validationTypes storage i.script i.reference.info legacy, rfl⟩ i.world (referenceArgs i)
      _ (Ready.validationReadyB_iff kind storage i.script i.reference.info legacy i.world
        (referenceArgs i)))
    fun record => do
      let i ← inputs legacy (ownership == .owned) object "try_from" record
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source ⟨validationTypes
        storage i.script i.reference.info legacy, rfl⟩
          i.world (referenceArgs i)) (validationFn kind ownership storage i.script i.reference.info
            legacy i.world (referenceArgs i)) := by
        rw [source_eq]
        exact validation_graph kind ownership storage i.script i.reference.info legacy i.world
          (referenceArgs i)
      return decideProjected _ _ graph (project (stateProjection i false)
        (resultJson storage (validationValueJson kind)) reasonJson)
        (← parseObs (ownership == .owned) record.outcome) obsJson

def validationAccountsCheck (kind : ValidationKind) (ownership : InfoStorage) (storage :
  AnchorErrorOperations.Storage)
    (legacy : Bool) (object : String) (source : FamilyRun (ValidationAccountsAt kind ownership
      storage))
    (source_eq : source = familyAtStorageRun _ _ storage (validationAccountsRun kind ownership))
    (contracts : FamilyContracts (ValidationAccountsAt kind ownership storage))
    (contracts_eq : contracts = (ValidationAccountsAt kind ownership storage).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy (ownership == .owned) object "try_accounts" record
    let index : (ValidationAccountsAt kind ownership storage).Index :=
      ⟨validationAccountsTypes storage i.script i.reference.info legacy, rfl⟩
    let ready := match i.accounts.remaining with
      | [] => true
      | info :: _ => Ready.validationReadyB kind storage i.script i.reference.info i.world
        ⟨i.args.profile, info⟩
    return decideRequires contracts contracts_eq index (i.world, i.accounts) i.args
      ready (by
        dsimp only [ready, index, ValidationAccountsAt, familyAtStorage, validationAccountsFamily]
        cases i.accounts.remaining with
        | nil => exact iff_of_true rfl trivial
        | cons info rest =>
          exact Ready.validationReadyB_iff kind storage i.script i.reference.info
            legacy i.world ⟨i.args.profile, info⟩))
    fun record => do
      let i ← inputs legacy (ownership == .owned) object "try_accounts" record
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source
        ⟨validationAccountsTypes storage i.script i.reference.info legacy, rfl⟩
          (i.world, i.accounts) i.args)
          (consumeFn storage (validationFn kind ownership storage i.script i.reference.info legacy)
            (i.world, i.accounts) i.args) := by
        rw [source_eq]
        exact validationAccounts_graph kind ownership storage i.script i.reference.info legacy _ _
      return decideProjected _ _ graph (project (accountsProjection i)
        (fun state => resultJson storage (validationValueJson kind) state.1) reasonJson)
        (← parseObs (ownership == .owned) record.outcome) obsJson

def payloadCheck (kind : PayloadKind) (ownership : InfoStorage) (storage :
  AnchorErrorOperations.Storage)
    (legacy checked : Bool) (object method : String) (source : FamilyRun (PayloadAt kind ownership
      storage))
    (source_eq : source = familyAtStorageRun _ _ storage (payloadRun kind ownership))
    (contracts : FamilyContracts (PayloadAt kind ownership storage))
    (contracts_eq : contracts = (PayloadAt kind ownership storage).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy (ownership == .owned) object method record
    return decideRequires contracts contracts_eq
      ⟨payloadTypes storage i.script i.reference.info checked, rfl⟩ i.world (accountArgs i)
      _ (Ready.payloadReadyB_iff kind ownership storage i.script i.reference.info checked i.world
        (accountArgs i)))
    fun record => do
      let i ← inputs legacy (ownership == .owned) object method record
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source ⟨payloadTypes
        storage i.script i.reference.info checked, rfl⟩ i.world (accountArgs i))
          (payloadFn kind ownership storage i.script i.reference.info checked i.world (accountArgs
            i)) := by
        rw [source_eq]
        exact payload_graph kind ownership storage i.script i.reference.info checked i.world
          (accountArgs i)
      return decideProjected _ _ graph (project (stateProjection i false)
        (resultJson storage (payloadValueJson kind)) reasonJson)
        (← parseObs (ownership == .owned) record.outcome) obsJson

def payloadAccountsCheck (kind : PayloadKind) (ownership : InfoStorage) (storage :
  AnchorErrorOperations.Storage)
    (legacy : Bool) (object : String) (source : FamilyRun (PayloadAccountsAt kind ownership
      storage))
    (source_eq : source = familyAtStorageRun _ _ storage (payloadAccountsRun kind ownership))
    (contracts : FamilyContracts (PayloadAccountsAt kind ownership storage))
    (contracts_eq : contracts = (PayloadAccountsAt kind ownership storage).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy (ownership == .owned) object "try_accounts" record
    let index : (PayloadAccountsAt kind ownership storage).Index :=
      ⟨payloadAccountsTypes storage i.script i.reference.info, rfl⟩
    let ready := match i.accounts.remaining with
      | [] => true
      | info :: _ => Ready.payloadReadyB kind ownership storage i.script i.reference.info true
        i.world ⟨i.args.profile, info.info⟩
    return decideRequires contracts contracts_eq index (i.world, i.accounts) i.args
      ready (by
        dsimp only [ready, index, PayloadAccountsAt, familyAtStorage, payloadAccountsFamily]
        cases i.accounts.remaining with
        | nil => exact iff_of_true rfl trivial
        | cons info rest =>
          exact Ready.payloadReadyB_iff kind ownership storage i.script
            i.reference.info true i.world ⟨i.args.profile, info.info⟩))
    fun record => do
      let i ← inputs legacy (ownership == .owned) object "try_accounts" record
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source
        ⟨payloadAccountsTypes storage i.script i.reference.info, rfl⟩ (i.world, i.accounts) i.args)
          (consumeFn storage (fun current args => payloadFn kind ownership storage i.script
            i.reference.info true
            current args.toAccountInfoArgs) (i.world, i.accounts) i.args) := by
        rw [source_eq]
        exact payloadAccounts_graph kind ownership storage i.script i.reference.info _ _
      return decideProjected _ _ graph (project (accountsProjection i)
        (fun state => resultJson storage (payloadValueJson kind) state.1) reasonJson)
        (← parseObs (ownership == .owned) record.outcome) obsJson

def reloadCheck (mode : ReloadMode) (storage : AnchorErrorOperations.Storage) (legacy owned : Bool)
    (object : String) (source : FamilyRun (ReloadAt mode storage))
    (source_eq : source = familyAtStorageRun _ _ storage (reloadRun mode))
    (contracts : FamilyContracts (ReloadAt mode storage))
    (contracts_eq : contracts = (ReloadAt mode storage).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy owned object "reload" record
    return decideRequires contracts contracts_eq ⟨reloadTypes storage i.script i.reference.info,
      rfl⟩
      i.world (accountArgs i) _ (Ready.reloadReadyB_iff mode storage i.script i.reference.info
        i.world (accountArgs i)))
    fun record => do
      let i ← inputs legacy owned object "reload" record
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source ⟨reloadTypes
        storage i.script i.reference.info, rfl⟩ i.world (accountArgs i))
          (reloadFn mode storage i.script i.reference.info i.world (accountArgs i)) := by
        rw [source_eq]
        exact reload_graph mode storage i.script i.reference.info i.world (accountArgs i)
      return decideProjected _ _ graph (project (stateProjection i true)
        (resultJson storage (fun _ _ => Json.null)) reasonJson) (← parseObs owned record.outcome)
          obsJson

def exitCheck (kind : PayloadKind) (cloneLocal : Bool) (storage : AnchorErrorOperations.Storage)
    (legacy owned : Bool) (object : String) (source : FamilyRun (ExitAt kind cloneLocal storage))
    (source_eq : source = familyAtStorageRun _ _ storage (exitRun kind cloneLocal))
    (contracts : FamilyContracts (ExitAt kind cloneLocal storage))
    (contracts_eq : contracts = (ExitAt kind cloneLocal storage).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy owned object "exit" record
    return decideRequires contracts contracts_eq ⟨exitTypes storage i.script i.reference.info, rfl⟩
      i.world (makeExitArgs kind i) _ (Ready.exitReadyB_iff kind cloneLocal storage i.script
        i.reference.info i.world (makeExitArgs kind i)))
    fun record => do
      let i ← inputs legacy owned object "exit" record
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source ⟨exitTypes
        storage i.script i.reference.info, rfl⟩ i.world (makeExitArgs kind i))
          (exitFn kind cloneLocal storage i.script i.reference.info i.world (makeExitArgs kind i))
            := by
        rw [source_eq]
        exact exit_graph kind cloneLocal storage i.script i.reference.info i.world (makeExitArgs
          kind i)
      return decideProjected _ _ graph (project (stateProjection i false)
        (resultJson storage (fun _ _ => Json.null)) reasonJson) (← parseObs owned record.outcome)
          obsJson

def closeCheck (cloneSource : Bool) (mode : CloseMode) (storage : AnchorErrorOperations.Storage)
    (legacy owned : Bool) (object : String) (source : FamilyRun (CloseAt cloneSource mode storage))
    (source_eq : source = familyAtStorageRun _ _ storage (closeRun cloneSource mode))
    (contracts : FamilyContracts (CloseAt cloneSource mode storage))
    (contracts_eq : contracts = (CloseAt cloneSource mode storage).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy owned object "close" record
    let args ← makeCloseArgs i
    return decideRequires contracts contracts_eq ⟨closeTypes storage, rfl⟩
      i.world args _ (Ready.closeReadyB_iff cloneSource mode storage i.world args))
    fun record => do
      let i ← inputs legacy owned object "close" record
      let args ← makeCloseArgs i
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source ⟨closeTypes
        storage, rfl⟩ i.world args)
          (closeFn cloneSource mode storage i.world args) := by
        rw [source_eq]
        exact close_graph cloneSource mode storage i.world args
      return decideProjected _ _ graph (project (stateProjection i false)
        (resultJson storage (fun _ _ => Json.null)) closeReason) (← parseObs owned record.outcome)
          obsJson

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
