/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Checks

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor

abbrev OptionAt (storage : AnchorErrorOperations.Storage) :=
  familyAtStorage optionalFamily (fun types => types.errorStorage) storage
abbrev BoxAt (storage : AnchorErrorOperations.Storage) :=
  familyAtStorage collectionBoxedFamily (fun types => types.errorStorage) storage
abbrev OptionCloseAt (storage : AnchorErrorOperations.Storage) :=
  familyAtStorage optionCloseFamily (fun types => types.errorStorage) storage

def optionAccountsCheck (storage : AnchorErrorOperations.Storage) (legacy owned : Bool)
    (source : FamilyRun (OptionAt storage))
    (source_eq : source = familyAtStorageRun _ _ storage optionalRun)
    (contracts : FamilyContracts (OptionAt storage))
    (contracts_eq : contracts = (OptionAt storage).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy owned "option" "try_accounts" record
    return decideRequires contracts contracts_eq ⟨optionTypes storage i.script i.reference.info
      false, rfl⟩
      (i.world, i.accounts) i.args true (iff_of_true rfl trivial))
    fun record => do
      let i ← inputs legacy owned "option" "try_accounts" record
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source ⟨optionTypes
        storage i.script i.reference.info false, rfl⟩ (i.world, i.accounts) i.args)
          (optionAccountsFn false storage i.script i.reference.info (i.world, i.accounts) i.args)
            := by
        rw [source_eq]
        exact optionAccounts_graph false storage i.script i.reference.info _ _
      return decideProjected _ _ graph (project (accountsProjection i)
        (fun state => resultJson storage (fun _ value => optionJson (toJson (α := Nat)) value)
          state.1) reasonJson)
        (← parseObs owned record.outcome) obsJson

def boxValueJson (state : W) (resource : Nat) : Json :=
  (state.2.payloadBoxes[resource]?.join).map toJson |>.getD "<missing payload Box>"

def boxAccountsCheck (storage : AnchorErrorOperations.Storage) (legacy owned : Bool)
    (source : FamilyRun (BoxAt storage))
    (source_eq : source = familyAtStorageRun _ _ storage collectionBoxedRun)
    (contracts : FamilyContracts (BoxAt storage))
    (contracts_eq : contracts = (BoxAt storage).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy owned "boxed" "try_accounts" record
    return decideRequires contracts contracts_eq ⟨collectionTypes storage i.script
      i.reference.info, rfl⟩
      (i.world, i.accounts) i.args true (iff_of_true rfl trivial))
    fun record => do
      let i ← inputs legacy owned "boxed" "try_accounts" record
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source ⟨collectionTypes
        storage i.script i.reference.info, rfl⟩ (i.world, i.accounts) i.args)
          (boxAccountsFn storage i.script i.reference.info (i.world, i.accounts) i.args) := by
        rw [source_eq]
        exact boxAccounts_graph storage i.script i.reference.info _ _
      return decideProjected _ _ graph (project (accountsProjection i)
        (fun state => resultJson storage boxValueJson state.1) reasonJson) (← parseObs owned
          record.outcome) obsJson

def boxExitCheck (storage : AnchorErrorOperations.Storage) (legacy owned : Bool)
    (source : FamilyRun boxedDispatchFamily) (source_eq : source = boxedDispatchRun)
    (contracts : FamilyContracts (boxedDispatchFamily))
    (contracts_eq : contracts = (boxedDispatchFamily).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy owned "boxed" "exit" record
    let types := dispatchTypes storage (innerExitFn storage i.script i.reference.info)
    return decideRequires contracts contracts_eq types i.world ((0 : Nat), i.args.programId)
      (i.world.2.payloadBoxes[0]?.join.isSome) Option.isSome_iff_exists)
    fun record => do
      let i ← inputs legacy owned "boxed" "exit" record
      let callback := innerExitFn storage i.script i.reference.info
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source (dispatchTypes
        storage callback) i.world ((0 : Nat), i.args.programId))
          (boxDispatchFn storage callback i.world (0, i.args.programId)) := by
        rw [source_eq]
        exact boxDispatch_graph storage callback i.world _
      return decideProjected _ _ graph (project (stateProjection i false)
        (resultJson storage (fun _ _ => Json.null)) reasonJson) (← parseObs owned record.outcome)
          obsJson

def boxCloseCheck (storage : AnchorErrorOperations.Storage) (legacy owned : Bool)
    (source : FamilyRun boxedDispatchFamily) (source_eq : source = boxedDispatchRun)
    (contracts : FamilyContracts (boxedDispatchFamily))
    (contracts_eq : contracts = (boxedDispatchFamily).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy owned "boxed" "close" record
    let args ← makeCloseArgs i
    let types := dispatchTypes storage (innerCloseFn storage i.script i.reference.info)
    return decideRequires contracts contracts_eq types i.world ((0 : Nat), args.destination)
      (i.world.2.payloadBoxes[0]?.join.isSome) Option.isSome_iff_exists)
    fun record => do
      let i ← inputs legacy owned "boxed" "close" record
      let args ← makeCloseArgs i
      let callback := innerCloseFn storage i.script i.reference.info
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source (dispatchTypes
        storage callback) i.world ((0 : Nat), args.destination))
          (boxDispatchFn storage callback i.world (0, args.destination)) := by
        rw [source_eq]
        exact boxDispatch_graph storage callback i.world _
      return decideProjected _ _ graph (project (stateProjection i false)
        (resultJson storage (fun _ _ => Json.null)) reasonJson) (← parseObs owned record.outcome)
          obsJson

def optionalValue (i : Inputs) : Option Nat := if i.optionalSome then some i.innerValue else none

def optionExitCheck (storage : AnchorErrorOperations.Storage) (legacy owned : Bool)
    (source : FamilyRun optionDispatchFamily) (source_eq : source = optionDispatchRun)
    (contracts : FamilyContracts (optionDispatchFamily))
    (contracts_eq : contracts = (optionDispatchFamily).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy owned "option" "exit" record
    let types := dispatchTypes storage (innerExitFn storage i.script i.reference.info)
    return decideRequires contracts contracts_eq types i.world (optionalValue i, i.args.programId)
      true (iff_of_true rfl trivial))
    fun record => do
      let i ← inputs legacy owned "option" "exit" record
      let callback := innerExitFn storage i.script i.reference.info
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source (dispatchTypes
        storage callback) i.world (optionalValue i, i.args.programId))
          (optionDispatchFn storage callback i.world (optionalValue i, i.args.programId)) := by
        rw [source_eq]
        exact optionDispatch_graph storage callback i.world _
      return decideProjected _ _ graph (project (stateProjection i false)
        (resultJson storage (fun _ _ => Json.null)) reasonJson) (← parseObs owned record.outcome)
          obsJson

def optionCloseCheck (storage : AnchorErrorOperations.Storage) (legacy owned : Bool)
    (source : FamilyRun (OptionCloseAt storage))
    (source_eq : source = familyAtStorageRun _ _ storage optionCloseRun)
    (contracts : FamilyContracts (OptionCloseAt storage))
    (contracts_eq : contracts = (OptionCloseAt storage).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy owned "option" "close" record
    let args ← makeCloseArgs i
    return decideRequires contracts contracts_eq ⟨optionCloseTypes storage i.script
      i.reference.info, rfl⟩
      i.world (optionalValue i, args.destination) true (iff_of_true rfl trivial))
    fun record => do
      let i ← inputs legacy owned "option" "close" record
      let args ← makeCloseArgs i
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source
        ⟨optionCloseTypes storage i.script i.reference.info, rfl⟩
          i.world (optionalValue i, args.destination))
          (optionCloseFn storage i.script i.reference.info i.world (optionalValue i,
            args.destination)) := by
        rw [source_eq]
        exact optionClose_graph storage i.script i.reference.info i.world (optionalValue i,
          args.destination)
      return decideProjected _ _ graph (project (stateProjection i false)
        (resultJson storage (fun _ _ => Json.null)) reasonJson) (← parseObs owned record.outcome)
          obsJson

def defaultExitTypes (storage : AnchorErrorOperations.Storage) : DefaultExitTypes := ⟨W, Nat, Error
  storage⟩

def defaultExitCheck (storage : AnchorErrorOperations.Storage) (legacy owned : Bool)
    (source : FamilyRun defaultExitFamily) (source_eq : source = defaultExitRun)
    (contracts : FamilyContracts (defaultExitFamily))
    (contracts_eq : contracts = (defaultExitFamily).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy owned "default" "exit" record
    return decideRequires contracts contracts_eq (defaultExitTypes storage) i.world (i.innerValue,
      i.args.programId)
      true (iff_of_true rfl trivial))
    fun record => do
      let i ← inputs legacy owned "default" "exit" record
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source
        (defaultExitTypes storage) i.world (i.innerValue, i.args.programId))
          (some (.returned (.ok ()) i.world)) := by
        rw [source_eq]
        intro outcome
        exact (returnsOf_iff _ _ _ _).trans
          (SolanalibTest.Conformance.Library.Families.Anchor.PGraph.eq_right _ outcome)
      return decideProjected _ _ graph (project (stateProjection i false)
        (resultJson storage (fun _ _ => Json.null)) Empty.elim) (← parseObs owned record.outcome)
          obsJson

def uncheckedArgs (ownership : InfoStorage) (i : Inputs) : UncheckedInput ownership :=
  match ownership with
  | .owned => i.reference.info
  | .borrowed => i.reference

def uncheckedValueJson (ownership : InfoStorage) (state : W) : UncheckedInput ownership → Json :=
  match ownership with
  | .owned => fun value => infoValueJson state value none
  | .borrowed => fun value => infoValueJson state value.info none

def uncheckedCheck (ownership : InfoStorage) (legacy : Bool)
    (source : FamilyRun (uncheckedFromFamily ownership)) (source_eq : source = uncheckedFromRun
      ownership)
    (contracts : FamilyContracts (uncheckedFromFamily ownership))
    (contracts_eq : contracts = (uncheckedFromFamily ownership).contract)
    (function : String) (generics : List (String × String)) (name : String) : Checker :=
  checker function generics name (fun record => do
    let i ← inputs legacy (ownership == .owned) "unchecked_account" "try_from" record
    return decideRequires contracts contracts_eq W i.world (uncheckedArgs ownership i)
      true (iff_of_true rfl trivial))
    fun record => do
      let i ← inputs legacy (ownership == .owned) "unchecked_account" "try_from" record
      let graph : SolanalibTest.Conformance.Library.Families.Anchor.PGraph (source W i.world
        (uncheckedArgs ownership i))
          (some (.returned (uncheckedArgs ownership i) i.world)) := by
        rw [source_eq]
        intro outcome
        exact (returnsOf_iff _ _ _ _).trans
          (SolanalibTest.Conformance.Library.Families.Anchor.PGraph.eq_right _ outcome)
      return decideProjected _ _ graph (project (stateProjection i false)
        (uncheckedValueJson ownership) Empty.elim) (← parseObs (ownership == .owned)
          record.outcome) obsJson

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
