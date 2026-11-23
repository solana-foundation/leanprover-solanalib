/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.World

/-! Executable graphs follow the actual shared error operations. The inline
and boxed versions preserve their distinct allocation and destruction effects. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Families.Anchor

def fromPayloadFn (storage : AnchorErrorOperations.Storage) (state : W) (payload : ErrorPayload) :
    Option (DepOut (Error storage)) :=
  match storage with
  | .inline => some (.returned payload state)
  | .boxed => some ((newBox state payload).map AnchorErrorOwned.Error.mk)

theorem fromPayload_graph (storage : AnchorErrorOperations.Storage) (state : W) (payload :
  ErrorPayload) :
    PGraph (AnchorErrorOperations.fromPayload storage errors state payload)
      (fromPayloadFn storage state payload) := by
  cases storage
  · exact PGraph.eq_left _
  · exact PGraph.map AnchorErrorOwned.Error.mk (PGraph.ofFunction newBox state payload)

def fromCodeFn (storage : AnchorErrorOperations.Storage) (state : W) (code :
  AnchorErrorOperations.Code) :
    Option (DepOut (Error storage)) :=
  (some (copyString state code.name)).bind (PGraph.bindK fun name afterName =>
    (some (copyString afterName code.message)).bind (PGraph.bindK fun message afterMessage =>
      fromPayloadFn storage afterMessage (.anchor ⟨name, code.number, message, none, none⟩)))

theorem fromCode_graph (storage : AnchorErrorOperations.Storage) (state : W) (code :
  AnchorErrorOperations.Code) :
    PGraph (AnchorErrorOperations.fromCode storage errors state code) (fromCodeFn storage state
      code) :=
  PGraph.bind (PGraph.ofFunction copyString state code.name) fun name afterName =>
    PGraph.bind (PGraph.ofFunction copyString afterName code.message) fun message afterMessage =>
      fromPayload_graph storage afterMessage (.anchor ⟨name, code.number, message, none, none⟩)

def depLift {Value : Type} : DepOut Value → Out Value :=
  fun outcome => AnchorAccount.widen (AccountInfoRc.liftOutcome (Unwind := String) outcome)

theorem dependency_graph (storage : AnchorErrorOperations.Storage) {Args Value : Type}
    {run : Callback.Run W Args Value Empty Unit} {state : W} {args : Args}
    {fn : Option (DepOut Value)} (graph : PGraph (run state args) fn) :
    PGraph (dependency (base storage) run state args) (fn.map depLift) := by
  apply PGraph.congr (PGraph.exists_eq depLift graph)
  intro outcome
  constructor
  · rintro ⟨middle, ⟨produced, called, rfl⟩, equal⟩
    exact ⟨produced, called, equal⟩
  · rintro ⟨produced, called, equal⟩
    exact ⟨AccountInfoRc.liftOutcome produced, ⟨produced, called, rfl⟩, equal⟩

def codeFn (storage : AnchorErrorOperations.Storage) (state : W) (failure : Code) :
    Option (Out (Error storage)) :=
  (fromCodeFn storage state ⟨failure.payload.name, failure.payload.code,
    failure.payload.message⟩).map depLift

theorem code_graph (storage : AnchorErrorOperations.Storage) (state : W) (failure : Code) :
    PGraph (code (base storage) failure state ()) (codeFn storage state failure) :=
  dependency_graph storage (fromCode_graph storage state _)

def accountCodeFn (storage : AnchorErrorOperations.Storage) (state : W) (failure :
  AnchorAccount.Code) :
    Option (Out (Error storage)) :=
  (fromCodeFn storage state ⟨failure.payload.name, failure.payload.code,
    failure.payload.message⟩).map depLift

theorem accountCode_graph (storage : AnchorErrorOperations.Storage) (state : W) (failure :
  AnchorAccount.Code) :
    PGraph (accountCode (base storage) failure state ()) (accountCodeFn storage state failure) :=
  dependency_graph storage (fromCode_graph storage state _)

def programFn (storage : AnchorErrorOperations.Storage) (state : W) (failure : Program) :
    Option (Out (Error storage)) :=
  (fromPayloadFn storage state (.program ⟨failure, none, none⟩)).map depLift

theorem program_graph (storage : AnchorErrorOperations.Storage) (state : W) (failure :
  ProgramError.Value) :
    PGraph (programError (base storage) failure state ()) (programFn storage state (.plain
      failure)) :=
  dependency_graph storage (fromPayload_graph storage state _)

def dropsFn (resources : List Nat) : List (W → Option (DepOut Unit)) :=
  resources.map fun resource state => dropString state resource

theorem drops_graph : ∀ resources : List Nat,
    PGraph.DropsGraph (resources.map fun resource state outcome => errors.dropString state resource
      outcome)
      (dropsFn resources)
  | [] => trivial
  | _ :: rest => ⟨fun _ => PGraph.ofOption _, drops_graph rest⟩

def dropStringsFn (state : W) (resources : List Nat) : Option (DepOut Unit) :=
  PGraph.cleanupFn (fun _ impossible _ => nomatch impossible) (dropsFn resources) (.returned ()
    state)

theorem dropStrings_graph (state : W) (resources : List Nat) :
    PGraph (AnchorErrorOperations.dropStrings errors resources state ()) (dropStringsFn state
      resources) :=
  PGraph.cleanup (fun _ impossible _ => nomatch impossible) _ _ (drops_graph resources) _

def dropErrorRawFn (storage : AnchorErrorOperations.Storage) (state : W) (error : Error storage) :
    Option (DepOut Unit) :=
  match storage with
  | .inline => dropStringsFn state (error.strings Program.strings)
  | .boxed => (currentBox state error.resource).bind fun payload =>
      (dropStringsFn state (payload.strings Program.strings)).bind
        (PGraph.bindK fun _ after => freeBox after error.resource)

theorem dropErrorRaw_graph (storage : AnchorErrorOperations.Storage) (state : W) (error : Error
  storage) :
    PGraph (AnchorErrorOperations.drop storage errors state error) (dropErrorRawFn storage state
      error) := by
  cases storage
  · exact dropStrings_graph state _
  · apply PGraph.exists_step (PGraph.ofOption _)
    intro payload
    exact PGraph.bind (dropStrings_graph state _) fun _ _ => PGraph.ofOption _

def dropErrorFn (storage : AnchorErrorOperations.Storage) (error : Error storage) (state : W) :
    Option (Out Unit) := (dropErrorRawFn storage state error).map depLift

theorem dropError_graph (storage : AnchorErrorOperations.Storage) (error : Error storage) (state :
  W) :
    PGraph (dropError (base storage) error state) (dropErrorFn storage error state) :=
  dependency_graph storage (dropErrorRaw_graph storage state error)

def updatePayloadFn (storage : AnchorErrorOperations.Storage) (state : W) (error : Error storage)
    (update : ErrorPayload → ErrorPayload) : Option (DepOut (Error storage)) :=
  match storage with
  | .inline => some (.returned (update error) state)
  | .boxed => (currentBox state error.resource).bind fun payload =>
      (writeBox state error.resource (update payload)).map fun after => .returned error after

theorem updatePayload_graph (storage : AnchorErrorOperations.Storage) (state : W) (error : Error
  storage)
    (update : ErrorPayload → ErrorPayload) :
    PGraph (AnchorErrorOperations.updatePayload storage errors update state error)
      (updatePayloadFn storage state error update) := by
  cases storage
  · exact PGraph.eq_left _
  · have graph := PGraph.exists_step (PGraph.ofOption (currentBox state error.resource))
      (fun payload => PGraph.exists_eq' (fun after => (Outcome.returned error after : DepOut _))
        (PGraph.ofOption (writeBox state error.resource (update payload))))
    apply PGraph.congr graph
    intro outcome
    exact ⟨fun ⟨payload, after, loaded, stored, equal⟩ => ⟨payload, loaded, after, stored, equal⟩,
      fun ⟨payload, loaded, after, stored, equal⟩ => ⟨payload, after, loaded, stored, equal⟩⟩

def withPubkeysRawFn (storage : AnchorErrorOperations.Storage) (state : W) (error : Error storage)
    (left right : Solanalib.Runtime.Pubkey) : Option (DepOut (Error storage)) :=
  (AnchorErrorOperations.currentPayload storage errors state error).bind fun payload =>
    (dropStringsFn state (AnchorErrorOwned.comparedStrings payload.compared)).bind
      (PGraph.bindK fun _ after => updatePayloadFn storage after error
        (AnchorErrorOperations.Payload.withCompared (some (.pubkeys left right))))

theorem withPubkeysRaw_graph (storage : AnchorErrorOperations.Storage) (state : W) (error : Error
  storage)
    (left right : Solanalib.Runtime.Pubkey) :
    PGraph (AnchorErrorOperations.withPubkeys storage errors left right state error)
      (withPubkeysRawFn storage state error left right) := by
  apply PGraph.exists_step (PGraph.ofOption _)
  intro payload
  exact PGraph.bind (dropStrings_graph state _) fun _ after => updatePayload_graph storage after
    error _

def withPubkeysFn (storage : AnchorErrorOperations.Storage) (state : W) (error : Error storage)
    (left right : Solanalib.Runtime.Pubkey) : Option (Out (Error storage)) :=
  (withPubkeysRawFn storage state error left right).map depLift

theorem withPubkeys_graph (storage : AnchorErrorOperations.Storage) (state : W) (error : Error
  storage)
    (left right : Solanalib.Runtime.Pubkey) :
    PGraph (dependency (base storage) (AnchorErrorOperations.withPubkeys storage errors left right)
      state error)
      (withPubkeysFn storage state error left right) :=
  dependency_graph storage (withPubkeysRaw_graph storage state error left right)

def rcRawFn (increment : Bool) (state : W) (info : AccountInfo.Value) : Option (DepOut Unit) :=
  (rcStep increment state (.lamports, info.lamports)).bind
    (PGraph.bindK fun _ after => rcStep increment after (.data, info.data))

def cloneFn (state : W) (info : AccountInfo.Value) :
    Option (Out AccountInfo.Value) :=
  ((rcStep true state (.lamports, info.lamports)).bind (PGraph.bindK fun _ after =>
    (rcStep true after (.data, info.data)).map (Outcome.map fun _ => info))).map depLift

theorem clone_graph (storage : AnchorErrorOperations.Storage) (state : W) (info :
  AccountInfo.Value) :
    PGraph (cloneInfo (base storage) rc state info) (cloneFn state info) :=
  dependency_graph storage (PGraph.bind (PGraph.ofOption _) fun _ _ =>
    PGraph.map (fun _ => info) (PGraph.ofOption _))

def dropInfoFn (info : AccountInfo.Value) (state : W) :
    Option (Out Unit) := (rcRawFn false state info).map depLift

theorem dropInfo_graph (storage : AnchorErrorOperations.Storage) (info : AccountInfo.Value) (state
  : W) :
    PGraph (dropInfo (base storage) rc info state) (dropInfoFn info state) :=
  dependency_graph storage (PGraph.bind (PGraph.ofOption _) fun _ _ => PGraph.ofOption _)

def retainFn (ownership : InfoStorage) (state : W) (info : AccountInfo.Value) : Option (Out
  AccountInfo.Value) :=
  match ownership with
  | .owned => cloneFn state info
  | .borrowed => some (.returned info state)

theorem retain_graph (ownership : InfoStorage) (storage : AnchorErrorOperations.Storage)
    (state : W) (info : AccountInfo.Value) :
    PGraph (retainInfo ownership (base storage) rc state info) (retainFn ownership state info) := by
  cases ownership
  · exact clone_graph storage state info
  · exact PGraph.eq_right _

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
