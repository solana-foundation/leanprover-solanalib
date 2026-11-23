/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Parsing

/-! Projection retains all recorded account bytes, alias and record identities,
callback observations, result fields and owned-error liveness. Panic text normalization
maps the two RefCell borrow messages to "borrow panic" and the exact Option::unwrap
None message to "arithmetic overflow". These mappings apply wherever `normalizePanic`
is used, including fixture callback reasons, regardless of the origin of the panic. -/

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor

def programJson (state : W) : Program → Option Json
  | .plain value => some (programErrorJson value)
  | .legacyBorsh resource => (currentString state resource).map fun text => variantJson
    "BorshIoError" [text]

def payloadJson (state : W) : ErrorPayload → Option Json
  | .anchor value => do
    let name ← currentString state value.name
    let message ← currentString state value.message
    let origin ← AnchorErrorOwned.observeOrigin (currentString state) value.origin
    let compared ← AnchorErrorOwned.observeCompared (currentString state) value.compared
    pure (tagged "AnchorError" (Json.mkObj [("name", name), ("code", toJson value.number.toNat),
      ("message", message), ("origin", originJson origin), ("compared", comparedJson compared)]))
  | .program value => do
    let error ← programJson state value.error
    let origin ← AnchorErrorOwned.observeOrigin (currentString state) value.origin
    let compared ← AnchorErrorOwned.observeCompared (currentString state) value.compared
    pure (tagged "ProgramError" (Json.mkObj [("error", error), ("origin", originJson origin),
      ("compared", comparedJson compared)]))

def errorJson (storage : AnchorErrorOperations.Storage) (state : W) (error : Error storage) : Json
  :=
  ((AnchorErrorOperations.currentPayload storage errors state error).bind (payloadJson state)).getD
    "<missing owned error resource>"

def infoValueJson (state : W) (info : AccountInfo.Value) (payload : Option Nat) : Json :=
  Json.mkObj [("info", infoJson (currentInfo state info)), ("payload", optionJson toJson payload)]

def validationValueJson (kind : ValidationKind) (state : W) : kind.Value Nat → Json :=
  match kind with
  | .signer => fun value => infoValueJson state value.info none
  | .system | .unchecked | .accountInfo => fun value => infoValueJson state value none
  | .program => fun value => infoValueJson state value.info none
  | .interface => fun value => infoValueJson state value.program.info none
  | .sysvar => fun value => infoValueJson state value.info (some value.value)

def payloadValueJson (kind : PayloadKind) (state : W) : kind.constructor.Result Nat → Json :=
  match kind with
  | .account => fun value => infoValueJson state value.info (some value.value)
  | .interfaceAccount => fun value => infoValueJson state value.account.info (some
    value.account.value)

def resultJson {Value : Type} (storage : AnchorErrorOperations.Storage) (render : W → Value → Json)
    (state : W) : Except (Error storage) Value → Json :=
  exceptJson (errorJson storage state) (render state)

def normalizePanic (message : String) : String :=
  if message == "RefCell already borrowed" || message == "RefCell already mutably borrowed" then
    "borrow panic"
  else if message == "called `Option::unwrap()` on a `None` value" then "arithmetic \
    overflow"
  else message

def reasonJson : AnchorAccount.ConstructorUnwind String → String
  | .inl .borrowFailed => "borrow panic"
  | .inr reason => normalizePanic reason

def closeReason : ClosePanic ⊕ AnchorAccount.ConstructorUnwind String → String
  | .inl .borrowFailed => "borrow panic"
  | .inl .arithmeticOverflow => "arithmetic overflow"
  | .inr reason => reasonJson reason

abbrev Obs := Outcome StateObs String String Unit

def project {State Value Unwind Terminal : Type}
    (state : State → StateObs) (value : State → Value → Json) (reason : Unwind → String) :
    Outcome State Value Unwind Terminal → Obs
  | .returned result after => .returned ((value after result).compress) (state after)
  | .unwound why after => .unwound (reason why) (state after)
  | .terminated _ => .terminated ()

def parseObs (legacyBumps : Bool) (outcome : Json) : Result (Option Obs) :=
  parseOutcome (fun value => pure value.compress) (asStateObs legacyBumps)
    (some ∘ normalizePanic) noReason outcome

def stateJson (state : StateObs) : Json := Json.mkObj [
  ("region", reprStr state.world.region), ("leases", listJson leaseJson state.world.leases),
  ("spare", listJson bytesJson state.spare), ("padding", listJson bytesJson state.padding),
  ("count", toJson state.count), ("ref_counts", toJson state.counts), ("log", toJson state.log),
  ("fresh_live", toJson state.freshLive), ("program_string_dropped", optionJson toJson
    state.programStringDropped),
  ("payload", optionJson toJson state.payload),
  ("syscalls", Json.parse state.syscalls |>.toOption.getD .null),
  ("accounts", optionJson (fun (remaining, bumps, reallocs) => Json.mkObj [("remaining", toJson
    remaining),
    ("bumps", toJson bumps), ("reallocs", listJson pubkeyJson reallocs)]) state.accounts)]

def obsJson : Option Obs → Json
  | none => "<no finite outcome>"
  | some (.returned value state) => returnedJson (Json.parse value |>.toOption.getD .null)
    (stateJson state)
  | some (.unwound reason state) => Json.mkObj [("exit", "unwound"), ("reason", reason), (
    "state",
    stateJson state)]
  | some (.terminated _) => Json.mkObj [("exit", "terminated")]

def stateProjection (input : Inputs) (payload : Bool) : W → StateObs := stateObs input.input
  payload none

def accountsProjection (input : Inputs) (state : CW) : StateObs := stateObs input.input false (some
  state.2) state.1

def accountArgs (input : Inputs) : AccountInfo.Args := ⟨input.args.profile, input.reference.info⟩
def referenceArgs (input : Inputs) : ReferenceArgs := ⟨input.args.profile, input.reference⟩

def makeExitArgs (kind : PayloadKind) (input : Inputs) : ExitArgs kind Nat :=
  match kind with
  | .account => ⟨input.args.profile, ⟨input.innerValue, input.reference.info⟩, input.args.programId⟩
  | .interfaceAccount => ⟨input.args.profile, ⟨⟨input.innerValue, input.reference.info⟩,
    input.savedOwner⟩, input.args.programId⟩

def makeCloseArgs (input : Inputs) : Result CloseArgs := do
  let some destination := input.destination | throw "missing moved close destination"
  pure ⟨input.args.profile, input.reference.info, destination.info⟩

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
