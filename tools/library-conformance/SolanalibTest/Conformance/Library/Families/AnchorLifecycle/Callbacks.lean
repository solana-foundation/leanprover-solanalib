/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.Errors

/-! The native drivers supply these concrete trait implementations. Each
scripted call records its actual argument, Rc counts and live leases before
performing its effects. Missing script entries have no finite interpretation.
The library under test remains the published crate, with no replaced body. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Families.Anchor

structure Step where
  key : Solanalib.Runtime.Pubkey
  assign : Option Solanalib.Runtime.Pubkey
  lamports : Option Nat
  value : Nat
  error : Nat
  panic : Bool
  bytes : Solanalib.Runtime.Bytes
  deriving DecidableEq, Repr

structure Script where
  owner : List Step
  checkOwner : List Step
  id : List Step
  checkId : List Step
  decode : List Step
  serialize : List Step
  dropPayload : List Step
  sysvar : List Step
  inner : List Step
  discriminatorMessage : String := "Account discriminator did not match what was expected"
  deriving DecidableEq, Repr

def Event.sameCall : Event → Event → Bool
  | .owner, .owner | .id, .id | .checkOwner _, .checkOwner _ | .checkId _, .checkId _
  | .decode _ _, .decode _ _ | .serialize _, .serialize _ | .write _, .write _
  | .dropPayload _, .dropPayload _ | .sysvar _, .sysvar _ => true
  | .innerAccounts _ _ _, .innerAccounts _ _ _ | .innerAccounts _ _ _, .innerExit _ _
  | .innerAccounts _ _ _, .innerClose _ _ | .innerExit _ _, .innerAccounts _ _ _
  | .innerExit _ _, .innerExit _ _ | .innerExit _ _, .innerClose _ _
  | .innerClose _ _, .innerAccounts _ _ _ | .innerClose _ _, .innerExit _ _
  | .innerClose _ _, .innerClose _ _ => true
  | _, _ => false

def begin (steps : List Step) (target : AccountInfo.Value) (event : Event) (state : W) :
    Option (Step × W) :=
  (steps[callCount state (Event.sameCall event)]?).map fun step => (step, push state target event)

/-- AccountInfo::assign changes the referenced owner. The scripted lamport
write uses an actual exclusive RefCell lease and releases it before returning.
No writable-metadata check is invented for this local SDK operation. -/
def effectsFn (target : AccountInfo.Value) (step : Step) (state : W) : Option (SigOut Unit) :=
  let assigned := match step.assign with
    | none => state
    | some key => (state.1, { state.2 with owners := state.2.owners.set target.ownerRef.id key })
  match step.lamports with
  | none => some (.returned () assigned)
  | some balance =>
    let (acquired, during) := AccountInfo.tryBorrow .exclusive target.lamports assigned.1
    match acquired with
    | .error _ => some (.unwound "RefCell already borrowed" (during, assigned.2))
    | .ok guard => match Borrow.current during guard with
      | .error _ | .ok (_, .data _) => none
      | .ok (_, .lamports _) =>
        let (written, afterWrite) := Borrow.write during guard (.lamports (UInt64.ofNat balance))
        match written with
        | .error _ => none
        | .ok () =>
          let (released, after) := Borrow.release afterWrite guard
          match released with
          | .error _ => none
          | .ok () => some (.returned () (after, assigned.2))

def sigDep {Value : Type} : DepOut Value → SigOut Value := AccountInfoRc.liftOutcome

def customFn (storage : AnchorErrorOperations.Storage) (state : W) (number : Nat) :
    Option (SigOut (Error storage)) :=
  (fromPayloadFn storage state (.program ⟨.plain (.custom (UInt32.ofNat number)), none, none⟩)).map
    sigDep

def returnedFn (storage : AnchorErrorOperations.Storage) (state : W) (step : Step) :
    Option (SigOut (Except (Error storage) Unit)) :=
  if step.error = 0 then some (.returned (.ok ()) state)
  else (customFn storage state step.error).map (Outcome.map Except.error)

def keyFn (steps : List Step) (target : AccountInfo.Value) (event : Event) (label : String)
    (state : W) : Option (SigOut Solanalib.Runtime.Pubkey) := do
  let (step, logged) ← begin steps target event state
  (effectsFn target step logged).bind (PGraph.bindK fun _ after =>
    some (if step.panic then .unwound label after else .returned step.key after))

def checkFn (storage : AnchorErrorOperations.Storage) (steps : List Step)
    (target : AccountInfo.Value) (event : Event) (label : String) (state : W) :
    Option (SigOut (Except (Error storage) Unit)) := do
  let (step, logged) ← begin steps target event state
  (effectsFn target step logged).bind (PGraph.bindK fun _ after =>
    if step.panic then some (.unwound label after) else returnedFn storage after step)

def discriminator : Solanalib.Runtime.Bytes := [1, 2, 3, 4, 5, 6, 7, 8]

def decodeFn (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (checked : Bool) (state : W) (args : AnchorAccount.DecodeArgs) :
    Option (SigOut (AnchorConstructOwned.Decoded (Error storage) Nat)) := do
  let (step, logged) ← begin script.decode target (.decode checked args.bytes) state
  (effectsFn target step logged).bind (PGraph.bindK fun _ after =>
    if step.panic then some (.unwound "script deserialize" after)
    else if step.error ≠ 0 then (customFn storage after step.error).map
      (Outcome.map fun error => ⟨.error error, args.bytes⟩)
    else if checked && !(discriminator.isPrefixOf args.bytes) then
      (fromCodeFn storage after ⟨"AccountDiscriminatorMismatch", 3002,
        script.discriminatorMessage⟩).map
          (fun produced => (sigDep produced).map fun error => ⟨.error error, args.bytes⟩)
    else some (.returned ⟨.ok step.value, args.bytes.drop 8⟩ after))

def dropPayloadFn (script : Script) (target : AccountInfo.Value) (state : W) (value : Nat) :
    Option (SigOut Unit) := do
  let (step, logged) ← begin script.dropPayload target (.dropPayload value) state
  (effectsFn target step logged).bind (PGraph.bindK fun _ after =>
    some (if step.panic then .unwound "script drop_payload" after else .returned () after))

def serializeFn (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (state : W) (args : SerializeArgs Nat) :
    Option (SigOut (Except (Error storage) Unit)) := do
  let (step, logged) ← begin script.serialize target (.serialize args.payload) state
  (effectsFn target step logged).bind (PGraph.bindK fun _ after =>
    match Borrow.current after.1 args.guard with
    | .error _ | .ok (_, .lamports _) => none
    | .ok (_, .data bytes) =>
      let count := min step.bytes.length (bytes.length - args.position)
      let writtenBytes := bytes.take args.position ++ step.bytes.take count ++ bytes.drop
        (args.position + count)
      let (written, afterWrite) := Borrow.write after.1 args.guard (.data writtenBytes)
      match written with
      | .error _ => none
      | .ok () =>
        let copied := if args.position < bytes.length then
          { after.2 with memoryCopies := after.2.memoryCopies ++ [step.bytes.take count] } else
            after.2
        let final := push (afterWrite, copied) target (.write count)
        if step.panic then some (.unwound "script serialize" final) else returnedFn storage final
          step)

def sysvarFn (legacy : Bool) (script : Script) (target : AccountInfo.Value)
    (state : W) (reference : AccountReference) : Option (SigOut (Except Program Nat)) := do
  let (step, logged) ← begin script.sysvar target (.sysvar reference.identity) state
  (effectsFn target step logged).bind (PGraph.bindK fun _ after =>
    if step.panic then some (.unwound "script from_account_info" after)
    else if step.error = 1 then
      if legacy then
        let resource := after.2.strings.length
        let final := (after.1, { after.2 with
          strings := after.2.strings ++ [some "owned syscall decoder failure"],
          programString := some resource })
        some (.returned (.error (.legacyBorsh resource)) final)
      else some (.returned (.error (.plain .borshIoError)) after)
    else if step.error = 0 then some (.returned (.ok step.value) after)
    else some (.returned (.error (.plain (.custom (UInt32.ofNat step.error)))) after))

def payloadTypes (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (checked : Bool) : PayloadTypes where
  toBase := base storage
  Payload := Nat
  ownerAt := ownerAt
  owner := fun state _ outcome => keyFn script.owner target .owner "script owner" state = some
    outcome
  checkOwner := fun state reference outcome =>
    checkFn storage script.checkOwner target (.checkOwner reference.id) "script check_owner" state
      = some outcome
  deserialize := fun state args outcome => decodeFn storage script target checked state args = some
    outcome
  rc := rc

def validationTypes (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) (legacy : Bool) : ValidationTypes where
  toBase := base storage
  Payload := Nat
  ownerAt := ownerAt
  id := fun state _ outcome => keyFn script.id target .id "script id" state = some outcome
  checkId := fun state key outcome =>
    checkFn storage script.checkId target (.checkId key) "script check_id" state = some outcome
  fromAccountInfo := fun state reference outcome => sysvarFn legacy script target state reference =
    some outcome
  rc := rc

def reloadTypes (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) : ReloadTypes where
  toPayloadTypes := payloadTypes storage script target true
  payload := payloadFocus
  dropPayload := fun state value outcome => dropPayloadFn script target state value = some outcome

def exitTypes (storage : AnchorErrorOperations.Storage) (script : Script)
    (target : AccountInfo.Value) : ExitTypes where
  toBase := base storage
  Payload := Nat
  ownerAt := ownerAt
  owner := fun state _ outcome => keyFn script.owner target .owner "script owner" state = some
    outcome
  serialize := fun state args outcome => serializeFn storage script target state args = some outcome
  rc := rc

def closeTypes (storage : AnchorErrorOperations.Storage) : CloseTypes where
  toBase := base storage
  sdk := sdk
  borrow_eq := fun _ => rfl
  rc := rc

/-- Widening adds the local panic variants of the constructor; it does not admit a
new callback outcome. -/
theorem widened_graph {Args Value : Type} {run : Callback.Run W Args Value String Unit}
    {state : W} {args : Args} {fn : Option (SigOut Value)} (graph : PGraph (run state args) fn) :
    PGraph (AnchorAccount.widenCallback run state args) (fn.map AnchorAccount.widen) :=
  PGraph.exists_eq AnchorAccount.widen graph

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
