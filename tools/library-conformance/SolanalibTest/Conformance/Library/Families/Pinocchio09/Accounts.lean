/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Pinocchio09.AccountRequires
import Solanalib.Specs.Pinocchio.Guard

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.Pinocchio09.Accounts

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.PinocchioAccount
open AccountsV1

namespace Api
export Solanalib.Specs.Pinocchio.account_info.AccountInfo (key_contract key_run owner_contract
  owner_run
  is_signer_contract is_signer_run is_writable_contract is_writable_run
  is_owned_by_contract is_owned_by_run lamports_contract lamports_run data_len_contract data_len_run
  try_borrow_data_contract try_borrow_data_run try_borrow_mut_data_contract try_borrow_mut_data_run
  try_borrow_mut_lamports_contract try_borrow_mut_lamports_run resize_contract resize_run)
end Api

def method {A V : Type} (name : String) (contract : Solanalib.Contracts.Model State A V)
    (run : State → A → V × State) (pre : ∀ s a, Decidable (contract.requires s a))
    (args : Before → Json → Result A) (value : V → State → Json) : Checker where
  function := "pinocchio::account_info::AccountInfo::" ++ name
  generics := []
  reference := "Solanalib.Specs.Pinocchio.account_info.AccountInfo." ++ name ++ "_run"
  decides := ["Solanalib.Specs.Pinocchio.account_info.AccountInfo." ++ name ++ "_run"]
  decidesRequires := ["Solanalib.Specs.Pinocchio.account_info.AccountInfo." ++ name ++
    "_run"]
  check := fun c => do
    let before ← beforeOf c.state
    let args ← args before c.args
    let expected := run before.state args
    return withReady (@decide (contract.requires before.state args) (pre before.state args)) <|
      observe (returnsOf run before.state args)
        (some (Outcome.returned expected.1 expected.2 : Outcome State V Empty Empty))
        (returnsOf_graph run before.state args)
        (returnJson value (fun s => stateJson before s before.aux)) c.outcome

def keyValue (reference : PubkeyRef) (state : State) : Json :=
  Json.mkObj [("offset", toJson (match reference.field with | .key => (8 : Nat) | .owner => 40)),
    ("bytes", match reference.read state with | some key => pubkeyJson key | none => Json.null)]

def lamportsPre (state : State) (handle : Handle) : Decidable (Api.lamports_contract.requires state
  handle) :=
  lamportsPresentDec state handle

def ordinary : List Checker := [
  method "key" Api.key_contract Api.key_run (fun _ _ => inferInstanceAs (Decidable True))
    Before.handle keyValue,
  method "owner" Api.owner_contract Api.owner_run (fun _ _ => inferInstanceAs (Decidable True))
    Before.handle keyValue,
  method "is_signer" Api.is_signer_contract Api.is_signer_run
    (fun s a => inferInstanceAs (Decidable (∃ h, s.lookup a = some h)))
    Before.handle (fun value _ => toJson value),
  method "is_writable" Api.is_writable_contract Api.is_writable_run
    (fun s a => inferInstanceAs (Decidable (∃ h, s.lookup a = some h)))
    Before.handle (fun value _ => toJson value),
  method "is_owned_by" Api.is_owned_by_contract Api.is_owned_by_run
    (fun s a => inferInstanceAs (Decidable (∃ h, s.lookup a.1 = some h)))
    (fun before j => do return (← before.handle j, ← pubkeyOf (← field j "key")))
    (fun value _ => toJson value),
  method "lamports" Api.lamports_contract Api.lamports_run lamportsPre
    Before.handle (fun value _ => toJson value.toNat),
  method "data_len" Api.data_len_contract Api.data_len_run dataPresentDec
    Before.handle (fun value _ => toJson value),
  method "try_borrow_data" Api.try_borrow_data_contract Api.try_borrow_data_run
    (fun s a => fieldPresentDec s a .data) Before.handle (fun value _ => exceptJson
      programErrorJson guardJson value),
  method "try_borrow_mut_data" Api.try_borrow_mut_data_contract Api.try_borrow_mut_data_run
    (fun s a => fieldPresentDec s a .data) Before.handle (fun value _ => exceptJson
      programErrorJson guardJson value),
  method "try_borrow_mut_lamports" Api.try_borrow_mut_lamports_contract
    Api.try_borrow_mut_lamports_run
    (fun s a => fieldPresentDec s a .lamports) Before.handle (fun value _ => exceptJson
      programErrorJson guardJson value)
]

/-- All parser-produced account states have a balance cell. This separate
negative theorem tests the same registered precondition on a missing cell. -/
theorem lamports_pre_rejects_missing :
    @decide (Api.lamports_contract.requires State.empty ⟨0⟩) (lamportsPre State.empty ⟨0⟩) = false
      := rfl

def zeroStep (before : World) (request : ZeroRequest) : Outcome World Unit Empty Json :=
  .returned () (zeroRange before.1 request,
    before.2.record (Json.mkObj [("syscall", "sol_memset_"), ("byte", toJson (0 : Nat)),
      ("n", toJson request.length)]))

abbrev resizeIndex : ResizeIndex where
  Aux := Aux
  Terminal := Json
  zero := Callback.ofFunction zeroStep
  zeroCorrect := by intro before request after called; cases called; rfl

def resizeComputed (before : World) (args : Handle × Nat) :
    Outcome World (Except ProgramError.Value Unit) Empty Json :=
  if resizeCallsZero before.1 args then
    zeroOutcome resizeIndex (zeroStep (resizeBeforeZero before.1 args, before.2)
      (resizeZeroRequest before.1 args))
  else .returned (resize before.1 args).1 ((resize before.1 args).2, before.2)

theorem resize_graph (before : World) (args : Handle × Nat)
    (outcome : Outcome World (Except ProgramError.Value Unit) Empty Json) :
    Api.resize_run resizeIndex before args outcome ↔ some (resizeComputed before args) = some
      outcome := by
  change resizeRunAt resizeIndex before args outcome ↔ _
  unfold resizeRunAt resizeComputed
  split
  · change (∃ produced, zeroStep _ _ = produced ∧ outcome = zeroOutcome resizeIndex produced) ↔ _
    simp only [Option.some.injEq]
    constructor
    · rintro ⟨produced, called, finished⟩
      cases called
      exact finished.symm
    · intro finished
      exact ⟨_, rfl, finished.symm⟩
  · exact ⟨fun h => congrArg some h.symm, fun h => (Option.some.inj h).symm⟩

def resizeOutcomeJson (before : Before) :
    Outcome World (Except ProgramError.Value Unit) Empty Json → Json
  | .returned value after => returnedJson (exceptJson programErrorJson (fun _ => Json.null) value)
      (stateJson before after.1 after.2)
  | .unwound reason _ => nomatch reason
  | .terminated details => put details "exit" "terminated"

def resizeChecker : Checker where
  function := "pinocchio::account_info::AccountInfo::resize"
  generics := []
  reference := "Solanalib.Specs.Pinocchio.account_info.AccountInfo.resize_run"
  decides := ["Solanalib.Specs.Pinocchio.account_info.AccountInfo.resize_run"]
  decidesRequires := ["Solanalib.Specs.Pinocchio.account_info.AccountInfo.resize_run"]
  check := fun c => do
    let before ← beforeOf c.state
    let args := (← before.handle c.args, ← natField c.args "new_len")
    let world : World := (before.state, before.aux)
    return withReady (@decide ((Api.resize_contract.contract resizeIndex).requires world args)
      (dataPresentDec world.1 args.1)) <|
      observe (Api.resize_run resizeIndex world args) (some (resizeComputed world args))
        (resize_graph world args) (resizeOutcomeJson before) c.outcome

def guardMethod {V : Type} (function name : String)
    (contract : Solanalib.Contracts.Model guardProfile.World Guard V)
    (pre : ∀ s a, Decidable (contract.requires s a))
    (relation : guardProfile.World → Guard → Outcome guardProfile.World V Empty Empty → Prop)
    (run : guardProfile.World → Guard → V × guardProfile.World)
    (evaluated : relation = returnsOf run) (value : V → guardProfile.World → Json) : Checker where
  function := function
  generics := [("T", "[u8]")]
  reference := "Solanalib.Specs.Pinocchio.account_info." ++ name ++ "_run"
  decides := ["Solanalib.Specs.Pinocchio.account_info." ++ name ++ "_run"]
  decidesRequires := ["Solanalib.Specs.Pinocchio.account_info." ++ name ++ "_run"]
  check := fun c => do
    let before ← beforeOf c.state
    let guard ← guardOf c.args
    let world := guardWorld before
    let expected := run world guard
    return withReady (@decide (contract.requires world guard) (pre world guard)) <|
      observe (relation world guard) (some (.returned expected.1 expected.2))
        (fun outcome => by rw [evaluated]; exact returnsOf_graph run world guard outcome)
        (returnJson value (fun s => guardWorldJson before s)) c.outcome

def derefFn (mutable : Bool) (world : guardProfile.World) (guard : Guard) :
    Reference × guardProfile.World := (⟨guard, mutable⟩, world)
def guards : List Checker := [
  guardMethod "<pinocchio::account_info::Ref<'_, T> as core::ops::deref::Deref>::deref"
    "Ref.deref"
    (Solanalib.Specs.Pinocchio.account_info.Ref.deref_contract.contract guardProfile) (fun _ _ =>
      inferInstanceAs (Decidable True))
    (Solanalib.Specs.Pinocchio.account_info.Ref.deref_run guardProfile) (derefFn false) rfl
      referenceJson,
  guardMethod "<pinocchio::account_info::RefMut<'_, T> as core::ops::deref::Deref>::deref"
    "RefMut.deref"
    (Solanalib.Specs.Pinocchio.account_info.RefMut.deref_contract.contract guardProfile) (fun _ _
      => inferInstanceAs (Decidable True))
    (Solanalib.Specs.Pinocchio.account_info.RefMut.deref_run guardProfile) (derefFn false) rfl
      referenceJson,
  guardMethod "<pinocchio::account_info::RefMut<'_, T> as \
    core::ops::deref::DerefMut>::deref_mut"
    "RefMut.deref_mut"
    (Solanalib.Specs.Pinocchio.account_info.RefMut.deref_mut_contract.contract guardProfile) (fun _
      _ => inferInstanceAs (Decidable True))
    (Solanalib.Specs.Pinocchio.account_info.RefMut.deref_mut_run guardProfile) (derefFn true) rfl
      referenceJson]

structure MapInput where
  guard : Guard
  panics : Bool
  mutate : Bool
  start : Nat
  length : Nat

def mapInput (j : Json) : Result MapInput := do
  return ⟨← guardOf j, ← boolField j "panics", ← boolField j "mutate", ← natField j "start", ←
    natField j "len"⟩

def mapStep (input : MapInput) : MapStep := fun before cell _ =>
  let store := if input.mutate then
    match (before.1.lookupCell cell).map Borrow.Cell.value with
    | some (.data data) => (Borrow.replaceCell before.1 cell (.data {
        data with backing := data.backing.set 0 99 })).2
    | _ => before.1
    else before.1
  let after : guardProfile.World := (store, before.2.1, before.2.2.event "map")
  if input.panics then .unwound "map callback" after
  else .returned (.bytes input.start input.length) after

def mapComputed (world : guardProfile.World) (input : MapInput) :
    Option (Outcome guardProfile.World Guard String Json) := do
  let slot ← world.1.resolve input.guard
  let _ ← world.1.lookupCell slot.cell
  return finishMap mapProfile input.guard slot.view (mapStep input world slot.cell slot.view)

theorem map_graph (world : guardProfile.World) (input : MapInput)
    (outcome : Outcome guardProfile.World Guard String Json) :
    Solanalib.Specs.Pinocchio.account_info.RefMut.map_run mapProfile world (mapArgs input.guard
      (mapStep input)) outcome ↔
      mapComputed world input = some outcome := by
  change mapRunAt mapProfile world (mapArgs input.guard (mapStep input)) outcome ↔ _
  constructor
  · rintro ⟨slot, cell, produced, live, present, called, rfl⟩
    change mapStep input world slot.cell slot.view = produced at called
    cases called
    change world.1.resolve input.guard = some slot at live
    simp [mapComputed, live, present, mapArgs, Option.bind]
  · intro computed
    change (world.1.resolve input.guard).bind (fun slot =>
      (world.1.lookupCell slot.cell).bind (fun _ =>
        some (finishMap mapProfile input.guard slot.view (mapStep input world slot.cell
          slot.view)))) = some outcome at computed
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at computed
    obtain ⟨slot, live, cell, present, finished⟩ := computed
    exact ⟨slot, cell, _, live, present, rfl, finished.symm⟩

def mapOutcomeJson (before : Before) (input : MapInput) :
    Outcome guardProfile.World Guard String Json → Json
  | .returned guard world => returnedJson (guardJson guard) (guardWorldJson before world)
  | .unwound reason world => Json.mkObj [("exit", "unwound"), ("reason", toJson reason),
      ("state", guardWorldJson before world [input.guard.id])]
  | .terminated details => put details "exit" "terminated"

def mapChecker : Checker where
  function := "pinocchio::account_info::RefMut::<'a, T>::map"
  generics := [("T", "[u8]")]
  reference := "Solanalib.Specs.Pinocchio.account_info.RefMut.map_run"
  decides := ["Solanalib.Specs.Pinocchio.account_info.RefMut.map_run"]
  decidesRequires := ["Solanalib.Specs.Pinocchio.account_info.RefMut.map_run"]
  check := fun c => do
    let before ← beforeOf c.state
    let input ← mapInput c.args
    let world := guardWorld before
    let args := mapArgs input.guard (mapStep input)
    return withReady (@decide ((Solanalib.Specs.Pinocchio.account_info.RefMut.map_contract.contract
      mapProfile).requires world args)
      (mapReadyDec world input.guard (mapStep input))) <|
      observe (Solanalib.Specs.Pinocchio.account_info.RefMut.map_run mapProfile world args)
        (mapComputed world input) (map_graph world input) (mapOutcomeJson before input) c.outcome

def checkers : List Checker := ordinary ++ [resizeChecker] ++ guards ++ [mapChecker]

end SolanalibTest.Conformance.Library.Families.Pinocchio09.Accounts
