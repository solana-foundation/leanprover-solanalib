/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.construct
public import Solanalib.Specs.AnchorLang.loading

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

set_option maxRecDepth 4096

namespace SolanalibTest.Specs.AnchorLang.OwnedErrors

open Solanalib.Contracts.Model Solanalib.Specs.Core

structure Aux where
  heap : AnchorErrorOwned.Reference.State
  owner : Solanalib.Runtime.Pubkey
  ownerCalls : Nat

abbrev World := AnchorAccount.World Aux

def heapFocus : Owned.Focus World AnchorErrorOwned.Reference.State where
  get := fun state => state.2.heap
  set := fun state heap => (state.1, { state.2 with heap })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def baseOps := AnchorErrorOwned.Reference.ops.focus heapFocus

/-- This primitive interpretation assigns a new owner while constructing the
name String. The modeled SDK must observe this effect after error allocation. -/
def errors : AnchorErrorOwned.Ops World AnchorErrorOwned.Reference.StringId
    AnchorErrorOwned.Reference.BoxId AnchorErrorOwned.Reference.Failure :=
  { baseOps with
    copyLiteral := Callback.bind baseOps.copyLiteral
      (fun resource after outcome => outcome = .returned resource
        (after.1, { after.2 with owner := .ofNat 9 })) }

def types : AnchorConstructOwned.Types where
  Aux := Aux
  Payload := Nat
  Unwind := String
  Terminal := AnchorErrorOwned.Reference.Failure
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  errors := errors
  discriminator := [10]
  ownerAt := fun state _ => state.owner
  owner := Callback.ofFunction fun state _ =>
    if state.2.ownerCalls = 0 then .returned (.ofNat 99)
      (state.1, { state.2 with ownerCalls := 1 })
    else .returned (.ofNat 88) (state.1, { state.2 with owner := .ofNat 7, ownerCalls := 2 })
  checkOwner := Callback.ofFunction fun state _ => .returned (.ok ()) state
  deserialize := Callback.ofFunction fun state _ => .returned ⟨.ok 7, []⟩
    (state.1, { state.2 with owner := .ofNat 5 })

/-- Actual Box allocations initialize their payload, and the Owner callback
changes only the separate owner fields. These prove the reached resource gate. -/
theorem owner_resources_ready (state : World) (args : AccountInfo.Args) :
    AnchorConstructOwned.OwnerCheckReady types state args := by
  intro expected after first mismatch name afterName copied message afterMessage formatted resource
    afterBox boxed
  have laws := AnchorErrorOwned.Reference.ops.focus_laws AnchorErrorOwned.Reference.ops_laws
    heapFocus
  have held := laws.box.current afterMessage (AnchorConstructOwned.ownerErrorPayload types name
    message)
    resource afterBox boxed
  refine ⟨held, ?_⟩
  intro produced called
  change (if afterBox.2.ownerCalls = 0 then Outcome.returned (.ofNat 99)
    (afterBox.1, { afterBox.2 with ownerCalls := 1 }) else
    .returned (.ofNat 88) (afterBox.1, { afterBox.2 with owner := .ofNat 7, ownerCalls := 2 })) =
      produced at called
  split at called <;> cases called
  · exact ⟨rfl, laws.store.available _ _ _ _ held⟩
  · exact ⟨rfl, laws.store.available _ _ _ _ held⟩

def initialAux : Aux := ⟨AnchorErrorOwned.Reference.initial 3, .zero, 0⟩
def initial : World := (AccountInfo.sampleState, initialAux)
def afterOwner : World := (initial.1, { initial.2 with ownerCalls := 1 })
def wrongCode : AnchorErrorOwned.Code :=
  ⟨AnchorAccount.Code.ownedByWrongProgram.payload.name,
    AnchorAccount.Code.ownedByWrongProgram.payload.code,
    AnchorAccount.Code.ownedByWrongProgram.payload.message⟩
def nameResult := AnchorErrorOwned.Reference.stringResult false afterOwner.2.heap wrongCode.name
def afterName : World := (afterOwner.1, ⟨nameResult.2, .ofNat 9, 1⟩)
def messageResult := AnchorErrorOwned.Reference.stringResult true afterName.2.heap wrongCode.message
def afterMessage : World := (afterName.1, { afterName.2 with heap := messageResult.2 })
def payload : AnchorErrorOwned.Payload AnchorErrorOwned.Reference.StringId :=
  .anchor ⟨nameResult.1, wrongCode.number, messageResult.1, none, none⟩
def boxResult := AnchorErrorOwned.Reference.boxResult afterMessage.2.heap payload
def error : AnchorErrorOwned.Error AnchorErrorOwned.Reference.BoxId := ⟨boxResult.1⟩
def afterBuild : World := (afterMessage.1, { afterMessage.2 with heap := boxResult.2 })
def afterSecondOwner : World := (afterBuild.1, { afterBuild.2 with owner := .ofNat 7, ownerCalls :=
  2 })
def diagnosticHeap := AnchorErrorOwned.Reference.writeBox afterSecondOwner.2.heap error.resource
  (payload.withPubkeys (.ofNat 9) (.ofNat 88))
def diagnosticState : World := (afterSecondOwner.1,
  { afterSecondOwner.2 with heap := diagnosticHeap.getD (AnchorErrorOwned.Reference.initial 0) })

theorem copied_name : errors.copyLiteral afterOwner wrongCode.name (.returned nameResult.1
  afterName) := by
  refine ⟨.returned nameResult.1 (heapFocus.set afterOwner nameResult.2), ?_, rfl⟩
  exact ⟨.returned nameResult.1 nameResult.2, rfl, rfl⟩

theorem formatted_message : errors.formatLiteral afterName wrongCode.message
    (.returned messageResult.1 afterMessage) :=
  ⟨.returned messageResult.1 messageResult.2, rfl, rfl⟩

theorem allocated_box : errors.newBox afterMessage payload (.returned boxResult.1 afterBuild) :=
  ⟨.returned boxResult.1 boxResult.2, rfl, rfl⟩

theorem allocation_changes_owner : AnchorErrorOwned.buildCode errors afterOwner wrongCode
    (.returned error afterBuild) := by
  apply (AnchorErrorOwned.buildCode_returned_iff _ _ _ _ _).mpr
  refine ⟨nameResult.1, afterName, messageResult.1, afterMessage, ?_, ?_, ?_⟩
  · refine ⟨.returned nameResult.1 (heapFocus.set afterOwner nameResult.2), ?_, rfl⟩
    exact ⟨.returned nameResult.1 nameResult.2, rfl, rfl⟩
  · exact ⟨.returned messageResult.1 messageResult.2, rfl, rfl⟩
  · exact ⟨.returned boxResult.1 boxResult.2, rfl, rfl⟩

theorem code_returns : AnchorConstructOwned.code types .ownedByWrongProgram afterOwner ()
    (.returned error afterBuild) :=
  ⟨.returned error afterBuild, ⟨.returned error afterBuild, allocation_changes_owner, rfl⟩, rfl⟩

theorem replace_diagnostic : AnchorErrorOwned.withPubkeys errors afterSecondOwner
    (error, .ofNat 9, .ofNat 88) (.returned error diagnosticState) := by
  refine ⟨payload, rfl, .returned () afterSecondOwner, rfl, payload, rfl, diagnosticState, rfl, rfl⟩

/-- The diagnostic left key is read after all error allocations and before
the second Owner callback. Both changes remain visible in the final state. -/
theorem owner_diagnostic_reads_after_allocation :
    AnchorConstructOwned.ownerCheck types initial AccountInfo.sampleArgs
      (.returned (.error error) diagnosticState) := by
  obtain ⟨final, _, stored, retained⟩ := AnchorConstructOwned.owner_mismatch_return_retain
    (owner_resources_ready initial AccountInfo.sampleArgs)
    (show types.owner initial () (.returned (.ofNat 99) afterOwner) from rfl)
    (by decide) copied_name formatted_message allocated_box
    (show types.owner afterBuild () (.returned (.ofNat 88) afterSecondOwner) from rfl)
  change some diagnosticState = some final at stored
  cases stored
  exact retained

theorem diagnostic_and_final_owner_differ :
    AnchorErrorOwned.current errors diagnosticState error =
      some ((AnchorAccount.error .ownedByWrongProgram).replaceCompared (.pubkeys (.ofNat 9) (.ofNat
        88))) ∧
    types.ownerAt diagnosticState.2 AccountInfo.sampleInfo.ownerRef = .ofNat 7 ∧
    diagnosticState.2.ownerCalls = 2 := ⟨rfl, rfl, rfl⟩

/-- This Owner mismatch cannot reach the data scope of the Loader. Its admitted
error branch therefore needs no law for an uncalled guarded factory. -/
theorem owner_mismatch_loader_ready :
    ((AnchorConstructOwned.family .loader).contract types).requires initial AccountInfo.sampleArgs
      := by
  refine ⟨owner_resources_ready initial AccountInfo.sampleArgs, ?_⟩
  intro checked owned
  obtain ⟨expected, ⟨produced, called, widened⟩, matching⟩ :=
    AnchorConstructOwned.ownerCheck_returned_ok owned
  change .returned (.ofNat 99) afterOwner = produced at called
  cases called
  cases widened
  exact False.elim ((by decide : _root_.Solanalib.Runtime.Pubkey.zero ≠ .ofNat 99) matching)

/-- Owner changes during error allocation are exercised inside the complete
Loader constructor family with all callback effects retained. -/
theorem owner_mutation_is_family_execution :
    FamilyHasExecution (AnchorConstructOwned.family .loader)
      (AnchorConstructOwned.reference .loader) types := by
  refine ⟨initial, AccountInfo.sampleArgs, .returned (.error error) diagnosticState,
    owner_mismatch_loader_ready, ?_⟩
  exact ⟨.returned (.error error) diagnosticState, owner_diagnostic_reads_after_allocation, rfl⟩

def unwindTypes : AnchorConstructOwned.Types :=
  { types with
    owner := Callback.ofFunction fun state _ =>
      if state.2.ownerCalls = 0 then .returned (.ofNat 99)
        (state.1, { state.2 with ownerCalls := 1 })
      else .unwound "second owner" (state.1, { state.2 with owner := .ofNat 7, ownerCalls := 2 }) }

theorem unwind_owner_resources_ready (state : World) (args : AccountInfo.Args) :
    AnchorConstructOwned.OwnerCheckReady unwindTypes state args := by
  intro expected after first mismatch name afterName copied message afterMessage formatted resource
    afterBox boxed
  have laws := AnchorErrorOwned.Reference.ops.focus_laws AnchorErrorOwned.Reference.ops_laws
    heapFocus
  have held := laws.box.current afterMessage (AnchorConstructOwned.ownerErrorPayload unwindTypes
    name message)
    resource afterBox boxed
  refine ⟨held, ?_⟩
  intro produced called
  change (if afterBox.2.ownerCalls = 0 then Outcome.returned (.ofNat 99)
    (afterBox.1, { afterBox.2 with ownerCalls := 1 }) else
    .unwound "second owner" (afterBox.1, { afterBox.2 with owner := .ofNat 7, ownerCalls := 2 })) =
      produced at called
  split at called <;> cases called
  · exact ⟨rfl, laws.store.available _ _ _ _ held⟩
  · rfl

def nameDroppedHeap : AnchorErrorOwned.Reference.State :=
  ⟨[none, some wrongCode.message], afterSecondOwner.2.heap.boxes, 0,
    afterSecondOwner.2.heap.events ++ [.dropString nameResult.1 wrongCode.name]⟩
def nameDropped : World := heapFocus.set afterSecondOwner nameDroppedHeap
def stringsDroppedHeap : AnchorErrorOwned.Reference.State :=
  ⟨[none, none], nameDroppedHeap.boxes, 0,
    nameDroppedHeap.events ++ [.dropString messageResult.1 wrongCode.message]⟩
def stringsDropped : World := heapFocus.set nameDropped stringsDroppedHeap
def droppedHeap : AnchorErrorOwned.Reference.State :=
  ⟨[none, none], [none], 0, stringsDroppedHeap.events ++ [.freeBox error.resource]⟩
def dropped : World := heapFocus.set stringsDropped droppedHeap

theorem built_error_fields : AnchorErrorOwned.dropStrings errors [nameResult.1, messageResult.1]
    afterSecondOwner () (.returned () stringsDropped) := by
  refine ⟨.returned () nameDropped, ?_, .returned () stringsDropped, ?_, rfl⟩
  · exact ⟨.returned () nameDroppedHeap, ⟨wrongCode.name, rfl, rfl⟩, rfl⟩
  · exact ⟨.returned () stringsDroppedHeap, ⟨wrongCode.message, rfl, rfl⟩, rfl⟩

theorem built_error_free : errors.freeBox stringsDropped error.resource (.returned () dropped) :=
  ⟨.returned () droppedHeap, ⟨payload, rfl, rfl⟩, rfl⟩

theorem built_error_drop : AnchorErrorOwned.dropError errors error afterSecondOwner
    (.returned () dropped) := by
  refine ⟨payload, rfl, .returned () stringsDropped, ?_, ?_⟩
  · refine ⟨.returned () nameDropped, ?_, .returned () stringsDropped, ?_, rfl⟩
    · exact ⟨.returned () nameDroppedHeap, ⟨wrongCode.name, rfl, rfl⟩, rfl⟩
    · exact ⟨.returned () stringsDroppedHeap, ⟨wrongCode.message, rfl, rfl⟩, rfl⟩
  · exact ⟨.returned () droppedHeap, ⟨payload, rfl, rfl⟩, rfl⟩

/-- An unwind from the second Owner call destroys the already built name,
message and Box, after preserving the current owner assignment of the callback. -/
theorem second_owner_unwind_drops_error :
    AnchorConstructOwned.ownerCheck unwindTypes initial AccountInfo.sampleArgs
      (.unwound (.inr "second owner") dropped) := by
  exact AnchorConstructOwned.owner_mismatch_unwind_retain
    (unwind_owner_resources_ready initial AccountInfo.sampleArgs)
    (show unwindTypes.owner initial () (.returned (.ofNat 99) afterOwner) from rfl)
    (by decide) copied_name formatted_message allocated_box
    (show unwindTypes.owner afterBuild () (.unwound "second owner" afterSecondOwner) from rfl)
    built_error_fields built_error_free

/-- The exact Loader family retains the second Owner unwind and all three
actual destructor returns under the reached resource admission. -/
theorem second_owner_unwind_is_family_execution :
    FamilyHasExecution
      Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_contract
      Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_run unwindTypes :=
        by
  refine ⟨initial, AccountInfo.sampleArgs, .unwound (.inr "second owner") dropped, ?_, ?_⟩
  · refine ⟨unwind_owner_resources_ready initial AccountInfo.sampleArgs, ?_⟩
    intro checked owned
    obtain ⟨expected, ⟨produced, called, widened⟩, matching⟩ :=
      AnchorConstructOwned.ownerCheck_returned_ok owned
    change .returned (.ofNat 99) afterOwner = produced at called
    cases called
    cases widened
    exact False.elim ((by decide : _root_.Solanalib.Runtime.Pubkey.zero ≠ .ofNat 99) matching)
  · exact ⟨.unwound (.inr "second owner") dropped, second_owner_unwind_drops_error, rfl⟩

theorem unwind_resources_retired : AnchorErrorOwned.current errors dropped error = none ∧
    errors.currentString dropped nameResult.1 = none ∧
    errors.currentString dropped messageResult.1 = none ∧
    types.ownerAt dropped.2 AccountInfo.sampleInfo.ownerRef = .ofNat 7 := ⟨rfl, rfl, rfl, rfl⟩

def decodedAux : Aux := { initialAux with owner := .ofNat 5 }

/-- Changing the auxiliary owner preserves the live shared data guard and
its bytes on every exit of this concrete decoder. -/
theorem decoder_ready : AnchorConstructOwned.DecodeReady types
    (AnchorAccount.sampleAfterInit, initialAux) AccountInfo.sampleArgs := by
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro guard during acquired view bytes current produced called
  change (Except.ok (⟨1, 0⟩ : Borrow.Guard), AnchorAccount.sampleDataDuring) =
    (.ok guard, during) at acquired
  cases acquired
  cases called
  exact AnchorAccount.sharedDataFrame_refl _ _ AnchorAccount.sampleDataDuring_valid

theorem interface_ready :
    ((AnchorConstructOwned.family .interfaceAccount).contract types).requires
      initial AccountInfo.sampleArgs := by
  refine ⟨?_, ?_⟩
  · intro _ impossible
    cases impossible
  intro after started checked owned
  have same : after = (AnchorAccount.sampleAfterInit, initialAux) :=
    (Outcome.returned.inj started).2
  cases same
  obtain ⟨produced, called, widened⟩ := owned
  change .returned (.ok ()) (AnchorAccount.sampleAfterInit, initialAux) = produced at called
  cases called
  cases widened
  exact decoder_ready

theorem decoder_changes_current_owner : AnchorConstructOwned.decodeAccount types
    (AnchorAccount.sampleAfterInit, initialAux) AccountInfo.sampleArgs
    (.returned (.ok (7 : Nat)) (AnchorAccount.sampleAfterDecode, decodedAux)) := by
  refine ⟨.returned (.ok (7 : Nat)) (AnchorAccount.sampleDataDuring, decodedAux), ?_, rfl⟩
  exact ⟨.returned ⟨.ok (7 : Nat), []⟩ (AnchorAccount.sampleDataDuring, decodedAux),
    ⟨.returned ⟨.ok (7 : Nat), []⟩ (AnchorAccount.sampleDataDuring, decodedAux), rfl, rfl⟩, rfl⟩

/-- The complete interface constructor captures the new owner of the decoder and
releases its temporary guard. Its retained Info.owner remains an entry snapshot. -/
theorem interface_records_decoded_owner :
    AnchorConstructOwned.run .interfaceAccount types initial AccountInfo.sampleArgs
      (.returned (.ok (AnchorAccount.InterfaceAccount.mk
        ⟨(7 : Nat), AccountInfo.sampleInfo⟩ (.ofNat 5)))
        (AnchorAccount.sampleAfterDecode, decodedAux)) := by
  have checked : AnchorAccount.widenCallback types.checkOwner
      (AnchorAccount.sampleAfterInit, initialAux) AccountInfo.sampleInfo.ownerRef
      (.returned (.ok ()) (AnchorAccount.sampleAfterInit, initialAux)) :=
    ⟨.returned (.ok ()) (AnchorAccount.sampleAfterInit, initialAux), rfl, rfl⟩
  obtain ⟨decoded, released, retained⟩ := AnchorConstructOwned.interface_retain
    interface_ready rfl checked rfl rfl
    (show types.deserialize (AnchorAccount.sampleDataDuring, initialAux)
      ⟨AccountInfo.sampleInfo, ⟨1, 0⟩, [10, 20, 30]⟩
      (.returned ⟨.ok (7 : Nat), []⟩ (AnchorAccount.sampleDataDuring, decodedAux)) from rfl)
  change some (Outcome.returned (Except.ok (7 : Nat))
    (AnchorAccount.sampleAfterDecode, decodedAux)) = some decoded at released
  cases released
  exact retained

/-- The owner-changing decoder supplies a complete family execution. -/
theorem decoder_mutation_is_family_execution :
    FamilyHasExecution (AnchorConstructOwned.family .interfaceAccount)
      (AnchorConstructOwned.reference .interfaceAccount) types :=
  ⟨initial, AccountInfo.sampleArgs,
    .returned (.ok (AnchorAccount.InterfaceAccount.mk
      ⟨(7 : Nat), AccountInfo.sampleInfo⟩ (.ofNat 5)))
      (AnchorAccount.sampleAfterDecode, decodedAux),
    interface_ready, interface_records_decoded_owner⟩

theorem later_observation_sees_decoded_owner :
    types.ownerAt decodedAux (AccountInfo.clone AccountInfo.sampleInfo).ownerRef = .ofNat 5 ∧
    AccountInfo.sampleInfo.owner = .zero ∧
    AnchorAccount.sampleAfterDecode.sharedCount AccountInfo.sampleInfo.data = 0 := ⟨rfl, rfl, rfl⟩

/-- An abstract width outside the Rust binding does not suppress an Owner
unwind before any data borrow or error allocation is reached. -/
def abstractArgs : AccountInfo.Args :=
  { AccountInfo.sampleArgs with profile := { AccountInfo.sampleProfile with wordBits := 0 } }

def stoppingTypes : AnchorConstructOwned.Types :=
  { types with owner := Callback.ofFunction fun before _ => .unwound "owner stop" before }

theorem abstract_width_retains_owner_unwind :
    ¬ AccountInfo.Valid abstractArgs.profile initial.1 abstractArgs.info ∧
    (Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_contract.contract
      stoppingTypes).requires initial abstractArgs ∧
    Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_run stoppingTypes
      initial abstractArgs (.unwound (.inr "owner stop") initial) := by
  refine ⟨?_, ?_, ?_⟩
  · intro valid
    exact (by decide : ¬ 2 ≤ 0) valid.1
  · refine ⟨?_, ?_⟩
    · intro expected after called
      cases called
    intro checked owned
    obtain ⟨expected, ⟨produced, called, widened⟩, _⟩ :=
      AnchorConstructOwned.ownerCheck_returned_ok owned
    change .unwound "owner stop" initial = produced at called
    cases called
    cases widened
  · refine ⟨.unwound (.inr "owner stop") initial, ?_, rfl⟩
    exact ⟨.unwound (.inr "owner stop") initial,
      ⟨.unwound "owner stop" initial, rfl, rfl⟩, rfl⟩

namespace BoxLoss

abbrev Heap := Option (AnchorErrorOwned.Payload Bool)
abbrev State := AnchorAccount.World Heap

/-- The small provider really creates a Box with two distinct String fields. -/
def errors : AnchorErrorOwned.Ops State Bool Unit String where
  currentString := fun _ resource => some (if resource then "message" else "name")
  currentBox := fun state _ => state.2
  copyLiteral := Callback.ofFunction fun state _ => .returned false state
  formatLiteral := Callback.ofFunction fun state _ => .returned true state
  newBox := Callback.ofFunction fun state payload => .returned () (state.1, some payload)
  writeBox := fun state _ payload => state.2.map fun _ => (state.1, some payload)
  dropString := Callback.ofFunction fun state _ => .returned () state
  freeBox := Callback.ofFunction fun state _ => .returned () (state.1, none)

def types : AnchorConstructOwned.Types where
  Aux := Heap
  Payload := Unit
  Unwind := String
  Terminal := String
  StringResource := Bool
  BoxResource := Unit
  errors := errors
  discriminator := []
  ownerAt := fun _ _ => .zero
  owner := Callback.ofFunction fun state _ => .returned (.ofNat 1) (state.1, none)
  checkOwner := Callback.ofFunction fun state _ => .returned (.ok ()) state
  deserialize := Callback.ofFunction fun state _ => .returned ⟨.ok (), []⟩ state

def before : State := (AccountInfo.sampleState, none)
def payload : AnchorErrorOwned.Payload Bool := AnchorConstructOwned.ownerErrorPayload types false
  true
def afterBuild : State := (before.1, some payload)

theorem mismatch : (_root_.Solanalib.Runtime.Pubkey.zero : _root_.Solanalib.Runtime.Pubkey) ≠
  .ofNat 1 := by decide

theorem actual_initialized_allocation :
    AnchorConstructOwned.code types .ownedByWrongProgram before () (.returned ⟨()⟩ afterBuild) ∧
    AnchorErrorOwned.Ready errors afterBuild ⟨()⟩ := by
  refine ⟨AnchorConstructOwned.code_from_allocations rfl rfl rfl, payload, rfl, ?_, ?_⟩
  · decide
  · intro resource _
    exact ⟨if resource then "message" else "name", rfl⟩

/-- The real return of the second Owner destroys only the current error Box. -/
theorem actual_erasing_return : types.owner afterBuild () (.returned (.ofNat 1) before) := rfl

theorem erasing_return_not_ready : ¬ AnchorConstructOwned.OwnerCheckReady types before
  AccountInfo.sampleArgs := by
  intro ready
  have admitted := ready (.ofNat 1) before rfl mismatch false before rfl true before rfl ()
    afterBuild rfl
  have impossible := (admitted.2 _ actual_erasing_return).1
  change (none : Option (AnchorErrorOwned.Payload Bool)) = some payload at impossible
  cases impossible

theorem registered_loader_rejects_erasing_return :
    ¬ (Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_contract.contract
      types).requires
      before AccountInfo.sampleArgs := by
  intro ready
  exact erasing_return_not_ready ready.1

theorem raw_with_pubkeys_empty (left right : _root_.Solanalib.Runtime.Pubkey)
    (outcome : Outcome State (AnchorErrorOwned.Error Unit) Empty String) :
    ¬ AnchorErrorOwned.withPubkeys errors before (⟨()⟩, left, right) outcome := by
  rintro ⟨_, present, _⟩
  cases present

theorem raw_owner_check_empty
    (outcome : Outcome State (Except (AnchorConstructOwned.Error types) Unit)
      (AnchorAccount.ConstructorUnwind String) (AnchorAccount.ConstructorTerminal String)) :
    ¬ AnchorConstructOwned.ownerCheck types before AccountInfo.sampleArgs outcome := by
  simp [AnchorConstructOwned.ownerCheck, AnchorConstructOwned.code,
    AnchorConstructOwned.dependency, AnchorAccount.widenCallback, AccountInfoRc.lift,
    Callback.bind, Callback.map, Callback.ofFunction, AnchorAccount.widen,
    AccountInfoRc.liftOutcome, AnchorErrorOwned.buildCode, AnchorErrorOwned.fromAnchor,
    AnchorErrorOwned.withPubkeys, Owned.protect, types, errors, before, mismatch]

def unwindTypes : AnchorConstructOwned.Types :=
  { types with owner := Callback.ofFunction fun state _ =>
      if state.2.isSome then .unwound "erased error" (state.1, none)
      else .returned (.ofNat 1) (state.1, none) }

/-- The unwinding variant has the same valid allocation prefix and a real
second callback exit. Its destructor cannot read the erased current payload. -/
theorem actual_erasing_unwind : unwindTypes.owner afterBuild () (.unwound "erased error" before) :=
  rfl

theorem erasing_unwind_not_ready :
    ¬ AnchorConstructOwned.OwnerCheckReady unwindTypes before AccountInfo.sampleArgs := by
  intro ready
  have admitted := ready (.ofNat 1) before rfl mismatch false before rfl true before rfl ()
    afterBuild rfl
  have impossible := admitted.2 _ actual_erasing_unwind
  change (none : Option (AnchorErrorOwned.Payload Bool)) = some payload at impossible
  cases impossible

theorem registered_loader_rejects_erasing_unwind :
    ¬ (Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_contract.contract
      unwindTypes).requires
      before AccountInfo.sampleArgs := by
  intro ready
  exact erasing_unwind_not_ready ready.1

theorem raw_drop_error_empty (outcome : Outcome State Unit Empty String) :
    ¬ AnchorErrorOwned.dropError errors ⟨()⟩ before outcome := by
  rintro ⟨_, present, _⟩
  cases present

def uninitializedTypes : AnchorConstructOwned.Types :=
  { types with
    errors := { errors with newBox := Callback.ofFunction fun state _ => .returned () state } }

/-- A primitive Box return is checked before the diagnostic callback, even
when that return never initialized the supplied payload. -/
theorem registered_loader_rejects_uninitialized_box :
    uninitializedTypes.errors.newBox before payload (.returned () before) ∧
    ¬ (Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_contract.contract
      uninitializedTypes).requires before AccountInfo.sampleArgs := by
  refine ⟨rfl, ?_⟩
  intro ready
  have impossible := (ready.1 (.ofNat 1) before rfl mismatch false before rfl true before rfl ()
    before rfl).1
  cases impossible

end BoxLoss

end SolanalibTest.Specs.AnchorLang.OwnedErrors
