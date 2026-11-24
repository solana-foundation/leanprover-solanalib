/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorViewsContracts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorViews.Sample

/-- A shared AccountInfo alias and a separately owned decoded payload. -/
def wrapper : Wrapper Nat :=
  ⟨⟨7, { AccountInfo.sampleInfo with isWritable := true }⟩, 19, some .zero⟩

def infoWrapper : Wrapper Unit :=
  ⟨⟨(), wrapper.account.info⟩, 19, none⟩

/-- The source reference loan is distinct from the RefCell loans of the account. -/
def guard : Borrow.Guard := ⟨0, 0⟩
def slot : Borrow.Slot Unit := ⟨⟨0⟩, .exclusive, 0, ()⟩
def policy : Borrow.Policy := ⟨100⟩
def store : Store Nat := ⟨[⟨some wrapper, policy⟩], [some slot]⟩
def infoStore : Store Unit := ⟨[⟨some infoWrapper, policy⟩], [some slot]⟩
def before : World Nat (List String) := (store, [])
def infoBefore : World Unit (List String) := (infoStore, [])
def moveBefore : World Nat (List String) := (⟨store.cells, []⟩, [])

theorem readable : Readable store guard := ⟨wrapper, rfl⟩
theorem infoReadable : Readable infoStore guard := ⟨infoWrapper, rfl⟩
theorem writable : Writable store guard := ⟨readable, slot, rfl, rfl⟩
theorem movable : Movable moveBefore.1 ⟨0⟩ := ⟨⟨⟨some wrapper, policy⟩, wrapper, rfl, rfl⟩, rfl⟩

def projection : ProjectionTypes := ⟨Nat, List String⟩

theorem shared_execution : FamilyHasExecution sharedFamily sharedReference projection :=
  ⟨before, guard, .returned (PayloadRef.mk guard false) before, readable, rfl⟩

theorem sysvarMutable_execution :
    FamilyHasExecution sysvarMutableFamily sysvarMutableReference projection :=
  ⟨before, guard, .returned (PayloadRef.mk guard true) before, writable, rfl⟩

theorem info_execution (storage : InfoStorage) :
    FamilyHasExecution (infoFamily storage) (infoRun storage) projection :=
  ⟨before, guard, .returned (infoReference storage before guard).1 before, readable, rfl⟩

theorem key_execution : FamilyHasExecution keyFamily keyRun projection :=
  ⟨before, guard, .returned wrapper.account.info.key before, readable, rfl⟩

def pubkeyTypes : Type := Unit

theorem pubkey_execution : FamilyHasExecution pubkeyFamily pubkeyRun pubkeyTypes :=
  ⟨(), Solanalib.Runtime.Pubkey.zero, .returned Solanalib.Runtime.Pubkey.zero (), trivial, rfl⟩

/-- The witness records each Rc field operation at its actual call site. -/
def rc : AccountInfoRc.Ops (List String) String where
  cloneRc := Callback.ofFunction fun state args =>
    .returned () (state ++ [match args.1 with
      | .lamports => "clone_lamports"
      | .data => "clone_data"])
  dropRc := Callback.ofFunction fun state args =>
    .returned () (state ++ [match args.1 with
      | .lamports => "drop_lamports"
      | .data => "drop_data"])

def infoDeps (storage : InfoStorage) : InfoDeps storage (List String) String :=
  match storage with | .owned => rc | .borrowed => ()

def cloneTypes (storage : InfoStorage) : CloneTypes storage where
  Payload := Nat
  Aux := List String
  Unwind := String
  Terminal := String
  clonePayload := Callback.ofFunction fun state arg => .returned (arg.value + 1) (state ++
    ["clone"])
  info := infoDeps storage

def cloneTrace : InfoStorage → List String
  | .owned => ["clone", "clone_lamports", "clone_data"]
  | .borrowed => ["clone"]

def cloneAfter (storage : InfoStorage) : World Nat (List String) :=
  (place policy (wrapper.withPayload 8) (store, cloneTrace storage)).2

theorem clone_run (storage : InfoStorage) :
    cloneRun storage (cloneTypes storage) before guard (.returned ⟨1⟩ (cloneAfter storage)) := by
  cases storage <;>
    simp [cloneRun, currentCell, before, store, slot, guard,
      Borrow.State.resolve, Borrow.State.lookupSlot, Borrow.State.lookupCell,
      Borrow.State.insert,
      cloneTypes, Callback.bind, Callback.ofFunction, Callback.map,
      Owned.Focus.lift, Owned.Focus.snd, Owned.Focus.liftOutcome,
      cloneInfo, infoDeps, AccountInfoRc.lift, AccountInfoRc.liftOutcome,
      AccountInfoRc.cloneCall, rc, cloneAfter, cloneTrace, place,
      wrapper, Wrapper.withPayload, AccountInfo.clone] <;> rfl

theorem clone_execution (storage : InfoStorage) :
    FamilyHasExecution (cloneFamily storage) (cloneReference storage) (cloneTypes storage) :=
  ⟨before, guard, .returned (Borrow.Handle.mk 1) (cloneAfter storage), readable, clone_run storage⟩

def infoCloneTypes (storage : InfoStorage) : InfoCloneTypes storage :=
  ⟨List String, String, infoDeps storage⟩

def infoCloneTrace : InfoStorage → List String
  | .owned => ["clone_lamports", "clone_data"]
  | .borrowed => []

def infoCloneAfter (storage : InfoStorage) : World Unit (List String) :=
  (place policy infoWrapper (infoStore, infoCloneTrace storage)).2

theorem infoClone_run (storage : InfoStorage) :
    infoCloneRun storage (infoCloneTypes storage) infoBefore guard
      (.returned ⟨1⟩ (infoCloneAfter storage)) := by
  cases storage <;>
    simp [infoCloneRun, currentCell, infoBefore, infoStore, slot, guard,
      Borrow.State.resolve, Borrow.State.lookupSlot, Borrow.State.lookupCell,
      Borrow.State.insert,
      infoCloneTypes, Callback.bind, Callback.ofFunction, Callback.map,
      Owned.Focus.lift, Owned.Focus.snd, Owned.Focus.liftOutcome,
      cloneInfo, infoDeps, AccountInfoRc.lift, AccountInfoRc.liftOutcome,
      AccountInfoRc.cloneCall, rc, infoCloneAfter, infoCloneTrace, place,
      infoWrapper, AccountInfo.clone] <;> rfl

theorem infoClone_execution (storage : InfoStorage) :
    FamilyHasExecution (infoCloneFamily storage) (infoCloneReference storage) (infoCloneTypes
      storage) :=
  ⟨infoBefore, guard, .returned (Borrow.Handle.mk 1) (infoCloneAfter storage),
    infoReadable, infoClone_run storage⟩

def moveTypes (storage : InfoStorage) : MoveTypes storage :=
  ⟨Nat, List String, String, infoDeps storage⟩

def moveTrace : InfoStorage → List String
  | .owned => ["drop_lamports", "drop_data"]
  | .borrowed => []

def moveAfter (storage : InfoStorage) : World Nat (List String) :=
  ((retire moveBefore ⟨0⟩).1, moveTrace storage)

theorem intoInner_run (storage : InfoStorage) :
    intoInnerRun storage (moveTypes storage) moveBefore ⟨0⟩ (.returned (7 : Nat) (moveAfter
      storage)) := by
  cases storage <;>
    simp [intoInnerRun, moveTypes, moveBefore, moveAfter, store,
      Borrow.State.lookupCell, Borrow.State.lease, Borrow.State.exclusiveCount,
      Borrow.State.sharedCount, Borrow.State.count, Callback.map, Callback.bind,
      Callback.ofFunction, Owned.Focus.lift, Owned.Focus.snd, Owned.Focus.liftOutcome,
      dropInfo, infoDeps, AccountInfoRc.lift, AccountInfoRc.liftOutcome,
      AccountInfoRc.dropCall, rc, moveTrace, retire, wrapper] <;> rfl

theorem intoInner_execution (storage : InfoStorage) :
    FamilyHasExecution (intoInnerFamily storage) (intoInnerReference storage) (moveTypes storage) :=
  ⟨moveBefore, Borrow.Handle.mk 0, .returned (7 : Nat) (moveAfter storage), movable, intoInner_run
    storage⟩

def setTypes : SetTypes where
  Payload := Nat
  Aux := List String
  Unwind := String
  Terminal := String
  dropPayload := Callback.ofFunction fun state _ => .returned () (state ++ ["drop"])

def setAfter : World Nat (List String) :=
  ((writePayload store ⟨guard, true⟩ 9).2, ["drop"])

theorem setInner_run : setInnerRun setTypes before (guard, (9 : Nat)) (.returned () setAfter) := by
  exact ⟨.returned () (store, ["drop"]), ⟨.returned () ["drop"], rfl, rfl⟩, rfl⟩

theorem setInner_execution : FamilyHasExecution setInnerFamily setInnerReference setTypes :=
  ⟨before, (guard, (9 : Nat)), .returned () setAfter, writable, setInner_run⟩

def mutableTypes : MutableTypes where
  Payload := Nat
  Aux := List String
  Unwind := String
  Terminal := String
  debug := true
  log := Callback.ofFunction fun state message => .returned () (state ++ [message])
  panic := Callback.ofFunction fun state _ => .unwound "explicit panic" state

theorem mutable_execution : FamilyHasExecution mutableFamily mutableReference mutableTypes :=
  ⟨before, guard, .returned (PayloadRef.mk guard true) before, writable, rfl⟩

def sysvarTypes (storage : InfoStorage) : SysvarCloneTypes storage where
  Payload := Nat
  Error := ProgramError.Value
  Aux := List String
  Unwind := String
  Terminal := String
  info := infoDeps storage
  fromInfo := Callback.ofFunction fun state _ => .returned (.ok 23) (state ++ ["from_info"])
  unwrap := Callback.ofFunction fun state _ => .unwound "unwrap" state

def sysvarTrace : InfoStorage → List String
  | .owned => ["clone_lamports", "clone_data", "from_info"]
  | .borrowed => ["from_info"]

def sysvarAfter (storage : InfoStorage) : World Nat (List String) :=
  (place policy (wrapper.withPayload 23) (store, sysvarTrace storage)).2

theorem sysvarClone_run (storage : InfoStorage) :
    sysvarCloneRun storage (sysvarTypes storage) before guard (.returned ⟨1⟩ (sysvarAfter storage))
      := by
  cases storage <;>
    simp [sysvarCloneRun, currentCell, before, store, slot, guard,
      Borrow.State.resolve, Borrow.State.lookupSlot, Borrow.State.lookupCell,
      Borrow.State.insert,
      sysvarTypes, Callback.bind, Callback.ofFunction, Callback.map,
      Owned.Focus.lift, Owned.Focus.snd, Owned.Focus.liftOutcome,
      cloneInfo, infoDeps, AccountInfoRc.lift, AccountInfoRc.liftOutcome,
      AccountInfoRc.cloneCall, rc, sysvarAfter, sysvarTrace, place,
      wrapper, Wrapper.withPayload, AccountInfo.clone, Owned.protect, Owned.onUnwind] <;> rfl

theorem sysvarClone_execution (storage : InfoStorage) :
    FamilyHasExecution (sysvarCloneFamily storage) (sysvarCloneReference storage) (sysvarTypes
      storage) :=
  ⟨before, guard, .returned (Borrow.Handle.mk 1) (sysvarAfter storage), readable, sysvarClone_run
    storage⟩

end Solanalib.Specs.Core.AnchorViews.Sample
