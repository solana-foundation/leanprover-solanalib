/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.CpiRequestCheckedFamily

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.CpiRequest.Checked

universe u v w

/-- The pure result of the checked path of v2 for the borrowed-AccountView identity
instance. Read-only metadata performs no borrow check in this revision. -/
def checkDirectV2 (pool : AccountView.State) (rawHeader : AccountView.Handle → RawHeader)
    (item : Solanalib.Runtime.CpiMeta)
    (account : AccountView.Handle) : Except Error Descriptor :=
  if (pool.account account).metadata.address ≠ item.key then .error .InvalidArgument
  else if item.writableByte != 0 && AccountView.isBorrowed pool account then
    .error .AccountBorrowFailed
  else .ok (captureV2 pool rawHeader account)

/-- Pure positional preparation for the identity instance. The theorem below
derives this computation from the actual repeated-callback model. -/
def prepareDirectV2 (pool : AccountView.State) (rawHeader : AccountView.Handle → RawHeader) :
    List Solanalib.Runtime.CpiMeta → List AccountView.Handle → Except Error (List Descriptor)
  | [], _ => .ok []
  | _ :: _, [] => .error .NotEnoughAccountKeys
  | item :: items, account :: accounts =>
    match checkDirectV2 pool rawHeader item account with
    | .error error => .error error
    | .ok descriptor => Except.map (descriptor :: ·) (prepareDirectV2 pool rawHeader items accounts)

/-- Identity initialization observes the current pool without changing state. -/
theorem initializeV2_identity {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (pool : State → AccountView.State) (rawHeader : State → AccountView.Handle → RawHeader) (before
      : State) (account : AccountView.Handle)
    (outcome : Outcome State (Except Error Descriptor) Unwind Terminal) :
    initializeV2 pool rawHeader identityAsRef before account outcome ↔
      outcome = .returned (.ok (captureV2 (pool before) (rawHeader before) account)) before := by
  simp [initializeV2, Callback.bind, identityAsRef]

/-- Every repeated identity conversion preserves the same current account;
this reduction assumes no such property for an arbitrary `AsRef` provider. -/
theorem checkV2_identity {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (pool : State → AccountView.State) (rawHeader : State → AccountView.Handle → RawHeader) (item :
      Solanalib.Runtime.CpiMeta)
    (before : State) (account : AccountView.Handle)
    (outcome : Outcome State (Except Error Descriptor) Unwind Terminal) :
    checkV2 pool rawHeader identityAsRef item before account outcome ↔
      outcome = .returned (checkDirectV2 (pool before) (rawHeader before) item account) before := by
  by_cases address : ((pool before).account account).metadata.address = item.key
  · by_cases writable : item.writableByte != 0
    · by_cases borrowed : AccountView.isBorrowed (pool before) account
      · simp [checkV2, Callback.bind, identityAsRef, initializeV2, checkDirectV2,
          address, writable, borrowed]
      · simp [checkV2, Callback.bind, identityAsRef, initializeV2, checkDirectV2,
          address, writable, borrowed]
    · simp [checkV2, Callback.bind, identityAsRef, initializeV2, checkDirectV2,
        address, writable]
  · simp [checkV2, Callback.bind, identityAsRef, checkDirectV2, address]

/-- Full identity traversal is the pure ordered computation, including ignored
trailing accounts, duplicate occurrences and the first failing check. -/
theorem prepareV2_identity {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (pool : State → AccountView.State) (rawHeader : State → AccountView.Handle → RawHeader) (items
      : List Solanalib.Runtime.CpiMeta)
    (accounts : List AccountView.Handle) (before : State)
    (outcome : Outcome State (Except Error (List Descriptor)) Unwind Terminal) :
    prepareV2 pool rawHeader identityAsRef items accounts before outcome ↔
      outcome = .returned (prepareDirectV2 (pool before) (rawHeader before) items accounts) before
        := by
  induction items generalizing accounts before outcome with
  | nil => rfl
  | cons item items induction =>
    cases accounts with
    | nil => rfl
    | cons account accounts =>
      simp only [prepareV2, Callback.bind, checkV2_identity]
      cases checked : checkDirectV2 (pool before) (rawHeader before) item account with
      | error error => simp [checked, prepareDirectV2]
      | ok descriptor =>
        simp [checked, Callback.map, induction, Outcome.map, prepareDirectV2, eq_comm]

/-- The checked helper reduction used by ordinary fixed-reference SDK callers.
It is proved from the generic v2 pipeline, not installed as a new opaque call. -/
theorem directV2_iff {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (pool : State → AccountView.State) (rawHeader : State → AccountView.Handle → RawHeader) (invoke
      : Syscall State Unwind Terminal)
    (before : State) (request : Request AccountView.Handle)
    (outcome : Outcome State (Except Error Unit) Unwind Terminal) :
    directV2 pool rawHeader invoke before request outcome ↔
      if request.accounts.length < request.instruction.metas.length then
        outcome = .returned (.error .NotEnoughAccountKeys) before
      else match prepareDirectV2 (pool before) (rawHeader before) request.instruction.metas
        request.accounts with
        | .error error => outcome = .returned (.error error) before
        | .ok accounts => invokePrepared invoke request.instruction request.signers accounts before
          outcome := by
  simp only [directV2, innerV2]
  split
  · rfl
  · simp only [Callback.bind, prepareV2_identity]
    cases prepareDirectV2 (pool before) (rawHeader before) request.instruction.metas
      request.accounts <;> simp

/-- A successful unchecked invocation produces exactly the ordinary SDK Ok. -/
theorem invokePrepared_returned {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (invoke : Syscall State Unwind Terminal) (instruction : Solanalib.Runtime.CpiInstruction)
    (signers : List (List Solanalib.Runtime.Bytes)) (accounts : List Descriptor) (before after :
      State)
    (executed : invoke before ⟨instruction, accounts, signers⟩ (.returned () after)) :
    invokePrepared invoke instruction signers accounts before (.returned (.ok ()) after) :=
  ⟨.returned () after, executed, rfl⟩

/-- Every unchecked unwind is retained with its actual state. -/
theorem invokePrepared_unwound {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (invoke : Syscall State Unwind Terminal) (instruction : Solanalib.Runtime.CpiInstruction)
    (signers : List (List Solanalib.Runtime.Bytes)) (accounts : List Descriptor) (before after :
      State)
    (reason : Unwind)
    (executed : invoke before ⟨instruction, accounts, signers⟩ (.unwound reason after)) :
    invokePrepared invoke instruction signers accounts before (.unwound reason after) :=
  ⟨.unwound reason after, executed, rfl⟩

/-- Every unchecked terminal exit is retained and cannot trigger later cleanup. -/
theorem invokePrepared_terminated {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (invoke : Syscall State Unwind Terminal) (instruction : Solanalib.Runtime.CpiInstruction)
    (signers : List (List Solanalib.Runtime.Bytes)) (accounts : List Descriptor) (before : State)
    (reason : Terminal)
    (executed : invoke before ⟨instruction, accounts, signers⟩ (.terminated reason)) :
    invokePrepared invoke instruction signers accounts before (.terminated reason) :=
  ⟨.terminated reason, executed, rfl⟩

/-- The unchecked signature cannot inject a new ordinary SDK error after CPI. -/
theorem invokePrepared_no_error {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (invoke : Syscall State Unwind Terminal) (instruction : Solanalib.Runtime.CpiInstruction)
    (signers : List (List Solanalib.Runtime.Bytes)) (accounts : List Descriptor) (before after :
      State)
    (error : Error) :
    ¬ invokePrepared invoke instruction signers accounts before (.returned (.error error) after) :=
      by
  rintro ⟨actual, _, returned⟩
  cases actual <;> simp [Outcome.map] at returned

end Solanalib.Specs.Core.CpiRequest.Checked
