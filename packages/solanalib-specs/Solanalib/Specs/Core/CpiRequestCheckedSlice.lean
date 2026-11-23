/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.CpiRequestChecked
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.CpiRequest.Checked

universe u v w x y

/-- V1 constructs Boolean fields through the Boolean getters of AccountView. Their
representation bytes are normalized to 0 or 1; no raw padding byte is copied. -/
def capture (pool : AccountView.State) (account : AccountView.Handle) : Descriptor :=
  let current := pool.account account
  let flags := normalizedHeader pool account
  ⟨account, current.dataLen, 0, flags.isSigner, flags.isWritable, flags.executable, none⟩

/-- Local check order for InstructionView 1.0.0: address first, then any borrow
for writable metadata or an exclusive borrow for read-only metadata. The
operation neither acquires nor releases an account-data guard. -/
def checkV1 (pool : AccountView.State) (item : Solanalib.Runtime.CpiMeta)
    (account : AccountView.Handle) : Except Error Descriptor :=
  if (pool.account account).metadata.address ≠ item.key then .error .InvalidArgument
  else if (if item.writableByte != 0 then AccountView.isBorrowed pool account
      else AccountView.isBorrowedMut pool account) then .error .AccountBorrowFailed
  else .ok (capture pool account)

/-- The v1 positional traversal preserves duplicates and stops at the first
error. Extra supplied accounts are not visited or included in the CPI array. -/
def prepareV1 (pool : AccountView.State) :
    List Solanalib.Runtime.CpiMeta → List AccountView.Handle → Except Error (List Descriptor)
  | [], _ => .ok []
  | _ :: _, [] => .error .NotEnoughAccountKeys
  | item :: metas, account :: accounts => do
    let descriptor ← checkV1 pool item account
    let rest ← prepareV1 pool metas accounts
    pure (descriptor :: rest)

/-- The common v1 inner wrapper checks the whole input count before visiting
any account. Validation failures are ordinary errors at the state of this check. -/
def innerV1 {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (pool : State → AccountView.State) (invoke : Syscall State Unwind Terminal)
    (before : State) (request : Request AccountView.Handle) :
    Outcome State (Except Error Unit) Unwind Terminal → Prop :=
  if request.accounts.length < request.instruction.metas.length then
    fun outcome => outcome = .returned (.error .NotEnoughAccountKeys) before
  else match prepareV1 (pool before) request.instruction.metas request.accounts with
    | .error error => fun outcome => outcome = .returned (.error error) before
    | .ok accounts => invokePrepared invoke request.instruction request.signers accounts before

/-- The v1 slice wrapper owns a temporary uninitialized boxed CPI array.
Allocation is before the supplied-account count check. The drop of the retained token consults the
actual eventual state. These primitive dependency relations
do not claim a standard-library implementation or impose an allocator strategy. -/
structure Storage (State : Type u) (Resource : Type v)
    (Unwind : Type w) (Terminal : Type x) where
  /-- Allocate the exact requested descriptor capacity, including size zero. -/
  allocate : Callback.Run State Nat Resource Unwind Terminal
  /-- Drop the boxed storage; initialized descriptors have no element destructor. -/
  drop : Callback.Run State Resource Unit Unwind Terminal
  /-- Explicit terminal policy if storage destruction itself unwinds during unwind. -/
  doubleUnwind : Owned.DoubleUnwind State Unwind Terminal

/-- V1 dynamic wrapper: reject more than 128 instruction accounts before
allocation; otherwise retain allocation effects, run the checked body, and
drop the actual owned box on every surviving return/unwind. Terminal exits
stop without cleanup. No failure is relabeled as an SDK allocation error. -/
def sliceV1 {State : Type u} {Resource : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (pool : State → AccountView.State) (storage : Storage State Resource Unwind Terminal)
    (invoke : Syscall State Unwind Terminal)
    (before : State) (request : Request AccountView.Handle) :
    Outcome State (Except Error Unit) Unwind Terminal → Prop :=
  if 128 < request.instruction.metas.length then
    fun outcome => outcome = .returned (.error .InvalidArgument) before
  else Callback.bind storage.allocate (fun resource state outcome =>
    Owned.scope storage.doubleUnwind [fun current => storage.drop current resource]
      (fun current (_ : Unit) => innerV1 pool invoke current request) state () outcome)
    before request.instruction.metas.length

end Solanalib.Specs.Core.CpiRequest.Checked
