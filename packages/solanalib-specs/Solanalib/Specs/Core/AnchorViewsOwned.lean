/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorViews
public import Solanalib.Specs.Core.AnchorViewsAssignment
public import Solanalib.Specs.Core.AccountInfoRc
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorViews

/-- Only the owned-AccountInfo profile has Rc operations. Borrowed wrappers
do not require an irrelevant clone/drop assumption on those cells. -/
def InfoDeps (storage : InfoStorage) (Aux Terminal : Type) : Type :=
  match storage with
  | .owned => AccountInfoRc.Ops Aux Terminal
  | .borrowed => Unit

/-- Clone the stored AccountInfo only when it is an owned field. Cloning a
shared reference neither clones the two Rc values nor calls a payload trait. -/
def cloneInfo (storage : InfoStorage) {Aux Unwind Terminal : Type}
    (deps : InfoDeps storage Aux Terminal) :
    Callback.Run Aux AccountInfo.Value AccountInfo.Value Unwind Terminal :=
  match storage with
  | .owned => AccountInfoRc.lift (AccountInfoRc.cloneCall deps)
  | .borrowed => Callback.ofFunction fun before info => .returned info before

/-- Dropping a stored reference is inert. An owned AccountInfo drops its two
Rc owners in declaration order through the existing dependency family. -/
def dropInfo (storage : InfoStorage) {Aux Unwind Terminal : Type}
    (deps : InfoDeps storage Aux Terminal) :
    Callback.Run Aux AccountInfo.Value Unit Unwind Terminal :=
  match storage with
  | .owned => AccountInfoRc.lift (AccountInfoRc.dropCall deps)
  | .borrowed => Callback.ofFunction fun before _ => .returned () before

/-- Payload clone is the actual generic T::clone call. Its results may differ
from the source payload and its interior effects and all exits are retained.
The selected wrapper objects are framed; callback-accessible interiors and
other resources belong to the auxiliary state. -/
structure CloneTypes (storage : InfoStorage) where
  Payload : Type
  Aux : Type
  Unwind : Type
  Terminal : Type
  clonePayload : Callback.Run Aux (PayloadArg Payload) Payload Unwind Terminal
  info : InfoDeps storage Aux Terminal

/-- Find the current cell behind the source reference, including its logical
loan policy. No target width or finite Rust borrow-counter limit is assumed. -/
def currentCell {Payload : Type} (store : Store Payload) (guard : Borrow.Guard) :
    Option (Borrow.Cell (Option (Wrapper Payload))) :=
  (store.resolve guard).bind fun slot => store.lookupCell slot.cell

/-- A returned owned wrapper receives a fresh object identity, retaining its
own decoded field and the supplied info alias. This is logical placement of a
by-value Rust result, not a Box or heap-allocation callback. -/
def place {Payload Aux : Type} (policy : Borrow.Policy) (wrapper : Wrapper Payload)
    (before : World Payload Aux) : Borrow.Handle × World Payload Aux :=
  let result := before.1.insert policy (some wrapper)
  (result.1, result.2, before.2)

/-- Derived Account/InterfaceAccount clone evaluates the decoded field first,
then the owned AccountInfo (0.27) or its shared reference (later versions),
then the copied saved owner. Clone never acquires an account-data borrow. -/
def cloneRun (storage : InfoStorage) (types : CloneTypes storage) :
    Callback.Run (World types.Payload types.Aux) Borrow.Guard Borrow.Handle
      types.Unwind types.Terminal :=
  fun before guard final =>
    match currentCell before.1 guard with
    | none => False
    | some cell => match cell.value with
      | none => False
      | some wrapper =>
        Callback.bind (Owned.Focus.snd.lift types.clonePayload)
          (fun payload after =>
            Callback.bind (Owned.Focus.snd.lift (cloneInfo storage types.info))
              (fun info finished result =>
                let placed := place cell.policy
                  { wrapper with account := ⟨payload, info⟩ } finished
                result = .returned placed.1 placed.2)
              after wrapper.account.info)
          before ⟨⟨guard, false⟩, (payloadLocation before.1 ⟨guard, false⟩).getD ⟨0⟩,
            wrapper.account.value⟩ final

/-- Info-only wrapper clones have no T::clone callback: the type of Program is a
PhantomData, and Signer/SystemAccount/UncheckedAccount contain only the info.
The payload parameter is absent because these wrappers own no decoded value. -/
structure InfoCloneTypes (storage : InfoStorage) where
  Aux : Type
  Terminal : Type
  info : InfoDeps storage Aux Terminal

/-- The same ownership scheduling for a wrapper with no decoded payload. -/
def infoCloneRun (storage : InfoStorage) (types : InfoCloneTypes storage) :
    Callback.Run (World Unit types.Aux) Borrow.Guard Borrow.Handle Empty types.Terminal :=
  fun before guard final =>
    match currentCell before.1 guard with
    | none => False
    | some cell => match cell.value with
      | none => False
      | some wrapper =>
        Callback.bind (Owned.Focus.snd.lift (cloneInfo storage types.info))
          (fun info after result =>
            let placed := place cell.policy
              { wrapper with account := ⟨(), info⟩ } after
            result = .returned placed.1 placed.2)
          before wrapper.account.info final

/-- A by-value receiver must be a current owner with no outstanding source
loan. This admission guard has no source error return: the move rules of Rust must
establish it before calling into_inner. -/
def Movable {Payload : Type} (store : Store Payload) (handle : Borrow.Handle) : Prop :=
  (∃ cell wrapper, store.lookupCell handle = some cell ∧ cell.value = some wrapper) ∧
    store.lease handle = .free

/-- Consuming a wrapper preserves its table identity as a permanent tombstone. -/
def retire {Payload Aux : Type} (before : World Payload Aux) (handle : Borrow.Handle) :
    World Payload Aux := ((Borrow.replaceCell before.1 handle none).2, before.2)

structure MoveTypes (storage : InfoStorage) where
  Payload : Type
  Aux : Type
  Terminal : Type
  info : InfoDeps storage Aux Terminal

/-- into_inner moves the exact payload owner out and retires the wrapper.
The 0.27 owned info is dropped after the move; later references have no Rc
effects. No payload clone, deserialize, serialize or drop callback is called. -/
def intoInnerRun (storage : InfoStorage) (types : MoveTypes storage) :
    Callback.Run (World types.Payload types.Aux) Borrow.Handle types.Payload Empty types.Terminal :=
  fun before handle final =>
    match before.1.lookupCell handle with
    | none => False
    | some cell => match cell.value with
      | none => False
      | some wrapper =>
        before.1.lease handle = .free ∧
          Callback.map (fun _ => wrapper.account.value)
            (Owned.Focus.snd.lift (dropInfo storage types.info))
            (retire before handle) wrapper.account.info final

structure SetTypes where
  Payload : Type
  Aux : Type
  Unwind : Type
  Terminal : Type
  dropPayload : Callback.Run Aux (PayloadArg Payload) Unit Unwind Terminal

/-- The selected old payload is dropped at its source identity, with callback
effects in Aux. The new owner is then installed on return and unwind, retaining
the receiver, its loan, its AccountInfo reference and its saved owner. -/
def setInnerRun (types : SetTypes) :
    Callback.Run (World types.Payload types.Aux) (Borrow.Guard × types.Payload) Unit
      types.Unwind types.Terminal :=
  fun before args final =>
    match current before.1 args.1 with
    | none => False
    | some wrapper => ∃ dropped,
      (Owned.Focus.snd.lift types.dropPayload) before
        ⟨⟨args.1, true⟩, (payloadLocation before.1 ⟨args.1, true⟩).getD ⟨0⟩,
          wrapper.account.value⟩ dropped ∧
        AnchorViewsAssignment.replaceAfter
          (fun state value => ((writePayload state.1 ⟨args.1, true⟩ value).2, state.2))
          args.2 dropped = final

/-- The debug branch has an actual logging dependency followed by an actual
panic. Both use the current auxiliary state and can terminate or unwind. -/
structure MutableTypes where
  Payload : Type
  Aux : Type
  Unwind : Type
  Terminal : Type
  debug : Bool
  log : Callback.Run Aux String Unit Unwind Terminal
  panic : Callback.Run Aux Unit Empty Unwind Terminal

/-- Account and InterfaceAccount share this exact debug check. No writable
check is performed with anchor-debug disabled, and Sysvar uses a different
infallible reference projection. The panic branch returns no reference. -/
def mutableRun (types : MutableTypes) :
    Callback.Run (World types.Payload types.Aux) Borrow.Guard PayloadRef
      types.Unwind types.Terminal :=
  fun before guard final =>
    match current before.1 guard with
    | none => False
    | some wrapper =>
      if types.debug && !wrapper.account.info.isWritable then
        Callback.bind (Owned.Focus.snd.lift types.log)
          (fun _ after => Callback.map (fun impossible : Empty => nomatch impossible)
            (Owned.Focus.snd.lift types.panic) after ())
          before "The given Account is not mutable" final
      else final = .returned ⟨guard, true⟩ before

/-- Sysvar::clone calls from_account_info anew; it does not clone its cached decoded value. Error is
the complete owned ProgramError representation of the selected dependency (including old
BorshIoError strings). The unwrap dependency is the whole consuming Err branch of
Result::unwrap: it includes Debug formatting, panic and destruction of that error owner, with
their actual state effects. -/
structure SysvarCloneTypes (storage : InfoStorage) where
  Payload : Type
  Error : Type
  Aux : Type
  Unwind : Type
  Terminal : Type
  info : InfoDeps storage Aux Terminal
  fromInfo : Callback.Run Aux InfoArg (Except Error Payload) Unwind Terminal
  unwrap : Callback.Run Aux Error Empty Unwind Terminal

/-- The already copied/cloned info field is cleaned on decoding/unwrap unwind.
The owner is transferred only on normal construction. Abort skips cleanup. -/
def sysvarCloneRun (storage : InfoStorage) (types : SysvarCloneTypes storage) :
    Callback.Run (World types.Payload types.Aux) Borrow.Guard Borrow.Handle
      types.Unwind types.Terminal :=
  fun before guard final =>
    match currentCell before.1 guard with
    | none => False
    | some cell => match cell.value with
      | none => False
      | some wrapper =>
        Callback.bind (Owned.Focus.snd.lift (cloneInfo storage types.info))
          (fun info after =>
            let decoded : Callback.Run types.Aux InfoArg types.Payload
                types.Unwind types.Terminal :=
              Callback.bind types.fromInfo fun result state =>
                match result with
                | .ok value => fun outcome => outcome = .returned value state
                | .error error => Callback.map (fun impossible : Empty => nomatch impossible)
                    types.unwrap state error
            let guardedDecode := Owned.protect (fun _ _ _ _ => False)
              [fun state outcome => dropInfo storage types.info state info outcome] decoded
            Callback.bind (Owned.Focus.snd.lift guardedDecode)
              (fun value finished result =>
                let placed := place cell.policy
                  { wrapper with account := ⟨value, info⟩ } finished
                result = .returned placed.1 placed.2)
              after ⟨(infoReference storage before guard).1, wrapper.account.info⟩)
          before wrapper.account.info final

end Solanalib.Specs.Core.AnchorViews
