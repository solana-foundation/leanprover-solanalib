/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountView
public import Solanalib.Specs.Core.Callback
public import Solanalib.Specs.Core.CpiRequest

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.CpiRequest.Checked

universe u v w x y

/-- The three source-local checked-helper errors use the canonical SDK names. -/
abbrev Error := Solanalib.Runtime.InstrError

/-- The four contiguous flag bytes copied by the v2 CPI initializer. They are
source bytes, not Boolean-normalized observations. -/
structure RawHeader where
  /-- Source signer flag byte, including noncanonical nonzero values. -/
  isSigner : UInt8
  /-- Source writable flag byte, including noncanonical nonzero values. -/
  isWritable : UInt8
  /-- Source executable flag byte. -/
  executable : UInt8
  /-- The fourth byte copied with the flags, without an assumed zero value. -/
  padding : UInt8
  deriving DecidableEq, Repr

/-- One explicit canonical-byte interpretation used by samples. This is not
assumed for an arbitrary source header; v2 callers supply their actual bytes. -/
def normalizedHeader (pool : AccountView.State) (account : AccountView.Handle) : RawHeader :=
  let current := pool.account account
  ⟨if current.metadata.signer then 1 else 0,
    if current.metadata.writable then 1 else 0,
    if current.metadata.executable then 1 else 0, 0⟩

/-- An initialized CPI entry retains the source identity for its address,
owner, lamports and data references. Scalars are copied at initialization.
Pointer layout and legal access remain source bindings. -/
structure Descriptor where
  /-- Identity supplying the retained field references. -/
  account : AccountView.Handle
  /-- Data length copied when the entry is initialized. -/
  dataLen : Nat
  /-- AccountView has no rent epoch; both initializers supply zero. -/
  rentEpoch : Nat
  /-- the normalized Boolean byte of V1, or the exact copied signer byte of v2. -/
  isSigner : UInt8
  /-- the normalized Boolean byte of V1, or the exact copied writable byte of v2. -/
  isWritable : UInt8
  /-- the normalized Boolean byte of V1, or the exact copied executable byte of v2. -/
  executable : UInt8
  /-- V2 copies this source padding byte. V1 does not read that source byte;
  `none` makes no statement about padding of its separately constructed struct. -/
  copiedPadding : Option UInt8
  deriving DecidableEq, Repr

/-- The initializer of V2 copies the raw current four-byte header and current length
from the account selected by its own final AsRef. It retains that same account
for all pointer-valued fields and does not normalize its copied flag bytes. -/
def captureV2 (pool : AccountView.State) (rawHeader : AccountView.Handle → RawHeader)
    (account : AccountView.Handle) : Descriptor :=
  let current := pool.account account
  let header := rawHeader account
  ⟨account, current.dataLen, 0, header.isSigner, header.isWritable,
    header.executable, some header.padding⟩

/-- Only the unchecked invocation remains opaque. Its source signature returns
unit, so an ordinary completion cannot supply an SDK `Result::Err`. Unwind and
terminal exits, when admitted by the selected dependency interpretation, retain
their actual effects. No runtime implementation or success guarantee is added. -/
abbrev Syscall (State : Type u) (Unwind : Type v) (Terminal : Type w) :=
  Callback.Run State (Request Descriptor) Unit Unwind Terminal

/-- One actual generic `A::as_ref` call. The v2 wrapper calls it separately for
address comparison, writable borrow checking and entry initialization. -/
abbrev AsRef (State : Type u) (Account : Type v) (Unwind : Type w) (Terminal : Type x) :=
  Callback.Run State Account AccountView.Handle Unwind Terminal

/-- The standard borrowed-AccountView instance returns the original identity
without changing the state. Its Rust interpretation is a separate binding. -/
def identityAsRef {State : Type u} {Unwind : Type v} {Terminal : Type w} :
    AsRef State AccountView.Handle Unwind Terminal :=
  fun before account outcome => outcome = .returned account before

/-- Initialization uses a fresh actual `as_ref` result and its returned state;
it does not substitute the account used by an earlier validation call. -/
def initializeV2 {State : Type u} {Account : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (pool : State → AccountView.State) (rawHeader : State → AccountView.Handle → RawHeader)
    (asRef : AsRef State Account Unwind Terminal) :
    Callback.Run State Account (Except Error Descriptor) Unwind Terminal :=
  Callback.bind asRef fun account state outcome =>
    outcome = .returned (.ok (captureV2 (pool state) (rawHeader state) account)) state

/-- V2 checks the current address after its first callback. Only writable
metadata invokes the second callback and `check_borrow_mut`; every account
then invokes `as_ref` again for initialization. Every callback exit is kept. -/
def checkV2 {State : Type u} {Account : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (pool : State → AccountView.State) (rawHeader : State → AccountView.Handle → RawHeader)
    (asRef : AsRef State Account Unwind Terminal)
    (item : Solanalib.Runtime.CpiMeta) :
    Callback.Run State Account (Except Error Descriptor) Unwind Terminal :=
  fun before source => Callback.bind asRef (fun account state outcome =>
    if ((pool state).account account).metadata.address ≠ item.key then
      outcome = .returned (.error .InvalidArgument) state
    else if item.writableByte != 0 then
      Callback.bind asRef (fun borrowedAccount afterBorrow result =>
        if AccountView.isBorrowed (pool afterBorrow) borrowedAccount then
          result = .returned (.error .AccountBorrowFailed) afterBorrow
        else initializeV2 pool rawHeader asRef afterBorrow source result) state source outcome
    else initializeV2 pool rawHeader asRef state source outcome) before source

/-- Source-ordered v2 traversal. A descriptor is captured before later
callbacks run, and each callback receives the real state of the preceding callback.
No callback is run for an unused trailing source account. -/
def prepareV2 {State : Type u} {Account : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (pool : State → AccountView.State) (rawHeader : State → AccountView.Handle → RawHeader)
    (asRef : AsRef State Account Unwind Terminal) :
    List Solanalib.Runtime.CpiMeta → List Account →
      State → Outcome State (Except Error (List Descriptor)) Unwind Terminal → Prop
  | [], _, before, outcome => outcome = .returned (.ok []) before
  | _ :: _, [], before, outcome => outcome = .returned (.error .NotEnoughAccountKeys) before
  | item :: metas, account :: accounts, before, outcome =>
    Callback.bind (checkV2 pool rawHeader asRef item) (fun checked state result =>
      match checked with
      | .error error => result = .returned (.error error) state
      | .ok descriptor =>
        Callback.map (Except.map (descriptor :: ·))
          (fun next (_ : Unit) => prepareV2 pool rawHeader asRef metas accounts next)
          state () result) before account outcome

/-- Forward the exact prepared prefix and signer tree. The unchecked unit
return becomes `Ok(())`; its actual state, unwind and terminal exits survive. -/
def invokePrepared {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (invoke : Syscall State Unwind Terminal) (instruction : Solanalib.Runtime.CpiInstruction)
    (signers : List (List Solanalib.Runtime.Bytes)) (accounts : List Descriptor) :
    State → Outcome State (Except Error Unit) Unwind Terminal → Prop :=
  fun before => Callback.map (fun (_ : Unit) => (Except.ok () : Except Error Unit))
    invoke before ⟨instruction, accounts, signers⟩

/-- The common v2 inner wrapper checks the whole input count before any
`as_ref`, then sequences every actual validation/initialization callback. -/
def innerV2 {State : Type u} {Account : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (pool : State → AccountView.State) (rawHeader : State → AccountView.Handle → RawHeader)
    (asRef : AsRef State Account Unwind Terminal)
    (invoke : Syscall State Unwind Terminal)
    (before : State) (request : Request Account) :
    Outcome State (Except Error Unit) Unwind Terminal → Prop :=
  if request.accounts.length < request.instruction.metas.length then
    fun outcome => outcome = .returned (.error .NotEnoughAccountKeys) before
  else Callback.bind
    (fun state (_ : Unit) => prepareV2 pool rawHeader asRef request.instruction.metas
      request.accounts state)
    (fun prepared state outcome => match prepared with
      | .error error => outcome = .returned (.error error) state
      | .ok accounts => invokePrepared invoke request.instruction request.signers accounts state
        outcome)
    before ()

/-- The fixed-array helpers use the v2 borrowed-AccountView instance. This is
the same checked path as generic v2, with pure identity conversion; it does not
replace the wrapper with an arbitrary result-returning provider. -/
def directV2 {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (pool : State → AccountView.State) (rawHeader : State → AccountView.Handle → RawHeader)
    (invoke : Syscall State Unwind Terminal)
    (before : State) (request : Request AccountView.Handle) :
    Outcome State (Except Error Unit) Unwind Terminal → Prop :=
  innerV2 pool rawHeader identityAsRef invoke before request


end Solanalib.Specs.Core.CpiRequest.Checked
