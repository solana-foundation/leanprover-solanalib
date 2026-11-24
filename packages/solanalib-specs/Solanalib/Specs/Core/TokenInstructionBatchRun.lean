/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionBatch
public import Solanalib.Specs.Core.Callback
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Batch

/-- Independent source type parameters for a generic `AsRef<AccountView>`
implementation. Callback effects are represented by the ambient state. -/
structure Types where
  /-- Type of additional callback effects. -/
  Ambient : Type
  /-- Arbitrary Rust MultisigSigner value interpretation. -/
  Signer : Type
  /-- Reasons for an unwind carrying the actual resulting state. -/
  Unwind : Type
  /-- Reasons for an exit that carries no post-state. -/
  Terminal : Type

/-- The source callback can return an account, unwind with effects, or stop.
It has no ordinary `ProgramError` result. -/
abbrev AsRef (types : Types) :=
  Callback.Run (Context types.Ambient) types.Signer AccountView.Handle types.Unwind types.Terminal

/-- Lift only callback-owned state. The exclusive batch-buffer frame and its
committed lengths survive both ordinary returns and unwinding unchanged. -/
def liftContext {Ambient Value Unwind Terminal : Type} (before : State Ambient) :
    Outcome (Context Ambient) Value Unwind Terminal → Outcome (State Ambient) Value Unwind Terminal
  | .returned value context => .returned value { before with context }
  | .unwound reason context => .unwound reason { before with context }
  | .terminated reason => .terminated reason

/-- The same callback relation, with the separate batch buffers of the source framed. -/
def framedAsRef {types : Types} (asRef : AsRef types) :
    Callback.Run (State types.Ambient) types.Signer AccountView.Handle types.Unwind types.Terminal
      :=
  fun before signer outcome =>
    ∃ actual, asRef before.context signer actual ∧ liftContext before actual = outcome

/-- Run each `as_ref` and immediately initialize its entry before the next call.
A second call to this relation is a separate traversal, with separate outcomes. -/
def signerPass {types : Types} (asRef : AsRef types)
    (write : State types.Ambient → Nat → AccountView.Handle → State types.Ambient)
    (before : State types.Ambient) (offset : Nat) (signers : List types.Signer) :
    Outcome (State types.Ambient) Unit types.Unwind types.Terminal → Prop :=
  match signers with
  | [] => fun outcome => outcome = .returned () before
  | signer :: rest =>
    Callback.bind (framedAsRef asRef)
      (fun handle current outcome =>
        signerPass asRef write (write current offset handle) (offset + 1) rest outcome)
      before signer

/-- Capacity is tested before either borrow flag. Only source and destination
are checked; mint, authority and signer-account flags are not checked here. -/
def writeAccounts {types : Types} (asRef : AsRef types) :
    Callback.Run (State types.Ambient) (Transfer types.Signer) (Except Error Nat)
      types.Unwind types.Terminal :=
  fun before args outcome =>
    let expected := 4 + args.multisigSigners.length
    if before.buffers.accounts.length - before.lengths.accounts < expected then
      outcome = .returned (.error .InvalidArgument) before
    else if AccountView.isBorrowed before.context.world args.fromAccount ||
        AccountView.isBorrowed before.context.world args.toAccount then
      outcome = .returned (.error .AccountBorrowFailed) before
    else
      Callback.map (fun _ => Except.ok expected)
        (fun current (_ : Unit) =>
          signerPass asRef writeAccount current (before.lengths.accounts + 4) args.multisigSigners)
        (writeBaseAccounts before args) () outcome

/-- The metadata writer repeats every generic callback. It uses its own slice
capacity and does not repeat the source/destination borrow check. -/
def writeMetas {types : Types} (asRef : AsRef types) :
    Callback.Run (State types.Ambient) (Transfer types.Signer) (Except Error Nat)
      types.Unwind types.Terminal :=
  fun before args outcome =>
    let expected := 4 + args.multisigSigners.length
    if before.buffers.instructionAccounts.length - before.lengths.instructionAccounts < expected
      then
      outcome = .returned (.error .InvalidArgument) before
    else
      Callback.map (fun _ => Except.ok expected)
        (fun current (_ : Unit) =>
          signerPass asRef (fun state offset handle => writeMeta state offset handle true false)
            current (before.lengths.instructionAccounts + 4) args.multisigSigners)
        (writeBaseMetas before args) () outcome

/-- Ordered local preparation: reserve header room, write data, write accounts,
write metadata, then commit lengths and header. Every preceding write or
callback effect survives an error, unwind or terminal exit. -/
def intoBatch {types : Types} (asRef : AsRef types) :
    Callback.Run (State types.Ambient) (Transfer types.Signer) (Except Error Unit)
      types.Unwind types.Terminal :=
  fun before args outcome =>
    if before.buffers.data.length < before.lengths.data + 2 then
      outcome = .returned (.error .InvalidArgument) before
    else
      let (dataResult, afterData) := writeData before args
      match dataResult with
      | .error reason => outcome = .returned (.error reason) afterData
      | .ok dataCount =>
        Callback.bind (writeAccounts asRef)
          (fun accountResult afterAccounts next =>
            match accountResult with
            | .error reason => next = .returned (.error reason) afterAccounts
            | .ok accountCount =>
              Callback.bind (writeMetas asRef)
                (fun metaResult afterMetas last =>
                  match metaResult with
                  | .error reason => last = .returned (.error reason) afterMetas
                  | .ok metaCount => last =
                    .returned (.ok ()) (commit afterMetas dataCount accountCount metaCount))
                afterAccounts args next)
          afterData args outcome

/-- The generic writer receives the original signer slice and its interpretation. -/
structure IntoCall (types : Types) where
  /-- The original account references, integer values and signer slice. -/
  transfer : Transfer types.Signer
  /-- Explicit generic AsRef finite-exit interpretation. -/
  asRef : AsRef types

/-- The body model retains every supplied finite callback outcome. Legal source
references and target arithmetic remain Rust-binding obligations. -/
def intoFamily : Family where
  Index := Types
  State := fun types => State types.Ambient
  Args := IntoCall
  Value := fun _ => Except Error Unit
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun _ => {
    requires := fun _ _ => True
    post := fun before args => intoBatch args.asRef before args.transfer }

/-- The reference is the finite-exit relation, including all permitted callback
outcomes. No determinism or termination of an arbitrary callback is asserted. -/
def intoRun : FamilyRun intoFamily := fun _ before args => intoBatch args.asRef before args.transfer

/-- Reference partial correctness covers all source type parameters. -/
theorem intoReference : FamilyReference intoFamily intoRun := by
  intro _ _ _ _ _ execution
  exact execution

/-- The unchecked source provider returns unit, not `Result`. It may still
unwind or terminate, with exactly its actual effects. -/
structure InvokeCall (types : Types) where
  /-- Exact supplied signer seed tree, including empty values and duplicates. -/
  signers : List (List Bytes)
  /-- Opaque unchecked provider with a unit ordinary return and exact effects. -/
  invoke : Callback.Run (Context types.Ambient) Request
    Unit types.Unwind types.Terminal

/-- Only an ordinary unit return becomes `Ok(())`. No ordinary invocation
`ProgramError` is invented and no provider failure is erased. -/
def invokeSigned {types : Types} (before : State types.Ambient) (args : InvokeCall types)
    (outcome : Outcome (State types.Ambient) (Except Error Unit) types.Unwind types.Terminal) :
      Prop :=
  ∃ sent, request before args.signers = some sent ∧
    ∃ actual, args.invoke before.context sent actual ∧
      Outcome.map (fun _ => Except.ok ()) (liftContext before actual) = outcome

/-- Admission requires the three initialized prefixes used to construct the
request. Rust representation and opaque-provider correspondence remain separate
binding obligations; no missing prefix becomes a synthetic provider outcome. -/
def invokeFamily : Family where
  Index := Types
  State := fun types => State types.Ambient
  Args := InvokeCall
  Value := fun _ => Except Error Unit
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun _ => {
    requires := fun before _ => InvocationReady before
    post := invokeSigned }

/-- The exact request and provider outcome define the reference relation. -/
def invokeRun : FamilyRun invokeFamily := fun _ => invokeSigned

/-- Invocation reference correctness is generic in the provider and ambient state. -/
theorem invokeReference : FamilyReference invokeFamily invokeRun := by
  intro _ _ _ _ _ execution
  exact execution

/-- An empty signer suffix makes no callback. -/
theorem signerPass_nil {types : Types} (asRef : AsRef types)
    (write : State types.Ambient → Nat → AccountView.Handle → State types.Ambient)
    (before : State types.Ambient) (offset : Nat) :
    signerPass asRef write before offset [] (.returned () before) := rfl

/-- One returning callback is followed immediately by its write and the next
callback. The actual returned context is retained. -/
theorem signerPass_return {types : Types} (asRef : AsRef types)
    (write : State types.Ambient → Nat → AccountView.Handle → State types.Ambient)
    (before : State types.Ambient) (offset : Nat) (signer : types.Signer)
    (rest : List types.Signer) (handle : AccountView.Handle) (context : Context types.Ambient)
    (outcome : Outcome (State types.Ambient) Unit types.Unwind types.Terminal)
    (callback : asRef before.context signer (.returned handle context))
    (tail : signerPass asRef write (write { before with context } offset handle)
      (offset + 1) rest outcome) :
    signerPass asRef write before offset (signer :: rest) outcome :=
  ⟨.returned handle { before with context }, ⟨.returned handle context, callback, rfl⟩, tail⟩

/-- An unwinding callback preserves all prior writes and its own actual state;
it does not initialize its entry or call later signers. -/
theorem signerPass_unwind {types : Types} (asRef : AsRef types)
    (write : State types.Ambient → Nat → AccountView.Handle → State types.Ambient)
    (before : State types.Ambient) (offset : Nat) (signer : types.Signer)
    (rest : List types.Signer) (reason : types.Unwind) (context : Context types.Ambient)
    (callback : asRef before.context signer (.unwound reason context)) :
    signerPass asRef write before offset (signer :: rest)
      (.unwound reason { before with context }) :=
  ⟨.unwound reason { before with context }, ⟨.unwound reason context, callback, rfl⟩, rfl⟩

/-- A terminal callback yields no fabricated post-state. -/
theorem signerPass_terminal {types : Types} (asRef : AsRef types)
    (write : State types.Ambient → Nat → AccountView.Handle → State types.Ambient)
    (before : State types.Ambient) (offset : Nat) (signer : types.Signer)
    (rest : List types.Signer) (reason : types.Terminal)
    (callback : asRef before.context signer (.terminated reason)) :
    signerPass asRef write before offset (signer :: rest) (.terminated reason) :=
  ⟨.terminated reason, ⟨.terminated reason, callback, rfl⟩, rfl⟩

/-- Source header-capacity failure takes precedence over all writers and callbacks. -/
theorem intoBatch_header_error {types : Types} (asRef : AsRef types)
    (before : State types.Ambient) (args : Transfer types.Signer)
    (short : before.buffers.data.length < before.lengths.data + 2) :
    intoBatch asRef before args (.returned (.error .InvalidArgument) before) := by
  simp only [intoBatch, short, ↓reduceIte]

/-- Every finite provider outcome survives wrapper composition, with the
original request and actual effects. This does not assume termination. -/
theorem invokeSigned_provider {types : Types} (before : State types.Ambient)
    (args : InvokeCall types) (sent : Request)
    (decoded : request before args.signers = some sent)
    (actual : Outcome (Context types.Ambient) Unit types.Unwind types.Terminal)
    (provider : args.invoke before.context sent actual) :
    invokeSigned before args (Outcome.map (fun _ => Except.ok ()) (liftContext before actual)) :=
  ⟨sent, decoded, actual, provider, rfl⟩

/-- Initialized source admission supplies the request needed to continue with
every actual finite provider outcome. The provider may remain nondeterministic. -/
theorem InvocationReady.progress {types : Types} {before : State types.Ambient}
    (ready : InvocationReady before) (args : InvokeCall types) :
    ∃ sent, request before args.signers = some sent ∧
      ∀ actual, args.invoke before.context sent actual →
        invokeSigned before args (Outcome.map (fun _ => Except.ok ()) (liftContext before actual))
          := by
  obtain ⟨sent, decoded⟩ := request_exists ready args.signers
  exact ⟨sent, decoded, fun actual provider => invokeSigned_provider before args sent decoded
    actual provider⟩

/-- A successful unchecked provider produces only the source `Ok(())`, while
preserving all its effects and the separate buffers of the batch. -/
theorem invokeSigned_return {types : Types} (before : State types.Ambient)
    (args : InvokeCall types) (sent : Request)
    (decoded : request before args.signers = some sent)
    (context : Context types.Ambient)
    (provider : args.invoke before.context sent (.returned () context)) :
    invokeSigned before args (.returned (.ok ()) { before with context }) :=
  invokeSigned_provider before args sent decoded (.returned () context) provider

/-- Missing initialization is outside source admission, not an invented
ordinary error or terminal result from the opaque provider. -/
theorem invokeSigned_no_request {types : Types} (before : State types.Ambient)
    (args : InvokeCall types) (missing : request before args.signers = none)
    (outcome : Outcome (State types.Ambient) (Except Error Unit) types.Unwind types.Terminal) :
    ¬ invokeSigned before args outcome := by
  rintro ⟨sent, decoded, _⟩
  simp [missing] at decoded

/-- Once capacity and the two borrow flags permit the account writer, its
outcomes are exactly those of the first ordered callback pass. -/
theorem writeAccounts_pass {types : Types} (asRef : AsRef types)
    (before : State types.Ambient) (args : Transfer types.Signer)
    (actual : Outcome (State types.Ambient) Unit types.Unwind types.Terminal)
    (capacity : ¬ before.buffers.accounts.length - before.lengths.accounts <
      4 + args.multisigSigners.length)
    (available : (AccountView.isBorrowed before.context.world args.fromAccount ||
      AccountView.isBorrowed before.context.world args.toAccount) = false)
    (pass : signerPass asRef writeAccount (writeBaseAccounts before args)
      (before.lengths.accounts + 4) args.multisigSigners actual) :
    writeAccounts asRef before args
      (Outcome.map (fun _ => Except.ok (4 + args.multisigSigners.length)) actual) := by
  simp only [writeAccounts, capacity, ↓reduceIte, available, Bool.false_eq_true]
  exact ⟨actual, pass, rfl⟩

/-- The second callback pass has its own capacity condition and no new borrow
test; it starts in the actual state left by the first pass. -/
theorem writeMetas_pass {types : Types} (asRef : AsRef types)
    (before : State types.Ambient) (args : Transfer types.Signer)
    (actual : Outcome (State types.Ambient) Unit types.Unwind types.Terminal)
    (capacity : ¬ before.buffers.instructionAccounts.length - before.lengths.instructionAccounts <
      4 + args.multisigSigners.length)
    (pass : signerPass asRef (fun state offset handle => writeMeta state offset handle true false)
      (writeBaseMetas before args) (before.lengths.instructionAccounts + 4)
      args.multisigSigners actual) :
    writeMetas asRef before args
      (Outcome.map (fun _ => Except.ok (4 + args.multisigSigners.length)) actual) := by
  simp only [writeMetas, capacity, ↓reduceIte]
  exact ⟨actual, pass, rfl⟩

/-- A fully returning preparation commits exactly the counts supplied by all
three writers, after their actual effects. -/
theorem intoBatch_success {types : Types} (asRef : AsRef types)
    (before : State types.Ambient) (args : Transfer types.Signer)
    (afterData afterAccounts afterMetas : State types.Ambient)
    (dataCount accountCount metaCount : Nat)
    (header : ¬ before.buffers.data.length < before.lengths.data + 2)
    (data : writeData before args = (.ok dataCount, afterData))
    (accounts : writeAccounts asRef afterData args (.returned (.ok accountCount) afterAccounts))
    (metas : writeMetas asRef afterAccounts args (.returned (.ok metaCount) afterMetas)) :
    intoBatch asRef before args
      (.returned (.ok ()) (commit afterMetas dataCount accountCount metaCount)) := by
  simp only [intoBatch, header, ↓reduceIte, data]
  exact ⟨.returned (.ok accountCount) afterAccounts, accounts,
    .returned (.ok metaCount) afterMetas, metas, rfl⟩

/-- Account-writer errors retain the already written data and the actual state of the account
writer. No metadata writer is run. -/
theorem intoBatch_account_error {types : Types} (asRef : AsRef types)
    (before : State types.Ambient) (args : Transfer types.Signer)
    (afterData afterAccounts : State types.Ambient) (dataCount : Nat) (reason : Error)
    (header : ¬ before.buffers.data.length < before.lengths.data + 2)
    (data : writeData before args = (.ok dataCount, afterData))
    (accounts : writeAccounts asRef afterData args (.returned (.error reason) afterAccounts)) :
    intoBatch asRef before args (.returned (.error reason) afterAccounts) := by
  simp only [intoBatch, header, ↓reduceIte, data]
  exact ⟨.returned (.error reason) afterAccounts, accounts, rfl⟩

/-- Metadata-writer errors retain every data/account write and every effect
from the completed first callback pass. -/
theorem intoBatch_meta_error {types : Types} (asRef : AsRef types)
    (before : State types.Ambient) (args : Transfer types.Signer)
    (afterData afterAccounts afterMetas : State types.Ambient)
    (dataCount accountCount : Nat) (reason : Error)
    (header : ¬ before.buffers.data.length < before.lengths.data + 2)
    (data : writeData before args = (.ok dataCount, afterData))
    (accounts : writeAccounts asRef afterData args (.returned (.ok accountCount) afterAccounts))
    (metas : writeMetas asRef afterAccounts args (.returned (.error reason) afterMetas)) :
    intoBatch asRef before args (.returned (.error reason) afterMetas) := by
  simp only [intoBatch, header, ↓reduceIte, data]
  exact ⟨.returned (.ok accountCount) afterAccounts, accounts,
    .returned (.error reason) afterMetas, metas, rfl⟩

/-- The buffer effects of the source constructor, with its returned Batch descriptor. -/
def newContract : Solanalib.Contracts.Model Buffers Unit (Except Error Lengths) :=
  .returning (fun _ _ => True)
    (fun before _ result after => (result, after) = newBatch before)

/-- Exact total mathematical constructor, preserving the selected buffers. -/
def newReference : Buffers → Unit → Except Error Lengths × Buffers := fun before _ => newBatch
  before

/-- Every mathematical constructor execution satisfies its value/effect contract. -/
theorem newReference_realizes : newContract.RealizedBy newReference := by
  intro _ _ _
  rfl

/-- The specialized TransferChecked constructor stores its inputs and an empty
signer slice; it performs no account or token validation. -/
def transferNewContract : Solanalib.Contracts.Model Unit SingleTransfer (Transfer
  AccountView.Handle) :=
  Instruction.valueContract (fun _ => True) singleTransfer

/-- Exact mathematical single-owner constructor. -/
def transferNewReference : Unit → SingleTransfer → Transfer AccountView.Handle × Unit :=
  Instruction.valueReference singleTransfer

/-- Full constructor value equality, including all account references. -/
theorem transferNewReference_realizes : transferNewContract.RealizedBy transferNewReference :=
  Instruction.valueReference_realizes (fun _ => True) singleTransfer

end Solanalib.Specs.Core.Token.Batch
