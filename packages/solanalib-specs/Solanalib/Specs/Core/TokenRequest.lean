/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstruction
public import Solanalib.Specs.Core.CpiRequestCheckedFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Request

/-- The current account pool, raw header bytes and outcome types are shared with
the checked v2 CPI entry. Legal source handles remain an explicit interpretation obligation. -/
abbrev Types := CpiRequest.Checked.HeaderTypes

/-- Values read by the Pinocchio Token-2022 checked-transfer helper. The supplied
program ID is deliberately arbitrary: this helper performs no program-ID check. -/
structure Transfer where
  /-- The caller-supplied program identity. -/
  programId : Solanalib.Runtime.Pubkey
  /-- The source account identity in the current pool. -/
  source : AccountView.Handle
  /-- The readonly mint account identity. -/
  mint : AccountView.Handle
  /-- The destination account identity in the current pool. -/
  destination : AccountView.Handle
  /-- The readonly signer authority identity in the current pool. -/
  authority : AccountView.Handle
  /-- Mathematical amount; the Rust binding supplies the source u64 bound. -/
  amount : Nat
  /-- Mathematical decimals; the Rust binding supplies the source u8 bound. -/
  decimals : Nat

/-- The metadata order and account-value order are both source/mint/destination/
authority. Keys come from the current entry pool. Signer seeds never add account
metas or change their flags. -/
def transferRequest (pool : AccountView.State) (transfer : Transfer)
    (signers : List (List Bytes)) : CpiRequest.Request AccountView.Handle :=
  CpiRequest.signed (Instruction.transferCheckedInstruction {
    programId := transfer.programId
    source := (pool.account transfer.source).metadata.address
    mint := (pool.account transfer.mint).metadata.address
    destination := (pool.account transfer.destination).metadata.address
    authority := (pool.account transfer.authority).metadata.address
    signers := []
    amount := transfer.amount
    decimals := transfer.decimals })
    [transfer.source, transfer.mint, transfer.destination, transfer.authority]
    signers

/-- The three borrowed account identities used by the close wrapper. -/
structure Close where
  /-- The caller-supplied program identity. -/
  programId : Solanalib.Runtime.Pubkey
  /-- The token account requested closed. -/
  account : AccountView.Handle
  /-- The destination account identity in the current pool. -/
  destination : AccountView.Handle
  /-- The readonly signer authority identity in the current pool. -/
  authority : AccountView.Handle

/-- Current pool keys supply the exact close request: writable account/destination,
readonly signer authority and tag nine. -/
def closeRequest (pool : AccountView.State) (close : Close)
    (signers : List (List Bytes)) : CpiRequest.Request AccountView.Handle :=
  CpiRequest.signed (Instruction.authorityInstruction {
    programId := close.programId
    source := (pool.account close.account).metadata.address
    destination := (pool.account close.destination).metadata.address
    authority := (pool.account close.authority).metadata.address
    signers := [] } Instruction.closeAccountData)
    [close.account, close.destination, close.authority] signers

/-- Four source handles and four metadata entries satisfy the static bound. -/
theorem transferRequest_cardinality (pool : AccountView.State) (transfer : Transfer)
    (signers : List (List Bytes)) :
    (transferRequest pool transfer signers).accounts.length = 4 ∧
    (transferRequest pool transfer signers).instruction.metas.length = 4 ∧
    (transferRequest pool transfer signers).accounts.length ≤ 64 :=
  ⟨rfl, rfl, by change 4 ≤ 64; decide⟩

/-- Three source handles and three metadata entries satisfy the static bound. -/
theorem closeRequest_cardinality (pool : AccountView.State) (close : Close)
    (signers : List (List Bytes)) :
    (closeRequest pool close signers).accounts.length = 3 ∧
    (closeRequest pool close signers).instruction.metas.length = 3 ∧
    (closeRequest pool close signers).accounts.length ≤ 64 :=
  ⟨rfl, rfl, by change 3 ≤ 64; decide⟩

/-- A transfer, ordered signer seeds and the actual opaque invocation relation. -/
structure SignedTransferCall (types : Types) where
  /-- The checked-transfer request fields. -/
  transfer : Transfer
  /-- Ordered nested signer seed groups, preserving duplicates. -/
  signers : List (List Bytes)
  /-- Opaque unit-returning invocation after checked preparation succeeds. -/
  invoke : CpiRequest.Checked.Syscall types.State types.Unwind types.Terminal

/-- A transfer and opaque invocation with an empty signer-seed list. -/
structure UnsignedTransferCall (types : Types) where
  /-- The checked-transfer request fields. -/
  transfer : Transfer
  /-- Opaque unit-returning invocation after checked preparation succeeds. -/
  invoke : CpiRequest.Checked.Syscall types.State types.Unwind types.Terminal

/-- A close request, ordered signer seeds and actual opaque invocation. -/
structure SignedCloseCall (types : Types) where
  /-- The close-account request fields. -/
  close : Close
  /-- Ordered nested signer seed groups, preserving duplicates. -/
  signers : List (List Bytes)
  /-- Opaque unit-returning invocation after checked preparation succeeds. -/
  invoke : CpiRequest.Checked.Syscall types.State types.Unwind types.Terminal

/-- All state/pool/provider instantiations of the signed transfer wrapper. -/
def signedTransferFamily : Family where
  Index := Types
  State := fun types => types.State
  Args := SignedTransferCall
  Value := fun _ => Except CpiRequest.Checked.Error Unit
  Unwind := fun types => types.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args outcome =>
      CpiRequest.Checked.directV2 types.pool types.rawHeader args.invoke before
        (transferRequest (types.pool before) args.transfer args.signers) outcome }

/-- The signed transfer reference runs v2 checks before the opaque unit call. -/
def signedTransferRun : FamilyRun signedTransferFamily := fun types before args =>
  CpiRequest.Checked.directV2 types.pool types.rawHeader args.invoke before
    (transferRequest (types.pool before) args.transfer args.signers)

/-- The exact checked reference realizes the reusable source family. -/
theorem signedTransferReference : FamilyReference signedTransferFamily signedTransferRun := by
  intro _ _ _ _ _ result
  exact result

/-- The unsigned wrapper family supplies an empty signer-seed list. -/
def unsignedTransferFamily : Family where
  Index := Types
  State := fun types => types.State
  Args := UnsignedTransferCall
  Value := fun _ => Except CpiRequest.Checked.Error Unit
  Unwind := fun types => types.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args outcome => CpiRequest.Checked.directV2 types.pool types.rawHeader
      args.invoke before
      (transferRequest (types.pool before) args.transfer []) outcome }

/-- The unsigned transfer reference uses the same signed preparation with no seeds. -/
def unsignedTransferRun : FamilyRun unsignedTransferFamily := fun types before args =>
  CpiRequest.Checked.directV2 types.pool types.rawHeader args.invoke before
    (transferRequest (types.pool before) args.transfer [])

/-- The exact checked reference realizes the reusable source family. -/
theorem unsignedTransferReference : FamilyReference unsignedTransferFamily unsignedTransferRun := by
  intro _ _ _ _ _ result
  exact result

/-- All state/pool/provider instantiations of the signed close wrapper. -/
def signedCloseFamily : Family where
  Index := Types
  State := fun types => types.State
  Args := SignedCloseCall
  Value := fun _ => Except CpiRequest.Checked.Error Unit
  Unwind := fun types => types.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args outcome =>
      CpiRequest.Checked.directV2 types.pool types.rawHeader args.invoke before
        (closeRequest (types.pool before) args.close args.signers) outcome }

/-- The signed close reference runs the same v2 checked path over three accounts. -/
def signedCloseRun : FamilyRun signedCloseFamily := fun types before args =>
  CpiRequest.Checked.directV2 types.pool types.rawHeader args.invoke before
    (closeRequest (types.pool before) args.close args.signers)

/-- The exact checked reference realizes the reusable source family. -/
theorem signedCloseReference : FamilyReference signedCloseFamily signedCloseRun := by
  intro _ _ _ _ _ result
  exact result

/-- A closed finite AccountView pool; the state records actual dependency effects. -/
def sampleTypes : Types := CpiRequest.Checked.sampleHeaderTypes

/-- A closed checked-transfer sample retaining four ordered account references. -/
def sampleTransfer : Transfer where
  programId := .zero
  source := ⟨3⟩
  mint := ⟨5⟩
  destination := ⟨3⟩
  authority := ⟨9⟩
  amount := 513
  decimals := 6

/-- A closed close-account sample retaining three ordered references. -/
def sampleClose : Close where
  programId := .zero
  account := ⟨3⟩
  destination := ⟨3⟩
  authority := ⟨9⟩

/-- A unit-returning opaque completion that changes the mathematical state. -/
def sampleProvider : CpiRequest.Checked.Syscall Nat Nat Nat :=
  CpiRequest.Checked.sampleProvider

/-- The closed signed-transfer call used by the execution witness. -/
def sampleSignedTransfer : SignedTransferCall sampleTypes :=
  ⟨sampleTransfer, [[], [[], [7, 8]]], sampleProvider⟩

/-- The same closed transfer with no signer seeds. -/
def sampleUnsignedTransfer : UnsignedTransferCall sampleTypes := ⟨sampleTransfer, sampleProvider⟩

/-- The closed signed-close call used by the execution witness. -/
def sampleSignedClose : SignedCloseCall sampleTypes :=
  ⟨sampleClose, [[], [[], [7, 8]]], sampleProvider⟩

/-- The checked family has a concrete admissible input. -/
theorem signedTransferSatisfiable : FamilySatisfiable signedTransferFamily sampleTypes :=
  ⟨(0 : Nat), sampleSignedTransfer, True.intro⟩

/-- Nonempty checked preparation reaches the actual unit-returning callback. -/
theorem signedTransferHasExecution :
    FamilyHasExecution signedTransferFamily signedTransferRun sampleTypes := by
  refine ⟨(0 : Nat), sampleSignedTransfer, .returned (.ok ()) (4 : Nat), True.intro, ?_⟩
  apply (CpiRequest.Checked.directV2_iff _ _ _ _ _ _).2
  simp [transferRequest, sampleSignedTransfer, sampleTransfer, sampleTypes, sampleProvider,
    CpiRequest.Checked.sampleHeaderTypes, CpiRequest.Checked.sampleTypes,
      CpiRequest.Checked.samplePool,
    CpiRequest.Checked.sampleProvider, CpiRequest.Checked.prepareDirectV2,
    CpiRequest.Checked.checkDirectV2, CpiRequest.Checked.invokePrepared,
    Callback.map, Outcome.map, Except.map, AccountView.isBorrowed,
    Borrow.State.lease, Borrow.State.sharedCount, Borrow.State.exclusiveCount,
    Borrow.State.count, Instruction.transferCheckedInstruction, CpiRequest.signed,
    Instruction.authorityMetas, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

/-- The checked family has a concrete admissible input. -/
theorem unsignedTransferSatisfiable : FamilySatisfiable unsignedTransferFamily sampleTypes :=
  ⟨(0 : Nat), sampleUnsignedTransfer, True.intro⟩

/-- Nonempty checked preparation reaches the actual unit-returning callback. -/
theorem unsignedTransferHasExecution :
    FamilyHasExecution unsignedTransferFamily unsignedTransferRun sampleTypes := by
  refine ⟨(0 : Nat), sampleUnsignedTransfer, .returned (.ok ()) (4 : Nat), True.intro, ?_⟩
  apply (CpiRequest.Checked.directV2_iff _ _ _ _ _ _).2
  simp [transferRequest, sampleUnsignedTransfer, sampleTransfer, sampleTypes, sampleProvider,
    CpiRequest.Checked.sampleHeaderTypes, CpiRequest.Checked.sampleTypes,
      CpiRequest.Checked.samplePool,
    CpiRequest.Checked.sampleProvider, CpiRequest.Checked.prepareDirectV2,
    CpiRequest.Checked.checkDirectV2, CpiRequest.Checked.invokePrepared,
    Callback.map, Outcome.map, Except.map, AccountView.isBorrowed,
    Borrow.State.lease, Borrow.State.sharedCount, Borrow.State.exclusiveCount,
    Borrow.State.count, Instruction.transferCheckedInstruction, CpiRequest.signed,
    Instruction.authorityMetas, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

/-- The checked family has a concrete admissible input. -/
theorem signedCloseSatisfiable : FamilySatisfiable signedCloseFamily sampleTypes :=
  ⟨(0 : Nat), sampleSignedClose, trivial⟩

/-- Nonempty checked preparation reaches the actual unit-returning callback. -/
theorem signedCloseHasExecution : FamilyHasExecution signedCloseFamily signedCloseRun sampleTypes
  := by
  refine ⟨(0 : Nat), sampleSignedClose, .returned (.ok ()) (3 : Nat), trivial, ?_⟩
  apply (CpiRequest.Checked.directV2_iff _ _ _ _ _ _).2
  simp [closeRequest, sampleSignedClose, sampleClose, sampleTypes, sampleProvider,
    CpiRequest.Checked.sampleHeaderTypes, CpiRequest.Checked.sampleTypes,
      CpiRequest.Checked.samplePool,
    CpiRequest.Checked.sampleProvider, CpiRequest.Checked.prepareDirectV2,
    CpiRequest.Checked.checkDirectV2, CpiRequest.Checked.invokePrepared,
    Callback.map, Outcome.map, Except.map, AccountView.isBorrowed,
    Borrow.State.lease, Borrow.State.sharedCount, Borrow.State.exclusiveCount,
    Borrow.State.count, Instruction.authorityInstruction, CpiRequest.signed,
    Instruction.authorityMetas, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

/-- The original seed tree, including empty signers and empty seeds, is passed
to the opaque invocation unchanged. -/
theorem transferRequest_signers (pool : AccountView.State) (transfer : Transfer)
    (signers : List (List Bytes)) : (transferRequest pool transfer signers).signers = signers := rfl

/-- Close preserves the same nested signer tree without flattening or deduplication. -/
theorem closeRequest_signers (pool : AccountView.State) (close : Close)
    (signers : List (List Bytes)) : (closeRequest pool close signers).signers = signers := rfl

/-- The selected Pinocchio helpers do not prevalidate the requested program ID. -/
theorem transferRequest_program (pool : AccountView.State) (transfer : Transfer)
    (signers : List (List Bytes)) :
    (transferRequest pool transfer signers).instruction.programId = transfer.programId := rfl

end Solanalib.Specs.Core.Token.Request
