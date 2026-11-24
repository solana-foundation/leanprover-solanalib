/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.CpiRequestCheckedFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.PinocchioSystem.instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.CpiRequest
open Solanalib.Specs.Core.CpiRequest.Checked

/-! Local fixed-array preparation uses the selected InstructionView 2.1.0
checked entry. Only its unit-returning unchecked invocation stays opaque.
Current pool observations supply keys; source handle validity remains a binding. -/

namespace allocate

namespace Allocate

/-- Borrowed account, allocation size and the selected opaque unit call. -/
structure Args (types : HeaderTypes) where
  /-- The current account identity, requested writable and signer. -/
  account : AccountView.Handle
  /-- Allocation size; interpreting this Nat as the source u64 is a binding obligation. -/
  space : Nat
  /-- Ordered nested signer seeds. -/
  signers : List (List _root_.Solanalib.Runtime.Bytes)
  /-- Unchecked invocation after local checks succeed. -/
  invoke : Syscall types.State types.Unwind types.Terminal

/-- Construct the exact fixed request using the current account keys. -/
def request {types : HeaderTypes} (before : types.State) (args : Args types) :
    Request AccountView.Handle :=
  signed (Instruction.systemAllocate
    ((types.pool before).account args.account).metadata.address args.space)
    [args.account] args.signers

/-- The source account array and metadata have the same fixed size, within
the InstructionView 2.1.0 const-generic capacity. -/
theorem request_cardinality {types : HeaderTypes} (before : types.State) (args : Args types) :
    (request before args).accounts.length = 1 ∧
    (request before args).instruction.metas.length = 1 ∧
    (request before args).accounts.length ≤ 64 := ⟨rfl, rfl, by change 1 ≤ 64; decide⟩

/-- Local construction followed by InstructionView 2.1.0 checked preparation. -/
def invoke_signed_contract : Family where
  Index := HeaderTypes
  State := fun types => types.State
  Args := Args
  Value := fun _ => Except Checked.Error Unit
  Unwind := fun types => types.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args => directV2 types.pool types.rawHeader args.invoke before (request
      before args) }

/-- Reference execution includes checks before the opaque unit-returning boundary. -/
def invoke_signed_run : FamilyRun invoke_signed_contract :=
  fun types before args => directV2 types.pool types.rawHeader args.invoke before (request before
    args)

/-- A closed current-pool interpretation for the nonempty witness. -/
def invoke_signed_sample : invoke_signed_contract.Index := sampleHeaderTypes

/-- Concrete existing source identities and a state-changing unit-returning callback. -/
def sampleArgs : Args invoke_signed_sample where
  account := ⟨3⟩
  space := 5
  signers := [[], [[], [8, 9]]]
  invoke := sampleProvider

/-- The exact checked reference realizes this source family. -/
theorem invoke_signed_reference :
    FamilyReference invoke_signed_contract invoke_signed_run := by
  intro _ _ _ _ _ execution
  exact execution

/-- The concrete input inhabits the operational family. -/
theorem invoke_signed_satisfiable :
    FamilySatisfiable invoke_signed_contract invoke_signed_sample :=
  ⟨(0 : Nat), sampleArgs, trivial⟩

/-- Actual nonempty checked preparation reaches normal opaque completion. -/
theorem invoke_signed_has_execution :
    FamilyHasExecution invoke_signed_contract invoke_signed_run invoke_signed_sample := by
  refine ⟨(0 : Nat), sampleArgs, .returned (.ok ()) (1 : Nat), trivial, ?_⟩
  apply (directV2_iff _ _ _ _ _ _).2
  simp [request, sampleArgs, invoke_signed_sample, sampleHeaderTypes, sampleTypes, samplePool,
    sampleProvider,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Instruction.systemAllocate,
    signed, Instruction.make, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

end Allocate

end allocate

namespace assign

namespace Assign

/-- Borrowed account, owner bytes and the selected opaque unit call. -/
structure Args (types : HeaderTypes) where
  /-- The current account identity, requested writable and signer. -/
  account : AccountView.Handle
  /-- The bytes of the exact proposed owner; authorization is outside this helper. -/
  owner : _root_.Solanalib.Runtime.Pubkey
  /-- Ordered nested signer seeds. -/
  signers : List (List _root_.Solanalib.Runtime.Bytes)
  /-- Unchecked invocation after local checks succeed. -/
  invoke : Syscall types.State types.Unwind types.Terminal

/-- Construct the exact fixed request using the current account keys. -/
def request {types : HeaderTypes} (before : types.State) (args : Args types) :
    Request AccountView.Handle :=
  signed (Instruction.systemAssign
    ((types.pool before).account args.account).metadata.address args.owner)
    [args.account] args.signers

/-- The source account array and metadata have the same fixed size, within
the InstructionView 2.1.0 const-generic capacity. -/
theorem request_cardinality {types : HeaderTypes} (before : types.State) (args : Args types) :
    (request before args).accounts.length = 1 ∧
    (request before args).instruction.metas.length = 1 ∧
    (request before args).accounts.length ≤ 64 := ⟨rfl, rfl, by change 1 ≤ 64; decide⟩

/-- Local construction followed by InstructionView 2.1.0 checked preparation. -/
def invoke_signed_contract : Family where
  Index := HeaderTypes
  State := fun types => types.State
  Args := Args
  Value := fun _ => Except Checked.Error Unit
  Unwind := fun types => types.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args => directV2 types.pool types.rawHeader args.invoke before (request
      before args) }

/-- Reference execution includes checks before the opaque unit-returning boundary. -/
def invoke_signed_run : FamilyRun invoke_signed_contract :=
  fun types before args => directV2 types.pool types.rawHeader args.invoke before (request before
    args)

/-- A closed current-pool interpretation for the nonempty witness. -/
def invoke_signed_sample : invoke_signed_contract.Index := sampleHeaderTypes

/-- Concrete existing source identities and a state-changing unit-returning callback. -/
def sampleArgs : Args invoke_signed_sample where
  account := ⟨3⟩
  owner := .zero
  signers := [[], [[], [8, 9]]]
  invoke := sampleProvider

/-- The exact checked reference realizes this source family. -/
theorem invoke_signed_reference :
    FamilyReference invoke_signed_contract invoke_signed_run := by
  intro _ _ _ _ _ execution
  exact execution

/-- The source scalar bounds admit this concrete input. -/
theorem invoke_signed_satisfiable :
    FamilySatisfiable invoke_signed_contract invoke_signed_sample := by
  refine ⟨(0 : Nat), sampleArgs, ?_⟩
  trivial

/-- Actual nonempty checked preparation reaches normal opaque completion. -/
theorem invoke_signed_has_execution :
    FamilyHasExecution invoke_signed_contract invoke_signed_run invoke_signed_sample := by
  refine ⟨(0 : Nat), sampleArgs, .returned (.ok ()) (1 : Nat), ?_, ?_⟩
  · trivial
  apply (directV2_iff _ _ _ _ _ _).2
  simp [request, sampleArgs, invoke_signed_sample, sampleHeaderTypes, sampleTypes, samplePool,
    sampleProvider,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Instruction.systemAssign,
    signed, Instruction.make, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

end Assign

end assign

namespace transfer

namespace Transfer

/-- The two borrowed identities and amount of the unsigned transfer. -/
structure Args (types : HeaderTypes) where
  /-- Funding account, requested writable and signer. -/
  fromAccount : AccountView.Handle
  /-- Destination, requested writable and allowed to alias the funding account. -/
  toAccount : AccountView.Handle
  /-- Transfer amount; interpreting this Nat as the source u64 is a binding obligation. -/
  lamports : Nat
  /-- Unchecked invocation after local checks succeed. -/
  invoke : Syscall types.State types.Unwind types.Terminal

/-- Construct the exact fixed request using the current account keys. -/
def request {types : HeaderTypes} (before : types.State) (args : Args types) :
    Request AccountView.Handle :=
  unsigned (Instruction.systemTransfer
    ((types.pool before).account args.fromAccount).metadata.address
    ((types.pool before).account args.toAccount).metadata.address args.lamports)
    [args.fromAccount, args.toAccount]

/-- The source account array and metadata have the same fixed size, within
the InstructionView 2.1.0 const-generic capacity. -/
theorem request_cardinality {types : HeaderTypes} (before : types.State) (args : Args types) :
    (request before args).accounts.length = 2 ∧
    (request before args).instruction.metas.length = 2 ∧
    (request before args).accounts.length ≤ 64 := ⟨rfl, rfl, by change 2 ≤ 64; decide⟩

/-- The unsigned wrapper runs the same checked path with an empty signer tree. -/
def invoke_contract : Family where
  Index := HeaderTypes
  State := fun types => types.State
  Args := Args
  Value := fun _ => Except Checked.Error Unit
  Unwind := fun types => types.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args => directV2 types.pool types.rawHeader args.invoke before (request
      before args) }

/-- Reference execution includes checks before the opaque unit-returning boundary. -/
def invoke_run : FamilyRun invoke_contract :=
  fun types before args => directV2 types.pool types.rawHeader args.invoke before (request before
    args)

/-- A closed current-pool interpretation for the nonempty witness. -/
def invoke_sample : invoke_contract.Index := sampleHeaderTypes

/-- Concrete existing source identities and a state-changing unit-returning callback. -/
def sampleArgs : Args invoke_sample where
  fromAccount := ⟨3⟩
  toAccount := ⟨3⟩
  lamports := 5
  invoke := sampleProvider

/-- The exact checked reference realizes this source family. -/
theorem invoke_reference :
    FamilyReference invoke_contract invoke_run := by
  intro _ _ _ _ _ execution
  exact execution

/-- The concrete input inhabits the operational family. -/
theorem invoke_satisfiable :
    FamilySatisfiable invoke_contract invoke_sample :=
  ⟨(0 : Nat), sampleArgs, trivial⟩

/-- Both source positions reach normal opaque completion, including their alias. -/
theorem invoke_has_execution :
    FamilyHasExecution invoke_contract invoke_run invoke_sample := by
  refine ⟨(0 : Nat), sampleArgs, .returned (.ok ()) (2 : Nat), trivial, ?_⟩
  apply (directV2_iff _ _ _ _ _ _).2
  simp [request, sampleArgs, invoke_sample, sampleHeaderTypes, sampleTypes, samplePool,
    sampleProvider,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed, Borrow.State.lease, Borrow.State.sharedCount,
    Borrow.State.exclusiveCount, Borrow.State.count, Instruction.systemTransfer,
    unsigned, Instruction.make, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

end Transfer

end transfer

end Solanalib.Specs.PinocchioSystem.instructions
