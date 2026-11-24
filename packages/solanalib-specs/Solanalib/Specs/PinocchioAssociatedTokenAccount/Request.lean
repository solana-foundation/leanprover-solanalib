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

namespace
  Solanalib.Specs.PinocchioAssociatedTokenAccount.instructions.create_idempotent.CreateIdempotent

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.CpiRequest
open Solanalib.Specs.Core.CpiRequest.Checked

/-- Borrowed accounts used by the six-element v2 checked call. The pool supplies
their current keys; source reference validity remains an interpretation obligation. -/
structure Args (types : HeaderTypes) where
  /-- Funding account, requested writable and signer. -/
  fundingAccount : AccountView.Handle
  /-- Associated account, requested writable. -/
  account : AccountView.Handle
  /-- Readonly wallet account. -/
  wallet : AccountView.Handle
  /-- Readonly token mint. -/
  mint : AccountView.Handle
  /-- Supplied System-program account; its key is not replaced or validated. -/
  systemProgram : AccountView.Handle
  /-- Supplied Token-program account; its key is not replaced or validated. -/
  tokenProgram : AccountView.Handle
  /-- Opaque unit-returning invocation after checked preparation succeeds. -/
  invoke : Syscall types.State types.Unwind types.Terminal

/-- Exact metadata and source handles are read at wrapper entry. There is no
intervening callback before the selected borrowed-AccountView checked call. -/
def request {types : HeaderTypes} (before : types.State) (args : Args types) :
    Request AccountView.Handle :=
  let pool := types.pool before
  unsigned (Instruction.associatedTokenCreateIdempotent
    (pool.account args.fundingAccount).metadata.address
    (pool.account args.account).metadata.address
    (pool.account args.wallet).metadata.address
    (pool.account args.mint).metadata.address
    (pool.account args.systemProgram).metadata.address
    (pool.account args.tokenProgram).metadata.address)
    [args.fundingAccount, args.account, args.wallet, args.mint,
      args.systemProgram, args.tokenProgram]

/-- The source arrays have the same fixed cardinality; the const-generic
64-account bound does not add a runtime error branch to this wrapper. -/
theorem request_cardinality {types : HeaderTypes} (before : types.State) (args : Args types) :
    (request before args).accounts.length = 6 ∧
    (request before args).instruction.metas.length = 6 ∧
    (request before args).accounts.length ≤ 64 := ⟨rfl, rfl, by change 6 ≤ 64; decide⟩

/-- The unsigned wrapper delegates with no seeds to the InstructionView 2.1.0
checked array entry. Existing-account behavior remains outside this helper. -/
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

/-- Reference execution includes the shared checked preparation. -/
def invoke_run : FamilyRun invoke_contract :=
  fun types before args => directV2 types.pool types.rawHeader args.invoke before (request before
    args)

/-- Closed pool and outcome types for the nonempty reference witness. -/
def invoke_sample : invoke_contract.Index := sampleHeaderTypes

/-- A six-position request retains the funding/wallet alias. -/
def sampleArgs : Args invoke_sample where
  fundingAccount := ⟨3⟩
  account := ⟨2⟩
  wallet := ⟨3⟩
  mint := ⟨4⟩
  systemProgram := ⟨5⟩
  tokenProgram := ⟨6⟩
  invoke := sampleProvider

/-- The exact reference realizes the registered family for every dependency. -/
theorem invoke_reference : FamilyReference invoke_contract invoke_run := by
  intro _ _ _ _ _ execution
  exact execution

/-- The wrapper has a concrete admissible input. -/
theorem invoke_satisfiable : FamilySatisfiable invoke_contract invoke_sample :=
  ⟨(0 : Nat), sampleArgs, trivial⟩

/-- Six actual initialized entries reach the opaque unit-returning provider. -/
theorem invoke_has_execution : FamilyHasExecution invoke_contract invoke_run invoke_sample := by
  refine ⟨(0 : Nat), sampleArgs, .returned (.ok ()) (6 : Nat), trivial, ?_⟩
  apply (directV2_iff _ _ _ _ _ _).2
  simp [request, sampleArgs, invoke_sample, sampleHeaderTypes, sampleTypes, samplePool,
    sampleProvider,
    prepareDirectV2, checkDirectV2, invokePrepared, Callback.map, Outcome.map, Except.map,
    AccountView.isBorrowed,
    Borrow.State.lease, Borrow.State.sharedCount, Borrow.State.exclusiveCount,
    Borrow.State.count, Instruction.associatedTokenCreateIdempotent, unsigned,
    Instruction.make, Instruction.accountMeta]
  exact ⟨_, rfl, rfl⟩

end Solanalib.Specs.PinocchioAssociatedTokenAccount.instructions.create_idempotent.CreateIdempotent
