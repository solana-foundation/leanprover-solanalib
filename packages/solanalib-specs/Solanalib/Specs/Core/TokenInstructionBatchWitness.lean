/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionBatchRun
public import Solanalib.Specs.Core.AccountViewWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Batch

/-- The registered sample has a nonempty generic signer slice, mutable ambient
state, and distinct unwind/terminal types. It does not restrict the family. -/
abbrev sampleTypes : Types := ⟨Nat, Unit, Nat, Nat⟩

/-- Deliberate aliasing: all base entries refer to the same existing account. -/
def sampleSingle : SingleTransfer :=
  ⟨AccountView.witnessHandle, AccountView.witnessHandle,
    AccountView.witnessHandle, AccountView.witnessHandle, 513, 6⟩

/-- One signer requires two separate `as_ref` calls. -/
def sampleTransfer : Transfer Unit := ⟨sampleSingle, [()]⟩

/-- Initialized discriminator, capacity for one complete instruction, and spare uninitialized
account/metadata storage for the one-signer sample. -/
def sampleBuffers : Buffers :=
  ⟨some 255 :: List.replicate 12 none, List.replicate 5 none, List.replicate 5 none⟩

/-- A fresh selected Batch with no account or metadata prefixes yet. -/
def sampleState : State Nat := ⟨⟨AccountView.witnessState, 0⟩, sampleBuffers, ⟨1, 0, 0⟩⟩

/-- A partial callback interpretation that requires its returned handle to
exist, changes the ambient counter, and preserves the actual account world. -/
def sampleAsRef : AsRef sampleTypes := fun before _ outcome =>
  AccountView.Ready before.world AccountView.witnessHandle ∧
  outcome = .returned AccountView.witnessHandle { before with ambient := before.ambient + 1 }

/-- The generic input records its callback interpretation explicitly. -/
def sampleIntoCall : IntoCall sampleTypes := ⟨sampleTransfer, sampleAsRef⟩

/-- The exact state after the fixed ten-byte payload writer. -/
def sampleAfterData : State Nat := (writeData sampleState sampleTransfer).2

/-- The first pass initializes four base descriptors and one callback descriptor. -/
def sampleAfterAccounts : State Nat :=
  writeAccount
    { writeBaseAccounts sampleAfterData sampleTransfer with
      context := ⟨AccountView.witnessState, 1⟩ }
    4 AccountView.witnessHandle

/-- The second pass independently calls the signer again, taking ambient state
from one to two, and writes its metadata reference. -/
def sampleAfterMetas : State Nat :=
  writeMeta
    { writeBaseMetas sampleAfterAccounts sampleTransfer with
      context := ⟨AccountView.witnessState, 2⟩ }
    4 AccountView.witnessHandle true false

/-- The complete committed sample is thirteen data bytes and five entries in
each account slice. Its ambient state records both callback invocations. -/
def sampleCommitted : State Nat := commit sampleAfterMetas 10 5 5

/-- The registered family admits its explicit two-pass execution input. -/
theorem sampleInto_requires : (intoFamily.contract sampleTypes).requires sampleState sampleIntoCall
  :=
  True.intro

/-- The first pass uses a real returning callback with its ambient effect. -/
theorem sampleAccounts_execute :
    writeAccounts sampleAsRef sampleAfterData sampleTransfer
      (.returned (.ok 5) sampleAfterAccounts) := by
  apply writeAccounts_pass sampleAsRef sampleAfterData sampleTransfer
    (.returned () sampleAfterAccounts) (by decide) (by decide)
  apply signerPass_return sampleAsRef writeAccount
    (writeBaseAccounts sampleAfterData sampleTransfer) 4 () [] AccountView.witnessHandle
    ⟨AccountView.witnessState, 1⟩ (.returned () sampleAfterAccounts)
  · exact ⟨AccountView.witness_ready, rfl⟩
  · rfl

/-- The second pass repeats the callback and observes its actual new state. -/
theorem sampleMetas_execute :
    writeMetas sampleAsRef sampleAfterAccounts sampleTransfer
      (.returned (.ok 5) sampleAfterMetas) := by
  apply writeMetas_pass sampleAsRef sampleAfterAccounts sampleTransfer
    (.returned () sampleAfterMetas) (by decide)
  apply signerPass_return sampleAsRef
    (fun state offset handle => writeMeta state offset handle true false)
    (writeBaseMetas sampleAfterAccounts sampleTransfer) 4 () [] AccountView.witnessHandle
    ⟨AccountView.witnessState, 2⟩ (.returned () sampleAfterMetas)
  · exact ⟨AccountView.witness_ready, rfl⟩
  · rfl

/-- An actual finite successful execution of the generic two-pass relation. -/
theorem sampleInto_execute :
    intoBatch sampleAsRef sampleState sampleTransfer (.returned (.ok ()) sampleCommitted) :=
  intoBatch_success sampleAsRef sampleState sampleTransfer
    sampleAfterData sampleAfterAccounts sampleAfterMetas 10 5 5
    (by decide) rfl sampleAccounts_execute sampleMetas_execute

/-- The closed reference family has an actual execution with two callback effects. -/
theorem intoHasExecution : FamilyHasExecution intoFamily intoRun sampleTypes :=
  ⟨sampleState, sampleIntoCall, .returned (.ok ()) sampleCommitted,
    sampleInto_requires, sampleInto_execute⟩

/-- Nonvacuity follows from the same registered actual execution. -/
theorem intoSatisfiable : FamilySatisfiable intoFamily sampleTypes :=
  intoHasExecution.satisfiable

/-- The nonempty permitted buffer witness of the constructor. -/
theorem newSatisfiable : newContract.Satisfiable :=
  ⟨sampleBuffers, (), True.intro⟩

/-- The specialized constructor accepts all four retained references and the
selected source-width integer values. -/
theorem transferNewSatisfiable : transferNewContract.Satisfiable :=
  ⟨(), sampleSingle, True.intro⟩

/-- The initial one-byte committed prefix is initialized and in bounds;
both account prefixes are empty. -/
theorem sampleInvocationReady : InvocationReady sampleState := by
  unfold InvocationReady PrefixReady
  decide

/-- Both successful writer passes leave complete initialized prefixes,
including every repeated account and metadata entry. -/
theorem sampleCommittedInvocationReady : InvocationReady sampleCommitted := by
  unfold InvocationReady PrefixReady
  decide

/-- A fresh Batch decodes exactly its discriminator, with empty account prefixes. -/
def sampleRequest (signers : List (List Bytes)) : Request :=
  ⟨legacyProgramId, [], [255], [], signers⟩

theorem sampleRequest_decodes (signers : List (List Bytes)) :
    request sampleState signers = some (sampleRequest signers) := rfl

/-- This unchecked provider returns unit after changing ambient state. Its
argument remains the full live-reference request descriptor. -/
def sampleInvokeCall : InvokeCall sampleTypes :=
  ⟨[[], [[], [7, 8]]], fun before request outcome =>
    outcome = .returned () { before with ambient := before.ambient + request.data.length }⟩

/-- A real provider execution witnesses the invocation family, with its own
state effect and original empty-containing signer seed tree. -/
theorem invokeHasExecution : FamilyHasExecution invokeFamily invokeRun sampleTypes := by
  refine ⟨sampleState, sampleInvokeCall,
    .returned (.ok ()) { sampleState with context := ⟨AccountView.witnessState, 1⟩ },
    sampleInvocationReady, ?_⟩
  exact invokeSigned_return (types := sampleTypes) sampleState sampleInvokeCall
    (sampleRequest sampleInvokeCall.signers) (sampleRequest_decodes _)
    ⟨AccountView.witnessState, 1⟩ rfl

/-- Invocation nonvacuity is tied to the same provider execution. -/
theorem invokeSatisfiable : FamilySatisfiable invokeFamily sampleTypes :=
  invokeHasExecution.satisfiable

end Solanalib.Specs.Core.Token.Batch
