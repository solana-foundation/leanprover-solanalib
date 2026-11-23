/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OpaqueCpiSdk
public import Solanalib.Specs.Core.Callback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.OpaqueCpi.Sdk.Owned

open Solanalib.Runtime

/-- The source dependency that clones an instruction into owned stable storage
and later destroys that storage. Its state includes allocator observations.
Panic-abort is selected by the reviewed on-chain build profiles. -/
structure Provider : Type 1 where
  State : Type
  Resource : Type
  Terminal : Type
  current : State → Resource → Option CpiInstruction
  clone : Callback.Run State CpiInstruction Resource Empty Terminal
  drop : Callback.Run State Resource Unit Empty Terminal
  /-- The returned owner observes the complete ordered instruction. -/
  clone_current : ∀ before instruction resource after,
    clone before instruction (.returned resource after) →
      current after resource = some instruction
  /-- Cloning creates a fresh owner, rather than consuming the owner of the input. -/
  clone_fresh : ∀ before instruction resource after,
    clone before instruction (.returned resource after) →
      current before resource = none
  /-- Normal destruction retires the same retained owner. -/
  drop_current : ∀ before resource after,
    drop before resource (.returned () after) → current after resource = none

/-- Source allocation and the canonical runtime remain separate dependencies. -/
structure Index : Type 1 where
  runtime : OpaqueCpi.Index
  storage : Provider

structure State (index : Index) where
  source : Sdk.State
  storage : index.storage.State

/-- Runtime failures and local allocation/cleanup aborts are not conflated. -/
inductive Terminal (index : Index) where
  | runtime (error : InstrError)
  | local (reason : index.storage.Terminal)

/-- The assumed whole-signature contract for owned stable-instruction releases.
Borrow checking precedes cloning; an ordinary CPI success precedes destruction.
A terminal exit does not invent a final heap or perform subsequent cleanup. -/
inductive Run (index : Index) (before : State index) (args : Args) :
    Outcome (State index) (Except ProgramError.Value Unit) Empty (Terminal index) → Prop
  | metering :
      Run index before args (.terminated (.runtime .ComputationalBudgetExceeded))
  | borrowError {borrows : BorrowState}
      (checked : preflight args.accounts before.source.borrows args.instruction.metas =
        (false, borrows)) :
      Run index before args (.returned (.error .accountBorrowFailed)
        ⟨⟨before.source.invocation, borrows⟩, before.storage⟩)
  | cloneTerminal {borrows : BorrowState} {reason : index.storage.Terminal}
      (checked : preflight args.accounts before.source.borrows args.instruction.metas =
        (true, borrows))
      (clone : index.storage.clone before.storage args.instruction (.terminated reason)) :
      Run index before args (.terminated (.local reason))
  | runtimeTerminal {borrows : BorrowState} {resource : index.storage.Resource}
      {prepared : index.storage.State} {error : InstrError}
      (checked : preflight args.accounts before.source.borrows args.instruction.metas =
        (true, borrows))
      (clone : index.storage.clone before.storage args.instruction (.returned resource prepared))
      (invoke : OpaqueCpi.run index.runtime before.source.invocation args.runtimeRequest
        (.terminated error)) :
      Run index before args (.terminated (.runtime error))
  | dropTerminal {borrows : BorrowState} {resource : index.storage.Resource}
      {prepared : index.storage.State} {invoked : InvState}
      {reason : index.storage.Terminal}
      (checked : preflight args.accounts before.source.borrows args.instruction.metas =
        (true, borrows))
      (clone : index.storage.clone before.storage args.instruction (.returned resource prepared))
      (invoke : OpaqueCpi.run index.runtime before.source.invocation args.runtimeRequest
        (.returned () invoked))
      (drop : index.storage.drop prepared resource (.terminated reason)) :
      Run index before args (.terminated (.local reason))
  | returned {borrows : BorrowState} {resource : index.storage.Resource}
      {prepared final : index.storage.State} {invoked : InvState}
      (checked : preflight args.accounts before.source.borrows args.instruction.metas =
        (true, borrows))
      (clone : index.storage.clone before.storage args.instruction (.returned resource prepared))
      (invoke : OpaqueCpi.run index.runtime before.source.invocation args.runtimeRequest
        (.returned () invoked))
      (drop : index.storage.drop prepared resource (.returned () final)) :
      Run index before args (.returned (.ok ()) ⟨⟨invoked, borrows⟩, final⟩)

def signedFamily : Family where
  Index := Index
  State := State
  Args := fun _ => Args
  Value := fun _ => Except ProgramError.Value Unit
  Unwind := fun _ => Empty
  Terminal := Terminal
  contract := fun index => { requires := fun _ _ => True, post := Run index }

def signedRun : FamilyRun signedFamily := Run

theorem signedReference : FamilyReference signedFamily signedRun := by
  intro _ _ _ _ _ execution
  exact execution

def unsignedFamily : Family where
  Index := Index
  State := State
  Args := fun _ => UnsignedArgs
  Value := fun _ => Except ProgramError.Value Unit
  Unwind := fun _ => Empty
  Terminal := Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before args => Run index before args.signed }

def unsignedRun : FamilyRun unsignedFamily := fun index before args =>
  Run index before args.signed

theorem unsignedReference : FamilyReference unsignedFamily unsignedRun := by
  intro _ _ _ _ _ execution
  exact execution

/-- Every ordinary error is the earlier borrow check, before allocation. -/
theorem error_before_clone {index : Index} {before after : State index} {args : Args}
    {error : ProgramError.Value}
    (returned : Run index before args (.returned (.error error) after)) :
    error = .accountBorrowFailed ∧ after.storage = before.storage ∧
      after.source.invocation = before.source.invocation := by
  cases returned
  exact ⟨rfl, rfl, rfl⟩

/-- A returned success has an exact fresh clone and retires that same owner.
The source instruction remains a borrowed input throughout this sequence. -/
theorem success_storage {index : Index} {before after : State index} {args : Args}
    (returned : Run index before args (.returned (.ok ()) after)) :
    ∃ resource prepared,
      index.storage.current before.storage resource = none ∧
      index.storage.current prepared resource = some args.instruction ∧
      index.storage.current after.storage resource = none ∧
      OpaqueCpi.run index.runtime before.source.invocation args.runtimeRequest
        (.returned () after.source.invocation) := by
  cases returned with
  | returned checked cloned invoked dropped =>
    exact ⟨_, _, index.storage.clone_fresh _ _ _ _ cloned,
      index.storage.clone_current _ _ _ _ cloned,
      index.storage.drop_current _ _ _ dropped, invoked⟩

/-- An allocation or cleanup abort is impossible after a failed borrow check.
No terminating clone outcome is silently relabeled as a recoverable error. -/
theorem borrow_error_blocks_local_terminal {index : Index} {before : State index}
    {args : Args} {borrows : BorrowState} {reason : index.storage.Terminal}
    (failed : preflight args.accounts before.source.borrows args.instruction.metas =
      (false, borrows)) :
    ¬ Run index before args (.terminated (.local reason)) := by
  intro stopped
  cases stopped with
  | cloneTerminal checked _ => rw [failed] at checked; cases checked
  | dropTerminal checked _ _ _ => rw [failed] at checked; cases checked

end Solanalib.Specs.Core.OpaqueCpi.Sdk.Owned
