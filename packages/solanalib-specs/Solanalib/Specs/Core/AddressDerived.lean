/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressOperations
public import Solanalib.Specs.Core.Instruction

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Address.Operations

open Solanalib.Contracts.Model Solanalib.Specs.Core Address.Syscall

/-! Address-only projections of PDA wrappers. These prepare the exact ordered seeds and program ID
of the SDK, then run the complete selected dependency model.
The bump of the search result is discarded; its state and abnormal exits are not. -/

structure AssociatedInputs where
  wallet : Value
  mint : Value
  tokenProgram : Value

def associatedInputs (args : AssociatedInputs) : PdaInputs :=
  ⟨[args.wallet.bytes, args.tokenProgram.bytes, args.mint.bytes],
    Instruction.associatedTokenProgramId⟩

def loaderInputs (program : Value) : PdaInputs :=
  ⟨[program.bytes], Solanalib.Runtime.Ids.bpfLoaderUpgradeable⟩

def zeroDerivedRun {Args : Type} (inputs : Args → PdaInputs) (index : ZeroFindIndex) :
    Callback.Run index.State Args Value index.Unwind index.Terminal :=
  fun before args => Callback.map Prod.fst (zeroFindRun index) before (inputs args)

def zeroDerivedFamily (Args : Type) (inputs : Args → PdaInputs) : Family where
  Index := ZeroFindIndex
  State := fun index => index.State
  Args := fun _ => Args
  Value := fun _ => Address.Value
  Unwind := fun index => index.Unwind
  Terminal := fun index => index.Terminal
  contract := fun index => { requires := fun _ _ => True, post := zeroDerivedRun inputs index }

def zeroDerivedReference (Args : Type) (inputs : Args → PdaInputs) :
    FamilyRun (zeroDerivedFamily Args inputs) := zeroDerivedRun inputs

theorem zeroDerivedReference_correct (Args : Type) (inputs : Args → PdaInputs) :
    FamilyReference (zeroDerivedFamily Args inputs) (zeroDerivedReference Args inputs) :=
  fun _ _ _ _ _ execution => execution

theorem zeroDerivedSample_execution (Args : Type) (inputs : Args → PdaInputs) (args : Args) :
    FamilyHasExecution (zeroDerivedFamily Args inputs) (zeroDerivedReference Args inputs)
      zeroFindSample :=
  ⟨(), args, .returned .zero (), trivial,
    .returned (.zero, 253) (),
    ⟨.returned (some (.zero, 253)) (), ⟨.returned ⟨0, .zero, 253⟩ (), rfl, rfl⟩, rfl⟩, rfl⟩

structure UninitFindIndex extends Types where
  syscall : Callback.Run State PdaRequest PdaReply Unwind Terminal
  panic : Callback.Run State SearchPanic Empty Unwind Terminal

def uninitDerivedRun {Args : Type} (inputs : Args → PdaInputs) (index : UninitFindIndex) :
    Callback.Run index.State Args Value index.Unwind index.Terminal :=
  fun before args => Callback.map Prod.fst (findRun index.syscall index.panic) before (inputs args)

def uninitDerivedFamily (Args : Type) (inputs : Args → PdaInputs) : Family where
  Index := UninitFindIndex
  State := fun index => index.State
  Args := fun _ => Args
  Value := fun _ => Address.Value
  Unwind := fun index => index.Unwind
  Terminal := fun index => index.Terminal
  contract := fun index => {
    requires := fun before args => SuccessInitialized index.syscall before (inputs args)
    post := uninitDerivedRun inputs index }

def uninitDerivedReference (Args : Type) (inputs : Args → PdaInputs) :
    FamilyRun (uninitDerivedFamily Args inputs) := uninitDerivedRun inputs

theorem uninitDerivedReference_correct (Args : Type) (inputs : Args → PdaInputs) :
    FamilyReference (uninitDerivedFamily Args inputs) (uninitDerivedReference Args inputs) :=
  fun _ _ _ _ _ execution => execution

def uninitFindSample : UninitFindIndex where
  State := Unit
  Unwind := String
  Terminal := String
  syscall := Callback.ofFunction fun before _ => .returned ⟨0, some .zero, 251⟩ before
  panic := Callback.ofFunction fun before _ => .unwound panicMessage before

theorem uninitDerivedSample_execution (Args : Type) (inputs : Args → PdaInputs) (args : Args) :
    FamilyHasExecution (uninitDerivedFamily Args inputs) (uninitDerivedReference Args inputs)
      uninitFindSample := by
  refine ⟨(), args, .returned .zero (), ?_, ?_⟩
  · intro reply after step _
    cases step
    exact ⟨.zero, rfl⟩
  · refine ⟨.returned (.zero, 251) (), ?_, rfl⟩
    refine ⟨.returned (some (.zero, 251)) (), ?_, rfl⟩
    exact ⟨.returned ⟨0, some .zero, 251⟩ (), rfl,
      some (.zero, 251), ⟨.zero, rfl, rfl⟩, rfl⟩

end Solanalib.Specs.Core.Address.Operations
