/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLoaderIdentity
public import Solanalib.Specs.Core.AnchorLifecycleCloseSamples

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLoaderClose

/-- The 1.0.2 loader close uses boxed modern errors, the existing AccountInfo
store and the Rc destructor of its owned destination. It has no Owner callback,
payload serializer, discriminator or payload-layout dependency. -/
structure Types where
  Aux : Type
  Payload : Type
  Unwind : Type
  Terminal : Type
  StringResource : Type
  BoxResource : Type
  errors : AnchorErrorOwned.Ops (AnchorAccount.World Aux) StringResource BoxResource Terminal
  sdk : Owned.Focus (AnchorAccount.World Aux) AccountInfoSdk.State
  borrow_eq : ∀ state, (sdk.get state).borrow = state.1
  rc : AccountInfoRc.Ops (AnchorAccount.World Aux) Terminal

/-- Select the error storage and common-close profile of the reviewed release.
The lawful SDK focus shares the actual borrow state of the caller. -/
def Types.core (types : Types) : AnchorLifecycle.CloseTypes where
  Aux := types.Aux
  Unwind := types.Unwind
  Terminal := types.Terminal
  StringResource := types.StringResource
  BoxResource := types.BoxResource
  Program := ProgramError.Value
  errorStorage := .boxed
  errors := AnchorErrorOperations.Ops.fromOwned types.errors
  programValue := id
  sdk := types.sdk
  borrow_eq := types.borrow_eq
  rc := types.rc

structure Args (types : Types) where
  profile : AccountInfo.Profile
  loader : AnchorLoader.Value types.Payload
  destination : AnchorLoader.Reference

def Args.core {types : Types} (args : Args types) : AnchorLifecycle.CloseArgs :=
  ⟨args.profile, args.loader.account.info, args.destination.info⟩

abbrev Result (types : Types) := Except (AnchorErrorOwned.Error types.BoxResource) Unit
abbrev Unwind (types : Types) := AnchorLifecycle.CloseUnwind types.core
abbrev Terminal (types : Types) := AnchorLifecycle.CloseTerminal types.core

/-- `AccountLoader::close` borrows its source and moves its destination.
The common helper reads destination before source, credits then zeroes the
source, assigns the system owner, then resizes. The destination is dropped
after normal return or unwind, retaining all preceding source effects. -/
def run (types : Types) : Callback.Run (AnchorAccount.World types.Aux) (Args types)
    (Result types) (Unwind types) (Terminal types) :=
  fun before args => AnchorLifecycle.wrapperClose false .legacy types.core before args.core

def Ready (types : Types) (before : AnchorAccount.World types.Aux) (args : Args types) : Prop :=
  AnchorLifecycle.CommonCloseReady types.core before args.core

/-- The reached typed-read/resize domain guarantees a real local common-close
exit, including checked borrow errors and overflow unwind. It assumes no
allocator or destination destructor termination. -/
theorem core_exists {types : Types} {before : AnchorAccount.World types.Aux} {args : Args types}
    (ready : Ready types before args) :
    ∃ outcome, AnchorLifecycle.commonCloseCore .legacy (types.sdk.get before) args.core = some
      outcome :=
  AnchorLifecycle.CloseCoreReady.exists ready

/-- Every actual common-close outcome is retained through the source-required
destination cleanup, with the actual final world and exit of that cleanup. -/
theorem retain {types : Types} {before : AnchorAccount.World types.Aux} {args : Args types}
    {pending outcome}
    (called : AnchorLifecycle.commonClose .legacy types.core before args.core pending)
    (dropped : Owned.cleanup (fun _ _ _ _ => False)
      [fun state => AnchorLifecycle.closeLiftCall
        (fun state (_ : Unit) => AnchorLifecycle.dropInfo types.core.toBase types.rc
          args.destination.info state)
        state ()] pending outcome) : run types before args outcome := by
  exact ⟨pending, called, dropped⟩

def family : Family where
  Index := Types
  State := fun types => AnchorAccount.World types.Aux
  Args := Args
  Value := Result
  Unwind := Unwind
  Terminal := Terminal
  contract := fun types => { requires := Ready types, post := run types }

def reference : FamilyRun family := run

theorem reference_holds : FamilyReference family reference := by
  intro _ _ _ _ _ called
  exact called

/-- A self-close sample exercises the sequential alias behavior: the credited
same cell is subsequently zeroed, with the same owner/backing store. -/
def sample : Types where
  Aux := AnchorLifecycle.CloseSampleAux
  Payload := Nat
  Unwind := String
  Terminal := AnchorErrorOwned.Reference.Failure
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  errors := AnchorErrorOwned.Reference.ops.focus (Owned.Focus.snd.comp Owned.Focus.snd)
  sdk := AnchorLifecycle.closeSampleFocus
  borrow_eq := fun _ => rfl
  rc := AnchorLifecycle.sampleRc

def sampleArgs : Args sample :=
  ⟨AccountInfo.sampleProfile, AnchorLoader.sampleValue, AnchorLoader.sampleReference⟩

theorem has_execution : FamilyHasExecution family reference sample := by
  refine ⟨AnchorLifecycle.closeSampleBefore, sampleArgs,
    .returned (.ok ()) AnchorLifecycle.closeSampleAfter, ?_, ?_⟩
  · exact AnchorLifecycle.closeSample_ready .legacy .boxed
  · exact AnchorLifecycle.closeSample_wrapper false .legacy .boxed

end Solanalib.Specs.Core.AnchorLoaderClose
