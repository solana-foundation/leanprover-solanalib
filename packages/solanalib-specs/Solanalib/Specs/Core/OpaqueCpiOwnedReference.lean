/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OpaqueCpiSdkOwnedWitness
public import Solanalib.Specs.Core.OpaqueCpiReference

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.OpaqueCpi.Reference

open Solanalib.Runtime

/-- One-slot mock storage, reused at an arbitrary runtime index. Its local
terminal exits remain available; the following lemmas concern specific exit
constructors and do not discard those additional outcomes. -/
def ownedIndex (runtime : OpaqueCpi.Index) : Sdk.Owned.Index :=
  ⟨runtime, OwnedWitness.provider⟩

theorem owned_returned_iff (runtime : OpaqueCpi.Index) (before after : Sdk.State)
    (args : Sdk.Args) (value : Except ProgramError.Value Unit) :
    Sdk.Owned.Run (ownedIndex runtime) ⟨before, none⟩ args
      (.returned value ⟨after, none⟩) ↔ Sdk.run runtime before args (.returned value after) := by
  constructor
  · intro executed
    cases executed with
    | borrowError checked => exact Or.inr (by simp [Sdk.checkedRun, checked])
    | returned checked _ invoked _ =>
      exact Or.inr (by simpa [Sdk.checkedRun, checked, ownedIndex] using invoked)
  · rintro (impossible | executed)
    · cases impossible
    cases checked : Sdk.preflight args.accounts before.borrows args.instruction.metas with
    | mk result leases =>
      cases result with
      | false =>
        have same : (.returned value after : Outcome Sdk.State
            (Except ProgramError.Value Unit) Empty InstrError) =
            .returned (.error .accountBorrowFailed) ⟨before.invocation, leases⟩ :=
          by simpa [Sdk.checkedRun, checked] using executed
        cases same
        exact .borrowError checked
      | true =>
        have parts : value = .ok () ∧ after.borrows = leases ∧
            OpaqueCpi.run runtime before.invocation args.runtimeRequest
              (.returned () after.invocation) :=
          by simpa [Sdk.checkedRun, checked] using executed
        cases after
        rcases parts with ⟨rfl, rfl, invoked⟩
        exact .returned (resource := ()) checked ⟨rfl, rfl⟩ invoked rfl

theorem owned_runtime_terminal_iff (runtime : OpaqueCpi.Index) (before : Sdk.State)
    (args : Sdk.Args) (error : InstrError) :
    Sdk.Owned.Run (ownedIndex runtime) ⟨before, none⟩ args
      (.terminated (.runtime error)) ↔ Sdk.run runtime before args (.terminated error) := by
  constructor
  · intro executed
    cases executed with
    | metering => exact Or.inl rfl
    | runtimeTerminal checked _ invoked =>
      exact Or.inr (by simpa [Sdk.checkedRun, checked, ownedIndex] using invoked)
  · rintro (metered | executed)
    · cases metered
      exact .metering
    cases checked : Sdk.preflight args.accounts before.borrows args.instruction.metas with
    | mk result leases =>
      cases result with
      | false => simp [Sdk.checkedRun, checked] at executed
      | true =>
        have invoked : OpaqueCpi.run runtime before.invocation args.runtimeRequest
            (.terminated error) := by simpa [Sdk.checkedRun, checked] using executed
        exact .runtimeTerminal (resource := ()) checked ⟨rfl, rfl⟩ invoked

end Solanalib.Specs.Core.OpaqueCpi.Reference
