/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Sysvar

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.Sysvar

open Solanalib.Contracts.Model Solanalib.Specs.Core

def errorBackend (status : UInt64) : Sysvar.GetterIndex Sysvar.Clock where
  State := Nat
  Unwind := String
  Terminal := String
  target := .solana
  read := Callback.ofFunction fun before _ => .returned ⟨status, none⟩ (before + 1)

theorem pin_generic_bounds_error_needs_no_destination :
    Sysvar.get Sysvar.pinClockConfig (errorBackend 1) (4 : Nat) ()
      (.returned (.error .invalidArgument) (5 : Nat)) :=
  ⟨.returned ⟨1, none⟩ (5 : Nat), rfl, rfl⟩

theorem arbitrary_nonzero_status_is_preserved_as_error :
    Sysvar.get Sysvar.pinClockConfig (errorBackend 99) (4 : Nat) ()
      (.returned (.error .unsupportedSysvar) (5 : Nat)) :=
  ⟨.returned ⟨99, none⟩ (5 : Nat), rfl, rfl⟩

theorem uninitialized_success_violates_success_law :
    ¬ Sysvar.GetterReady Sysvar.pinClockConfig (errorBackend 0) (4 : Nat) := by
  intro ready
  obtain ⟨value, initialized⟩ := ready ⟨0, none⟩ (5 : Nat) rfl rfl
  cases initialized

/-- The real finite return of the provider cannot be decoded. Family admission
rejects this backend instead of allowing that local filter to erase its exit. -/
theorem uninitialized_provider_return_is_rejected :
    ¬ ((Sysvar.getterFamily Sysvar.pinClockConfig).contract (errorBackend 0)).requires
        (4 : Nat) () ∧
      (errorBackend 0).read (4 : Nat) (.solana, Sysvar.pinClockConfig.request)
        (.returned ⟨0, none⟩ (5 : Nat)) ∧
      ¬ ∃ outcome, Sysvar.get Sysvar.pinClockConfig (errorBackend 0) (4 : Nat) () outcome := by
  refine ⟨uninitialized_success_violates_success_law, rfl, ?_⟩
  rintro ⟨outcome, exit, read, forwarded⟩
  cases read
  obtain ⟨value, initialized, _⟩ := forwarded
  cases initialized

def invalidClock : Sysvar.Clock := { Sysvar.zeroClock with slot := Solanalib.Runtime.U64_LIMIT }

/-- A present destination is forwarded even when it violates the separate
Clock representation law. The family does not silently filter that return. -/
theorem invalid_initialized_value_has_raw_execution :
    ¬ Sysvar.clockValid invalidClock ∧
      FamilyHasExecution (Sysvar.getterFamily Sysvar.pinClockConfig)
        (Sysvar.getterRun Sysvar.pinClockConfig) (Sysvar.getterSample invalidClock) := by
  refine ⟨?_, Sysvar.getterSample_hasExecution Sysvar.pinClockConfig invalidClock⟩
  intro valid
  exact Nat.lt_irrefl Solanalib.Runtime.U64_LIMIT valid.1

theorem initialized_provider_successes_are_valid :
    ∀ value, Sysvar.get Sysvar.pinClockConfig (Sysvar.getterSample Sysvar.zeroClock)
      () () (.returned (.ok value) ()) → Sysvar.clockValid value := by
  intro value step
  apply Sysvar.get_success_valid Sysvar.pinClockConfig
    (Sysvar.getterSample Sysvar.zeroClock) () () value _ step
  intro reply after actual read _ initialized
  cases read
  cases initialized
  exact Sysvar.zeroClock_valid

/-- The generic existence helper also covers a converter that maps the status of the
sample to an ordinary error. No success-status premise is needed. -/
theorem sample_error_conversion_keeps_error_execution :
    let config : Sysvar.GetterConfig Sysvar.Clock :=
      { Sysvar.pinClockConfig with error := fun _ => some .invalidArgument }
    FamilyHasExecution (Sysvar.getterFamily config) (Sysvar.getterRun config)
        (Sysvar.getterSample Sysvar.zeroClock) ∧
      Sysvar.get config (Sysvar.getterSample Sysvar.zeroClock) () ()
        (.returned (.error .invalidArgument) ()) :=
  ⟨Sysvar.getterSample_hasExecution _ _, ⟨.returned ⟨0, some Sysvar.zeroClock⟩ (), rfl, rfl⟩⟩

def unwindBackend : Sysvar.GetterIndex Sysvar.Clock where
  State := Nat
  Unwind := String
  Terminal := String
  target := .hostStub
  read := Callback.ofFunction fun before _ => .unwound "stub" (before + 2)

theorem host_callback_unwind_remains_in_raw_family :
    FamilyHasExecution (Sysvar.getterFamily Sysvar.pinClockConfig)
      (Sysvar.getterRun Sysvar.pinClockConfig) unwindBackend := by
  refine ⟨(4 : Nat), (), .unwound "stub" (6 : Nat), ?_, ?_⟩
  · intro _ _ read _
    cases read
  · exact ⟨.unwound "stub" (6 : Nat), rfl, rfl⟩

/-- Error statuses never inspect the absent destination. The exact same
finite provider reply witnesses the progress of the admitted getter. -/
theorem nonzero_error_provider_is_admitted (status : UInt64) (nonzero : status ≠ 0) :
    ((Sysvar.getterFamily Sysvar.pinClockConfig).contract (errorBackend status)).requires
        (4 : Nat) () ∧
      ∃ outcome, Sysvar.get Sysvar.pinClockConfig (errorBackend status) (4 : Nat) () outcome := by
  have ready : Sysvar.GetterReady Sysvar.pinClockConfig (errorBackend status) (4 : Nat) := by
    intro reply after read success
    cases read
    simp only [Sysvar.pinClockConfig, Sysvar.genericError, nonzero, ↓reduceIte] at success
    split at success <;> cases success
  exact ⟨ready, (Sysvar.get_hasOutcome_iff _ _ _ ready).2
    ⟨.returned ⟨status, none⟩ (5 : Nat), rfl⟩⟩

def mixedBackend : Sysvar.GetterIndex Sysvar.Clock where
  State := Nat
  Unwind := String
  Terminal := String
  target := .solana
  read := fun before _ outcome =>
    outcome = .returned ⟨0, some Sysvar.zeroClock⟩ (before + 1) ∨
      outcome = .returned ⟨0, none⟩ (before + 2)

/-- One decodable nondeterministic branch does not admit a provider whose
other successful branch loses its destination. -/
theorem mixed_success_provider_is_rejected :
    Sysvar.get Sysvar.pinClockConfig mixedBackend (4 : Nat) ()
        (.returned (.ok Sysvar.zeroClock) (5 : Nat)) ∧
      ¬ ((Sysvar.getterFamily Sysvar.pinClockConfig).contract mixedBackend).requires (4 : Nat) ()
        := by
  refine ⟨⟨.returned ⟨0, some Sysvar.zeroClock⟩ (5 : Nat), Or.inl rfl,
    Sysvar.zeroClock, rfl, rfl⟩, ?_⟩
  intro ready
  obtain ⟨_, impossible⟩ := ready ⟨0, none⟩ (6 : Nat) (Or.inr rfl) rfl
  cases impossible

/-- Admission follows the actual converter, not a hard-coded status-zero
test: a nonzero status classified as success still needs a destination. -/
theorem nonzero_converted_success_needs_initialization :
    let config : Sysvar.GetterConfig Sysvar.Clock :=
      { Sysvar.pinClockConfig with error := fun _ => none }
    ¬ ((Sysvar.getterFamily config).contract (errorBackend 99)).requires (4 : Nat) () := by
  dsimp only
  intro ready
  obtain ⟨_, impossible⟩ := ready ⟨99, none⟩ (5 : Nat) rfl rfl
  cases impossible

/-- Conversely, status zero classified as an ordinary error has a complete
admitted execution even with no initialized destination. -/
theorem zero_converted_error_keeps_uninitialized_reply :
    let config : Sysvar.GetterConfig Sysvar.Clock :=
      { Sysvar.pinClockConfig with error := fun _ => some .invalidArgument }
    ((Sysvar.getterFamily config).contract (errorBackend 0)).requires (4 : Nat) () ∧
      Sysvar.get config (errorBackend 0) (4 : Nat) ()
        (.returned (.error .invalidArgument) (5 : Nat)) := by
  refine ⟨?_, .returned ⟨0, none⟩ (5 : Nat), rfl, rfl⟩
  intro _ _ _ impossible
  cases impossible

def terminalBackend : Sysvar.GetterIndex Sysvar.Clock where
  State := Nat
  Unwind := String
  Terminal := String
  target := .solana
  read := Callback.ofFunction fun _ _ => .terminated "metered"

theorem terminal_provider_is_admitted_and_retained :
    ((Sysvar.getterFamily Sysvar.pinClockConfig).contract terminalBackend).requires (4 : Nat) () ∧
      Sysvar.get Sysvar.pinClockConfig terminalBackend (4 : Nat) () (.terminated "metered") := by
  refine ⟨?_, .terminated "metered", rfl, rfl⟩
  intro _ _ read _
  cases read

def changingBackend : Sysvar.GetterIndex Sysvar.Clock where
  State := Nat
  Unwind := String
  Terminal := String
  target := .solana
  read := Callback.ofFunction fun before _ =>
    .returned ⟨0, some { Sysvar.zeroClock with slot := 7 }⟩ (before + 3)

/-- A stateful admitted read continues with its actual clock and state. The
second callback observes both, so replacing either would change the result. -/
theorem initialized_success_reaches_stateful_continuation :
    ((Sysvar.getterFamily Sysvar.pinClockConfig).contract changingBackend).requires (4 : Nat) () ∧
      Callback.bind (Sysvar.get Sysvar.pinClockConfig changingBackend)
        (fun result (after : Nat) outcome => outcome = .returned
          (match result with | .ok clock => clock.slot + after | .error _ => 0) (after * 2))
        (4 : Nat) () (.returned (14 : Nat) (14 : Nat)) := by
  refine ⟨?_, .returned (.ok { Sysvar.zeroClock with slot := 7 }) (7 : Nat), ?_, rfl⟩
  · intro reply after read _
    cases read
    exact ⟨_, rfl⟩
  · exact ⟨.returned ⟨0, some { Sysvar.zeroClock with slot := 7 }⟩ (7 : Nat), rfl,
      _, rfl, rfl⟩

end SolanalibTest.Specs.Core.Sysvar
