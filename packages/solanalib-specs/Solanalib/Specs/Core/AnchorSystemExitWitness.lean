/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSystemWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSystem.Sample

/-- The exact source-converted error returned at a concrete sample state. -/
def convertedError (profile : Profile) (state : State (profile.Program Nat))
    (program : profile.Program Nat) : Error (index profile) :=
  match profile, state, program with
  | .inlineLegacy, _, program => .program ⟨program, none, none⟩
  | .boxedLegacy, state, _ | .boxedModern, state, _ => ⟨state.boxes.length⟩

/-- Inline conversion has no allocation; boxed conversion appends the full
program error, including an older owned String handle, with absent diagnostics. -/
def afterConversion (profile : Profile) (state : State (profile.Program Nat))
    (program : profile.Program Nat) : State (profile.Program Nat) :=
  match profile, state, program with
  | .inlineLegacy, state, _ => state
  | .boxedLegacy, state, program | .boxedModern, state, program =>
    { state with boxes := state.boxes ++ [some (.program ⟨program, none, none⟩)] }

/-- The fixed conversion in this sample executes exactly once in its actual state. -/
theorem conversion_returns (profile : Profile) (state : State (profile.Program Nat))
    (program : profile.Program Nat) :
    AnchorErrorOperations.fromProgram profile.storage (errors profile) state program
      (.returned (convertedError profile state program) (afterConversion profile state program)) :=
        by
  cases profile with
  | inlineLegacy => rfl
  | boxedLegacy => exact ⟨.returned state.boxes.length _, rfl, rfl⟩
  | boxedModern => exact ⟨.returned state.boxes.length _, rfl, rfl⟩

/-- Read the exact converted payload; a status-code-only replacement or newly
invented String identity cannot satisfy this equation. -/
theorem converted_payload (profile : Profile) (state : State (profile.Program Nat))
    (program : profile.Program Nat) :
    AnchorErrorOperations.currentPayload profile.storage (errors profile)
      (afterConversion profile state program) (convertedError profile state program) =
      some (.program ⟨program, none, none⟩) := by
  cases profile with
  | inlineLegacy => rfl
  | boxedLegacy | boxedModern =>
    simp [AnchorErrorOperations.currentPayload, Profile.storage, convertedError,
      afterConversion, errors]

/-- A full wrapper index whose opaque provider returns a chosen error after
recording the request and preserving its source-visible effect. -/
def errorIndex (profile : Profile) (program : profile.Program Nat) : Index profile :=
  { index profile with
    invoke := Callback.ofFunction fun state current =>
      .returned (.error program)
        { state with calls := state.calls ++ [current], effects := state.effects ++ [70] } }

/-- Actual returned error flow: invocation, conversion, then ordinary cleanup.
Both the moved error and the state of the provider survive into the final result. -/
theorem run_error (profile : Profile) (operation : Operation)
    (program : profile.Program Nat) :
    run (errorIndex profile program) (before profile) (args profile operation)
      (.returned (.error (convertedError profile (afterInvoke (before profile) (args profile
        operation)) program))
        (afterScope (afterConversion profile (afterInvoke (before profile) (args profile
          operation)) program)
          (args profile operation) (builtValue (before profile)))) := by
  apply run_after_build (errorIndex profile program) (args profile operation) (before profile)
    (afterBuild (before profile) (args profile operation)) (builtValue (before profile))
    (.returned (.error (convertedError profile (afterInvoke (before profile) (args profile
      operation)) program))
      (afterConversion profile (afterInvoke (before profile) (args profile operation)) program))
  · exact build_returns _ _
  · exact invokeAndConvert_error (errorIndex profile program) _ _ _ _ _ _ program _
      (request_exact _ _) rfl (conversion_returns _ _ _)
  · exact (scope_returns _ _ _).cleanup_returned _ _

/-- A provider unwind with a changed state; there is no error conversion. -/
def unwindIndex (profile : Profile) (reason : Nat) : Index profile :=
  { index profile with
    invoke := Callback.ofFunction fun state current =>
      .unwound reason { state with calls := state.calls ++ [current], effects := state.effects ++
        [70] } }

/-- Opaque unwind effects survive the exact cleanup trace and retain the
original reason. No success is assumed to supply this witness. -/
theorem run_unwind (profile : Profile) (operation : Operation) (reason : Nat) :
    run (unwindIndex profile reason) (before profile) (args profile operation)
      (.unwound reason (afterScope (afterInvoke (before profile) (args profile operation))
        (args profile operation) (builtValue (before profile)))) := by
  apply run_after_build (unwindIndex profile reason) (args profile operation) (before profile)
    (afterBuild (before profile) (args profile operation)) (builtValue (before profile))
    (.unwound reason (afterInvoke (before profile) (args profile operation)))
  · exact build_returns _ _
  · exact invokeAndConvert_unwind (unwindIndex profile reason) _ _ _ _ _ reason (request_exact _ _)
      rfl
  · exact (scope_returns _ _ _).cleanup_unwound _ reason

/-- A finite terminal provider, with no invented normal result or post-state. -/
def terminalIndex (profile : Profile) (reason : Nat) : Index profile :=
  { index profile with invoke := fun _ _ outcome => outcome = .terminated reason }

/-- Termination stops before scope cleanup; its meaning is supplied by the
opaque provider and is not equated with a successful CPI or an unwind. -/
theorem run_terminal (profile : Profile) (operation : Operation) (reason : Nat) :
    run (terminalIndex profile reason) (before profile) (args profile operation) (.terminated
      reason) := by
  apply run_after_build (terminalIndex profile reason) (args profile operation) (before profile)
    (afterBuild (before profile) (args profile operation)) (builtValue (before profile))
      (.terminated reason)
  · exact build_returns _ _
  · exact invokeAndConvert_terminal (terminalIndex profile reason) _ _ _ _ reason (request_exact _
    _) rfl
  · exact (Owned.cleanup_terminated _ _ _ _).mpr rfl

/-- A provider with no finite outcome cannot be turned into a wrapper success,
error, unwind or terminal result by the constructor or cleanup of the model. -/
def noExitIndex (profile : Profile) : Index profile :=
  { index profile with invoke := fun _ _ _ => False }

/-- Negative control at the complete registered execution relation. -/
theorem no_fabricated_exit (profile : Profile) (operation : Operation)
    (outcome : Outcome (State (profile.Program Nat)) (Except (Error (index profile)) Unit) Nat Nat)
      :
    ¬ run (noExitIndex profile) (before profile) (args profile operation) outcome := by
  rintro ⟨constructed, built, continued⟩
  have exactBuild := (build_exact (before profile) (args profile operation) constructed).mp built
  subst constructed
  obtain ⟨pending, invoked, _⟩ := continued
  unfold invokeAndConvert at invoked
  split at invoked
  · exact invoked
  · obtain ⟨_, impossible, _⟩ := invoked
    exact impossible

end Solanalib.Specs.Core.AnchorSystem.Sample
