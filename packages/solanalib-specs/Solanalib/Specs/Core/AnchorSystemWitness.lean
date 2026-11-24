/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSystemSample

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSystem.Sample

/-- The actual sample metadata destructor preserves every unrelated field. -/
def dropMeta {Program : Type} (state : State Program) (resource : Nat) : State Program :=
  { state with construction := InstructionBuilder.Sample.retireMetas state.construction resource }

/-- The actual sample byte-vector destructor preserves every unrelated field. -/
def dropByte {Program : Type} (state : State Program) (resource : Nat) : State Program :=
  { state with construction := InstructionBuilder.Sample.retireBytes state.construction resource }

/-- One source-ordered pair of Rc drop calls has its exact finite sample exit. -/
theorem dropInfo_returns (Program : Type) (state : State Program) (account : AccountInfo.Value) :
    AnchorSystem.dropInfo (resources Program) account state (.returned () (dropInfoState state
      account)) := by
  refine ⟨.returned () (dropInfoState state account), ?_, rfl⟩
  exact ⟨.returned () (dropRc state .lamports account.lamports), rfl, rfl⟩

private theorem dropReturns_append {State Unwind Terminal : Type}
    {first second : List (Owned.DropAction State Unwind Terminal)}
    {before middle after : State}
    (left : Owned.DropReturns first before middle)
    (right : Owned.DropReturns second middle after) :
    Owned.DropReturns (first ++ second) before after := by
  induction left with
  | nil => exact right
  | cons action rest before middle final head tail induction =>
    exact .cons action (rest ++ second) before middle after head (induction right)

/-- Array/vector elements preserve every owned occurrence through cleanup,
including repeated account aliases. -/
theorem dropInfos_returns (Program : Type) (infos : List AccountInfo.Value)
    (state : State Program) :
    Owned.DropReturns (infos.map (AnchorSystem.dropInfo (resources Program)))
      state (dropInfos state infos) := by
  induction infos generalizing state with
  | nil => exact .nil state
  | cons account rest induction =>
    exact .cons _ _ state (dropInfoState state account) _
      (dropInfo_returns Program state account) (induction _)

/-- Context tail cleanup keeps the release-specific owned program distinction. -/
def afterTail {profile : Profile} {operation : Operation}
    (state : State (profile.Program Nat))
    (input : Args (index profile).resources profile.context operation) : State (profile.Program
      Nat) :=
  match profile, state, input with
  | .inlineLegacy, state, input | .boxedLegacy, state, input =>
    dropInfoState (dropRemaining state input.remaining) input.program
  | .boxedModern, state, input => dropRemaining state input.remaining

/-- The exact remaining-vector and optional program-account destructor trace. -/
theorem tail_returns {profile : Profile} {operation : Operation}
    (state : State (profile.Program Nat))
    (input : Args (index profile).resources profile.context operation) :
    Owned.DropReturns (contextTailDrops input) state (afterTail state input) := by
  cases profile with
  | inlineLegacy =>
    refine .cons _ _ state (dropRemaining state input.remaining) _ rfl ?_
    exact .cons _ [] _ _ _ (dropInfo_returns _ _ input.program) (.nil _)
  | boxedLegacy =>
    refine .cons _ _ state (dropRemaining state input.remaining) _ rfl ?_
    exact .cons _ [] _ _ _ (dropInfo_returns _ _ input.program) (.nil _)
  | boxedModern => exact .cons _ [] state (dropRemaining state input.remaining) _ rfl (.nil _)

/-- Final sample state in exact edition-2021 cleanup order. -/
def afterScope {profile : Profile} {operation : Operation}
    (state : State (profile.Program Nat))
    (input : Args (index profile).resources profile.context operation)
    (value : InstructionBuilder.Value (index profile).resources.types.builder) : State
      (profile.Program Nat) :=
  let instructionDropped := dropByte (dropMeta state value.metas) value.data
  afterTail (dropInfos instructionDropped (movedAccounts input)) input

/-- Metadata, bytes, array occurrences and context tail all have checked
finite exits, with state threaded through every destructor. -/
theorem scope_returns {profile : Profile} {operation : Operation}
    (state : State (profile.Program Nat))
    (input : Args (index profile).resources profile.context operation)
    (value : InstructionBuilder.Value (index profile).resources.types.builder) :
    Owned.DropReturns (invocationDrops input value) state (afterScope state input value) := by
  refine .cons _ _ state (dropMeta state value.metas) _ ?_ ?_
  · exact ⟨.returned () (InstructionBuilder.Sample.retireMetas state.construction value.metas),
    rfl, rfl⟩
  · refine .cons _ _ _ (dropByte (dropMeta state value.metas) value.data) _ ?_ ?_
    · exact ⟨.returned () (InstructionBuilder.Sample.retireBytes
        (dropMeta state value.metas).construction value.data), rfl, rfl⟩
    · exact dropReturns_append (dropInfos_returns _ _ _) (tail_returns _ input)

/-- Actual provider state after recording the full request and one effect. -/
def afterInvoke {profile : Profile} {operation : Operation}
    (state : State (profile.Program Nat))
    (input : Args (index profile).resources profile.context operation) : State (profile.Program
      Nat) :=
  let constructed := afterBuild state input
  { constructed with
    calls := constructed.calls ++ [⟨instruction input, movedAccounts input, input.signerSeeds⟩]
    effects := constructed.effects ++ [70] }

/-- This consistency execution preserves the actual provider mutation through
all later resource cleanup. It is not an assumed SDK/callee success theorem. -/
theorem run_returns {profile : Profile} {operation : Operation}
    (state : State (profile.Program Nat))
    (input : Args (index profile).resources profile.context operation) :
    run (index profile) state input
      (.returned (.ok ()) (afterScope (afterInvoke state input) input (builtValue state))) := by
  apply run_after_build (index profile) input state (afterBuild state input)
    (builtValue state) (.returned (.ok ()) (afterInvoke state input))
  · exact build_returns state input
  · exact invokeAndConvert_ok (index profile) input (builtValue state) _ _ _
      (request_exact state input) rfl
  · exact (scope_returns _ input (builtValue state)).cleanup_returned _ _

/-- Every operation/profile has a concrete admitted initial state. -/
theorem satisfiable (profile : Profile) (operation : Operation) :
    FamilySatisfiable (family profile operation) (index profile) :=
  ⟨before profile, args profile operation, build_ready _ _⟩

/-- One real finite model execution closes the same family/sample witness.
The universal family correctness theorem also covers other providers and all
of their actual error, unwind and terminal outcomes. -/
theorem execution (profile : Profile) (operation : Operation) :
    FamilyHasExecution (family profile operation) (reference profile operation) (index profile) :=
  ⟨before profile, args profile operation,
    .returned (.ok ()) (afterScope (afterInvoke (before profile) (args profile operation))
      (args profile operation) (builtValue (before profile))), build_ready _ _, run_returns _ _⟩

end Solanalib.Specs.Core.AnchorSystem.Sample
