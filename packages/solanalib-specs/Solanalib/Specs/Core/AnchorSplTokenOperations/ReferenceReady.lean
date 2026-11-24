/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.Reference

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations.Reference

open Execution

theorem copied_current (binding : Binding) (script : Script binding.release)
    (state after : State binding.release) (values : List ExtensionType) (resource : Nat)
    (copied : (types binding script).builder.extensions.copySlice state values (.returned resource
      after)) :
    after.extensions.current resource = some values := by
  change (some (Outcome.returned state.extensions.length
    { state with extensions := state.extensions ++ [some values]
                 events := state.events ++ [.literal .extensions values.length] }) :
      Option (Outcome (State binding.release) Nat Nat Nat)) =
    some (.returned resource after) at copied
  obtain ⟨rfl, rfl⟩ := Outcome.returned.inj (Option.some.inj copied)
  exact Owned.VectorState.allocate_current state.extensions values

theorem build_input_ready (binding : Binding) (script : Script binding.release)
    (state : State binding.release) (input : Construction) :
    BuildInputReady (types binding script).builder state input := by
  cases input with
  | ordinary _ => trivial
  | pointer _ _ => trivial
  | size program mint extensions =>
    intro _ _ allocated _ copied afterCopy execution
    exact ⟨extensions, copied_current binding script allocated afterCopy extensions copied
      execution⟩

theorem returned_current (binding : Binding) (script : Script binding.release)
    (state after : State binding.release) (key : Solanalib.Runtime.Pubkey) (resource : Nat)
    (returned : (types binding script).getReturnData state () (.returned (some (key, resource))
      after)) :
    (types binding script).builder.instruction.bytes.Live after resource := by
  change getReturnDataFn script state () = some (.returned (some (key, resource)) after) at returned
  unfold getReturnDataFn at returned
  cases selected : script.returned with
  | absent => simp only [selected, Option.some.injEq, Outcome.returned.injEq]
    at returned; cases returned.1
  | unwind reason => simp only [selected, Option.some.injEq] at returned; cases returned
  | terminal reason => simp only [selected, Option.some.injEq] at returned; cases returned
  | present program bytes =>
    simp only [selected, Option.some.injEq, Outcome.returned.injEq, Prod.mk.injEq] at returned
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := returned
    exact ⟨bytes, Owned.VectorState.allocate_current state.bytes bytes⟩

/-- A finite check of the exact reached invocation inputs. It is true on
earlier errors, unwinds or terminals because those branches never read them. -/
def requestsReadable (binding : Binding) (script : Script binding.release)
    (state : State binding.release) (args : Input (types binding script)) : Bool :=
  match buildFn (functions binding script) state (argsConstruction args) with
  | some (.returned (.ok instruction) built) =>
      match prepareFn (functions binding script) args built with
      | some (.returned accounts prepared) =>
          (request (types binding script) prepared args instruction accounts).isSome
      | _ => true
  | _ => true

/-- Every finite prefix of the deterministic interpretation is checked. This
is independent of whether the complete wrapper eventually returns. -/
theorem ready_of_requests (binding : Binding) (script : Script binding.release)
    (state : State binding.release) (args : Input (types binding script))
    (checked : requestsReadable binding script state args = true) :
    Ready (types binding script) state args where
  buildInput := build_input_ready binding script state (argsConstruction args)
  requestInput := by
    intro instruction built constructed accounts prepared preparedCall
    have buildEq := (build_graph (functions binding script) (graphs binding script)
      state (argsConstruction args) _).mp constructed
    have prepareEq := (prepare_graph (functions binding script) (graphs binding script)
      args built _).mp preparedCall
    have readable : (request (types binding script) prepared args instruction accounts).isSome =
      true := by
      simpa only [requestsReadable, buildEq, prepareEq] using checked
    apply (request_hasResult_iff (types binding script) prepared args instruction accounts).mp
    cases observed : request (types binding script) prepared args instruction accounts with
    | none => simp only [observed, Option.isSome_none, Bool.false_eq_true] at readable
    | some call => exact ⟨call, rfl⟩
  returnedBytes := by
    intro _ _ _ _ _ _ _ afterInvoke _ data returnedState returned
    exact returned_current binding script afterInvoke returnedState (selectedProgram args) data
      returned

/-- The finite input check is also necessary at this concrete interpretation.
It decides the registered admission predicate, not the existence of a good
completed wrapper outcome. -/
theorem requests_of_ready (binding : Binding) (script : Script binding.release)
    (state : State binding.release) (args : Input (types binding script))
    (ready : Ready (types binding script) state args) :
    requestsReadable binding script state args = true := by
  unfold requestsReadable
  cases built : buildFn (functions binding script) state (argsConstruction args) with
  | none => rfl
  | some produced =>
    cases produced with
    | unwound _ _ | terminated _ => rfl
    | returned value builtState =>
      cases value with
      | error _ => rfl
      | ok instruction =>
        dsimp only
        cases prepared : prepareFn (functions binding script) args builtState with
        | none => rfl
        | some produced =>
          cases produced with
          | unwound _ _ | terminated _ => rfl
          | returned accounts preparedState =>
            have readable := ready.requestInput instruction builtState
              ((build_graph (functions binding script) (graphs binding script) state
                (argsConstruction args) _).mpr built) accounts preparedState
              ((prepare_graph (functions binding script) (graphs binding script) args builtState
                _).mpr prepared)
            obtain ⟨call, current⟩ := (request_hasResult_iff (types binding script) preparedState
              args
              instruction accounts).mpr readable
            dsimp only
            rw [current]
            rfl

theorem ready_iff_requests (binding : Binding) (script : Script binding.release)
    (state : State binding.release) (args : Input (types binding script)) :
    Ready (types binding script) state args ↔ requestsReadable binding script state args = true :=
  ⟨requests_of_ready binding script state args, ready_of_requests binding script state args⟩

end Solanalib.Specs.Core.AnchorSplTokenOperations.Reference
