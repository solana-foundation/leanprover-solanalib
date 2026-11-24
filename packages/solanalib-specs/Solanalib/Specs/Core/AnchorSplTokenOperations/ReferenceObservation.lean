/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.ReferenceReady

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations.Reference

open Execution

def stateOf {release : Release} {Value Unwind : Type} :
    Outcome (State release) Value Unwind Nat → Option (State release)
  | .returned _ state | .unwound _ state => some state
  | .terminated _ => none

/-- An observation exists only for an actual finite raw wrapper execution. -/
def Observes {binding : Binding} (script : Script binding.release)
    (before : State binding.release) (args : Input (types binding script))
    {Value : Type} (project : Exit (types binding script) → Option Value) (value : Value) : Prop :=
  ∃ final, run (types binding script) before args final ∧ project final = some value

/-- The executable checker decides the projection of the registered relation,
including the possibility that a required read has no result. -/
theorem observes_iff {binding : Binding} (script : Script binding.release)
    (before : State binding.release) (args : Input (types binding script))
    {Value : Type} (project : Exit (types binding script) → Option Value) (value : Value) :
    Observes script before args project value ↔
      (runFn (functions binding script) before args).bind project = some value := by
  constructor
  · rintro ⟨final, called, observed⟩
    rw [(run_iff binding script before args final).mp called]
    exact observed
  · intro observed
    cases computed : runFn (functions binding script) before args with
    | none => simp only [computed, Option.bind_none, reduceCtorEq] at observed
    | some final =>
      exact ⟨final, (run_iff binding script before args final).mpr computed,
        by simpa only [computed, Option.bind_some] using observed⟩

def programErrorOf {binding : Binding} (script : Script binding.release) :
    Exit (types binding script) → Option (binding.release.ProgramError Nat)
  | .returned (.error error) state =>
      match AnchorErrorOperations.currentPayload binding.release.storage (errors script) state
        error with
      | some (.program payload) => some payload.error
      | _ => none
  | _ => none

def returnOf {binding : Binding} {script : Script binding.release} : Exit (types binding script) →
  Option Return
  | .returned (.ok value) _ => some value
  | _ => none

end Solanalib.Specs.Core.AnchorSplTokenOperations.Reference
