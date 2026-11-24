/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Callback
public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.RawSyscall

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-!
# Raw runtime calls with a fixed invocation

These interfaces use the existing runtime model at one fixed `World` and `InvCtx`.
They retain its registration decisions, symbolic primitives and complete request-phase state.
The input buffer of the request is the fixed initial snapshot; source output stores occur after that
phase and may change the actual invocation buffer. They add no runtime behavior or profile.
Source pointer translation, byte ownership, native integer bounds and the copying-memory
interpretation are separate Rust-binding obligations.

An ordinary request result includes its register and each pending buffer write. The source binding
composes the writes with the actual state using `InputWrites`. A terminal error is kept
as an instruction failure; it has no fabricated after-state. Compute exhaustion and translation
faults remain possible in a source implementation under the partial-correctness interface.
-/

namespace Solanalib.Specs.Core.RawRuntime

/-- One runtime environment shared by the raw library interfaces of a caller. -/
structure Index : Type 1 where
  world : Solanalib.Runtime.World
  context : Solanalib.Runtime.InvCtx

/-- Request result, including pending output bytes and the complete request-phase state. -/
abbrev Result := Except Solanalib.Runtime.InstrError (Solanalib.Runtime.SysAns ×
  Solanalib.Runtime.InvState)

/-- An operation is a function of the fixed invocation, initial state and mathematical inputs. -/
abbrev Step (Args : Type) := Index → Solanalib.Runtime.InvState → Args → Result

/-- Apply the unchanged runtime registration check before its request semantics. -/
def invoke (index : Index) (before : Solanalib.Runtime.InvState) (request :
  Solanalib.Runtime.SysReq) : Result :=
  bif request.registered index.world.prof then
    Solanalib.Runtime.sysStep index.world.prof index.world.prims index.world.sysvars
      index.world.epochStake
      index.context before request
  else .error .ProgramFailedToComplete

/-- Convert the exception result of the runtime into the common finite-outcome vocabulary. -/
def outcome : Result → Outcome Solanalib.Runtime.InvState Solanalib.Runtime.SysAns Empty
  Solanalib.Runtime.InstrError
  | .ok (answer, after) => .returned answer after
  | .error error => .terminated error

/-- A callable family; mathematical inputs have no source-representation precondition. -/
def family {Args : Type} (step : Step Args) : Family where
  Index := Index
  State := fun _ => Solanalib.Runtime.InvState
  Args := fun _ => Args
  Value := fun _ => Solanalib.Runtime.SysAns
  Unwind := fun _ => Empty
  Terminal := fun _ => Solanalib.Runtime.InstrError
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before args exit => match exit with
      | .returned answer after => step index before args = .ok (answer, after)
      | .unwound error _ => nomatch error
      | .terminated error => step index before args = .error error }

/-- The total mathematical reference computes the runtime result, without executing Rust. -/
def run {Args : Type} (step : Step Args) : FamilyRun (family step) :=
  fun index before args exit => outcome (step index before args) = exit

/-- The reference and independently stated finite-exit postcondition agree. -/
theorem run_iff {Args : Type} (step : Step Args) (index : Index) (before :
  Solanalib.Runtime.InvState)
    (args : Args) (exit : Outcome Solanalib.Runtime.InvState Solanalib.Runtime.SysAns Empty
      Solanalib.Runtime.InstrError) :
    run step index before args exit ↔ ((family step).contract index).post before args exit := by
  cases exit with
  | unwound reason _ => cases reason
  | returned answer after =>
    cases result : step index before args with
    | error error => simp [run, family, outcome, result]
    | ok pair => rcases pair with ⟨value, state⟩; simp [run, family, outcome, result]
  | terminated error =>
    cases result : step index before args with
    | error reason => simp [run, family, outcome, result]
    | ok pair => rcases pair with ⟨value, state⟩; simp [run, family, outcome, result]

/-- Universal reference correctness, with no hypotheses on the runtime profile. -/
theorem reference {Args : Type} (step : Step Args) : FamilyReference (family step) (run step) :=
  fun index before args exit _ execution => (run_iff step index before args exit).mp execution

/-- For ordinary supported requests, returned answers coincide with the canonical environment. -/
theorem invoke_returned_iff (index : Index) (before after : Solanalib.Runtime.InvState)
    (request : Solanalib.Runtime.SysReq) (ordinary : ∀ q, request ≠ .invoke q)
    (metered : request ≠ .remainingComputeUnits) (answer : Solanalib.Runtime.SysAns) :
    invoke index before request = .ok (answer, after) ↔
      Solanalib.Runtime.Env index.world index.context before request answer after := by
  unfold invoke Solanalib.Runtime.Env
  cases registered : request.registered index.world.prof <;>
    simp [ordinary, metered]

/-- An unavailable request terminates before `sysStep`. -/
theorem invoke_unregistered (index : Index) (before : Solanalib.Runtime.InvState) (request :
  Solanalib.Runtime.SysReq)
    (unregistered : request.registered index.world.prof = false) :
    invoke index before request = .error .ProgramFailedToComplete := by
  simp [invoke, unregistered]

end Solanalib.Specs.Core.RawRuntime
