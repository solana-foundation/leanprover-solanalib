/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OpaqueCpiSdk

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.OpaqueCpi.Reference

open Solanalib.Runtime

/-- A deterministic instance of the external callee processing contract. This
is a mock-boundary dependency, never an SDK invocation implementation. -/
abbrev CalleeFunction := TxState → Frame → Except InstrError TxState

def index (profile : Profile) (primitives : Prims) (context : InvCtx)
    (callee : CalleeFunction) : OpaqueCpi.Index :=
  ⟨profile, primitives, context, fun state frame result => callee state frame = result⟩

/-- Evaluate only the existing mathematical stages and the declared mock
callee. This reference has no source-language invocation or callee body. -/
def evaluate (profile : Profile) (primitives : Prims) (context : InvCtx)
    (callee : CalleeFunction) (before : InvState) (request : CpiReq) :
    Except InstrError InvState := do
  let prepared ← cpiPrepare profile primitives context before.ts request
  let synchronized ← updateCallee profile context before prepared.translated
  let returned ← callee synchronized.ts prepared.callee
  let (after, _) ← updateCaller profile context { synchronized with ts := returned }
    prepared.translated
  return after

theorem Success.evaluates {profile : Profile} {primitives : Prims} {context : InvCtx}
    {callee : CalleeFunction} {before : InvState} {request : CpiReq}
    (success : OpaqueCpi.Success (index profile primitives context callee) before request) :
    evaluate profile primitives context callee before request = .ok success.after := by
  have prepared := success.prepare
  have synchronized := success.synchronize
  have returned := success.execute
  have restored := success.restore
  dsimp only [index] at prepared synchronized returned restored
  simp only [evaluate, bind, Except.bind, prepared, synchronized, returned, restored, pure,
    Except.pure]

theorem Failure.evaluates {profile : Profile} {primitives : Prims} {context : InvCtx}
    {callee : CalleeFunction} {before : InvState} {request : CpiReq} {error : InstrError}
    (failure : OpaqueCpi.Failure (index profile primitives context callee) before request error) :
    evaluate profile primitives context callee before request = .error error := by
  cases failure with
  | prepare failed =>
    dsimp only [index] at failed
    simp only [evaluate, bind, Except.bind, failed]
  | synchronize prepared failed =>
    dsimp only [index] at prepared failed
    simp only [evaluate, bind, Except.bind, prepared, failed]
  | callee prepared synchronized failed =>
    dsimp only [index] at prepared synchronized failed
    simp only [evaluate, bind, Except.bind, prepared, synchronized, failed]
  | restore prepared synchronized returned failed =>
    dsimp only [index] at prepared synchronized returned failed
    simp only [evaluate, bind, Except.bind, prepared, synchronized, returned, failed]

/-- Every result of the evaluator supplies all ordered success/failure
evidence required by the registered relation. -/
theorem evaluated (profile : Profile) (primitives : Prims) (context : InvCtx)
    (callee : CalleeFunction) (before : InvState) (request : CpiReq) :
    match evaluate profile primitives context callee before request with
    | .ok after => ∃ success : OpaqueCpi.Success
        (index profile primitives context callee) before request, success.after = after
    | .error error => OpaqueCpi.Failure
        (index profile primitives context callee) before request error := by
  unfold evaluate
  cases prepared : cpiPrepare profile primitives context before.ts request with
  | error error => exact .prepare prepared
  | ok preparedValue =>
    simp only [bind, Except.bind]
    cases synchronized : updateCallee profile context before preparedValue.translated with
    | error error => exact .synchronize prepared synchronized
    | ok synchronizedValue =>
      dsimp only
      cases returned : callee synchronizedValue.ts preparedValue.callee with
      | error error => exact .callee prepared synchronized returned
      | ok returnedValue =>
        dsimp only
        cases restored : updateCaller profile context
            { synchronizedValue with ts := returnedValue } preparedValue.translated with
        | error error => exact .restore prepared synchronized returned restored
        | ok pair =>
          exact ⟨⟨preparedValue, prepared, synchronizedValue, synchronized, returnedValue,
            returned, pair.1, pair.2, restored⟩, rfl⟩

theorem returned_iff (profile : Profile) (primitives : Prims) (context : InvCtx)
    (callee : CalleeFunction) (before after : InvState) (request : CpiReq) :
    OpaqueCpi.run (index profile primitives context callee) before request
      (.returned () after) ↔ evaluate profile primitives context callee before request =
        .ok after := by
  constructor
  · rintro ⟨success, same⟩
    simpa only [same] using Success.evaluates success
  · intro result
    have witness := evaluated profile primitives context callee before request
    simpa only [result, OpaqueCpi.run] using witness

theorem terminated_iff (profile : Profile) (primitives : Prims) (context : InvCtx)
    (callee : CalleeFunction) (before : InvState) (request : CpiReq) (error : InstrError) :
    OpaqueCpi.run (index profile primitives context callee) before request
      (.terminated error) ↔ error = .ComputationalBudgetExceeded ∨
        evaluate profile primitives context callee before request = .error error := by
  constructor
  · rintro (metered | failure)
    · exact Or.inl metered
    · exact Or.inr (Failure.evaluates failure)
  · rintro (metered | result)
    · exact Or.inl metered
    · have witness := evaluated profile primitives context callee before request
      exact Or.inr (by simpa only [result, OpaqueCpi.run] using witness)

/-- The mathematical reference of the checked SDK, with metering retained as the
separate terminal alternative in the relation. -/
def sdkEvaluate (profile : Profile) (primitives : Prims) (context : InvCtx)
    (callee : CalleeFunction) (before : Sdk.State) (args : Sdk.Args) :
    Outcome Sdk.State (Except ProgramError.Value Unit) Empty InstrError :=
  let (checked, borrows) := Sdk.preflight args.accounts before.borrows args.instruction.metas
  if checked then
    match evaluate profile primitives context callee before.invocation args.runtimeRequest with
    | .ok after => .returned (.ok ()) ⟨after, borrows⟩
    | .error error => .terminated error
  else .returned (.error .accountBorrowFailed) ⟨before.invocation, borrows⟩

theorem sdk_returned_iff (profile : Profile) (primitives : Prims) (context : InvCtx)
    (callee : CalleeFunction) (before after : Sdk.State) (args : Sdk.Args)
    (value : Except ProgramError.Value Unit) :
    Sdk.run (index profile primitives context callee) before args (.returned value after) ↔
      sdkEvaluate profile primitives context callee before args = .returned value after := by
  cases after with
  | mk invocation borrows =>
    cases checked : Sdk.preflight args.accounts before.borrows args.instruction.metas with
    | mk success leases =>
      cases success with
      | false => simp [Sdk.run, Sdk.checkedRun, sdkEvaluate, checked, eq_comm]
      | true =>
        cases evaluated : evaluate profile primitives context callee before.invocation
            args.runtimeRequest with
        | error error =>
          simp [Sdk.run, Sdk.checkedRun, sdkEvaluate, checked, returned_iff, evaluated]
        | ok state =>
          simp [Sdk.run, Sdk.checkedRun, sdkEvaluate, checked, returned_iff, evaluated,
            Sdk.State.mk.injEq, and_comm, and_left_comm, eq_comm]

theorem sdk_terminated_iff (profile : Profile) (primitives : Prims) (context : InvCtx)
    (callee : CalleeFunction) (before : Sdk.State) (args : Sdk.Args) (error : InstrError) :
    Sdk.run (index profile primitives context callee) before args (.terminated error) ↔
      error = .ComputationalBudgetExceeded ∨
        sdkEvaluate profile primitives context callee before args = .terminated error := by
  cases checked : Sdk.preflight args.accounts before.borrows args.instruction.metas with
  | mk success leases =>
    cases success with
    | false => simp [Sdk.run, Sdk.checkedRun, sdkEvaluate, checked]
    | true =>
      simp only [Sdk.run, Sdk.checkedRun, sdkEvaluate, checked, ↓reduceIte,
        Outcome.terminated.injEq, terminated_iff, or_self_left]
      cases evaluated : evaluate profile primitives context callee before.invocation
          args.runtimeRequest with
      | error e => simp [eq_comm]
      | ok state => simp

end Solanalib.Specs.Core.OpaqueCpi.Reference
