/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.CpiRequest
public import Solanalib.Specs.Core.Family
public import Solanalib.Runtime.Frame

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-!
An invocation signature is an assumed interface. These relations use the
existing runtime stages around an explicit callee contract; they do not inspect,
execute or extract an SDK invocation body or a callee implementation.

Only a successful runtime invocation returns. Preparation, synchronization and
callee errors terminate the caller, with no invented state on a failed stage.
The metering alternative records an additional possible runtime abort.
-/

namespace Solanalib.Specs.Core.OpaqueCpi

open Solanalib.Runtime

/-- The external contract of processing one instruction, including the runtime
entry and exit checks of that instruction. It is not an SDK invocation oracle. -/
abbrev Callee := TxState → Frame → Except InstrError TxState → Prop

/-- A runtime configuration and the opaque callee contract. The source binding
separately establishes the pinned runtime profile and current invocation state. -/
structure Index : Type 1 where
  profile : Profile
  primitives : Prims
  context : InvCtx
  callee : Callee

/-- The canonical model instantiates the external contract with `ProcInstr`.
Its program behaviors remain explicit `World.programs` contracts. -/
def canonical (world : World) (context : InvCtx) : Index :=
  ⟨world.prof, world.prims, context, ProcInstr world⟩

/-- A normal invocation exposes all four stages in their actual order. The
callee can change state only as its explicit contract permits. -/
structure Success (index : Index) (before : InvState) (request : CpiReq) where
  prepared : CpiPrep
  prepare : cpiPrepare index.profile index.primitives index.context before.ts request =
    .ok prepared
  synchronized : InvState
  synchronize : updateCallee index.profile index.context before prepared.translated =
    .ok synchronized
  returned : TxState
  execute : index.callee synchronized.ts prepared.callee (.ok returned)
  after : InvState
  lengths : List (Nat × Nat)
  restore : updateCaller index.profile index.context
    { synchronized with ts := returned } prepared.translated = .ok (after, lengths)

/-- The ordinary raw status and each account-info result are the canonical
answer, including first-occurrence copyback and unused infos. -/
def Success.answer {index : Index} {before : InvState} {request : CpiReq}
    (success : Success index before request) : SysAns :=
  cpiAnswer success.after request success.lengths success.prepared.translated

@[simp] theorem Success.status {index : Index} {before : InvState} {request : CpiReq}
    (success : Success index before request) : success.answer.r0 = 0 := rfl

/-- Failure retains the earliest failing canonical stage. Partial mutations
inside a failed stage are not replaced with a fabricated unchanged post-state. -/
inductive Failure (index : Index) (before : InvState) (request : CpiReq) : InstrError → Prop
  | prepare {error : InstrError} :
      cpiPrepare index.profile index.primitives index.context before.ts request = .error error →
      Failure index before request error
  | synchronize {prepared : CpiPrep} {error : InstrError} :
      cpiPrepare index.profile index.primitives index.context before.ts request = .ok prepared →
      updateCallee index.profile index.context before prepared.translated = .error error →
      Failure index before request error
  | callee {prepared : CpiPrep} {synchronized : InvState} {error : InstrError} :
      cpiPrepare index.profile index.primitives index.context before.ts request = .ok prepared →
      updateCallee index.profile index.context before prepared.translated = .ok synchronized →
      index.callee synchronized.ts prepared.callee (.error error) →
      Failure index before request error
  | restore {prepared : CpiPrep} {synchronized : InvState} {returned : TxState}
      {error : InstrError} :
      cpiPrepare index.profile index.primitives index.context before.ts request = .ok prepared →
      updateCallee index.profile index.context before prepared.translated = .ok synchronized →
      index.callee synchronized.ts prepared.callee (.ok returned) →
      updateCaller index.profile index.context { synchronized with ts := returned }
        prepared.translated = .error error →
      Failure index before request error

/-- The invocation boundary, with no unwinding through the runtime. Metering
may abort at any point; no additional normal outcome is introduced. -/
def run (index : Index) (before : InvState) (request : CpiReq) :
    Outcome InvState Unit Empty InstrError → Prop
  | .returned () after => ∃ success : Success index before request, success.after = after
  | .unwound reason _ => nomatch reason
  | .terminated error => error = .ComputationalBudgetExceeded ∨ Failure index before request error

/-- Unit-returning unchecked invocation at the translated request boundary. -/
def unitFamily : Family where
  Index := Index
  State := fun _ => InvState
  Args := fun _ => CpiReq
  Value := fun _ => Unit
  Unwind := fun _ => Empty
  Terminal := fun _ => InstrError
  contract := fun index => { requires := fun _ _ => True, post := run index }

def unitRun : FamilyRun unitFamily := run

theorem unitReference : FamilyReference unitFamily unitRun := by
  intro _ _ _ _ _ execution
  exact execution

/-- Raw declarations return zero after success and otherwise terminate. This
is the on-chain runtime profile, not a nonzero-returning host-stub profile. -/
def rawRun (index : Index) (before : InvState) (request : CpiReq) :
    Outcome InvState UInt64 Empty InstrError → Prop
  | .returned status after => status = 0 ∧ run index before request (.returned () after)
  | .unwound reason _ => nomatch reason
  | .terminated error => run index before request (.terminated error)

def rawFamily : Family where
  Index := Index
  State := fun _ => InvState
  Args := fun _ => CpiReq
  Value := fun _ => UInt64
  Unwind := fun _ => Empty
  Terminal := fun _ => InstrError
  contract := fun index => { requires := fun _ _ => True, post := rawRun index }

def rawFamilyRun : FamilyRun rawFamily := rawRun

theorem rawReference : FamilyReference rawFamily rawFamilyRun := by
  intro _ _ _ _ _ execution
  exact execution

/-- A rejected preparation cannot be mistaken for a successful returned call. -/
theorem no_return_of_prepare_error {index : Index} {before after : InvState}
    {request : CpiReq} {error : InstrError}
    (failed : cpiPrepare index.profile index.primitives index.context before.ts request =
      .error error) : ¬ run index before request (.returned () after) := by
  rintro ⟨success, _⟩
  have prepared := success.prepare
  rw [failed] at prepared
  cases prepared

/-- A normal return has the complete canonical preparation, so a missing
account, seed error or privilege escalation is never a successful invocation. -/
theorem returned_prepared {index : Index} {before after : InvState} {request : CpiReq}
    (returned : run index before request (.returned () after)) :
    ∃ prepared, cpiPrepare index.profile index.primitives index.context before.ts request =
      .ok prepared := by
  obtain ⟨success, _⟩ := returned
  exact ⟨success.prepared, success.prepare⟩

/-- The runtime copyback changes the caller memory view, not the returned transaction account values
of the callee. -/
theorem Success.accounts {index : Index} {before : InvState} {request : CpiReq}
    (success : Success index before request) : success.after.ts = success.returned :=
  updateCaller_ts success.restore

/-- Under the canonical callee contract, ordinary read-only accounts retain
their synchronized values. The Instructions sysvar exception is explicit. -/
theorem Success.readonly {world : World} {context : InvCtx} {before : InvState}
    {request : CpiReq} (success : Success (canonical world context) before request)
    {identity : Nat} (readonly : ¬ WritableTx success.prepared.callee identity)
    (ordinary : ¬ IsIxSysvar success.synchronized.ts.keys identity) :
    success.after.ts.acct identity = success.synchronized.ts.acct identity := by
  rw [success.accounts]
  exact (ProcInstr.frame success.execute _ rfl).other identity
    (fun changed => changed.elim readonly ordinary)

/-- Successful canonical processing preserves the balance invariant of the runtime. -/
theorem Success.balance {world : World} {context : InvCtx} {before : InvState}
    {request : CpiReq} (success : Success (canonical world context) before request) :
    (success.after.ts.lamportSum : Int) - success.after.ts.lamportsDelta =
      success.synchronized.ts.lamportSum - success.synchronized.ts.lamportsDelta := by
  rw [success.accounts]
  exact (ProcInstr.frame success.execute _ rfl).balance

/-- A successful signature contract composes with the existing canonical
invocation trace. It supplies no implementation proof for the source call. -/
theorem Success.execution {world : World} {context : InvCtx} {before : InvState}
    {request : CpiReq} (success : Success (canonical world context) before request)
    {events : List (Event × Reply)} {ending : Final} {result : Except InstrError TxState}
    (rest : Invoke world context success.after events ending result) :
    Invoke world context before ((.sys (.invoke request), .sys success.answer) :: events)
      ending result :=
  Exec.cpi success.prepare success.synchronize success.execute success.restore rest

/-- Every ordinary canonical failure follows the corresponding existing
runtime rule; a failure does not need a fabricated reply or continuation. -/
theorem Failure.execution {world : World} {context : InvCtx} {before : InvState}
    {request : CpiReq} {error : InstrError}
    (failed : Failure (canonical world context) before request error)
    (reply : Reply) (events : List (Event × Reply)) (ending : Final) :
    Invoke world context before ((.sys (.invoke request), reply) :: events) ending
      (.error error) := by
  cases failed with
  | prepare h => exact Exec.cpiPrepareFail h
  | synchronize h h' => exact Exec.cpiCalleeSyncFail h h'
  | callee h h' call => exact Exec.cpiCalleeFail h h' call
  | restore h h' call restore => exact Exec.cpiCallerSyncFail h h' call restore

end Solanalib.Specs.Core.OpaqueCpi
