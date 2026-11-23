/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Callback
public import Solanalib.Specs.Core.Family
public import Solanalib.Runtime.Syscall

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.ReturnData

/-- program 4.0.0 dispatches on target_os=solana. A BPF architecture alone
does not select this branch; other targets call the overridable host stub. -/
inductive Target where
  /-- Dispatch to the Solana helper. -/
  | solanaOS
  /-- Dispatch to the overridable host stub of the source. -/
  | hostStub
  deriving DecidableEq, Repr

/-- The selected Solana callee forwards the byte slice and its length to the
void syscall. The host path retains its separately overridable stub identity. -/
inductive Request where
  /-- The complete source slice and forwarded length word. -/
  | solana (data : Solanalib.Runtime.Bytes) (length : UInt64)
  /-- The complete slice passed to the separate host override. -/
  | hostStub (data : Solanalib.Runtime.Bytes)
  deriving DecidableEq, Repr

/-- Neither source wrapper truncates the data or applies the runtime maximum. -/
def request (target : Target) (data : Solanalib.Runtime.Bytes) : Request :=
  match target with
  | .solanaOS => .solana data (UInt64.ofNat data.length)
  | .hostStub => .hostStub data

/-- A Solana request has the canonical value-level return-data meaning. A host
stub is not silently identified with a validator syscall. -/
def Request.canonical : Request → Option Solanalib.Runtime.SysReq
  | .solana data _ => some (.setReturnData data)
  | .hostStub _ => none

universe u v w

/-- Forward the finite outcome and state of the actual callee. The provider includes
its own access, metering, size checks or host override behavior. -/
def run {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (target : Target) (provider : Callback.Run State Request Unit Unwind Terminal) :
    Callback.Run State Solanalib.Runtime.Bytes Unit Unwind Terminal :=
  fun before data outcome => provider before (request target data) outcome

/-- Independent dispatch characterization, including the host stub branch. -/
def post {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (target : Target) (provider : Callback.Run State Request Unit Unwind Terminal)
    (before : State) (data : Solanalib.Runtime.Bytes) (outcome : Outcome State Unit Unwind
      Terminal) : Prop :=
  match target with
  | .solanaOS => provider before (.solana data (UInt64.ofNat data.length)) outcome
  | .hostStub => provider before (.hostStub data) outcome

theorem run_iff_post {State : Type u} {Unwind : Type v} {Terminal : Type w}
    (target : Target) (provider : Callback.Run State Request Unit Unwind Terminal)
    (before : State) (data : Solanalib.Runtime.Bytes) (outcome : Outcome State Unit Unwind
      Terminal) :
    run target provider before data outcome ↔ post target provider before data outcome := by
  cases target <;> rfl

/-- The length cast of the source is exact on its stated 64-bit slice profile. -/
theorem length_exact (data : Solanalib.Runtime.Bytes) (bounded : data.length <
  Solanalib.Runtime.U64_LIMIT) :
    (UInt64.ofNat data.length).toNat = data.length := by
  change data.length % 2^64 = data.length
  exact Nat.mod_eq_of_lt bounded

/-- The canonical runtime enforces its own limit and records the current program
id with the complete bytes. This does not assert that a supplied provider is
that runtime, nor establish pointer translation or compute admission. -/
theorem canonical_step (profile : Solanalib.Runtime.Profile) (primitives : Solanalib.Runtime.Prims)
    (sysvars : Solanalib.Runtime.Sysvars) (epochStake : Option Solanalib.Runtime.Pubkey → Nat)
    (context : Solanalib.Runtime.InvCtx) (state : Solanalib.Runtime.InvState) (data :
      Solanalib.Runtime.Bytes) :
    Solanalib.Runtime.sysStep profile primitives sysvars epochStake context state (.setReturnData
      data) =
      if Solanalib.Runtime.MAX_RETURN_DATA < data.length then .error .ProgramFailedToComplete
      else .ok (.ok0, { state with ts := { state.ts with
        returnData := (state.ts.key context.frame.programIdx, data) } }) := rfl

/-- The cfg and complete callee relation of the source wrapper. -/
structure Index where
  /-- The provider or the ambient state of the host override. -/
  State : Type
  /-- Reasons attached to finite unwinding exits. -/
  Unwind : Type
  /-- Reasons attached to terminal exits. -/
  Terminal : Type
  /-- The actual source cfg branch. -/
  target : Target
  /-- The supplied complete finite-exit callee relation. -/
  provider : Callback.Run State Request Unit Unwind Terminal

/-- Forward every provider outcome without a local length restriction.
Exact length-word equality is the separate `length_exact` result. -/
def family : Family where
  Index := Index
  State := Index.State
  Args := fun _ => Solanalib.Runtime.Bytes
  Value := fun _ => Unit
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := post index.target index.provider
  }

/-- Execute the selected forwarding operation at each model index. -/
def reference : FamilyRun family := fun index => run index.target index.provider

theorem reference_correct : FamilyReference family reference := by
  intro index before data outcome _ execution
  exact (run_iff_post index.target index.provider before data outcome).mp execution

/-- An inhabited argument-recording provider for model consistency. It does not
pretend to apply validator authorization, memory translation or compute checks. -/
def sample : Index where
  State := List Request
  Unwind := String
  Terminal := String
  target := .solanaOS
  provider := Callback.ofFunction fun state call => .returned () (state ++ [call])

theorem sample_hasExecution : FamilyHasExecution family reference sample :=
  ⟨[], [11, 12, 13], .returned () [.solana [11, 12, 13] 3],
    trivial, rfl⟩

end Solanalib.Specs.Core.ReturnData
