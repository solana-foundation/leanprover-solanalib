/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaProgram.ReturnData

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaProgram.ReturnData

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- One byte above the validator limit remains a representable source slice. -/
def oversized : Solanalib.Runtime.Bytes := List.replicate 1025 0x5a

/-- The source wrapper forwards the full payload; an override can return from it. -/
theorem oversized_reaches_provider :
    Solanalib.Specs.SolanaProgram.program.set_return_data_model
      Solanalib.Specs.SolanaProgram.program.set_return_data_sample [] oversized
      (.returned () [.solana oversized 1025]) := by
  change (Outcome.returned ()
    [ReturnData.Request.solana oversized (UInt64.ofNat oversized.length)] :
    Outcome (List ReturnData.Request) Unit String String) =
      .returned () [ReturnData.Request.solana oversized 1025]
  simp only [oversized, List.length_replicate]
  rfl

theorem oversized_model_contract :
    (Solanalib.Specs.SolanaProgram.program.set_return_data_contract.contract
      Solanalib.Specs.SolanaProgram.program.set_return_data_sample).ensures [] oversized
      () [.solana oversized 1025] :=
  (FamilyReference.at Solanalib.Specs.SolanaProgram.program.set_return_data_reference
    Solanalib.Specs.SolanaProgram.program.set_return_data_sample)
    [] oversized _ trivial oversized_reaches_provider

/-- Host dispatch preserves its override identity and the same complete bytes. -/
def host : ReturnData.Index := { ReturnData.sample with target := .hostStub }

theorem host_override_runs :
    Solanalib.Specs.SolanaProgram.program.set_return_data_model host [] [6, 7]
      (.returned () [.hostStub [6, 7]]) := rfl

theorem host_has_no_canonical_syscall :
    (ReturnData.request .hostStub [6, 7]).canonical = none ∧
    (ReturnData.request .solanaOS [6, 7]).canonical = some (.setReturnData [6, 7]) :=
  ⟨rfl, rfl⟩

/-- A host override can unwind after retaining effects from the call. -/
def unwinding : ReturnData.Index where
  State := List ReturnData.Request
  Unwind := String
  Terminal := String
  target := .hostStub
  provider := Callback.ofFunction fun before call => .unwound "override" (before ++ [call])

theorem unwind_retains_effects :
    Solanalib.Specs.SolanaProgram.program.set_return_data_model unwinding [] [6, 7]
      (.unwound "override" [.hostStub [6, 7]]) := rfl

/-- A runtime provider may fail terminally; the void wrapper invents no status. -/
def terminating : ReturnData.Index where
  State := Unit
  Unwind := Empty
  Terminal := Solanalib.Runtime.InstrError
  target := .solanaOS
  provider := Callback.ofFunction fun _ _ => .terminated .ProgramFailedToComplete

theorem terminal_failure_is_retained :
    Solanalib.Specs.SolanaProgram.program.set_return_data_model terminating () oversized
      (.terminated .ProgramFailedToComplete) := rfl

/-- The canonical runtime, separately, rejects the full oversized request. -/
theorem canonical_oversized_rejected (profile : Solanalib.Runtime.Profile) (primitives :
  Solanalib.Runtime.Prims)
    (sysvars : Solanalib.Runtime.Sysvars) (epochStake : Option Solanalib.Runtime.Pubkey → Nat)
    (context : Solanalib.Runtime.InvCtx) (state : Solanalib.Runtime.InvState) :
    Solanalib.Runtime.sysStep profile primitives sysvars epochStake context state
      (.setReturnData oversized) = .error .ProgramFailedToComplete := by
  rw [ReturnData.canonical_step]
  simp only [oversized, List.length_replicate, Solanalib.Runtime.MAX_RETURN_DATA, Nat.reduceLT,
    ite_true]

/-- The exact limit is accepted and tagged by the executing program, not a
caller-supplied tag; the rest of the invocation state is retained. -/
theorem canonical_exact_limit (profile : Solanalib.Runtime.Profile) (primitives :
  Solanalib.Runtime.Prims)
    (sysvars : Solanalib.Runtime.Sysvars) (epochStake : Option Solanalib.Runtime.Pubkey → Nat)
    (context : Solanalib.Runtime.InvCtx) (state : Solanalib.Runtime.InvState) :
    Solanalib.Runtime.sysStep profile primitives sysvars epochStake context state
      (.setReturnData (List.replicate 1024 0x5a)) =
      .ok (.ok0, { state with ts := { state.ts with
        returnData := (state.ts.key context.frame.programIdx, List.replicate 1024 0x5a) } }) := by
  rw [ReturnData.canonical_step]
  simp only [List.length_replicate, Solanalib.Runtime.MAX_RETURN_DATA, Nat.lt_irrefl, ite_false]

/-- An empty source slice still reaches the provider. -/
theorem empty_is_forwarded :
    Solanalib.Specs.SolanaProgram.program.set_return_data_model
      Solanalib.Specs.SolanaProgram.program.set_return_data_sample [] []
      (.returned () [.solana [] 0]) := rfl

end SolanalibTest.Specs.SolanaProgram.ReturnData
