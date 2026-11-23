/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenInstructionAllocatedFamilyWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SplTokenInterface.Instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.Instruction

/-- Distinct account, mint and owner keys expose the initialization wire order. -/
def initArgs : InitializeAccount3Args :=
  ⟨legacyProgramId, .ofNat 1, .ofNat 2, .ofNat 9⟩

/-- A multi-byte amount and repeated signers expose packing and alias order. -/
def transferArgs : TransferArgs :=
  ⟨⟨legacyProgramId, .ofNat 1, .ofNat 2, .ofNat 3, [.ofNat 4, .ofNat 4, .ofNat 5]⟩, 513⟩

/-- The owner is in wire data, rather than a third instruction account. -/
theorem initialize_owner_and_order :
    (initializeAccount3 .legacy initArgs).map
      (fun value => (value.metas.map Solanalib.Runtime.CpiMeta.key, value.data)) =
      .ok ([.ofNat 1, .ofNat 2], 18 :: (Solanalib.Runtime.Pubkey.ofNat 9).bytes) := by
  rfl

/-- A Token-2022 program ID is rejected by the legacy constructor. -/
theorem legacy_rejects_token2022 :
    initializeAccount3 .legacy { initArgs with programId := token2022ProgramId } =
      .error .IncorrectProgramId := by
  rfl

/-- Repeated multisig signers are retained in their original positions. -/
theorem transfer_duplicates_and_flags :
    (transfer transferArgs).map (fun value =>
      (value.metas.map Solanalib.Runtime.CpiMeta.key, value.metas.map
        Solanalib.Runtime.CpiMeta.signerByte,
        value.metas.map Solanalib.Runtime.CpiMeta.writableByte)) =
      .ok ([.ofNat 1, .ofNat 2, .ofNat 3, .ofNat 4, .ofNat 4, .ofNat 5],
        [0, 0, 0, 1, 1, 1], [1, 1, 0, 0, 0, 0]) := by
  rfl

theorem transfer_little_endian :
    (transfer transferArgs).map Solanalib.Runtime.CpiInstruction.data = .ok [3, 1, 2, 0, 0, 0, 0,
      0, 0] := by
  rfl

/-- Constructor admission does not impose the signer-count validation of the token program. -/
theorem transfer_has_no_constructor_multisig_limit :
    (transfer { transferArgs with signers := List.replicate 12 (.ofNat 4) }).map
      (fun value => value.metas.length) = .ok 15 := by
  rfl

theorem single_authority_is_signer :
    (transfer { transferArgs with signers := [] }).map
      (fun value => value.metas.map Solanalib.Runtime.CpiMeta.signerByte) = .ok [0, 0, 1] := by
  rfl

theorem maximum_amount_is_not_truncated :
    (transfer { transferArgs with amount := 2^64 - 1 }).map Solanalib.Runtime.CpiInstruction.data =
      .ok (3 :: List.replicate 8 255) := by
  rfl

namespace Allocation

open Solanalib.Specs.Core.Token.InstructionAllocated

/-- The operational plan for the same pure transfer control arguments. -/
def plan : Plan := transferPlan transferArgs

/-- This control keeps byte and metadata ownership through the successful
source sequence, while observing the actual wire value of the legacy transfer. -/
theorem successful_ownership_and_value :
    run Witness.sampleTypes Witness.initialState plan
      (.returned (.ok (Witness.returnedValue plan)) (Witness.returnedState plan)) ∧
    observe Witness.sampleTypes (Witness.returnedState plan) (Witness.returnedValue plan) =
      some (authorityInstruction transferArgs.toAuthorityArgs (transferData transferArgs.amount)) ∧
    Witness.sampleTypes.bytes.current (Witness.returnedState plan) (0 : Nat) =
      some [3, 1, 2, 0, 0, 0, 0, 0, 0] ∧
    Witness.sampleTypes.metas.current (Witness.returnedState plan) (0 : Nat) =
      some (authorityInstruction transferArgs.toAuthorityArgs (transferData
        transferArgs.amount)).metas :=
  ⟨Witness.run_returns plan (by rfl), rfl, rfl, rfl⟩

/-- No allocation dependency has a finite exit in this control. Program
rejection must therefore precede every allocation for its witness to exist. -/
def unavailableAllocators : Types := { Witness.sampleTypes with
  bytes := { Witness.sampleTypes.bytes with withCapacity := fun _ _ _ => False }
  metas := { Witness.sampleTypes.metas with
    withCapacity := fun _ _ _ => False
    fromList := fun _ _ _ => False } }

theorem rejected_program_precedes_allocator :
    run unavailableAllocators Witness.initialState { plan with programId := .zero }
      (.returned (.error .IncorrectProgramId) Witness.initialState) := by
  rfl

/-- The first data allocation unwinds before any byte or metadata owner exists. -/
def firstAllocationFails : Types := { unavailableAllocators with
  bytes := { unavailableAllocators.bytes with
    withCapacity := fun before _ outcome => outcome = .unwound (11 : Nat) before } }

/-- A failed first allocation propagates its unwind with no metadata callback
and no fabricated destructor for a vector which never returned an owner. -/
theorem first_allocation_failure :
    run firstAllocationFails Witness.initialState plan
      (.unwound (11 : Nat) Witness.initialState) :=
  Witness.run_capacity_unwound (by rfl) (by rfl) rfl

/-- This exceptional reference has an actual exit, and cannot also admit a
successful instruction or the exit of a later provider. -/
theorem first_allocation_failure_only
    (outcome : Outcome firstAllocationFails.State
      (Except Error (InstructionAllocated.Value firstAllocationFails))
      firstAllocationFails.Unwind firstAllocationFails.Terminal)
    (execution : run firstAllocationFails Witness.initialState plan outcome) :
    outcome = .unwound (11 : Nat) Witness.initialState := by
  unfold run at execution
  have admitted : checkProgram plan.programs plan.programId = .ok () := rfl
  rw [admitted] at execution
  obtain ⟨intermediate, allocated, result⟩ := execution
  change intermediate = .unwound (11 : Nat) Witness.initialState at allocated
  subst intermediate
  exact result

/-- The destructor accepts only the complete current instruction data. A
saved empty vector would fail this control even if its token were unchanged. -/
def metadataAllocationFails : Types := { Witness.sampleTypes with
  bytes := { Witness.sampleTypes.bytes with
    drop := fun state resource outcome =>
      Witness.sampleTypes.bytes.current state resource = some plan.data ∧
        Witness.sampleTypes.bytes.drop state resource outcome }
  metas := { Witness.sampleTypes.metas with
    withCapacity := fun state _ outcome => outcome = .unwound (12 : Nat) state } }

/-- Once all data is packed, a metadata allocation failure drops that current
byte vector; no metadata owner exists for cleanup on this path. -/
theorem metadata_failure_drops_constructed_data :
    run metadataAllocationFails Witness.initialState plan
      (.unwound (12 : Nat) (([none], []) : Witness.State)) := by
  refine Witness.run_from_prepared_data
    (metadata := .unwound (12 : Nat) (([some plan.data], []) : Witness.State)) (by rfl) (by rfl)
    (Witness.bytes_capacity [] [] Witness.sampleTypes.enumSize)
    (Witness.write_data_returns plan.dataSteps [] []) ?_ ?_
  · exact ⟨.unwound (12 : Nat) (([some plan.data], []) : Witness.State), rfl, rfl⟩
  · exact ⟨.returned () (([none], []) : Witness.State),
      ⟨rfl, Witness.bytes_drop plan.data []⟩, rfl⟩

end Allocation

end SolanalibTest.Specs.SplTokenInterface.Instructions
