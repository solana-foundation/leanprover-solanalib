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

namespace SolanalibTest.Specs.SplToken2022Interface.Instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.Instruction

/-- Distinct authority accounts with repeated signer keys expose metadata order. -/
def authority : AuthorityArgs :=
  ⟨legacyProgramId, .ofNat 1, .ofNat 2, .ofNat 3, [.ofNat 4, .ofNat 4]⟩

/-- A multi-byte amount and maximum decimals byte exercise checked packing. -/
def checked : TransferCheckedArgs := ⟨⟨authority, 513⟩, .ofNat 7, 255⟩

theorem both_ids_accepted :
    checkProgram .either legacyProgramId = .ok () ∧
      checkProgram .either token2022ProgramId = .ok () := by
  constructor <;> rfl

theorem unrelated_id_rejected :
    checkProgram .either .zero = .error .IncorrectProgramId := by
  rfl

/-- Close supports either token program, whereas withdrawal requires Token-2022. -/
theorem withdrawal_and_close_have_different_admission :
    (closeAccount .either authority).map Solanalib.Runtime.CpiInstruction.data = .ok [9] ∧
      withdrawExcessLamports authority = .error .IncorrectProgramId := by
  constructor <;> rfl

theorem withdrawal_encoding :
    (withdrawExcessLamports { authority with programId := token2022ProgramId }).map
      Solanalib.Runtime.CpiInstruction.data = .ok [38] := by
  rfl

theorem checked_order_and_multiplicity :
    (transferChecked .either checked).map (fun value =>
      (value.metas.map Solanalib.Runtime.CpiMeta.key, value.metas.map
        Solanalib.Runtime.CpiMeta.signerByte,
        value.metas.map Solanalib.Runtime.CpiMeta.writableByte)) =
      .ok ([.ofNat 1, .ofNat 7, .ofNat 2, .ofNat 3, .ofNat 4, .ofNat 4],
        [0, 0, 0, 0, 1, 1], [1, 0, 1, 0, 0, 0]) := by
  rfl

/-- A full-range decimals byte is serialized without mint validation. -/
theorem checked_full_decimals_byte :
    (transferChecked .either checked).map Solanalib.Runtime.CpiInstruction.data =
      .ok [12, 1, 2, 0, 0, 0, 0, 0, 0, 255] := by
  rfl

theorem initialize_accepts_legacy :
    (initializeAccount3 .either ⟨legacyProgramId, .ofNat 1, .ofNat 2, .ofNat 3⟩).map
      (fun value => value.metas.map Solanalib.Runtime.CpiMeta.key) = .ok [.ofNat 1, .ofNat 2] := by
  rfl

namespace Allocation

open Solanalib.Specs.Core.Token.InstructionAllocated

/-- The operational plan for the same checked-transfer wire control. -/
def plan : Plan := transferCheckedPlan .either checked

/-- Checked transfer runs its separate decimals push and all six ordered
metadata pushes before transferring the two live resources to its result. -/
theorem checked_execution_observes_full_instruction :
    run Witness.sampleTypes Witness.initialState plan
      (.returned (.ok (Witness.returnedValue plan)) (Witness.returnedState plan)) ∧
    observe Witness.sampleTypes (Witness.returnedState plan) (Witness.returnedValue plan) =
      some (transferCheckedInstruction checked) ∧
    Witness.sampleTypes.bytes.current (Witness.returnedState plan) (0 : Nat) =
      some [12, 1, 2, 0, 0, 0, 0, 0, 0, 255] ∧
    Witness.sampleTypes.metas.current (Witness.returnedState plan) (0 : Nat) =
      some (transferCheckedInstruction checked).metas :=
  ⟨Witness.run_returns plan (by rfl), rfl, rfl, rfl⟩

/-- A visible metadata mutation made by an exceptional primitive provider. -/
def changedMeta : Solanalib.Runtime.CpiMeta :=
  Solanalib.Specs.Core.Instruction.accountMeta (.ofNat 77) false true

/-- The failed push retains complete bytes and its partially changed metadata. -/
def partialState : Witness.State := ([some plan.data], [some [changedMeta]])

/-- A deliberately exceptional dependency interpretation partially modifies
the retained metadata vector before unwinding. Its destructor requires those
current contents; byte cleanup requires metadata retirement to have happened. -/
def partialFailure : Types := { Witness.sampleTypes with
  bytes := { Witness.sampleTypes.bytes with
    drop := fun state resource outcome =>
      Witness.sampleTypes.metas.current state (0 : Nat) = none ∧
        Witness.sampleTypes.bytes.drop state resource outcome }
  metas := { Witness.sampleTypes.metas with
    push := fun state (resource, _) outcome =>
      outcome = .unwound (31 : Nat) (state.1, state.2.set resource (some [changedMeta]))
    drop := fun state resource outcome =>
      Witness.sampleTypes.metas.current state resource = some [changedMeta] ∧
      Witness.sampleTypes.bytes.current state (0 : Nat) = some plan.data ∧
        Witness.sampleTypes.metas.drop state resource outcome } }

/-- The metadata cleanup observes the partial mutation and runs while the
packed byte owner is still live. -/
theorem partial_metadata_cleanup :
    buildMetas partialFailure plan.metas ([some plan.data], []) ()
      (.unwound (31 : Nat) (([some plan.data], [none]) : Witness.State)) := by
  refine Witness.build_metas_reserved
    (pushed := .unwound (31 : Nat) partialState)
    (Witness.metas_capacity [some plan.data] [] 6) ?_ ?_
  · exact ⟨.unwound (31 : Nat) partialState, rfl, rfl⟩
  · exact ⟨.returned () (([some plan.data], [none]) : Witness.State),
      ⟨rfl, rfl, Witness.metas_drop [some plan.data] [changedMeta]⟩, rfl⟩

/-- Both scopes clean up in source order: the current metadata allocation is
retired first, then the already constructed byte allocation. -/
theorem partial_mutation_is_observed_and_cleanup_ordered :
    run partialFailure Witness.initialState plan
      (.unwound (31 : Nat) (([none], [none]) : Witness.State)) := by
  refine Witness.run_from_prepared_data
    (metadata := .unwound (31 : Nat) (([some plan.data], [none]) : Witness.State))
    (by rfl) (by rfl) (Witness.bytes_capacity [] [] Witness.sampleTypes.enumSize)
    (Witness.write_data_returns plan.dataSteps [] []) ?_ ?_
  · exact partial_metadata_cleanup
  · exact ⟨.returned () (([none], [none]) : Witness.State),
      ⟨rfl, Witness.bytes_drop plan.data [none]⟩, rfl⟩

/-- Destructors have no finite exit in this interpretation. A terminal push
must bypass both scopes for the terminal execution witness to exist. -/
def terminalFailure : Types := { Witness.sampleTypes with
  bytes := { Witness.sampleTypes.bytes with drop := fun _ _ _ => False }
  metas := { Witness.sampleTypes.metas with
    push := fun _ _ outcome => outcome = .terminated (41 : Nat)
    drop := fun _ _ _ => False } }

theorem terminal_push_bypasses_both_destructors :
    run terminalFailure Witness.initialState plan (.terminated (41 : Nat)) := by
  refine Witness.run_from_prepared_data
    (metadata := .terminated (41 : Nat)) (by rfl) (by rfl)
    (Witness.bytes_capacity [] [] Witness.sampleTypes.enumSize)
    (Witness.write_data_returns plan.dataSteps [] []) ?_ ?_
  · refine Witness.build_metas_reserved (pushed := .terminated (41 : Nat))
      (Witness.metas_capacity [some plan.data] [] 6) ?_ ?_
    · exact ⟨.terminated (41 : Nat), rfl, rfl⟩
    · rfl
  · rfl

/-- The second unwind consumes the metadata owner. The explicit policy sees
that actual state and both reasons; there is no later byte destructor exit. -/
def doubleFailure : Types := { partialFailure with
  bytes := { partialFailure.bytes with drop := fun _ _ _ => False }
  metas := { partialFailure.metas with
    drop := fun state resource outcome =>
      Witness.sampleTypes.metas.current state resource = some [changedMeta] ∧
        outcome = .unwound (37 : Nat) (state.1, state.2.set resource none) }
  doubleUnwind := fun state original later terminal =>
    state = (([some plan.data], [none]) : Witness.State) ∧
      original = (31 : Nat) ∧ later = (37 : Nat) ∧ terminal = (99 : Nat) }

theorem double_unwind_uses_actual_state_and_policy :
    run doubleFailure Witness.initialState plan (.terminated (99 : Nat)) := by
  refine Witness.run_from_prepared_data
    (metadata := .terminated (99 : Nat)) (by rfl) (by rfl)
    (Witness.bytes_capacity [] [] Witness.sampleTypes.enumSize)
    (Witness.write_data_returns plan.dataSteps [] []) ?_ ?_
  · refine Witness.build_metas_reserved (pushed := .unwound (31 : Nat) partialState)
      (Witness.metas_capacity [some plan.data] [] 6) ?_ ?_
    · exact ⟨.unwound (31 : Nat) partialState, rfl, rfl⟩
    · exact ⟨.unwound (37 : Nat) (([some plan.data], [none]) : Witness.State),
        ⟨rfl, rfl⟩, (99 : Nat), ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  · rfl

/-- Initialization uses the literal metadata branch with an encoded owner. -/
def initializePlan : Plan := initializeAccount3Plan .either Witness.tokenInitialize

/-- InitializeAccount3 uses a metadata literal, not the reserved push branch.
Its exceptional provider still receives the completed 33-byte owner encoding. -/
def literalFailure : Types := { Witness.sampleTypes with
  bytes := { Witness.sampleTypes.bytes with
    drop := fun state resource outcome =>
      Witness.sampleTypes.bytes.current state resource = some initializePlan.data ∧
        Witness.sampleTypes.bytes.drop state resource outcome }
  metas := { Witness.sampleTypes.metas with
    fromList := fun state _ outcome => outcome = .unwound (19 : Nat) state } }

theorem literal_metadata_failure_cleans_owner_encoding :
    run literalFailure Witness.initialState initializePlan
      (.unwound (19 : Nat) (([none], []) : Witness.State)) := by
  refine Witness.run_from_prepared_data
    (metadata := .unwound (19 : Nat) (([some initializePlan.data], []) : Witness.State))
    (by rfl) (by rfl) (Witness.bytes_capacity [] [] Witness.sampleTypes.enumSize)
    (Witness.write_data_returns initializePlan.dataSteps [] []) ?_ ?_
  · rfl
  · exact ⟨.returned () (([none], []) : Witness.State),
      ⟨rfl, Witness.bytes_drop initializePlan.data []⟩, rfl⟩

end Allocation

namespace Withdrawal

open Solanalib.Specs.Core.Token.InstructionAllocated

/-- Primitive events distinguish literal construction, each signer push,
packing and the actual live contents seen by either destructor. -/
inductive Event where
  /-- The source constructs its fixed three-entry metadata literal. -/
  | literal (items : List Solanalib.Runtime.CpiMeta)
  /-- One source signer is appended to the retained metadata vector. -/
  | signerPush (item : Solanalib.Runtime.CpiMeta)
  /-- TokenInstruction::pack requests its byte-vector reservation. -/
  | dataCapacity (capacity : Nat)
  /-- One actual packed byte is pushed. -/
  | dataPush (byte : UInt8)
  /-- Byte destruction observes the current byte and metadata allocations. -/
  | dataDrop (bytes : Option Bytes) (metas : Option (List Solanalib.Runtime.CpiMeta))
  /-- Metadata destruction observes the current metadata and byte allocations. -/
  | metasDrop (metas : Option (List Solanalib.Runtime.CpiMeta)) (bytes : Option Bytes)
  deriving DecidableEq, Repr

/-- Separate live allocation ledgers with a primitive-operation log. -/
structure State where
  /-- Current byte allocations and retirement tombstones. -/
  bytes : Owned.VectorState UInt8 := []
  /-- Current metadata allocations and retirement tombstones. -/
  metas : Owned.VectorState Solanalib.Runtime.CpiMeta := []
  /-- Operations in their actual execution order. -/
  events : List Event := []
  deriving DecidableEq, Repr

/-- A lawful projection onto the byte ledger, preserving metadata and events. -/
def bytesFocus : Owned.Focus State (Owned.VectorState UInt8) where
  get := State.bytes
  set := fun state bytes => { state with bytes }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- A lawful projection onto the metadata ledger, preserving bytes and events. -/
def metasFocus : Owned.Focus State (Owned.VectorState Solanalib.Runtime.CpiMeta) where
  get := State.metas
  set := fun state metas => { state with metas }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- The shared vector reference supplies every actual byte operation. -/
def rawBytes : Owned.VectorOps State UInt8 Nat Nat Nat :=
  Owned.vectorReference.focus bytesFocus

/-- The same reference supplies operations on the distinct metadata ledger. -/
def rawMetas : Owned.VectorOps State Solanalib.Runtime.CpiMeta Nat Nat Nat :=
  Owned.vectorReference.focus metasFocus

/-- Recording an operation preserves its actual resource state. -/
def recordEvent (state : State) (event : Event) : State :=
  { state with events := state.events ++ [event] }

/-- Run the actual primitive before appending its entry observation. A
primitive exception propagates without manufacturing a normal result. -/
def logged {Args Result : Type} (operation : Callback.Run State Args Result Nat Nat)
    (event : State → Args → Event) : Callback.Run State Args Result Nat Nat :=
  fun before args => Callback.bind operation
    (fun value after outcome => outcome = .returned value (recordEvent after (event before args)))
    before args

/-- Byte allocation, writes and destruction retain the shared vector
semantics and append their exact call arguments or current observations. -/
def byteOps : Owned.VectorOps State UInt8 Nat Nat Nat := { rawBytes with
  withCapacity := logged rawBytes.withCapacity (fun _ capacity => .dataCapacity capacity)
  push := logged rawBytes.push (fun _ (_, byte) => .dataPush byte)
  drop := logged rawBytes.drop (fun state resource =>
    .dataDrop (rawBytes.current state resource) (rawMetas.current state 0)) }

/-- Metadata literal construction and each signer push are distinct calls.
Destruction observes the actual current metadata and byte ownership. -/
def metaOps : Owned.VectorOps State Solanalib.Runtime.CpiMeta Nat Nat Nat := { rawMetas with
  fromList := logged rawMetas.fromList (fun _ items => .literal items)
  push := logged rawMetas.push (fun _ (_, item) => .signerPush item)
  drop := logged rawMetas.drop (fun state resource =>
    .metasDrop (rawMetas.current state resource) (rawBytes.current state 0)) }

/-- A concrete event-logged dependency interpretation at the explicit
64-bit witness width and enum reservation 128. -/
def types : Types where
  State := State
  ByteResource := Nat
  MetaResource := Nat
  Unwind := Nat
  Terminal := Nat
  wordBits := 64
  enumSize := 128
  bytes := byteOps
  metas := metaOps
  doubleUnwind := fun _ original later terminal => terminal = original + later

/-- Token-2022 admission and two distinct signers prevent rejected-program
or repeated-key cases from hiding the source order. -/
def args : AuthorityArgs :=
  ⟨token2022ProgramId, .ofNat 1, .ofNat 2, .ofNat 3, [.ofNat 4, .ofNat 5]⟩

/-- The actual corrected withdrawal plan, not a separately invented schedule. -/
def plan : Plan := withdrawExcessLamportsPlan args

/-- The fixed three literal metadata entries of the source. -/
def baseMetas : List Solanalib.Runtime.CpiMeta :=
  [Solanalib.Specs.Core.Instruction.accountMeta (.ofNat 1) false true,
   Solanalib.Specs.Core.Instruction.accountMeta (.ofNat 2) false true,
   Solanalib.Specs.Core.Instruction.accountMeta (.ofNat 3) false false]

/-- First external signer, appended after the literal returns. -/
def firstSigner : Solanalib.Runtime.CpiMeta :=
  Solanalib.Specs.Core.Instruction.accountMeta (.ofNat 4) true false

/-- Second distinct external signer, appended after the first push. -/
def secondSigner : Solanalib.Runtime.CpiMeta :=
  Solanalib.Specs.Core.Instruction.accountMeta (.ofNat 5) true false

/-- All completed metadata, including the ordered signer tail. -/
def allMetas : List Solanalib.Runtime.CpiMeta := baseMetas ++ [firstSigner, secondSigner]

/-- Before admission, neither vector has been allocated. -/
def initialState : State := {}

/-- The literal returns one live metadata owner and no byte owner. -/
def literalState : State :=
  recordEvent { initialState with metas := [some baseMetas] } (.literal baseMetas)

/-- Only the first signer has been appended. -/
def firstSignerState : State :=
  recordEvent { literalState with metas := [some (baseMetas ++ [firstSigner])] }
    (.signerPush firstSigner)

/-- Metadata is complete before TokenInstruction::pack allocates bytes. -/
def metadataState : State :=
  recordEvent { firstSignerState with metas := [some allMetas] } (.signerPush secondSigner)

/-- Packing now owns a fresh empty byte vector while metadata remains live. -/
def allocatedState : State :=
  recordEvent { metadataState with bytes := [some []] } (.dataCapacity 128)

/-- Packing writes tag38 only after all metadata operations. -/
def successfulState : State :=
  recordEvent { allocatedState with bytes := [some [38]] } (.dataPush 38)

/-- Both returned handles retain their actual live typed allocations. -/
def returnedValue : InstructionAllocated.Value types :=
  ⟨token2022ProgramId, (0 : Nat), (0 : Nat)⟩

/-- The logged withdrawal passes the source program-ID check before allocation. -/
theorem admitted :
    checkProgram plan.programs plan.programId = .ok () := rfl

/-- The literal execution uses the actual vector allocation relation. -/
theorem literal_returns :
    types.metas.fromList initialState baseMetas (.returned (0 : Nat) literalState) :=
  ⟨.returned (0 : Nat) { initialState with metas := [some baseMetas] },
    ⟨.returned (0 : Nat) [some baseMetas], rfl, rfl⟩, rfl⟩

/-- The first signer push mutates the actual retained vector. -/
theorem first_signer_returns :
    types.metas.push literalState ((0 : Nat), firstSigner) (.returned () firstSignerState) :=
  ⟨.returned () { literalState with metas := [some (baseMetas ++ [firstSigner])] },
    ⟨.returned () [some (baseMetas ++ [firstSigner])], ⟨baseMetas, rfl, rfl⟩, rfl⟩, rfl⟩

/-- The second distinct signer is pushed after the first, preserving order. -/
theorem second_signer_returns :
    types.metas.push firstSignerState ((0 : Nat), secondSigner) (.returned () metadataState) :=
  ⟨.returned () { firstSignerState with metas := [some allMetas] },
    ⟨.returned () [some allMetas], ⟨baseMetas ++ [firstSigner], rfl, rfl⟩, rfl⟩, rfl⟩

/-- Both signer calls occur after the literal and before packing. -/
theorem signer_pushes_return :
    pushMetas types (0 : Nat) [firstSigner, secondSigner] literalState ()
      (.returned () metadataState) :=
  ⟨.returned () firstSignerState, first_signer_returns,
    .returned () metadataState, second_signer_returns, rfl⟩

/-- The byte allocation executes with the complete metadata vector already live. -/
theorem byte_capacity_returns :
    types.bytes.withCapacity metadataState 128 (.returned (0 : Nat) allocatedState) :=
  ⟨.returned (0 : Nat) { metadataState with bytes := [some []] },
    ⟨.returned (0 : Nat) [some []], rfl, rfl⟩, rfl⟩

/-- The tag push mutates the byte ledger and records its actual argument. -/
theorem tag_push_returns :
    types.bytes.push allocatedState ((0 : Nat), (38 : UInt8))
      (.returned () successfulState) :=
  ⟨.returned () { allocatedState with bytes := [some [38]] },
    ⟨.returned () [some [38]], ⟨[], rfl, rfl⟩, rfl⟩, rfl⟩

/-- The complete actual withdrawal plan executes its literal, each signer
push, byte allocation and tag packing, then transfers both live owners. -/
theorem successful_execution :
    run types initialState plan (.returned (.ok returnedValue) successfulState) := by
  refine Witness.run_from_prepared_metas
    (metas := (0 : Nat)) (prepared := metadataState) (data := .returned (0 : Nat) successfulState)
    admitted rfl ?_ ?_ ?_
  · exact Witness.build_metas_literal_tail literal_returns signer_pushes_return rfl
  · exact Witness.build_data_allocated byte_capacity_returns
      ⟨.returned () successfulState, tag_push_returns, rfl⟩ rfl
  · rfl

/-- The log fixes the successful operation order, and both owned handles
observe exactly the unchanged wire value of the source withdrawal. -/
theorem successful_observations :
    successfulState.events =
      [.literal baseMetas, .signerPush firstSigner, .signerPush secondSigner,
       .dataCapacity 128, .dataPush 38] ∧
    observe types successfulState returnedValue =
      some (authorityInstruction args withdrawExcessLamportsData) ∧
    rawBytes.current successfulState 0 = some [38] ∧
    rawMetas.current successfulState 0 = some allMetas := by
  decide +kernel

/-- The primary withdrawal family has a closed execution at this admitted
logged interpretation, excluding an empty or rejected-only control. -/
theorem has_execution :
    FamilyHasExecution (family AuthorityArgs withdrawExcessLamportsPlan)
      (reference AuthorityArgs withdrawExcessLamportsPlan) types :=
  ⟨initialState, args, .returned (.ok returnedValue) successfulState,
    trivial, successful_execution⟩

/-- A failed first signer push retains its actual appended element before
unwinding. No byte allocation or byte destruction has a finite exit here. -/
def partialMetadataTypes : Types := { types with
  bytes := { byteOps with
    withCapacity := fun _ _ _ => False
    push := fun _ _ _ => False
    drop := fun _ _ _ => False }
  metas := { metaOps with
    push := fun before item =>
      Callback.bind (fun state (_ : Unit) => metaOps.push state item)
        (fun _ after outcome => outcome = .unwound (31 : Nat) after) before () } }

/-- Only the partially populated metadata owner retires on the failed push. -/
def partialMetadataFinal : State :=
  recordEvent { firstSignerState with metas := [none] }
    (.metasDrop (some (baseMetas ++ [firstSigner])) none)

/-- Literal construction precedes the failed signer push. Its actual partial
metadata is destroyed, and the unavailable byte operations are never needed. -/
theorem partial_metadata_failure :
    run partialMetadataTypes initialState plan (.unwound (31 : Nat) partialMetadataFinal) := by
  apply Witness.run_metas_unwound admitted rfl
  refine Witness.build_metas_literal_tail (pushed := .unwound (31 : Nat) firstSignerState)
    literal_returns ?_ ?_
  · exact ⟨.unwound (31 : Nat) firstSignerState,
      ⟨.returned () firstSignerState, first_signer_returns, rfl⟩, rfl⟩
  · exact ⟨.returned () partialMetadataFinal,
      ⟨.returned () { firstSignerState with metas := [none] },
        ⟨.returned () [none], ⟨baseMetas ++ [firstSigner], rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- The failed first signer is present in the destructor observation; the
second signer, byte allocation and tag write never occurred. -/
theorem partial_metadata_observations :
    partialMetadataFinal.events =
      [.literal baseMetas, .signerPush firstSigner,
       .metasDrop (some (baseMetas ++ [firstSigner])) none] ∧
    partialMetadataFinal.bytes = [] ∧ partialMetadataFinal.metas = [none] := by
  decide +kernel

/-- A failed byte reservation has no returned byte token. Its attempt is
recorded after all metadata construction; byte drop is unavailable. -/
def allocationFailureTypes : Types := { types with bytes := { byteOps with
  withCapacity := fun before capacity outcome =>
    outcome = .unwound (41 : Nat) (recordEvent before (.dataCapacity capacity))
  push := fun _ _ _ => False
  drop := fun _ _ _ => False } }

/-- The failed byte-allocation attempt preserves the earlier metadata owner. -/
def allocationFailureState : State := recordEvent metadataState (.dataCapacity 128)

/-- Allocation failure cleans the metadata owner without inventing a byte slot. -/
def allocationFailureFinal : State :=
  recordEvent { allocationFailureState with metas := [none] }
    (.metasDrop (some allMetas) none)

/-- A byte reservation failure follows complete metadata construction and
cleans only that existing owner. No byte destructor can execute. -/
theorem byte_allocation_failure_cleans_metadata :
    run allocationFailureTypes initialState plan (.unwound (41 : Nat) allocationFailureFinal) := by
  refine Witness.run_from_prepared_metas
    (metas := (0 : Nat)) (prepared := metadataState)
    (data := .unwound (41 : Nat) allocationFailureState) admitted rfl ?_ ?_ ?_
  · exact Witness.build_metas_literal_tail literal_returns signer_pushes_return rfl
  · exact ⟨.unwound (41 : Nat) allocationFailureState, rfl, rfl⟩
  · exact ⟨.returned () allocationFailureFinal,
      ⟨.returned () { allocationFailureState with metas := [none] },
        ⟨.returned () [none], ⟨allMetas, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- The allocation-failure trace contains metadata cleanup but no byte write,
byte drop, or byte-vector tombstone. -/
theorem byte_allocation_failure_observations :
    allocationFailureFinal.events =
      [.literal baseMetas, .signerPush firstSigner, .signerPush secondSigner,
       .dataCapacity 128, .metasDrop (some allMetas) none] ∧
    allocationFailureFinal.bytes = [] ∧ allocationFailureFinal.metas = [none] := by
  decide +kernel

/-- The failed tag push performs its actual vector mutation before unwinding,
so cleanup must observe [38], not the old empty allocation. -/
def packingFailureTypes : Types := { types with bytes := { byteOps with
  push := fun before item =>
    Callback.bind (fun state (_ : Unit) => byteOps.push state item)
      (fun _ after outcome => outcome = .unwound (53 : Nat) after) before () } }

/-- The inner byte destructor used by packing retires the mutated bytes first, while
the earlier complete metadata allocation is still live. -/
def packingBytesDropped : State :=
  recordEvent { successfulState with bytes := [none] }
    (.dataDrop (some [38]) (some allMetas))

/-- Only after byte cleanup does the enclosing scope retire earlier metadata. -/
def packingFailureFinal : State :=
  recordEvent { packingBytesDropped with metas := [none] } (.metasDrop (some allMetas) none)

/-- A packing unwind cleans the current byte vector before prior metadata,
which is the reverse of the field drops of a successfully returned Instruction. -/
theorem packing_failure_cleans_data_then_metadata :
    run packingFailureTypes initialState plan (.unwound (53 : Nat) packingFailureFinal) := by
  refine Witness.run_from_prepared_metas
    (metas := (0 : Nat)) (prepared := metadataState)
    (data := .unwound (53 : Nat) packingBytesDropped) admitted rfl ?_ ?_ ?_
  · exact Witness.build_metas_literal_tail literal_returns signer_pushes_return rfl
  · refine Witness.build_data_allocated (written := .unwound (53 : Nat) successfulState)
      byte_capacity_returns ?_ ?_
    · exact ⟨.unwound (53 : Nat) successfulState,
        ⟨.returned () successfulState, tag_push_returns, rfl⟩, rfl⟩
    · exact ⟨.returned () packingBytesDropped,
        ⟨.returned () { successfulState with bytes := [none] },
          ⟨.returned () [none], ⟨[38], rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  · exact ⟨.returned () packingFailureFinal,
      ⟨.returned () { packingBytesDropped with metas := [none] },
        ⟨.returned () [none], ⟨allMetas, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- The data destructor sees the actual the mutation and live
metadata of the failed push; the later metadata destructor sees that bytes have been retired. -/
theorem packing_failure_observations :
    packingFailureFinal.events =
      [.literal baseMetas, .signerPush firstSigner, .signerPush secondSigner,
       .dataCapacity 128, .dataPush 38, .dataDrop (some [38]) (some allMetas),
       .metasDrop (some allMetas) none] ∧
    packingFailureFinal.bytes = [none] ∧ packingFailureFinal.metas = [none] := by
  decide +kernel

/-- The double-unwind policy checks both reasons and the exact state after
the byte destructor; prior metadata must still be live. -/
def doublePolicy : Owned.DoubleUnwind State Nat Nat :=
  fun state original later terminal => state = packingBytesDropped ∧
    original = 53 ∧ later = 59 ∧ terminal = 97

/-- Byte destruction performs its actual retirement and then unwinds. Prior
metadata destruction has no finite exit, so terminal cleanup must bypass it. -/
def doubleTypes : Types := { packingFailureTypes with
  bytes := { packingFailureTypes.bytes with
    drop := fun before resource =>
      Callback.bind (fun state (_ : Unit) => byteOps.drop state resource)
        (fun _ after outcome => outcome = .unwound (59 : Nat) after) before () }
  metas := { metaOps with drop := fun _ _ _ => False }
  doubleUnwind := doublePolicy }

/-- The second unwind terminates at the byte destructor of the packing. The enclosing
metadata owner remains live and its unavailable destructor is never called. -/
theorem second_unwind_stops_before_metadata :
    run doubleTypes initialState plan (.terminated (97 : Nat)) := by
  refine Witness.run_from_prepared_metas
    (metas := (0 : Nat)) (prepared := metadataState) (data := .terminated (97 : Nat))
    admitted rfl ?_ ?_ ?_
  · exact Witness.build_metas_literal_tail literal_returns signer_pushes_return rfl
  · refine Witness.build_data_allocated (written := .unwound (53 : Nat) successfulState)
      byte_capacity_returns ?_ ?_
    · exact ⟨.unwound (53 : Nat) successfulState,
        ⟨.returned () successfulState, tag_push_returns, rfl⟩, rfl⟩
    · exact ⟨.unwound (59 : Nat) packingBytesDropped,
        ⟨.returned () packingBytesDropped,
          ⟨.returned () { successfulState with bytes := [none] },
            ⟨.returned () [none], ⟨[38], rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩,
        (97 : Nat), ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  · rfl

/-- The actual state of the terminal policy records a byte drop but no metadata
drop, and retains the complete earlier metadata owner. -/
theorem second_unwind_observations :
    packingBytesDropped.events =
      [.literal baseMetas, .signerPush firstSigner, .signerPush secondSigner,
       .dataCapacity 128, .dataPush 38, .dataDrop (some [38]) (some allMetas)] ∧
    packingBytesDropped.bytes = [none] ∧ packingBytesDropped.metas = [some allMetas] := by
  decide +kernel

end Withdrawal

end SolanalibTest.Specs.SplToken2022Interface.Instructions
