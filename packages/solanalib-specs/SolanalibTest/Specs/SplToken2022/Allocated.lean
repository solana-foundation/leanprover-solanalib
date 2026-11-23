/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedWitness

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SplToken2022.Allocated

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.OnchainAllocated
open Solanalib.Specs.Core.Token.OnchainAllocated.Witness

/-- A CPI dependency returning an ordinary error after its observable state
effect; collection remains unavailable on this no-hook sample. -/
def errorDependencies : Dependencies sampleTypes where
  collect := unusedCollection
  invoke := returningInvocation (.error .InvalidAccountData)

/-- A CPI error survives every actual destructor. The callback effect is
retained, and its four cloned entries and both instruction vectors are freed. -/
theorem cpi_error_cleans_resources :
    invoke sampleTypes errorDependencies Onchain.witnessArgs initialState
      (.returned (.error .InvalidAccountData) finalState) :=
  invoke_from_prepared errorDependencies _ _ ⟨invocation_ready, rfl⟩
    (prepared_drop_trace.cleanup_returned sampleTypes.doubleUnwind
      (Except.error .InvalidAccountData : Except Error Unit))

/-- An actual unwind from the opaque call, after recording its state effect. -/
def unwindDependencies : Dependencies sampleTypes where
  collect := unusedCollection
  invoke := fun state request outcome => invocationReady state request ∧
    outcome = .unwound (37 : Nat) (invocationAfter state)

/-- Cleanup retains the original CPI unwind reason and its actual state
effect while consuming every temporary owner. -/
theorem cpi_unwind_cleans_resources :
    invoke sampleTypes unwindDependencies Onchain.witnessArgs initialState
      (.unwound (37 : Nat) finalState) :=
  invoke_from_prepared unwindDependencies _ _ ⟨invocation_ready, rfl⟩
    (prepared_drop_trace.cleanup_unwound sampleTypes.doubleUnwind (37 : Nat))

/-- The callback terminates after checking the exact live invocation boundary. -/
def terminalDependencies : Dependencies sampleTypes where
  collect := unusedCollection
  invoke := fun state request outcome => invocationReady state request ∧
    outcome = .terminated (53 : Nat)

/-- A terminal CPI exit stops at the call. No normal or unwinding destructor
execution is needed to derive this complete terminal invocation. -/
theorem cpi_terminal_bypasses_cleanup :
    invoke sampleTypes terminalDependencies Onchain.witnessArgs initialState
      (.terminated (53 : Nat)) :=
  invoke_from_prepared terminalDependencies _ _ ⟨invocation_ready, rfl⟩
    ((Owned.cleanup_terminated sampleTypes.doubleUnwind
      (prepared.drops sampleTypes) (53 : Nat) _).mpr rfl)

/-- The terminal cleanup equation also holds with a first destructor that
has no finite execution, excluding hidden cleanup requirements. -/
theorem terminal_cleanup_needs_no_destructor :
    Owned.cleanup sampleTypes.doubleUnwind
      ([fun _ _ => False] : List (Owned.DropAction State Nat Nat))
      (.terminated (53 : Nat) : Outcome State (Except Error Unit) Nat Nat)
      (.terminated (53 : Nat)) :=
  (Owned.cleanup_terminated sampleTypes.doubleUnwind _ (53 : Nat) _).mpr rfl

/-- A rejected token program still owns its four by-value input arguments. -/
def rejectedArgs : Onchain.Args := { Onchain.witnessArgs with tokenProgramId := .zero }

/-- Only the four original argument owners of the rejected call are retired. -/
def rejectedState : State := dropped arguments initialState

/-- Neither collection nor CPI has a finite execution for this control. -/
def absentDependencies : Dependencies sampleTypes where
  collect := unusedCollection
  invoke := fun _ _ _ => False

/-- Program rejection cleans the moved arguments, allocates no vector and
reaches neither mint borrowing nor the unavailable CPI callback. -/
theorem rejected_program_cleans_arguments :
    invoke sampleTypes absentDependencies rejectedArgs initialState
      (.returned (.error .IncorrectProgramId) rejectedState) := by
  have ready : dropsReady arguments initialState := by
    unfold arguments
    simp only [dropsReady, dropReady, rcReady]
    decide +kernel
  have baseFailed : base sampleTypes rejectedArgs initialState
      (.returned (.error .IncorrectProgramId) initialState) := by
    exact ⟨.returned (.error .IncorrectProgramId) initialState, (by rfl), rfl⟩
  have cleaned : Owned.cleanup sampleTypes.doubleUnwind (argumentDrops sampleTypes rejectedArgs)
      (.returned (.error .IncorrectProgramId) initialState :
        Outcome State (Except Error (Prepared sampleTypes)) Nat Nat)
      (.returned (.error .IncorrectProgramId) rejectedState) :=
    (drop_trace arguments initialState ready).cleanup_returned sampleTypes.doubleUnwind
      (Except.error .IncorrectProgramId : Except Error (Prepared sampleTypes))
  exact ⟨.returned (.error .IncorrectProgramId) rejectedState,
    ⟨.returned (.error .IncorrectProgramId) rejectedState,
      ⟨.returned (.error .IncorrectProgramId) initialState, baseFailed, cleaned⟩, rfl⟩, rfl⟩

/-- The rejected invocation retires only argument owners and performs no call
or allocation, preserving the initially unborrowed account world. -/
theorem rejected_resources :
    rejectedState.1 = Onchain.witnessState ∧
    rejectedState.2.bytes = [] ∧ rejectedState.2.metas = [] ∧
    rejectedState.2.infos = [] ∧ rejectedState.2.lamportsOwners = 1 ∧
    rejectedState.2.dataOwners = 1 ∧ rejectedState.2.rcEvents.length = 8 ∧
    rejectedState.2.invocations = 0 := by
  decide +kernel

/-- Completion unwinds after all indexed expressions returned. It leaves
their owners available for the actual prefix cleanup of the array engine. -/
def failingInfoLiteral : Owned.Array.Provider State AccountInfo.Value Nat Nat Nat :=
  { infoLiteral with finish := fun state _ outcome => outcome = .unwound (61 : Nat) state }

/-- A failing completion shares the same bounded evaluator schedule and
complete cleanup permutation as the normal sample provider. -/
def failingInfoTypes : Types := { sampleTypes with
  infoLiteral := failingInfoLiteral }

/-- The failed literal constructor has destroyed its four moved clones. -/
def arrayDroppedState : State := dropped accounts clone4

/-- The enclosing instruction destructor retires metadata before packed data. -/
def arrayFailureMetasState : State := metasFocus.set arrayDroppedState [none]

/-- The local instruction is gone before outer argument cleanup begins. -/
def arrayFailureLocalsState : State := bytesFocus.set arrayFailureMetasState [none]

/-- The final unwind state has no temporary Rc owners or instruction vectors. -/
def arrayFailureFinalState : State := dropped arguments arrayFailureLocalsState

/-- An info-vector allocation failure cannot call collection or CPI. -/
def failingInfoDependencies : Dependencies failingInfoTypes where
  collect := unusedCollection
  invoke := fun _ _ _ => False

/-- Four indexed clones precede the failing completion. The array engine
destroys those owned outputs exactly once, then retires temporary storage. -/
theorem info_constructor_failure_drops_array :
    initialInfos failingInfoTypes Onchain.witnessArgs instructionState
      (.unwound (61 : Nat) arrayDroppedState) := by
  refine ⟨.unwound (61 : Nat) arrayDroppedState, ?_, rfl⟩
  refine ⟨.unwound (⟨4, .finish⟩, (61 : Nat)) arrayDroppedState, ?_, rfl⟩
  apply literal_four_steps failingInfoTypes.literalProvider rfl
  refine .finishUnwind accounts clone4 clone4 clone4 (61 : Nat) _ rfl ⟨rfl, rfl⟩ rfl ?_
  refine ⟨.refl _, .unwound (61 : Nat) arrayDroppedState, ?_, rfl⟩
  have ready : dropsReady accounts clone4 := by
    unfold accounts
    simp only [List.replicate, dropsReady, dropReady, rcReady]
    decide +kernel
  have trace : Owned.DropReturns
      (accounts.map (dropInfo sampleTypes) ++
        [fun state outcome => outcome = .returned () state]) clone4 arrayDroppedState :=
    drop_trace_append (drop_trace accounts clone4 ready)
      (.cons _ [] arrayDroppedState arrayDroppedState arrayDroppedState rfl (.nil
        arrayDroppedState))
  exact trace.cleanup_unwound failingInfoTypes.doubleUnwind (61 : Nat)

/-- Failed array construction leaves the instruction alive for its enclosing
scope, which executes both field destructors in source order. -/
theorem array_failure_instruction_trace :
    Owned.DropReturns (instructionDrops failingInfoTypes (ownedInstruction plan))
      arrayDroppedState arrayFailureLocalsState := by
  refine .cons _ _ arrayDroppedState arrayFailureMetasState arrayFailureLocalsState ?_
    (.cons _ _ arrayFailureMetasState arrayFailureLocalsState arrayFailureLocalsState ?_
      (.nil arrayFailureLocalsState))
  · exact ⟨.returned () [none], ⟨plan.metas.items, rfl, rfl⟩, rfl⟩
  · exact ⟨.returned () [none], ⟨plan.data, rfl, rfl⟩, rfl⟩

/-- The full invocation unwinds before mint borrowing or CPI, after array,
instruction and original-argument cleanup. No cloned owner is dropped twice. -/
theorem info_allocation_failure_cleans_every_owner :
    invoke failingInfoTypes failingInfoDependencies Onchain.witnessArgs initialState
      (.unwound (61 : Nat) arrayFailureFinalState) := by
  have baseFailed : base failingInfoTypes Onchain.witnessArgs initialState
      (.unwound (61 : Nat) arrayFailureLocalsState) := by
    refine ⟨.returned (.ok (ownedInstruction plan)) instructionState,
      constructor_returns initialState plan rfl rfl (by rfl), ?_⟩
    exact ⟨.unwound (61 : Nat) arrayDroppedState,
      ⟨.unwound (61 : Nat) arrayDroppedState, info_constructor_failure_drops_array, rfl⟩,
      array_failure_instruction_trace.cleanup_unwound failingInfoTypes.doubleUnwind (61 : Nat)⟩
  have ready : dropsReady arguments arrayFailureLocalsState := by
    unfold arguments
    simp only [dropsReady, dropReady, rcReady]
    decide +kernel
  have cleaned : Owned.cleanup failingInfoTypes.doubleUnwind
      (argumentDrops failingInfoTypes Onchain.witnessArgs)
      (.unwound (61 : Nat) arrayFailureLocalsState :
        Outcome State (Except Error (Prepared failingInfoTypes)) Nat Nat)
      (.unwound (61 : Nat) arrayFailureFinalState) :=
    (drop_trace arguments arrayFailureLocalsState ready).cleanup_unwound
      failingInfoTypes.doubleUnwind (61 : Nat)
  exact ⟨.unwound (61 : Nat) arrayFailureFinalState,
    ⟨.unwound (61 : Nat) arrayFailureFinalState,
      ⟨.unwound (61 : Nat) arrayFailureLocalsState, baseFailed, cleaned⟩, rfl⟩, rfl⟩

/-- Failed info construction never allocated an info slot or acquired a mint
guard. All eight temporary account owners are retired and no CPI ran. -/
theorem info_allocation_failure_resources :
    arrayFailureFinalState.1 = Onchain.witnessState ∧
    arrayFailureFinalState.2.bytes = [none] ∧
    arrayFailureFinalState.2.metas = [none] ∧ arrayFailureFinalState.2.infos = [] ∧
    arrayFailureFinalState.2.lamportsOwners = 1 ∧
    arrayFailureFinalState.2.dataOwners = 1 ∧
    arrayFailureFinalState.2.rcEvents.length = 24 ∧
    arrayFailureFinalState.2.invocations = 0 := by
  decide +kernel

/-- An explicit constructor schedule may unwind at any chosen evaluated
prefix, including before the first expression. Earlier work is the normal
sample schedule; it does not manufacture an element at the failing boundary. -/
def interruptedLiteral (completed reason : Nat) :
    Owned.Array.Provider State AccountInfo.Value Nat Nat Nat := { infoLiteral with
  work := fun before (count, values) outcome =>
    if values.length = completed then outcome = .unwound reason before
    else infoLiteral.work before (count, values) outcome }

/-- Source types using that explicit early or partial constructor failure. -/
def interruptedTypes (completed reason : Nat) : Types := { sampleTypes with
  infoLiteral := interruptedLiteral completed reason }

/-- No collection or CPI exit can hide a missed early-construction failure. -/
def interruptedDependencies (completed reason : Nat) :
    Dependencies (interruptedTypes completed reason) where
  collect := unusedCollection
  invoke := fun _ _ _ => False

/-- Array work may fail before even the first AccountInfo clone. Only the storage retirement of the
empty prefix runs inside the array engine. -/
theorem initial_literal_can_fail_before_any_clone :
    initialInfos (interruptedTypes 0 67) Onchain.witnessArgs instructionState
      (.unwound (67 : Nat) instructionState) := by
  refine ⟨.unwound (67 : Nat) instructionState, ?_, rfl⟩
  refine ⟨.unwound (⟨0, .work⟩, (67 : Nat)) instructionState, ?_, rfl⟩
  refine .workUnwind [] instructionState instructionState (67 : Nat) _ rfl ?_
  refine ⟨.refl _, .unwound (67 : Nat) instructionState, ?_, rfl⟩
  exact ⟨.returned () instructionState, rfl, rfl⟩

/-- Metadata retirement after an initial literal failure before all clones. -/
def earlyMetasState : State := metasFocus.set instructionState [none]

/-- Both constructed instruction fields retire before original arguments. -/
def earlyLocalsState : State := bytesFocus.set earlyMetasState [none]

/-- The early failure consumes only the four originally moved function inputs. -/
def earlyFinalState : State := dropped arguments earlyLocalsState

/-- A complete invocation can fail before any clone while still dropping
its already constructed instruction and original inputs in source order. -/
theorem early_literal_failure_cleans_instruction_then_inputs :
    invoke (interruptedTypes 0 67) (interruptedDependencies 0 67)
      Onchain.witnessArgs initialState (.unwound (67 : Nat) earlyFinalState) := by
  have locals : Owned.DropReturns
      (instructionDrops (interruptedTypes 0 67) (ownedInstruction plan))
      instructionState earlyLocalsState := by
    refine .cons _ _ instructionState earlyMetasState earlyLocalsState ?_
      (.cons _ _ earlyMetasState earlyLocalsState earlyLocalsState ?_ (.nil earlyLocalsState))
    · exact ⟨.returned () [none], ⟨plan.metas.items, rfl, rfl⟩, rfl⟩
    · exact ⟨.returned () [none], ⟨plan.data, rfl, rfl⟩, rfl⟩
  have baseFailed : base (interruptedTypes 0 67) Onchain.witnessArgs initialState
      (.unwound (67 : Nat) earlyLocalsState) := by
    refine ⟨.returned (.ok (ownedInstruction plan)) instructionState,
      constructor_returns initialState plan rfl rfl (by rfl), ?_⟩
    exact ⟨.unwound (67 : Nat) instructionState,
      ⟨.unwound (67 : Nat) instructionState, initial_literal_can_fail_before_any_clone, rfl⟩,
      locals.cleanup_unwound sampleTypes.doubleUnwind (67 : Nat)⟩
  have ready : dropsReady arguments earlyLocalsState := by
    unfold arguments
    simp only [dropsReady, dropReady, rcReady]
    decide +kernel
  have inputs : Owned.cleanup (interruptedTypes 0 67).doubleUnwind
      (argumentDrops (interruptedTypes 0 67) Onchain.witnessArgs)
      (.unwound (67 : Nat) earlyLocalsState :
        Outcome State (Except Error (Prepared (interruptedTypes 0 67))) Nat Nat)
      (.unwound (67 : Nat) earlyFinalState) :=
    (drop_trace arguments earlyLocalsState ready).cleanup_unwound sampleTypes.doubleUnwind (67 :
      Nat)
  exact ⟨.unwound (67 : Nat) earlyFinalState,
    ⟨.unwound (67 : Nat) earlyFinalState,
      ⟨.unwound (67 : Nat) earlyLocalsState, baseFailed, inputs⟩, rfl⟩, rfl⟩

/-- No cloned owner, account-vector allocation, mint guard or CPI appears in
the early failure; its eight Rc events are exactly the original input drops. -/
theorem early_literal_failure_resources :
    earlyFinalState.1 = Onchain.witnessState ∧
    earlyFinalState.2.bytes = [none] ∧ earlyFinalState.2.metas = [none] ∧
    earlyFinalState.2.infos = [] ∧ earlyFinalState.2.lamportsOwners = 1 ∧
    earlyFinalState.2.dataOwners = 1 ∧ earlyFinalState.2.rcEvents.length = 8 ∧
    earlyFinalState.2.invocations = 0 := by
  decide +kernel

/-- Four distinct cell pairs distinguish an evaluated owner from an original
argument that has not yet moved into the literal of Execute. -/
def executeInfo (index : Nat) : AccountInfo.Value := { Onchain.witnessInfo with
  lamports := ⟨2 * index⟩
  data := ⟨2 * index + 1⟩
  ownerRef := ⟨index⟩ }

/-- Each selected pair contains real lamports and initialized mint bytes,
and no lease is live during these local construction controls. -/
def executeWorld : AccountInfo.State :=
  ⟨(List.replicate 4 Onchain.witnessState.cells).flatten, []⟩

/-- The four source argument roles have separate Rc cell identities. -/
def executeArgs : Onchain.Args := { Onchain.witnessArgs with
  source := executeInfo 0
  mint := executeInfo 1
  destination := executeInfo 2
  authority := executeInfo 3 }

/-- Each of the four field cells starts with one moved argument owner and
one outside owner. The aggregate counts are eight per field. -/
def executeInitialState : State :=
  (executeWorld, { lamportsOwners := 8, dataOwners := 8 })

/-- A real checked-transfer construction supplies the retained instruction
whose fields must drop before the outer unmoved arguments. -/
def executePlan : InstructionAllocated.Plan := transferPlan executeArgs

/-- Both instruction vectors are live before the literal work of Execute begins. -/
def executeInstructionState : State := constructed executeInitialState executePlan

/-- The account world with four separate cell pairs has no dangling guard or
conflicting lease. -/
theorem execute_world_valid : executeWorld.Valid := by
  constructor
  · intro id slot found
    simp [Borrow.State.lookupSlot, executeWorld] at found
  · intro handle cell found
    simp only [Borrow.State.exclusiveCount, Borrow.State.sharedCount, Borrow.State.count,
      executeWorld, List.countP_nil]
    exact ⟨by decide, by decide, Nat.zero_le _⟩

/-- Each selected AccountInfo has distinct correctly typed cells and a
representable initialized data payload. -/
theorem execute_info_valid (index : Nat) (selected : index ∈ [0, 1, 2, 3]) :
    AccountInfo.Valid AccountInfo.sampleProfile executeWorld (executeInfo index) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl
  all_goals
    refine ⟨by decide, execute_world_valid, by decide, ⟨40, rfl⟩,
      ⟨Onchain.witnessMintBytes, rfl, by decide⟩⟩

/-- The distinguishing source arguments satisfy the same account and width
admission as the positive no-hook family sample. -/
theorem execute_args_valid : executeArgs.Valid executeWorld := by
  refine ⟨by decide, ?_, ?_, by decide, ?_⟩
  · change 1 < Solanalib.Runtime.U64_LIMIT
    decide
  · change 0 < 256
    decide
  · intro info member
    change info ∈ [executeInfo 0, executeInfo 1, executeInfo 2, executeInfo 3] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals
      exact ⟨execute_info_valid _ (by decide), Onchain.witnessMintBytes, rfl, by decide⟩

/-- The retained byte and metadata allocations arise from the shared
operational constructor, not from an assumed whole-constructor callback. -/
theorem execute_instruction_constructed :
    InstructionAllocated.run sampleTypes.constructor executeInitialState executePlan
      (.returned (.ok (ownedInstruction executePlan)) executeInstructionState) :=
  constructor_returns executeInitialState executePlan rfl rfl rfl

/-- Append one observable destructor event without changing resources. -/
def recordCleanup (state : State) (event : CleanupEvent) : State :=
  (state.1, { state.2 with cleanupEvents := state.2.cleanupEvents ++ [event] })

/-- The four represented Rc cells of each source field are separate owners. -/
def executeCells : AccountInfoRc.Field → List Borrow.Handle
  | .lamports => [⟨0⟩, ⟨2⟩, ⟨4⟩, ⟨6⟩]
  | .data => [⟨1⟩, ⟨3⟩, ⟨5⟩, ⟨7⟩]

/-- This partial witness permits at most the two actual initial owners of
each represented cell to drop; it supplies no clone or overflow semantics. -/
def executeRcReady (state : State) (field : AccountInfoRc.Field)
    (cell : Borrow.Handle) : Prop :=
  cell ∈ executeCells field ∧
    state.2.rcEvents.count (.drop field cell) < 2 ∧ 0 < ownerCount state.2 field

/-- Consume one actual owner and record both its identity and whether the
retained instruction is still live at this exact destructor call. -/
def executeRcAfter (state : State) (field : AccountInfoRc.Field)
    (cell : Borrow.Handle) : State :=
  recordCleanup (rcAfter false state field cell)
    (.accountDrop field cell (bytesOps.current state 0).isSome (metasOps.current state 0).isSome)

/-- Only actual represented owners have a finite drop. No fifth-expression
clone can occur in these controls, which interrupt an earlier literal prefix. -/
def executeRcOps : AccountInfoRc.Ops State Nat where
  cloneRc := fun _ _ _ => False
  dropRc := fun state (field, cell) outcome =>
    executeRcReady state field cell ∧ outcome = .returned () (executeRcAfter state field cell)

/-- Metadata drops execute the shared vector destructor before recording
their completion, preserving its actual returned state. -/
def executeMetasOps : Owned.VectorOps State Solanalib.Runtime.CpiMeta Nat Nat Nat := { metasOps with
  drop := fun before resource outcome =>
    Callback.bind (fun state (_ : Unit) => metasOps.drop state resource)
      (fun _ state result => result = .returned () (recordCleanup state .metadataDrop))
      before () outcome }

/-- Byte drops likewise execute the shared vector destructor before their
observable completion event. -/
def executeBytesOps : Owned.VectorOps State UInt8 Nat Nat Nat := { bytesOps with
  drop := fun before resource outcome =>
    Callback.bind (fun state (_ : Unit) => bytesOps.drop state resource)
      (fun _ state result => result = .returned () (recordCleanup state .byteDrop))
      before () outcome }

/-- The selected prefix failure also observes the storage
retirement call of the provider. This fixture has no separately allocated literal storage. -/
def executeLiteral (completed : Nat) : Owned.Array.Provider State AccountInfo.Value Nat Nat Nat :=
  { interruptedLiteral completed 73 with
    retire := fun before _ outcome => outcome = .returned () (recordCleanup before .literalRetire) }

/-- An explicit partial-literal family member combines the indexed schedule,
actual AccountInfo destructor, and observed instruction-field destructors. -/
def executeTypes (completed : Nat) : Types := { interruptedTypes completed 73 with
  rc := executeRcOps
  bytes := executeBytesOps
  metas := executeMetasOps
  infoLiteral := executeLiteral completed }

/-- Both AccountInfo fields drop in their ordinary declaration order. -/
def executeDropAfter (state : State) (info : AccountInfo.Value) : State :=
  executeRcAfter (executeRcAfter state .lamports info.lamports) .data info.data

/-- Each field drop is checked in the state left by the preceding field. -/
def executeDropReady (state : State) (info : AccountInfo.Value) : Prop :=
  executeRcReady state .lamports info.lamports ∧
    executeRcReady (executeRcAfter state .lamports info.lamports) .data info.data

/-- The concrete lifted ordinary AccountInfo destructor used by the controls. -/
def executeDropInfo (info : AccountInfo.Value) : Owned.DropAction State Nat Nat :=
  fun state => AccountInfoRc.lift (AccountInfoRc.dropCall executeRcOps) state info

/-- The ordinary AccountInfo composition executes both actual Rc calls. -/
theorem execute_drop_returns (state : State) (info : AccountInfo.Value)
    (ready : executeDropReady state info) :
    executeDropInfo info state (.returned () (executeDropAfter state info)) :=
  ⟨.returned () (executeDropAfter state info),
    ⟨.returned () (executeRcAfter state .lamports info.lamports), ⟨ready.1, rfl⟩,
      ⟨ready.2, rfl⟩⟩, rfl⟩

/-- Thread the actual source-ordered destructor state changes. -/
def executeDropped : List AccountInfo.Value → State → State
  | [], state => state
  | info :: rest, state => executeDropped rest (executeDropAfter state info)

/-- Every selected destructor consumes a still-owned cell in its current state. -/
def executeDropsReady : List AccountInfo.Value → State → Prop
  | [], _ => True
  | info :: rest, state => executeDropReady state info ∧
      executeDropsReady rest (executeDropAfter state info)

/-- A sequence of actual Rc destructor executions exposes all intermediate
states to the later literal or instruction cleanup. -/
theorem execute_drop_trace (infos : List AccountInfo.Value) (state : State)
    (ready : executeDropsReady infos state) :
    Owned.DropReturns (infos.map executeDropInfo) state (executeDropped infos state) := by
  induction infos generalizing state with
  | nil => exact .nil state
  | cons info rest induction =>
    exact .cons _ _ state (executeDropAfter state info)
      (executeDropped rest (executeDropAfter state info))
      (execute_drop_returns state info ready.1) (induction (executeDropAfter state info) ready.2)

/-- Source and mint have moved into the literal; destination and authority
remain outer-scope owners. -/
def executePrefix : List AccountInfo.Value := [executeInfo 0, executeInfo 1]

/-- Evaluated array elements drop while both instruction vectors are live. -/
def executePrefixDropped : State := executeDropped executePrefix executeInstructionState

/-- Literal storage retirement follows the last evaluated-element drop. -/
def executeArrayDropped : State := recordCleanup executePrefixDropped .literalRetire

/-- The earlier instruction metadata field then retires. -/
def executeMetasDropped : State :=
  recordCleanup (metasFocus.set executeArrayDropped [none]) .metadataDrop

/-- The earlier instruction byte field retires before any unmoved argument. -/
def executeInstructionDropped : State :=
  recordCleanup (bytesFocus.set executeMetasDropped [none]) .byteDrop

/-- Only authority and destination are still owned by the outer scope,
and its reverse declaration order is preserved. -/
def executeRemaining : List AccountInfo.Value := [executeInfo 3, executeInfo 2]

/-- Every moved original has now dropped exactly once; outside owners remain. -/
def executeFinalState : State := executeDropped executeRemaining executeInstructionDropped

/-- The two completed moves and their normally returning prefix cleanup do
not depend on the surrounding double-unwind policy. -/
theorem execute_partial_literal_trace_with_policy
    (double : Owned.DoubleUnwind State Nat Nat) :
    ({ (executeTypes 2).literalProvider with double := double } :
      Owned.Array.Provider State AccountInfo.Value Nat Nat Nat).runDetailed 5
      (executeInfoAt (executeTypes 2) executeArgs (executeInfo 0)) executeInstructionState
      (.unwound (⟨2, .work⟩, (73 : Nat)) executeArrayDropped) := by
  refine .next [] executeInstructionState executeInstructionState executeInstructionState
    (executeInfo 0) _ (by decide) rfl rfl ?_
  refine .next [executeInfo 0] executeInstructionState executeInstructionState
    executeInstructionState
    (executeInfo 1) _ (by decide) rfl rfl ?_
  refine .workUnwind executePrefix executeInstructionState executeInstructionState (73 : Nat) _ rfl
    ?_
  refine ⟨.refl _, .unwound (73 : Nat) executeArrayDropped, ?_, rfl⟩
  have ready : executeDropsReady executePrefix executeInstructionState := by
    unfold executePrefix
    simp only [executeDropsReady, executeDropReady, executeRcReady]
    decide +kernel
  have trace : Owned.DropReturns
      (executePrefix.map executeDropInfo ++
        [fun state outcome => outcome = .returned () (recordCleanup state .literalRetire)])
      executeInstructionState executeArrayDropped :=
    drop_trace_append (execute_drop_trace executePrefix executeInstructionState ready)
      (.cons _ [] executePrefixDropped executeArrayDropped executeArrayDropped rfl
        (.nil executeArrayDropped))
  exact trace.cleanup_unwound double (73 : Nat)

/-- Two pure indexed moves precede the actual constructor-work unwind.
The array engine destroys just those evaluated owners and then its storage. -/
theorem execute_partial_literal_trace :
    (executeTypes 2).literalProvider.runDetailed 5
      (executeInfoAt (executeTypes 2) executeArgs (executeInfo 0)) executeInstructionState
      (.unwound (⟨2, .work⟩, (73 : Nat)) executeArrayDropped) :=
  execute_partial_literal_trace_with_policy (executeTypes 2).doubleUnwind

/-- The enclosing instruction drops metadata then data, threading both real
vector retirements and their ordered observations. -/
theorem execute_instruction_drop_trace :
    Owned.DropReturns (instructionDrops (executeTypes 2) (ownedInstruction executePlan))
      executeArrayDropped executeInstructionDropped := by
  refine .cons _ _ executeArrayDropped executeMetasDropped executeInstructionDropped ?_
    (.cons _ _ executeMetasDropped executeInstructionDropped executeInstructionDropped ?_
      (.nil executeInstructionDropped))
  · exact ⟨.returned () (metasFocus.set executeArrayDropped [none]),
      ⟨.returned () [none], ⟨executePlan.metas.items, rfl, rfl⟩, rfl⟩, rfl⟩
  · exact ⟨.returned () (bytesFocus.set executeMetasDropped [none]),
      ⟨.returned () [none], ⟨executePlan.data, rfl, rfl⟩, rfl⟩, rfl⟩

/-- Execute unwinds after prefix cleanup, then the earlier instruction,
then only the reverse still-unmoved argument suffix. -/
theorem execute_partial_failure_preserves_scope_order :
    executeInfos (executeTypes 2) executeArgs (executeInfo 0) (ownedInstruction executePlan)
      executeInstructionState (.unwound (73 : Nat) executeFinalState) := by
  refine ⟨.unwound (⟨2, .work⟩, (73 : Nat)) executeArrayDropped,
    execute_partial_literal_trace, ?_⟩
  have ready : executeDropsReady executeRemaining executeInstructionDropped := by
    unfold executeRemaining
    simp only [executeDropsReady, executeDropReady, executeRcReady]
    decide +kernel
  exact (drop_trace_append execute_instruction_drop_trace
    (execute_drop_trace executeRemaining executeInstructionDropped ready)).cleanup_unwound
      (executeTypes 2).doubleUnwind (73 : Nat)

/-- The distinguishing observation: prefix fields see live instruction
vectors; literal retirement and both instruction field drops intervene;
only the two remaining arguments then drop with both vectors dead. -/
theorem execute_partial_failure_observations :
    executeFinalState.2.cleanupEvents =
      [.accountDrop .lamports ⟨0⟩ true true, .accountDrop .data ⟨1⟩ true true,
       .accountDrop .lamports ⟨2⟩ true true, .accountDrop .data ⟨3⟩ true true,
       .literalRetire, .metadataDrop, .byteDrop,
       .accountDrop .lamports ⟨6⟩ false false, .accountDrop .data ⟨7⟩ false false,
       .accountDrop .lamports ⟨4⟩ false false, .accountDrop .data ⟨5⟩ false false] ∧
    executeFinalState.2.rcEvents =
      [.drop .lamports ⟨0⟩, .drop .data ⟨1⟩, .drop .lamports ⟨2⟩, .drop .data ⟨3⟩,
       .drop .lamports ⟨6⟩, .drop .data ⟨7⟩, .drop .lamports ⟨4⟩, .drop .data ⟨5⟩] ∧
    executeFinalState.2.bytes = [none] ∧ executeFinalState.2.metas = [none] ∧
    executeFinalState.2.infos = [] ∧ executeFinalState.2.lamportsOwners = 4 ∧
    executeFinalState.2.dataOwners = 4 ∧ executeFinalState.1 = executeWorld ∧
    executeFinalState.2.invocations = 0 := by
  decide +kernel

/-- Before any Execute move, literal retirement sees no owned elements. -/
def executeEarlyArrayState : State := recordCleanup executeInstructionState .literalRetire

/-- Metadata still drops before the arguments when no expression completed. -/
def executeEarlyMetasState : State :=
  recordCleanup (metasFocus.set executeEarlyArrayState [none]) .metadataDrop

/-- Both instruction fields have dropped before the first original argument. -/
def executeEarlyInstructionState : State :=
  recordCleanup (bytesFocus.set executeEarlyMetasState [none]) .byteDrop

/-- All four arguments remain caller-owned when literal work fails initially. -/
def executeEarlyRemaining : List AccountInfo.Value :=
  [executeInfo 3, executeInfo 2, executeInfo 1, executeInfo 0]

/-- Initial literal failure leaves precisely one outside owner of each cell. -/
def executeEarlyFinalState : State := executeDropped executeEarlyRemaining
  executeEarlyInstructionState

/-- Execute may fail before its first pure move. The instruction then drops,
followed by all four still-owned arguments in reverse declaration order. -/
theorem execute_failure_before_any_move :
    executeInfos (executeTypes 0) executeArgs (executeInfo 0) (ownedInstruction executePlan)
      executeInstructionState (.unwound (73 : Nat) executeEarlyFinalState) := by
  refine ⟨.unwound (⟨0, .work⟩, (73 : Nat)) executeEarlyArrayState, ?_, ?_⟩
  · refine .workUnwind [] executeInstructionState executeInstructionState (73 : Nat) _ rfl ?_
    refine ⟨.refl _, .unwound (73 : Nat) executeEarlyArrayState, ?_, rfl⟩
    exact ⟨.returned () executeEarlyArrayState, rfl, rfl⟩
  · have locals : Owned.DropReturns
        (instructionDrops (executeTypes 0) (ownedInstruction executePlan))
        executeEarlyArrayState executeEarlyInstructionState := by
      refine .cons _ _ executeEarlyArrayState executeEarlyMetasState executeEarlyInstructionState ?_
        (.cons _ _ executeEarlyMetasState executeEarlyInstructionState executeEarlyInstructionState
          ?_
          (.nil executeEarlyInstructionState))
      · exact ⟨.returned () (metasFocus.set executeEarlyArrayState [none]),
          ⟨.returned () [none], ⟨executePlan.metas.items, rfl, rfl⟩, rfl⟩, rfl⟩
      · exact ⟨.returned () (bytesFocus.set executeEarlyMetasState [none]),
          ⟨.returned () [none], ⟨executePlan.data, rfl, rfl⟩, rfl⟩, rfl⟩
    have ready : executeDropsReady executeEarlyRemaining executeEarlyInstructionState := by
      unfold executeEarlyRemaining
      simp only [executeDropsReady, executeDropReady, executeRcReady]
      decide +kernel
    exact (drop_trace_append locals
      (execute_drop_trace executeEarlyRemaining executeEarlyInstructionState ready)).cleanup_unwound
        (executeTypes 0).doubleUnwind (73 : Nat)

/-- Every account destructor observes dead instruction vectors after an
initial work failure, and the distinct cell identities occur in reverse order. -/
theorem execute_failure_before_any_move_observations :
    executeEarlyFinalState.2.cleanupEvents =
      [.literalRetire, .metadataDrop, .byteDrop,
       .accountDrop .lamports ⟨6⟩ false false, .accountDrop .data ⟨7⟩ false false,
       .accountDrop .lamports ⟨4⟩ false false, .accountDrop .data ⟨5⟩ false false,
       .accountDrop .lamports ⟨2⟩ false false, .accountDrop .data ⟨3⟩ false false,
       .accountDrop .lamports ⟨0⟩ false false, .accountDrop .data ⟨1⟩ false false] ∧
    executeEarlyFinalState.2.rcEvents.length = 8 ∧
    executeEarlyFinalState.2.bytes = [none] ∧ executeEarlyFinalState.2.metas = [none] ∧
    executeEarlyFinalState.2.infos = [] ∧ executeEarlyFinalState.2.lamportsOwners = 4 ∧
    executeEarlyFinalState.2.dataOwners = 4 ∧ executeEarlyFinalState.1 = executeWorld := by
  decide +kernel

/-- An explicit primitive dependency retires the actual metadata slot and
then unwinds. This is a model cleanup control, not a Rust destructor proof. -/
def executeUnwindingMetas : Owned.VectorOps State Solanalib.Runtime.CpiMeta Nat Nat Nat := {
  metasOps with
  drop := fun before resource outcome =>
    Callback.bind (fun state (_ : Unit) => metasOps.drop state resource)
      (fun _ state result => result = .unwound (79 : Nat) (recordCleanup state .metadataDrop))
      before () outcome }

/-- The terminal policy checks the actual destructor state, both unwind
reasons, and the absence of byte or remaining-argument cleanup. -/
def executeAbortPolicy : Owned.DoubleUnwind State Nat Nat :=
  fun state original later terminal =>
    state = executeMetasDropped ∧ original = 73 ∧ later = 79 ∧ terminal = 97

/-- Byte destruction has no finite exit in this control; a correct second
unwind must terminate before that action or any remaining original owner. -/
def executeDoubleTypes : Types := { executeTypes 2 with
  metas := executeUnwindingMetas
  bytes := { executeBytesOps with drop := fun _ _ _ => False }
  doubleUnwind := executeAbortPolicy }

/-- The second unwind is checked after partial array cleanup and metadata
retirement. It terminates before the unavailable byte destructor and before
the two still-owned original arguments. -/
theorem execute_second_unwind_stops_before_remaining :
    executeInfos executeDoubleTypes executeArgs (executeInfo 0) (ownedInstruction executePlan)
      executeInstructionState (.terminated (97 : Nat)) := by
  refine ⟨.unwound (⟨2, .work⟩, (73 : Nat)) executeArrayDropped,
    execute_partial_literal_trace_with_policy executeAbortPolicy, ?_⟩
  exact Owned.cleanup_double_unwind executeDoubleTypes.doubleUnwind _ _
    executeArrayDropped executeMetasDropped (73 : Nat) (79 : Nat) (97 : Nat)
    ⟨.returned () (metasFocus.set executeArrayDropped [none]),
      ⟨.returned () [none], ⟨executePlan.metas.items, rfl, rfl⟩, rfl⟩, rfl⟩
    ⟨rfl, rfl, rfl, rfl⟩

/-- The state required by the terminal policy retains the byte vector and
both unmoved original owners. Only the two evaluated owners have dropped. -/
theorem execute_second_unwind_observations :
    executeMetasDropped.2.cleanupEvents =
      [.accountDrop .lamports ⟨0⟩ true true, .accountDrop .data ⟨1⟩ true true,
       .accountDrop .lamports ⟨2⟩ true true, .accountDrop .data ⟨3⟩ true true,
       .literalRetire, .metadataDrop] ∧
    executeMetasDropped.2.rcEvents =
      [.drop .lamports ⟨0⟩, .drop .data ⟨1⟩, .drop .lamports ⟨2⟩, .drop .data ⟨3⟩] ∧
    executeMetasDropped.2.bytes = [some executePlan.data] ∧
    executeMetasDropped.2.metas = [none] ∧ executeMetasDropped.2.infos = [] ∧
    executeMetasDropped.2.lamportsOwners = 6 ∧ executeMetasDropped.2.dataOwners = 6 ∧
    executeMetasDropped.1 = executeWorld := by
  decide +kernel

end SolanalibTest.Specs.SplToken2022.Allocated
