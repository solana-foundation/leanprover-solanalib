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

namespace SolanalibTest.Specs.SplToken2022.Pda

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.OnchainAllocated
open Solanalib.Specs.Core.Token.OnchainAllocated.Witness

/-- The validation-address inputs of the hook retain both source seed slices. -/
def inputs : Address.Syscall.PdaInputs :=
  ⟨[Hook.extraAccountMetasSeed, Onchain.witnessArgs.mint.key.bytes], .zero⟩

/-- An observable primitive effect, independent of CPI or vector allocation. -/
def syscallAfter (state : State) : State :=
  (state.1, { state.2 with invocations := state.2.invocations + 7 })

/-- The primitive records an effect and unwinds before any ordinary reply. -/
def unwindingSyscall : Callback.Run State Address.Syscall.PdaRequest
    Address.Syscall.PdaReply Nat Nat :=
  fun state _ outcome => outcome = .unwound (71 : Nat) (syscallAfter state)

/-- All ownership providers are unchanged; only the actual syscall differs. -/
def unwindTypes : Types := { sampleTypes with
  pdaSyscall := unwindingSyscall }

/-- An unused hook collection or invocation has no assumed finite exit. -/
def dependencies (types : Types) : Dependencies types where
  collect := ⟨fun _ _ _ _ => False⟩
  invoke := fun _ _ _ => False

/-- The mathematical facet has a viable result for these exact hook seeds. -/
theorem mathematical_pda_exists :
    Address.tryFind ⟨Onchain.witnessArgs.crypto, inputs.seeds, inputs.programId⟩ =
      some (.zero, 255) := by
  decide +kernel

/-- Primitive normal-return agreement does not suppress independent unwind. -/
theorem unwind_normal_agreement :
    Address.Syscall.NormalPdaAgreement unwindingSyscall Onchain.witnessArgs.crypto := by
  intro before given reply after execution
  cases execution

/-- The selected wrapper preserves the exact abnormal exit and state of the syscall. -/
theorem find_unwinds : unwindTypes.findPda initialState inputs
    (.unwound (71 : Nat) (syscallAfter initialState)) := by
  refine ⟨hookPdaInputs_bounded Onchain.witnessArgs .zero, ?_⟩
  exact ⟨.unwound (71 : Nat) (syscallAfter initialState),
    ⟨.unwound (71 : Nat) (syscallAfter initialState), rfl, rfl⟩, rfl⟩

/-- Even a missing hook program cannot replace the earlier syscall unwind. -/
theorem hook_entry_unwinds_before_lookup :
    hookEntry unwindTypes Onchain.witnessArgs .zero initialState
      (.unwound (71 : Nat) (syscallAfter initialState)) :=
  ⟨.unwound (71 : Nat) (syscallAfter initialState),
    ⟨.unwound (71 : Nat) (syscallAfter initialState), find_unwinds, rfl⟩, rfl⟩

/-- The actual four argument owners are retired after the primitive effect. -/
def unwindFinal : State := dropped arguments (syscallAfter initialState)

/-- No instruction resource is inspected on the early-failure path. -/
def unusedPrepared : Prepared unwindTypes := ⟨⟨.zero, (99 : Nat), (98 : Nat)⟩, (97 : Nat)⟩

/-- Complete helper failure cleans its four moved arguments in source order,
without requiring any vector allocation, collection or opaque CPI execution. -/
theorem add_hook_unwind_cleans_arguments :
    addHook unwindTypes (dependencies unwindTypes) Onchain.witnessArgs .zero unusedPrepared
      initialState (.unwound (71 : Nat) unwindFinal) := by
  have ready : dropsReady arguments (syscallAfter initialState) := by
    unfold arguments
    simp only [dropsReady, dropReady, rcReady]
    decide +kernel
  have cleaned : Owned.cleanup unwindTypes.doubleUnwind
      (argumentDrops unwindTypes Onchain.witnessArgs)
      (.unwound (71 : Nat) (syscallAfter initialState) :
        Outcome State (Except Error
          (Solanalib.Runtime.Pubkey × AccountInfo.Value × Option AccountInfo.Value)) Nat Nat)
      (.unwound (71 : Nat) unwindFinal) :=
    (drop_trace arguments (syscallAfter initialState) ready).cleanup_unwound
      unwindTypes.doubleUnwind (71 : Nat)
  exact ⟨.unwound (71 : Nat) unwindFinal,
    ⟨.unwound (71 : Nat) (syscallAfter initialState), hook_entry_unwinds_before_lookup, cleaned⟩,
    rfl⟩

/-- The syscall marker survives all eight field drops, with no local allocation. -/
theorem unwind_cleanup_resources :
    unwindFinal.1 = Onchain.witnessState ∧
    unwindFinal.2.bytes = [] ∧ unwindFinal.2.metas = [] ∧ unwindFinal.2.infos = [] ∧
    unwindFinal.2.lamportsOwners = 1 ∧ unwindFinal.2.dataOwners = 1 ∧
    unwindFinal.2.rcEvents.length = 8 ∧ unwindFinal.2.invocations = 7 := by
  decide +kernel

/-- A terminal primitive needs neither normal output initialization nor cleanup. -/
def terminalTypes : Types := { sampleTypes with
  pdaSyscall := fun _ _ outcome => outcome = .terminated (73 : Nat)
  rc := { cloneRc := fun _ _ _ => False, dropRc := fun _ _ _ => False } }

/-- Terminal propagation does not require the deliberately unavailable Rc drops. -/
theorem add_hook_terminal_bypasses_cleanup :
    addHook terminalTypes (dependencies terminalTypes) Onchain.witnessArgs .zero
      ⟨⟨.zero, (99 : Nat), (98 : Nat)⟩, (97 : Nat)⟩ initialState (.terminated (73 : Nat)) := by
  have found : terminalTypes.findPda initialState inputs (.terminated (73 : Nat)) :=
    ⟨hookPdaInputs_bounded Onchain.witnessArgs .zero,
      .terminated (73 : Nat), ⟨.terminated (73 : Nat), rfl, rfl⟩, rfl⟩
  have entered : hookEntry terminalTypes Onchain.witnessArgs .zero initialState
      (.terminated (73 : Nat)) :=
    ⟨.terminated (73 : Nat), ⟨.terminated (73 : Nat), found, rfl⟩, rfl⟩
  refine ⟨.terminated (73 : Nat), ⟨.terminated (73 : Nat), entered, ?_⟩, rfl⟩
  exact (Owned.cleanup_terminated terminalTypes.doubleUnwind
    (argumentDrops terminalTypes Onchain.witnessArgs) (73 : Nat) _).mpr rfl

/-- A primitive returning an initialized key after an observable state change. -/
def returnedTypes : Types := { sampleTypes with
  pdaSyscall := fun state _ outcome =>
    outcome = .returned ⟨0, some .zero, 254⟩ (syscallAfter state) }

/-- The wrapper decodes both successful output slots using the state of the syscall. -/
theorem find_returns_outputs : returnedTypes.findPda initialState inputs
    (.returned (.zero, 254) (syscallAfter initialState)) := by
  refine ⟨hookPdaInputs_bounded Onchain.witnessArgs .zero, ?_⟩
  refine ⟨.returned (some (.zero, 254)) (syscallAfter initialState), ?_, rfl⟩
  exact Address.Syscall.tryRun_returned returnedTypes.pdaSyscall initialState
    (syscallAfter initialState) inputs ⟨0, some .zero, 254⟩ (some (.zero, 254))
    rfl ⟨.zero, rfl, rfl⟩

/-- Mandatory program lookup happens only after a successful syscall, and its
ordinary error retains the state effect of that syscall. -/
theorem successful_search_then_missing_program :
    hookEntry returnedTypes Onchain.witnessArgs .zero initialState
      (.returned (.error Hook.incorrectHookAccount) (syscallAfter initialState)) :=
  ⟨.returned (.ok (.zero, 254)) (syscallAfter initialState),
    ⟨.returned (.zero, 254) (syscallAfter initialState), find_returns_outputs, rfl⟩, rfl⟩

/-- A returned nonzero status does not establish a usable address output. -/
def rejectedTypes : Types := { sampleTypes with
  pdaSyscall := fun state _ outcome =>
    outcome = .returned ⟨8, some .zero, 17⟩ (syscallAfter state) }

/-- Nonzero status reaches the local panic only after the syscall state change;
the apparently initialized output slots do not turn it into a successful key. -/
theorem nonzero_status_panics_in_current_state :
    hookEntry rejectedTypes Onchain.witnessArgs .zero initialState
      (.unwound (102 : Nat) (syscallAfter initialState)) := by
  have tried : Address.Syscall.tryRun rejectedTypes.pdaSyscall initialState inputs
      (.returned none (syscallAfter initialState)) :=
    Address.Syscall.tryRun_returned rejectedTypes.pdaSyscall initialState
      (syscallAfter initialState) inputs ⟨8, some .zero, 17⟩ none rfl rfl
  have found : rejectedTypes.findPda initialState inputs
      (.unwound (102 : Nat) (syscallAfter initialState)) :=
    ⟨hookPdaInputs_bounded Onchain.witnessArgs .zero,
      .returned none (syscallAfter initialState), tried,
      .unwound (102 : Nat) (syscallAfter initialState), rfl, rfl⟩
  exact ⟨.unwound (102 : Nat) (syscallAfter initialState),
    ⟨.unwound (102 : Nat) (syscallAfter initialState), found, rfl⟩, rfl⟩

/-- Primitive output initialization is a separate binding obligation. The
model can describe a status-zero reply whose address output is unavailable. -/
def uninitializedTypes : Types := { sampleTypes with
  pdaSyscall := fun state _ outcome =>
    outcome = .returned ⟨0, none, 255⟩ (syscallAfter state) }

/-- The malformed output comes from an actual finite primitive return, with
its observable effect retained by that primitive relation. -/
theorem uninitialized_syscall_returns : uninitializedTypes.pdaSyscall initialState
    (Address.Syscall.pdaRequest inputs)
    (.returned ⟨0, none, 255⟩ (syscallAfter initialState)) := rfl

/-- The unchanged decoder supplies neither a fabricated address nor a panic
for an uninitialized success; this representation boundary remains partial. -/
theorem uninitialized_success_has_no_wrapper_exit : ∀ outcome,
    ¬ uninitializedTypes.findPda initialState inputs outcome := by
  intro outcome execution
  obtain ⟨middle, tried, _⟩ := execution.2
  obtain ⟨actual, called, continued⟩ := tried
  change actual = .returned ⟨0, none, 255⟩ (syscallAfter initialState) at called
  cases called
  obtain ⟨result, decoded, _⟩ := continued
  change ∃ address, (none : Option Address.Value) = some address ∧
    result = some (address, (255 : UInt8)) at decoded
  obtain ⟨_, impossible, _⟩ := decoded
  cases impossible

end SolanalibTest.Specs.SplToken2022.Pda
