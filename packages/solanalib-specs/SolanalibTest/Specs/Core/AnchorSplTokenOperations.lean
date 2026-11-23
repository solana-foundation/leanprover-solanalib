/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.Sample
public import Solanalib.Specs.Core.AnchorSplTokenOperations.ReferenceObservation

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SolanalibTest.Specs.Core.AnchorSplTokenOperations

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTokenOperations

abbrev Observed (binding : Binding) (script : Reference.Script binding.release)
    {Value : Type} (project : Exit (Reference.types binding script) → Option Value) (value : Value)
      :=
  Reference.Observes script (Sample.initial binding) (Sample.args binding) project value

theorem observed_iff (binding : Binding) (script : Reference.Script binding.release)
    {Value : Type} (project : Exit (Reference.types binding script) → Option Value) (value : Value)
      :
    Observed binding script project value ↔
      (Execution.runFn (Reference.functions binding script) (Sample.initial binding) (Sample.args
        binding)).bind
        project = some value :=
  Reference.observes_iff (binding := binding) script (Sample.initial binding) (Sample.args binding)
    project value

def stateProject {binding : Binding} {script : Reference.Script binding.release} {Value : Type}
    (project : Reference.State binding.release → Value) : Exit (Reference.types binding script) →
      Option Value :=
  fun final => (Reference.stateOf final).map project

def firstCall {binding : Binding} {script : Reference.Script binding.release} :
    Exit (Reference.types binding script) → Option Reference.RecordedCall :=
  fun final => (Reference.stateOf final).bind fun after => after.calls[0]?

def firstGetter {binding : Binding} {script : Reference.Script binding.release} :
    Exit (Reference.types binding script) → Option Reference.GetterObservation :=
  fun final => (Reference.stateOf final).bind fun after => after.getters[0]?

theorem every_binding_has_execution (binding : Binding) :
    FamilyHasExecution (family binding) (reference binding) (Sample.types binding) :=
      Sample.execution binding

/-- the source invocation order of MintTo is destination, mint, authority, while
the constructor metadata starts with the mint. -/
theorem mint_to_account_orders : Observed .token2022MintTo0321 (Sample.script _)
    (fun final => (firstCall final).map fun call =>
      (call.instruction.metas.map Solanalib.Runtime.CpiMeta.key, call.accounts.map
        AccountInfo.Value.key))
    ([.ofNat 1, .ofNat 2, .ofNat 3], [.ofNat 2, .ofNat 1, .ofNat 3]) := by
  rw [observed_iff]
  decide

theorem burn_checked_wire_and_accounts : Observed .token2022BurnChecked112 (Sample.script _)
    (fun final => (firstCall final).map fun call =>
      (call.instruction.data, call.instruction.metas.map Solanalib.Runtime.CpiMeta.key,
        call.accounts.map AccountInfo.Value.key))
    ([15, 42, 0, 0, 0, 0, 0, 0, 0, 9], [.ofNat 2, .ofNat 1, .ofNat 3], [.ofNat 2, .ofNat 1, .ofNat
      3]) := by
  rw [observed_iff]
  decide

theorem transfer_checked_mint_position : Observed .token2022TransferChecked029 (Sample.script _)
    (fun final => (firstCall final).map fun call =>
      (call.instruction.data, call.instruction.metas.map fun item => (item.signerByte,
        item.writableByte)))
    ([12, 42, 0, 0, 0, 0, 0, 0, 0, 9], [(0, 1), (0, 0), (0, 1), (1, 0)]) := by
  rw [observed_iff]
  decide

theorem unsigned_initializer_does_not_pass_seeds : Observed .token2022InitializeAccount3102
  (Sample.script _)
    (fun final => (firstCall final).map fun call => (call.seedReference, call.signers,
      call.accounts.map AccountInfo.Value.key))
    (none, [], [.ofNat 1, .ofNat 2]) := by
  rw [observed_iff]
  decide

theorem signed_empty_groups_are_retained : Observed .token2022TransferChecked112 (Sample.script _)
    (fun final => (firstCall final).map fun call => (call.seedReference, call.signers))
    (some 0, [[], [[1, 2], []]]) := by
  rw [observed_iff]
  decide

theorem legacy_program_ignores_context_key : Observed .tokenTransfer0321 (Sample.script _)
    (fun final => (firstCall final).map fun call => call.instruction.programId)
      Token.legacyProgramId := by
  rw [observed_iff]
  decide

theorem old_array_clones_before_invocation : Observed .tokenTransfer027 (Sample.script _)
    (fun final => (firstCall final).bind fun call => call.counts.lookup (.lamports, (Sample.info
      1).lamports)) 2 := by
  rw [observed_iff]
  decide

theorem moved_array_keeps_single_owner : Observed .tokenTransfer0321 (Sample.script _)
    (fun final => (firstCall final).bind fun call => call.counts.lookup (.lamports, (Sample.info
      1).lamports)) 1 := by
  rw [observed_iff]
  decide

theorem wrong_clone_count_rejected : ¬ Observed .tokenTransfer027 (Sample.script _)
    (fun final => (firstCall final).bind fun call => call.counts.lookup (.lamports, (Sample.info
      1).lamports)) 1 := by
  rw [observed_iff]
  decide

def sizeScript (returned : Reference.ReturnData) : Reference.Script .v0321 := { returned }

theorem size_success : Observed .token2022GetAccountDataSize0321
    (sizeScript (.present Token.token2022ProgramId [0x34, 0x12, 0, 0, 0, 0, 0, 0]))
    Reference.returnOf (.size 0x1234) := by
  rw [observed_iff]
  decide

theorem size_missing_data_error : Observed .token2022GetAccountDataSize0321 (sizeScript .absent)
    (Reference.programErrorOf _) .invalidInstructionData := by
  rw [observed_iff]
  decide

theorem size_wrong_key_precedes_length : Observed .token2022GetAccountDataSize0321
    (sizeScript (.present (.ofNat 99) [7])) (Reference.programErrorOf _) .incorrectProgramId := by
  rw [observed_iff]
  decide

theorem size_short_data_error : Observed .token2022GetAccountDataSize0321
    (sizeScript (.present Token.token2022ProgramId (List.replicate 7 0)))
    (Reference.programErrorOf _) .invalidInstructionData := by
  rw [observed_iff]
  decide

theorem size_long_data_error : Observed .token2022GetAccountDataSize0321
    (sizeScript (.present Token.token2022ProgramId (List.replicate 9 0)))
    (Reference.programErrorOf _) .invalidInstructionData := by
  rw [observed_iff]
  decide

/-- The getter runs after the destruction of the mint array, while both instruction
vectors remain live. This distinguishes a premature or delayed scope drop. -/
theorem getter_observes_statement_cleanup : Observed .token2022GetAccountDataSize0321
  (Sample.script _)
    (fun final => (firstGetter final).bind fun observation => do
      let count ← observation.counts.lookup (.lamports, (Sample.info 1).lamports)
      return (count, (observation.bytes.current 0).isSome, (observation.metas.current 0).isSome))
    (0, true, true) := by
  rw [observed_iff]
  decide

theorem delayed_mint_drop_rejected : ¬ Observed .token2022GetAccountDataSize0321 (Sample.script _)
    (fun final => (firstGetter final).bind fun observation => observation.counts.lookup (.lamports,
      (Sample.info 1).lamports)) 1 := by
  rw [observed_iff]
  decide

theorem size_full_cleanup_order : Observed .token2022GetAccountDataSize0321 (Sample.script _)
    (stateProject Reference.State.events)
    [.literal .metas 1, .literal .extensions 2,
     .reserve .bytes 128, .push .bytes 0, .extend .bytes 0 2, .extend .bytes 0 2,
     .release .extensions 0, .invoke, .dropRc .lamports ⟨2⟩, .dropRc .data ⟨3⟩,
     .getReturnData, .release .bytes 1, .release .metas 0, .release .bytes 0,
     .dropRc .lamports ⟨80⟩, .dropRc .data ⟨81⟩, .release .remaining 0,
     .dropRc .lamports ⟨100⟩, .dropRc .data ⟨101⟩] := by
  rw [observed_iff]
  decide

theorem invalid_return_vector_dropped_before_box : Observed .token2022GetAccountDataSize0321
    (sizeScript (.present (.ofNat 99) [7]))
    (stateProject fun state => state.events.dropWhile (· != .getReturnData))
    [.getReturnData, .release .bytes 1, .newBox 0, .release .metas 0, .release .bytes 0,
     .dropRc .lamports ⟨80⟩, .dropRc .data ⟨81⟩, .release .remaining 0,
     .dropRc .lamports ⟨100⟩, .dropRc .data ⟨101⟩] := by
  rw [observed_iff]
  decide

def inlineError : Reference.Script .v027 := { reply := .error (.borshIoError 0) }

theorem inline_legacy_error_keeps_owned_message : Observed .tokenBurn027 inlineError
    (fun final => do
      let error ← Reference.programErrorOf (binding := .tokenBurn027) inlineError final
      let state ← Reference.stateOf final
      return (error, state.boxes.length, state.strings[0]?.join))
    (.borshIoError 0, 0, some "owned dependency error") := by
  rw [observed_iff]
  decide

def boxedError : Reference.Script .v029 := { reply := .error (.borshIoError 0) }

theorem boxed_legacy_error_keeps_owned_message : Observed .token2022TransferChecked029 boxedError
    (fun final => do
      let error ← Reference.programErrorOf (binding := .token2022TransferChecked029) boxedError
        final
      let state ← Reference.stateOf final
      return (error, state.boxes.length, state.strings[0]?.join))
    (.borshIoError 0, 1, some "owned dependency error") := by
  rw [observed_iff]
  decide

def unwindScript : Reference.Script .v112 := { reply := .unwind 23, effect := 17 }

theorem invocation_unwind_keeps_effect_and_cleans_owners : Observed .token2022TransferChecked112
  unwindScript
    (fun final => match final with
      | .unwound reason state => some (reason, state.effect, state.counts.map Prod.snd,
        state.bytes, state.metas)
      | _ => none)
    ((23 : Nat), 17, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [none], [none]) := by
  rw [observed_iff]
  rfl

def terminalScript : Reference.Script .v112 := { reply := .terminal 71 }

theorem invocation_terminal_has_no_cleanup_state :
    run (Reference.types .token2022TransferChecked112 terminalScript)
      (Sample.initial _) (Sample.args _) (.terminated (71 : Nat)) := by
  exact (Reference.run_iff .token2022TransferChecked112 terminalScript _ _ _).mpr rfl

theorem terminal_has_no_returned_observation : ¬ Observed .token2022TransferChecked112
  terminalScript
    (stateProject Reference.State.effect) 1 := by
  rw [observed_iff]
  decide

def getterUnwind : Reference.Script .v0321 := { returned := .unwind 29, effect := 3 }

theorem getter_unwind_keeps_both_provider_effects : Observed .token2022GetAccountDataSize0321
  getterUnwind
    (fun final => match final with
      | .unwound reason state => some (reason, state.effect, state.counts.map Prod.snd,
        state.bytes, state.metas)
      | _ => none)
    ((29 : Nat), 6, [0, 0, 0, 0, 0, 0], [none], [none]) := by
  rw [observed_iff]
  rfl

namespace CheckedTransfer

/-- This is the binding selected by the source registry in this development. -/
abbrev binding : Binding := .token2022TransferChecked0321

/-- The selected wrapper keeps the mint position, authority signer flag,
moved account order, and the original outer seed reference. -/
theorem request_fields : Observed binding (Sample.script binding)
    (fun final => (firstCall final).map fun call =>
      (call.instruction.data, call.instruction.metas.map (fun entry => (entry.signerByte,
        entry.writableByte)),
        call.accounts.map AccountInfo.Value.key, call.seedReference, call.signers))
    ([12, 42, 0, 0, 0, 0, 0, 0, 0, 9], [(0, 1), (0, 0), (0, 1), (1, 0)],
      [.ofNat 1, .ofNat 2, .ofNat 3, .ofNat 4], some 0, [[], [[1, 2], []]]) := by
  rw [observed_iff]
  rfl

/-- Success keeps the provider effect and releases every wrapper-owned resource
without creating an error box. -/
theorem success_result_effect_and_cleanup : Observed binding (Sample.script binding)
    (fun final => do
      let value ← Reference.returnOf final
      let state ← Reference.stateOf final
      return (value, state.effect, state.calls.length, state.boxes,
        state.counts.map Prod.snd, state.bytes, state.metas, state.remaining))
    (.unit, 1, 1, [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [none], [none], [none]) := by
  rw [observed_iff]
  rfl

def errorScript : Reference.Script .v0321 := { reply := .error (.borshIoError 0), effect := 17 }

/-- The returned error retains its owned message and provider effect while
all four moved accounts, remaining owners, and the context program are released. -/
theorem error_payload_effect_and_cleanup : Observed binding errorScript
    (fun final => do
      let error ← Reference.programErrorOf (binding := binding) errorScript final
      let state ← Reference.stateOf final
      return (error, state.effect, state.boxes.length, state.strings[0]?.join,
        state.counts.map Prod.snd, state.bytes, state.metas, state.remaining))
    (.borshIoError 0, 17, 1, some "owned dependency error",
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [none], [none], [none]) := by
  rw [observed_iff]
  rfl

/-- Error boxing precedes instruction destruction; moved AccountInfo fields
drop in array order, followed by the remaining vector and program owner. -/
theorem error_cleanup_order : Observed binding errorScript
    (stateProject fun state => state.events.dropWhile (· != .invoke))
    [.invoke, .newBox 0, .release .metas 0, .release .bytes 0,
     .dropRc .lamports ⟨2⟩, .dropRc .data ⟨3⟩,
     .dropRc .lamports ⟨4⟩, .dropRc .data ⟨5⟩,
     .dropRc .lamports ⟨6⟩, .dropRc .data ⟨7⟩,
     .dropRc .lamports ⟨8⟩, .dropRc .data ⟨9⟩,
     .dropRc .lamports ⟨80⟩, .dropRc .data ⟨81⟩, .release .remaining 0,
     .dropRc .lamports ⟨100⟩, .dropRc .data ⟨101⟩] := by
  rw [observed_iff]
  decide

def unwindScript : Reference.Script .v0321 := { reply := .unwind 23, effect := 17 }

/-- Unwind retains the state of the callback and does not allocate an Anchor error. -/
theorem unwind_effect_and_cleanup : Observed binding unwindScript
    (fun final => match final with
      | .unwound reason state => some (reason, state.effect, state.boxes,
          state.counts.map Prod.snd, state.bytes, state.metas, state.remaining)
      | _ => none)
    ((23 : Nat), 17, [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [none], [none], [none]) := by
  rw [observed_iff]
  rfl

def terminalScript : Reference.Script .v0321 := { reply := .terminal 71 }

theorem terminal_exit : run (Reference.types binding terminalScript)
    (Sample.initial binding) (Sample.args binding) (.terminated (71 : Nat)) :=
  (Reference.run_iff binding terminalScript _ _ _).mpr rfl

/-- No state can be observed after the selected terminal provider exit. -/
theorem terminal_has_no_state (state : Reference.State .v0321) :
    ¬ Observed binding terminalScript (fun final => Reference.stateOf final) state := by
  rw [observed_iff]
  intro observed
  cases observed

/-- Rejection happens before the signer-seed read, even when no seed view is available. -/
def rejectedArgs : Input (Reference.types binding (Sample.script binding)) :=
  { Sample.args binding with context := {
      (Sample.args binding).context with program := { Sample.info 50 with key := .ofNat 99 } } }

def rejectedBefore : Reference.State .v0321 :=
  { Sample.initialFor binding rejectedArgs [Sample.info 40] with seeds := [] }

/-- The failing input is admitted and has a real error exit. It performs no
instruction allocation or invocation and still releases the intact context. -/
theorem constructor_rejection_is_admitted_and_cleans_context :
    Ready (Reference.types binding (Sample.script binding)) rejectedBefore rejectedArgs ∧
    Reference.Observes (Sample.script binding) rejectedBefore rejectedArgs
      (fun final => do
        let error ← Reference.programErrorOf (binding := binding) (Sample.script binding) final
        let state ← Reference.stateOf final
        return (error, state.calls.length, state.effect, state.bytes, state.metas,
          state.counts.map Prod.snd, state.boxes.length, state.remaining))
      (.incorrectProgramId, 0, 0, [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 1, [none]) := by
  constructor
  · exact Reference.ready_of_requests binding (Sample.script binding) rejectedBefore rejectedArgs
      (by decide)
  · rw [Reference.observes_iff]
    rfl

end CheckedTransfer

end SolanalibTest.Specs.Core.AnchorSplTokenOperations
