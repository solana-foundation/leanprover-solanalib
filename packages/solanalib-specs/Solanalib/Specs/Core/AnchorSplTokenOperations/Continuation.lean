/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.Wrappers

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations

/-- Conversion is performed only on a returned ProgramError. Every actual
unwind state and terminal reason passes through unchanged. -/
def Converted {binding : Binding} {Value : Type} (types : Types binding)
    (produced : Outcome types.builder.instruction.State
      (Except (binding.release.ProgramError types.StringResource) Value)
      types.builder.instruction.Unwind types.builder.instruction.Terminal)
    (pending : Outcome types.builder.instruction.State (Except (Error types) Value)
      types.builder.instruction.Unwind types.builder.instruction.Terminal) : Prop :=
  match produced with
  | .returned value after => convertResult types after value pending
  | .unwound reason after => pending = .unwound reason after
  | .terminated reason => pending = .terminated reason

/-- A readable request retains every exit of the exact supplied invocation,
and every actual error-conversion continuation. It invents no callee exit. -/
theorem invokeAndConvert_iff {binding : Binding} (types : Types binding) (args : Input types)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value)
    (before : types.builder.instruction.State) (call : CpiRequest.Request AccountInfo.Value)
    (readable : request types before args instruction accounts = some call)
    (pending : Outcome types.builder.instruction.State (Except (Error types) Unit)
      types.builder.instruction.Unwind types.builder.instruction.Terminal) :
    invokeAndConvert types args instruction accounts before () pending ↔
      ∃ invoked, types.invoke (seedReference args) before call invoked ∧ Converted types invoked
        pending := by
  constructor
  · rintro ⟨actual, found, invoked, called, continued⟩
    have equal : actual = call := Option.some.inj (found.symm.trans readable)
    subst actual
    refine ⟨invoked, called, ?_⟩
    cases invoked <;> exact continued
  · rintro ⟨invoked, called, continued⟩
    refine ⟨call, readable, invoked, called, ?_⟩
    cases invoked <;> exact continued

/-- An actual successful constructor and account preparation retain the same
instruction owner, the actual cloned/moved array and all intervening state. -/
theorem run_after_prepared {binding : Binding} (types : Types binding) (args : Input types)
    (before builtState preparedState : types.builder.instruction.State)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value) (final : Exit types)
    (built : build types.builder before (argsConstruction args) (.returned (.ok instruction)
      builtState))
    (prepared : prepareAccounts types args builtState () (.returned accounts preparedState))
    (continuation : afterPrepared types args instruction accounts preparedState () final) :
    run types before args final :=
  ⟨.returned (.ok instruction) builtState, built, .returned accounts preparedState, prepared,
    continuation⟩

/-- Once an admitted ordinary wrapper reaches the call, every actual CPI
exit, conversion exit and cleanup continuation yields its full wrapper exit.
In particular an effectful error/unwind is not replaced by a successful sample. -/
theorem Ready.tail_continuation {binding : Binding} (types : Types binding) (args : Input types)
    (before builtState preparedState : types.builder.instruction.State)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value)
    (ordinary : binding.operation ≠ .getAccountDataSize)
    (ready : Ready types before args)
    (built : build types.builder before (argsConstruction args) (.returned (.ok instruction)
      builtState))
    (prepared : prepareAccounts types args builtState () (.returned accounts preparedState)) :
    ∃ call, request types preparedState args instruction accounts = some call ∧
      ∀ invoked pending final,
        types.invoke (seedReference args) preparedState call invoked →
        Converted types invoked pending →
        Owned.cleanup types.builder.instruction.doubleUnwind (tailDrops types args instruction
          accounts)
          (Outcome.map (Except.map fun _ => Return.unit) pending) final →
        run types before args final := by
  obtain ⟨call, readable⟩ := (request_hasResult_iff types preparedState args instruction
    accounts).mpr
    (ready.requestInput instruction builtState built accounts preparedState prepared)
  refine ⟨call, readable, ?_⟩
  intro invoked pending final invocation converted cleaned
  apply run_after_prepared types args before builtState preparedState instruction accounts final
    built prepared
  simp only [afterPrepared, ordinary, ↓reduceIte]
  exact ⟨_, ⟨pending, (invokeAndConvert_iff types args instruction accounts preparedState call
    readable pending).mpr ⟨invoked, invocation, converted⟩, rfl⟩, cleaned⟩

/-- Source success is preserved across any actual normally returning cleanup
trace. The theorem retains the exact external call and the final cleanup state. -/
theorem Ready.tail_success {binding : Binding} (types : Types binding) (args : Input types)
    (before builtState preparedState invokedState finalState : types.builder.instruction.State)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value)
    (ordinary : binding.operation ≠ .getAccountDataSize) (ready : Ready types before args)
    (built : build types.builder before (argsConstruction args) (.returned (.ok instruction)
      builtState))
    (prepared : prepareAccounts types args builtState () (.returned accounts preparedState)) :
    ∃ call, request types preparedState args instruction accounts = some call ∧
      (types.invoke (seedReference args) preparedState call (.returned (.ok ()) invokedState) →
      Owned.DropReturns (tailDrops types args instruction accounts) invokedState finalState →
      run types before args (.returned (.ok .unit) finalState)) := by
  obtain ⟨call, readable, retained⟩ := ready.tail_continuation types args before builtState
    preparedState
    instruction accounts ordinary built prepared
  refine ⟨call, readable, ?_⟩
  intro invoked cleanup
  exact retained (.returned (.ok ()) invokedState) (.returned (.ok ()) invokedState) _ invoked rfl
    (cleanup.cleanup_returned _ (Except.ok Return.unit : Except (Error types) Return))

/-- An actual unwind remains an unwind with its original reason after the
actual normal cleanup trace. No destructor execution or termination is assumed. -/
theorem Ready.tail_unwind {binding : Binding} (types : Types binding) (args : Input types)
    (before builtState preparedState invokedState finalState : types.builder.instruction.State)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value)
    (ordinary : binding.operation ≠ .getAccountDataSize) (ready : Ready types before args)
    (built : build types.builder before (argsConstruction args) (.returned (.ok instruction)
      builtState))
    (prepared : prepareAccounts types args builtState () (.returned accounts preparedState))
    (reason : types.builder.instruction.Unwind) :
    ∃ call, request types preparedState args instruction accounts = some call ∧
      (types.invoke (seedReference args) preparedState call (.unwound reason invokedState) →
      Owned.DropReturns (tailDrops types args instruction accounts) invokedState finalState →
      run types before args (.unwound reason finalState)) := by
  obtain ⟨call, readable, retained⟩ := ready.tail_continuation types args before builtState
    preparedState
    instruction accounts ordinary built prepared
  refine ⟨call, readable, ?_⟩
  intro invoked cleanup
  exact retained (.unwound reason invokedState) (.unwound reason invokedState) _ invoked rfl
    (cleanup.cleanup_unwound _ reason)

/-- Terminal invocation stops before any cleanup action, even if every
destructor and allocation provider has no finite exit. -/
theorem Ready.tail_terminal {binding : Binding} (types : Types binding) (args : Input types)
    (before builtState preparedState : types.builder.instruction.State)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value)
    (ordinary : binding.operation ≠ .getAccountDataSize) (ready : Ready types before args)
    (built : build types.builder before (argsConstruction args) (.returned (.ok instruction)
      builtState))
    (prepared : prepareAccounts types args builtState () (.returned accounts preparedState))
    (reason : types.builder.instruction.Terminal) :
    ∃ call, request types preparedState args instruction accounts = some call ∧
      (types.invoke (seedReference args) preparedState call (.terminated reason) →
        run types before args (.terminated reason)) := by
  obtain ⟨call, readable, retained⟩ := ready.tail_continuation types args before builtState
    preparedState
    instruction accounts ordinary built prepared
  refine ⟨call, readable, ?_⟩
  intro invoked
  exact retained (.terminated reason) (.terminated reason) _ invoked rfl
    ((Owned.cleanup_terminated _ _ _ _).mpr rfl)

/-- A getter input determines a concrete pure decision and exactly its owned
Vec cleanup, before any Anchor error conversion. Only matching-key Some needs
a current byte observation; None and wrong-key branches remain admitted. -/
theorem decode_inputs_complete {binding : Binding} (types : Types binding)
    (before : types.builder.instruction.State) (expected : Solanalib.Runtime.Pubkey)
    (returned : Option (Solanalib.Runtime.Pubkey × types.builder.instruction.ByteResource))
    (ready : ∀ data, returned = some (expected, data) → types.builder.instruction.bytes.Live before
      data) :
    ∃ result,
      ∀ final, Owned.cleanup types.builder.instruction.doubleUnwind
        (match returned with
          | none => []
          | some (_, data) => [types.builder.instruction.bytes.dropAction data])
        (.returned result before) final → decodeReturnData types expected before returned final :=
          by
  cases returned with
  | none =>
    exact ⟨.error (binding.release.invalidInstructionData types.StringResource), fun _ cleaned =>
      cleaned⟩
  | some pair =>
    obtain ⟨key, data⟩ := pair
    apply decode_return_continuation types before expected key data
    intro same
    exact ready data (by rw [same])

/-- Bind any actual getter return, decoder/destructor exit and conversion
exit. Unwind/terminal decoder exits never enter error conversion. -/
theorem getSize_from_returned {binding : Binding} (types : Types binding)
    (expected : Solanalib.Runtime.Pubkey) (before returnedState : types.builder.instruction.State)
    (returned : Option (Solanalib.Runtime.Pubkey × types.builder.instruction.ByteResource))
    (decoded : Outcome types.builder.instruction.State
      (Except (binding.release.ProgramError types.StringResource) Return)
      types.builder.instruction.Unwind types.builder.instruction.Terminal) (pending : Exit types)
    (getter : types.getReturnData before () (.returned returned returnedState))
    (decoder : decodeReturnData types expected returnedState returned decoded)
    (converted : Converted types decoded pending) : getSize types expected before () pending := by
  refine ⟨.returned returned returnedState, getter, decoded, decoder, ?_⟩
  cases decoded <;> exact converted

/-- Finish the full size wrapper after its actual successful statement exit.
The array has already been released; the instruction and remaining context
remain owned until this final cleanup. -/
theorem run_after_size_statement {binding : Binding} (types : Types binding) (args : Input types)
    (before builtState preparedState afterStatement : types.builder.instruction.State)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value)
    (sizing : binding.operation = .getAccountDataSize)
    (built : build types.builder before (argsConstruction args) (.returned (.ok instruction)
      builtState))
    (prepared : prepareAccounts types args builtState () (.returned accounts preparedState))
    (statement : sizeInvoke types args instruction accounts preparedState () (.returned (.ok ())
      afterStatement))
    (pending final : Exit types) (getter : getSize types (selectedProgram args) afterStatement ()
      pending)
    (cleanup : Owned.cleanup types.builder.instruction.doubleUnwind
      (Token.InstructionAllocated.drops types.builder.instruction instruction ++
        remainingContextDrops types args)
      pending final) : run types before args final := by
  apply run_after_prepared types args before builtState preparedState instruction accounts final
    built prepared
  simp only [afterPrepared, sizing, ↓reduceIte]
  exact ⟨pending, ⟨.returned (.ok ()) afterStatement, statement, getter⟩, cleanup⟩

/-- For every actual getter return reached through an admitted size call,
the local decision exists and each supplied Vec-drop/conversion/final-cleanup
continuation yields the full source-wrapper result. -/
theorem Ready.size_return_continuation {binding : Binding} (types : Types binding) (args : Input
  types)
    (before builtState preparedState afterStatement returnedState : types.builder.instruction.State)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value)
    (sizing : binding.operation = .getAccountDataSize) (ready : Ready types before args)
    (built : build types.builder before (argsConstruction args) (.returned (.ok instruction)
      builtState))
    (prepared : prepareAccounts types args builtState () (.returned accounts preparedState))
    (statement : sizeInvoke types args instruction accounts preparedState () (.returned (.ok ())
      afterStatement))
    (returned : Option (Solanalib.Runtime.Pubkey × types.builder.instruction.ByteResource))
    (getter : types.getReturnData afterStatement () (.returned returned returnedState)) :
    ∃ result, ∀ decoded pending final,
      Owned.cleanup types.builder.instruction.doubleUnwind
        (match returned with
          | none => []
          | some (_, data) => [types.builder.instruction.bytes.dropAction data])
        (.returned result returnedState) decoded →
      Converted types decoded pending →
      Owned.cleanup types.builder.instruction.doubleUnwind
        (Token.InstructionAllocated.drops types.builder.instruction instruction ++
          remainingContextDrops types args)
        pending final → run types before args final := by
  have bytesReady : ∀ data, returned = some (selectedProgram args, data) →
      types.builder.instruction.bytes.Live returnedState data := by
    intro data equal
    apply ready.returnedBytes sizing instruction builtState built accounts preparedState prepared
      afterStatement statement data returnedState
    simpa only [equal] using getter
  obtain ⟨result, decision⟩ := decode_inputs_complete types returnedState (selectedProgram args)
    returned bytesReady
  refine ⟨result, ?_⟩
  intro decoded pending final dropped converted cleanup
  exact run_after_size_statement types args before builtState preparedState afterStatement
    instruction accounts
    sizing built prepared statement pending final
    (getSize_from_returned types (selectedProgram args) afterStatement returnedState returned
      decoded pending
      getter (decision decoded dropped) converted) cleanup

/-- Builder rejection converts exactly its source error before full-context
cleanup. No invocation or account clone is introduced on this path. -/
theorem run_build_error {binding : Binding} (types : Types binding) (args : Input types)
    (before after : types.builder.instruction.State) (error : Token.Error) (pending final : Exit
      types)
    (built : build types.builder before (argsConstruction args) (.returned (.error error) after))
    (converted : Callback.map Except.error (convert types) after (builderFailure types error)
      pending)
    (cleanup : Owned.cleanup types.builder.instruction.doubleUnwind (fullContextDrops types args)
      pending final) :
    run types before args final :=
  ⟨.returned (.error error) after, built, pending, converted, cleanup⟩

theorem run_build_unwind {binding : Binding} (types : Types binding) (args : Input types)
    (before after : types.builder.instruction.State) (reason : types.builder.instruction.Unwind)
    (final : Exit types) (built : build types.builder before (argsConstruction args) (.unwound
      reason after))
    (cleanup : Owned.cleanup types.builder.instruction.doubleUnwind (fullContextDrops types args)
      (.unwound reason after) final) : run types before args final :=
  ⟨.unwound reason after, built, cleanup⟩

theorem run_build_terminal {binding : Binding} (types : Types binding) (args : Input types)
    (before : types.builder.instruction.State) (reason : types.builder.instruction.Terminal)
    (built : build types.builder before (argsConstruction args) (.terminated reason)) :
    run types before args (.terminated reason) :=
  ⟨.terminated reason, built, rfl⟩

end Solanalib.Specs.Core.AnchorSplTokenOperations
