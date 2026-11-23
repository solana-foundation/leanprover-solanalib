/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.Resources

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorSplTokenOperations

/-- The source `map_err(Into::into)` retains success and moves an error into
the release-selected Anchor representation in the actual returned state. -/
def convertResult {binding : Binding} {Value : Type} (types : Types binding) :
    Callback.Run types.builder.instruction.State
      (Except (binding.release.ProgramError types.StringResource) Value)
      (Except (Error types) Value) types.builder.instruction.Unwind
        types.builder.instruction.Terminal :=
  fun before value => match value with
  | .ok result => fun final => final = .returned (.ok result) before
  | .error error => Callback.map Except.error (convert types) before error

/-- Borrow the constructed instruction and seed slices at this exact state,
then call the supplied invocation signature. The callee implementation is not
part of the wrapper model. Conversion precedes the surrounding cleanup. -/
def invokeAndConvert {binding : Binding} (types : Types binding) (args : Input types)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value) :
    Callback.Run types.builder.instruction.State Unit (Except (Error types) Unit)
      types.builder.instruction.Unwind types.builder.instruction.Terminal :=
  fun before _ final => ∃ call, request types before args instruction accounts = some call ∧
    Callback.bind (fun state (_ : Unit) => types.invoke (seedReference args) state call)
      (fun value state => convertResult types state value) before () final

/-- The size decoder owns the returned Vec. It checks the program key before
reading its bytes, and releases that Vec before the outer Anchor conversion.
Length must be exactly eight, not merely a readable eight-byte prefix. -/
def decodeReturnData {binding : Binding} (types : Types binding) (expected :
  Solanalib.Runtime.Pubkey) :
    Callback.Run types.builder.instruction.State
      (Option (Solanalib.Runtime.Pubkey × types.builder.instruction.ByteResource))
      (Except (binding.release.ProgramError types.StringResource) Return)
      types.builder.instruction.Unwind types.builder.instruction.Terminal :=
  fun before value final => match value with
  | none => final = .returned (.error (binding.release.invalidInstructionData
    types.StringResource)) before
  | some (key, data) =>
      if key ≠ expected then
        Owned.cleanup types.builder.instruction.doubleUnwind
          [types.builder.instruction.bytes.dropAction data]
          (.returned (.error (binding.release.incorrectProgramId types.StringResource)) before)
            final
      else ∃ bytes, types.builder.instruction.bytes.current before data = some bytes ∧
        Owned.cleanup types.builder.instruction.doubleUnwind
          [types.builder.instruction.bytes.dropAction data]
          (.returned (if bytes.length = 8 then .ok (.size (UInt64.ofNat (Solanalib.Runtime.leNat
            bytes)))
            else .error (binding.release.invalidInstructionData types.StringResource)) before) final

/-- The getter is an explicit signature-level provider. Each returned vector
is decoded and dropped before the resulting ProgramError is converted. -/
def getSize {binding : Binding} (types : Types binding) (expected : Solanalib.Runtime.Pubkey) :
    Callback.Run types.builder.instruction.State Unit (Except (Error types) Return)
      types.builder.instruction.Unwind types.builder.instruction.Terminal :=
  Callback.bind types.getReturnData fun returned before =>
    Callback.bind (fun state (_ : Unit) => decodeReturnData types expected state returned)
      (fun result state => convertResult types state result) before ()

/-- The statement temporary in `invoke(...)?;` is gone before the getter.
On Err, conversion happens inside the statement before this array cleanup.
An unwind also releases the array before the enclosing instruction/context. -/
def sizeInvoke {binding : Binding} (types : Types binding) (args : Input types)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value) :
    Callback.Run types.builder.instruction.State Unit (Except (Error types) Unit)
      types.builder.instruction.Unwind types.builder.instruction.Terminal :=
  Owned.scope types.builder.instruction.doubleUnwind (infoDrops types accounts)
    (invokeAndConvert types args instruction accounts)

/-- Normal tail-expression cleanup for the reviewed edition-2021 helpers.
The copied/moved array is distinct from the fields still owned by CpiContext. -/
def tailDrops {binding : Binding} (types : Types binding) (args : Input types)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value) :=
  Token.InstructionAllocated.drops types.builder.instruction instruction ++
    infoDrops types accounts ++ remainingContextDrops types args

/-- Size querying has a statement boundary before its return expression;
ordinary helpers have a single invoke/map_err tail expression. -/
def afterPrepared {binding : Binding} (types : Types binding) (args : Input types)
    (instruction : InstructionOwner types) (accounts : List AccountInfo.Value) :
    Callback.Run types.builder.instruction.State Unit (Except (Error types) Return)
      types.builder.instruction.Unwind types.builder.instruction.Terminal :=
  if binding.operation = .getAccountDataSize then
    Owned.scope types.builder.instruction.doubleUnwind
      (Token.InstructionAllocated.drops types.builder.instruction instruction ++
        remainingContextDrops types args)
      (Callback.bind (sizeInvoke types args instruction accounts)
        fun result before => match result with
        | .error error => fun final => final = .returned (.error error) before
        | .ok () => getSize types (selectedProgram args) before ())
  else Owned.scope types.builder.instruction.doubleUnwind (tailDrops types args instruction
    accounts)
    (Callback.map (Except.map fun _ => Return.unit) (invokeAndConvert types args instruction
      accounts))

/-- Construction precedes all argument moves/clones. Program rejection and
fallible pointer conversion leave the context intact for its full destructor.
Each primitive terminal stops with no invented subsequent cleanup or state. -/
def run {binding : Binding} (types : Types binding) :
    Callback.Run types.builder.instruction.State (Input types) (Except (Error types) Return)
      types.builder.instruction.Unwind types.builder.instruction.Terminal :=
  fun before args final => ∃ built, build types.builder before (argsConstruction args) built ∧
    match built with
    | .returned (.error error) after =>
        Owned.scope types.builder.instruction.doubleUnwind (fullContextDrops types args)
          (Callback.map Except.error (convert types)) after (builderFailure types error) final
    | .returned (.ok instruction) after =>
        Callback.bind (prepareAccounts types args)
          (fun accounts state => afterPrepared types args instruction accounts state ()) after ()
            final
    | .unwound reason after => Owned.cleanup types.builder.instruction.doubleUnwind
        (fullContextDrops types args) (.unwound reason after) final
    | .terminated reason => final = .terminated reason

/-- These gates concern only actual reached partial reads: the copied
extension vector, the borrowed instruction and seeds, and matching-key return
data. They assume neither a successful CPI nor any finite dependency exit. -/
structure Ready {binding : Binding} (types : Types binding)
    (before : types.builder.instruction.State) (args : Input types) : Prop where
  buildInput : BuildInputReady types.builder before (argsConstruction args)
  requestInput : ∀ instruction builtState,
    build types.builder before (argsConstruction args) (.returned (.ok instruction) builtState) →
    ∀ accounts preparedState,
      prepareAccounts types args builtState () (.returned accounts preparedState) →
      RequestReadable types preparedState args instruction
  returnedBytes : binding.operation = .getAccountDataSize →
    ∀ instruction builtState,
      build types.builder before (argsConstruction args) (.returned (.ok instruction) builtState) →
    ∀ accounts preparedState,
      prepareAccounts types args builtState () (.returned accounts preparedState) →
    ∀ afterInvoke,
      sizeInvoke types args instruction accounts preparedState () (.returned (.ok ()) afterInvoke) →
    ∀ data returnedState,
      types.getReturnData afterInvoke ()
        (.returned (some (selectedProgram args, data)) returnedState) →
      types.builder.instruction.bytes.Live returnedState data

def family (binding : Binding) : Family where
  Index := Types binding
  State := fun types => types.builder.instruction.State
  Args := Input
  Value := fun types => Except (Error types) Return
  Unwind := fun types => types.builder.instruction.Unwind
  Terminal := fun types => types.builder.instruction.Terminal
  contract := fun types => { requires := Ready types, post := run types }

def reference (binding : Binding) : FamilyRun (family binding) := run

theorem reference_holds (binding : Binding) : FamilyReference (family binding) (reference binding)
  := by
  intro _ _ _ _ _ execution
  exact execution

/-- The local decoder has an actual finite exit for every admitted input and
each actual destructor continuation. Wrong-key branches need no byte read. -/
theorem decode_return_continuation {binding : Binding} (types : Types binding)
    (before : types.builder.instruction.State) (expected key : Solanalib.Runtime.Pubkey)
    (data : types.builder.instruction.ByteResource)
    (readable : key = expected → types.builder.instruction.bytes.Live before data) :
    ∃ result, ∀ final,
      Owned.cleanup types.builder.instruction.doubleUnwind
        [types.builder.instruction.bytes.dropAction data] (.returned result before) final →
      decodeReturnData types expected before (some (key, data)) final := by
  by_cases same : key = expected
  · obtain ⟨bytes, current⟩ := readable same
    refine ⟨if bytes.length = 8 then .ok (.size (UInt64.ofNat (Solanalib.Runtime.leNat bytes)))
      else .error (binding.release.invalidInstructionData types.StringResource), ?_⟩
    intro final cleaned
    simp only [decodeReturnData, same, ne_eq, not_true_eq_false, ↓reduceIte]
    exact ⟨bytes, current, cleaned⟩
  · refine ⟨.error (binding.release.incorrectProgramId types.StringResource), ?_⟩
    intro final cleaned
    simpa only [decodeReturnData, same, ne_eq, not_false_eq_true, ↓reduceIte] using cleaned

end Solanalib.Specs.Core.AnchorSplTokenOperations
