/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOperationsCallbacks
public import Solanalib.Specs.Core.AnchorErrorOwnedContracts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOperations

/-- Operational From<AnchorError> family. The full owned input is moved into
the selected representation; primitive Box exits remain explicit. -/
def fromAnchorFamily : Family where
  Index := Types
  State := Types.State
  Args := fun types => AnchorPayload types.StringResource
  Value := Types.Error
  Unwind := fun _ => Empty
  Terminal := Types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fromAnchor types.storage types.ops }

def fromAnchorRun : FamilyRun fromAnchorFamily := fun types => fromAnchor types.storage types.ops

theorem fromAnchor_reference : FamilyReference fromAnchorFamily fromAnchorRun :=
  fun _ _ _ _ _ run => run

/-- The complete dependency error, including any legacy String, is moved.
The family does not replace it by a numeric code or require it to be builtin. -/
def fromProgramFamily : Family where
  Index := Types
  State := Types.State
  Args := Types.Program
  Value := Types.Error
  Unwind := fun _ => Empty
  Terminal := Types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fromProgram types.storage types.ops }

def fromProgramRun : FamilyRun fromProgramFamily := fun types => fromProgram types.storage types.ops

theorem fromProgram_reference : FamilyReference fromProgramFamily fromProgramRun :=
  fun _ _ _ _ _ run => run

/-- Same-receiver diagnostic replacement, including the actual destructor calls of the old
comparison and any terminal exit of those dependencies. -/
def pubkeysFamily : Family where
  Index := Types
  State := Types.State
  Args := fun types => types.Error × Solanalib.Runtime.Pubkey × Solanalib.Runtime.Pubkey
  Value := Types.Error
  Unwind := fun _ => Empty
  Terminal := Types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args =>
      withPubkeys types.storage types.ops args.2.1 args.2.2 before args.1 }

def pubkeysRun : FamilyRun pubkeysFamily := fun types before args =>
  withPubkeys types.storage types.ops args.2.1 args.2.2 before args.1

theorem pubkeys_reference : FamilyReference pubkeysFamily pubkeysRun :=
  fun _ _ _ _ _ run => run

/-- Source replacement preserves borrowed filename data and releases only an
old owned account name, if one was present. -/
def sourceFamily : Family where
  Index := Types
  State := Types.State
  Args := fun types => types.Error × AnchorError.Source
  Value := Types.Error
  Unwind := fun _ => Empty
  Terminal := Types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args => withSource types.storage types.ops args.2 before args.1 }

def sourceRun : FamilyRun sourceFamily := fun types before args =>
  withSource types.storage types.ops args.2 before args.1

theorem source_reference : FamilyReference sourceFamily sourceRun :=
  fun _ _ _ _ _ run => run

/-- Generated ErrorCode enums use a finite, source-reviewed table. A Fin
argument cannot designate an absent enum variant or inject arbitrary text. -/
def codeFamily (codes : Array Code) : Family where
  Index := Types
  State := Types.State
  Args := fun _ => Fin codes.size
  Value := Types.Error
  Unwind := fun _ => Empty
  Terminal := Types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before code => fromCode types.storage types.ops before codes[code] }

def codeRun (codes : Array Code) : FamilyRun (codeFamily codes) :=
    fun (types : Types) (before : types.State) (code : Fin codes.size) =>
  fromCode types.storage types.ops before codes[code]

theorem code_reference (codes : Array Code) : FamilyReference (codeFamily codes) (codeRun codes) :=
  fun _ _ _ _ _ run => run

/-- ErrorCode::name has only one String-copy dependency. No Box, ProgramError
or unrelated formatting operation is required by this source call. -/
structure CodeNameTypes where
  State : Type
  StringResource : Type
  Terminal : Type
  copyLiteral : Callback.Run State String StringResource Empty Terminal

def codeNameFamily (codes : Array Code) : Family where
  Index := CodeNameTypes
  State := CodeNameTypes.State
  Args := fun _ => Fin codes.size
  Value := CodeNameTypes.StringResource
  Unwind := fun _ => Empty
  Terminal := CodeNameTypes.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before code => types.copyLiteral before codes[code].name }

def codeNameRun (codes : Array Code) : FamilyRun (codeNameFamily codes) :=
    fun (types : CodeNameTypes) (before : types.State) (code : Fin codes.size) =>
  types.copyLiteral before codes[code].name

theorem codeName_reference (codes : Array Code) :
    FamilyReference (codeNameFamily codes) (codeNameRun codes) := fun _ _ _ _ _ run => run

/-- Finite primitive provider, with actual allocated String/Box identities.
The selected sample uses inline payloads; boxed executions are tested too. -/
abbrev sampleTypes : Types where
  State := AnchorErrorOwned.Reference.State
  Program := ProgramError.Value
  StringResource := AnchorErrorOwned.Reference.StringId
  BoxResource := AnchorErrorOwned.Reference.BoxId
  Terminal := AnchorErrorOwned.Reference.Failure
  storage := .inline
  ops := Ops.fromOwned AnchorErrorOwned.Reference.ops

abbrev samplePayload : Payload ProgramError.Value AnchorErrorOwned.Reference.StringId :=
  .anchor AnchorErrorOwned.sampleAnchor

theorem fromAnchor_hasExecution :
    FamilyHasExecution fromAnchorFamily fromAnchorRun sampleTypes :=
  ⟨AnchorErrorOwned.sampleAnchorState, AnchorErrorOwned.sampleAnchor, _, trivial, rfl⟩

theorem fromAnchor_satisfiable : FamilySatisfiable fromAnchorFamily sampleTypes :=
  fromAnchor_hasExecution.satisfiable

theorem fromProgram_hasExecution :
    FamilyHasExecution fromProgramFamily fromProgramRun sampleTypes :=
  ⟨AnchorErrorOwned.Reference.initial 0, .invalidAccountData, _, trivial, rfl⟩

theorem fromProgram_satisfiable : FamilySatisfiable fromProgramFamily sampleTypes :=
  fromProgram_hasExecution.satisfiable

theorem pubkeys_hasExecution : FamilyHasExecution pubkeysFamily pubkeysRun sampleTypes := by
  refine ⟨AnchorErrorOwned.sampleAnchorState,
    (samplePayload, Solanalib.Runtime.Pubkey.ofNat 3, Solanalib.Runtime.Pubkey.ofNat 4),
    .returned (samplePayload.withCompared (some (.pubkeys
      (Solanalib.Runtime.Pubkey.ofNat 3) (Solanalib.Runtime.Pubkey.ofNat 4))))
        AnchorErrorOwned.sampleAnchorState,
    trivial, ?_⟩
  exact ⟨samplePayload, rfl, .returned () AnchorErrorOwned.sampleAnchorState,
    rfl, rfl⟩

theorem pubkeys_satisfiable : FamilySatisfiable pubkeysFamily sampleTypes :=
  pubkeys_hasExecution.satisfiable

theorem source_hasExecution : FamilyHasExecution sourceFamily sourceRun sampleTypes := by
  refine ⟨AnchorErrorOwned.sampleAnchorState, (samplePayload, ⟨"source.rs", 7⟩),
    .returned (samplePayload.withOrigin (some (.source ⟨"source.rs", 7⟩)))
      AnchorErrorOwned.sampleAnchorState, trivial, ?_⟩
  exact ⟨samplePayload, rfl, .returned () AnchorErrorOwned.sampleAnchorState,
    rfl, rfl⟩

theorem source_satisfiable : FamilySatisfiable sourceFamily sampleTypes :=
  source_hasExecution.satisfiable

/-- The first concrete enum arm supplies a closed witness in each source
facade. Its two actual allocations occur in source evaluation order. -/
theorem code_hasExecution (codes : Array Code) (code : Fin codes.size) :
    FamilyHasExecution (codeFamily codes) (codeRun codes) sampleTypes := by
  let before := AnchorErrorOwned.Reference.initial 2
  let name := AnchorErrorOwned.Reference.stringResult false before codes[code].name
  let message := AnchorErrorOwned.Reference.stringResult true name.2 codes[code].message
  refine ⟨before, code, .returned (.anchor ⟨name.1, codes[code].number, message.1, none, none⟩)
    message.2, trivial, ?_⟩
  refine ⟨.returned name.1 name.2, ?_, .returned message.1 message.2, ?_, rfl⟩
  · change AnchorErrorOwned.Reference.allocateString false before codes[code].name = _
    rfl
  · change AnchorErrorOwned.Reference.allocateString true name.2 codes[code].message = _
    rfl

theorem code_satisfiable (codes : Array Code) (code : Fin codes.size) :
    FamilySatisfiable (codeFamily codes) sampleTypes := (code_hasExecution codes code).satisfiable

abbrev codeNameSample : CodeNameTypes where
  State := AnchorErrorOwned.Reference.State
  StringResource := AnchorErrorOwned.Reference.StringId
  Terminal := AnchorErrorOwned.Reference.Failure
  copyLiteral := AnchorErrorOwned.Reference.ops.copyLiteral

theorem codeName_hasExecution (codes : Array Code) (code : Fin codes.size) :
    FamilyHasExecution (codeNameFamily codes) (codeNameRun codes) codeNameSample :=
  ⟨AnchorErrorOwned.Reference.initial 1, code,
    .returned (AnchorErrorOwned.Reference.stringResult false
      (AnchorErrorOwned.Reference.initial 1) codes[code].name).1
      (AnchorErrorOwned.Reference.stringResult false
      (AnchorErrorOwned.Reference.initial 1) codes[code].name).2, trivial, rfl⟩

theorem codeName_satisfiable (codes : Array Code) (code : Fin codes.size) :
    FamilySatisfiable (codeNameFamily codes) codeNameSample :=
  (codeName_hasExecution codes code).satisfiable

end Solanalib.Specs.Core.AnchorErrorOperations
