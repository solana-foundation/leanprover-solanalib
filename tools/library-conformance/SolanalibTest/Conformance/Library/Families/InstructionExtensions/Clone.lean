/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram.Capabilities
import Solanalib.Specs.SolanaProgram.Instruction
import SolanalibTest.Conformance.Library.Families.InstructionExtensions.Common
import SolanalibTest.Conformance.Library.Families.Instructions.Values
import Solanalib.Specs.SolanaInstruction.AccountMetaGeneric

set_option autoImplicit false

open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.InstructionExtensions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Borsh
open SolanalibTest.Conformance.Library.Families.Instructions

def metadataTypes : InstructionMeta.Types := InstructionMeta.sample

def metadataFn (before : Instruction.Meta) : Outcome Instruction.Meta Instruction.Meta Empty Empty
  :=
  .returned ((metadataTypes.access.current before ()).getD before) before

def metadataOutcomeJson : Outcome Instruction.Meta Instruction.Meta Empty Empty → Json
  | .returned value state => returnedJson (metaJson value) (metaJson state)
  | .unwound impossible _ => nomatch impossible
  | .terminated impossible => nomatch impossible

theorem metadata_graph (before : Instruction.Meta)
    (outcome : Outcome Instruction.Meta Instruction.Meta Empty Empty) :
    Solanalib.Specs.SolanaInstruction.AccountMeta.clone_run metadataTypes before () outcome ↔
      metadataFn before = outcome := by
  simp [Solanalib.Specs.SolanaInstruction.AccountMeta.clone_run, InstructionMeta.reference,
    InstructionMeta.run, metadataTypes, InstructionMeta.sample, metadataFn, eq_comm]

instance metadataRequires (before : Instruction.Meta) :
    Decidable ((Solanalib.Specs.SolanaInstruction.AccountMeta.clone_contract.contract
      metadataTypes).requires
      before ()) := isTrue ⟨before, trivial, rfl⟩

/-- Native records are made while the original Rust shared borrow is live.
The chosen unit-reference index has that exact admission for every metadata value. -/
theorem metadata_requires_at_recorded_index (before : Instruction.Meta) :
    (Solanalib.Specs.SolanaInstruction.AccountMeta.clone_contract.contract metadataTypes).requires
      before () :=
  of_decide_eq_true (show @decide _ (metadataRequires before) = true from rfl)

def metadataCloneChecker (legacy : Bool) : Checker where
  function := if legacy then
    "<solana_program::instruction::AccountMeta as core::clone::Clone>::clone"
    else "<solana_instruction::account_meta::AccountMeta as core::clone::Clone>::clone"
  generics := []
  reference := "Solanalib.Specs.SolanaInstruction.AccountMeta.clone_run"
  decides := ["Solanalib.Specs.SolanaInstruction.AccountMeta.clone_run"]
  decidesRequires := ["Solanalib.Specs.SolanaInstruction.AccountMeta.clone_run"]
  check := fun c => do
    let before ← metaOf c.state
    let required := decide
      ((Solanalib.Specs.SolanaInstruction.AccountMeta.clone_contract.contract
        metadataTypes).requires before ())
    let recorded ← parseOutcome metaOf metaOf noReason noReason c.outcome
    let verdict := decideGraph _ (metadataFn before) (metadata_graph before) recorded
      metadataOutcomeJson
    pure ⟨required && verdict.admitted, verdict.expected⟩

namespace Program

theorem metadata_graph (before : Instruction.Meta)
    (outcome : Outcome Instruction.Meta Instruction.Meta Empty Empty) :
    Solanalib.Specs.SolanaProgram.instruction.AccountMeta.clone_run metadataTypes before () outcome
      ↔
      metadataFn before = outcome := by
  simp [Solanalib.Specs.SolanaProgram.instruction.AccountMeta.clone_run, InstructionMeta.reference,
    InstructionMeta.run, metadataTypes, InstructionMeta.sample, metadataFn, eq_comm]

instance metadataRequires (before : Instruction.Meta) :
    Decidable ((Solanalib.Specs.SolanaProgram.instruction.AccountMeta.clone_contract.contract
      metadataTypes).requires
      before ()) := isTrue ⟨before, trivial, rfl⟩

theorem metadata_requires_at_recorded_index (before : Instruction.Meta) :
    (Solanalib.Specs.SolanaProgram.instruction.AccountMeta.clone_contract.contract
      metadataTypes).requires before () :=
  of_decide_eq_true (show @decide _ (metadataRequires before) = true from rfl)

def metadataCloneChecker : Checker where
  function := "<solana_program::instruction::AccountMeta as core::clone::Clone>::clone"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.instruction.AccountMeta.clone_run"
  decides := ["Solanalib.Specs.SolanaProgram.instruction.AccountMeta.clone_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.instruction.AccountMeta.clone_run"]
  check := fun c => do
    let before ← metaOf c.state
    let required := decide
      ((Solanalib.Specs.SolanaProgram.instruction.AccountMeta.clone_contract.contract
        metadataTypes).requires before ())
    let recorded ← parseOutcome metaOf metaOf noReason noReason c.outcome
    let verdict := decideGraph _ (metadataFn before) (metadata_graph before) recorded
      metadataOutcomeJson
    pure ⟨required && verdict.admitted, verdict.expected⟩

def accountMetaNewChecker : Checker where
  function := "solana_program::instruction::AccountMeta::new"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.instruction.AccountMeta.new_model"
  decides := ["Solanalib.Specs.SolanaProgram.instruction.AccountMeta.new_model"]
  check := decidePure Solanalib.Specs.SolanaProgram.instruction.AccountMeta.new_model
    (Solanalib.Specs.SolanaProgram.Capabilities.reference .instruction_AccountMeta_new PUnit.unit)
      account_meta_new_evaluated metaArgs metaOf metaJson

def accountMetaNewReadonlyChecker : Checker where
  function := "solana_program::instruction::AccountMeta::new_readonly"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.instruction.AccountMeta.new_readonly_model"
  decides := ["Solanalib.Specs.SolanaProgram.instruction.AccountMeta.new_readonly_model"]
  check := decidePure Solanalib.Specs.SolanaProgram.instruction.AccountMeta.new_readonly_model
    (Solanalib.Specs.SolanaProgram.Capabilities.reference .instruction_AccountMeta_new_readonly
      PUnit.unit) account_meta_new_readonly_evaluated
    metaArgs metaOf metaJson

end Program

def metadataCheckers (legacy : Bool) : List Checker :=
  if legacy then
    [Program.accountMetaNewChecker, Program.accountMetaNewReadonlyChecker,
      Program.metadataCloneChecker]
  else
    [accountMetaNewChecker, accountMetaNewReadonlyChecker, metadataCloneChecker false]

end SolanalibTest.Conformance.Library.Families.InstructionExtensions

namespace SolanalibTest.Conformance.Library.Families.InstructionExtensions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Borsh
open SolanalibTest.Conformance.Library.Families.Instructions

def cloneTypes : InstructionClone.Types := ⟨State, Unit, Nat, Nat, Empty, String⟩

def copyMetas (failAt : Option Nat) (before : State) (resource : Nat) : Out Nat :=
  match metasAt before resource with
  | some values => metaFromList failAt before values
  | none => .terminated "invalid metadata resource"

def copyBytes (failAt : Option Nat) (before : State) (resource : Nat) : Out Nat :=
  match bytesAt before resource with
  | some values => byteFromList failAt before values
  | none => .terminated "invalid byte resource"

def cloneProviders (failAt : Option Nat) : InstructionClone.Providers cloneTypes where
  access := ⟨fun state _ => state.source.isSome = true, fun state _ => state.source⟩
  metas := ⟨metaVec failAt, Callback.ofFunction (copyMetas failAt)⟩
  bytes := ⟨byteVec failAt, Callback.ofFunction (copyBytes failAt)⟩
  doubleUnwind := doubleUnwind

def cloneArgs (failAt : Option Nat) : InstructionClone.Args cloneTypes := ⟨(), cloneProviders
  failAt⟩

def sourceValue (source : Instruction.Value) : Value := ⟨source.programId, 0, 0⟩

def cloneBefore (source : Instruction.Value) : State where
  metas := [some source.metas]
  bytes := [some source.data]
  source := some (sourceValue source)

def copyFn (failAt : Option Nat) (source : Value) (before : State) : Out Value :=
  Outcome.bind (copyMetas failAt before source.metas) fun metas after =>
    Outcome.map (fun bytes => ⟨source.programId, metas, bytes⟩) (copyBytes failAt after source.data)

theorem copy_graph (failAt : Option Nat) (source : Value) (before : State) (outcome : Out Value) :
    InstructionClone.copyRun cloneTypes (cloneProviders failAt) source before () outcome ↔
      copyFn failAt source before = outcome := by
  exact bind_graph _ _ (copyMetas failAt)
    (fun metas after => Outcome.map (fun bytes => (⟨source.programId, metas, bytes⟩ : Value))
      (copyBytes failAt after source.data))
    (fun _ _ _ => Iff.rfl)
    (fun _ _ _ => (protect_iff _ _ _ _ _ _).trans (Callback.map_ofFunction _ _ _ _ _))
    before source.metas outcome

theorem clone_graph (source : Instruction.Value) (failAt : Option Nat) (outcome : Out Value) :
    Solanalib.Specs.SolanaProgram.instruction.Instruction.clone_run cloneTypes (cloneBefore source)
      (cloneArgs failAt) outcome ↔
      copyFn failAt (sourceValue source) (cloneBefore source) = outcome := by
  change (∃ value, some (sourceValue source) = some value ∧
      InstructionClone.copyRun cloneTypes (cloneProviders failAt) value (cloneBefore source) ()
        outcome) ↔ _
  simp only [Option.some.injEq, copy_graph]
  constructor
  · rintro ⟨_, rfl, h⟩; exact h
  · intro h; exact ⟨_, rfl, h⟩

instance cloneRequires (source : Instruction.Value) (failAt : Option Nat) :
    Decidable ((Solanalib.Specs.SolanaProgram.instruction.Instruction.clone_contract.contract
      cloneTypes).requires
      (cloneBefore source) (cloneArgs failAt)) := isTrue ⟨sourceValue source, rfl, rfl⟩

/-- The recorded source includes both live input slots and a live original
shared reference. Fresh output allocations remain separate slots. -/
theorem clone_requires_at_recorded_index (source : Instruction.Value) (failAt : Option Nat) :
    (Solanalib.Specs.SolanaProgram.instruction.Instruction.clone_contract.contract
      cloneTypes).requires
      (cloneBefore source) (cloneArgs failAt) :=
  of_decide_eq_true (show @decide _ (cloneRequires source failAt) = true from rfl)

def instructionCloneChecker (legacy : Bool) : Checker where
  function := if legacy then
    "<solana_program::instruction::Instruction as core::clone::Clone>::clone"
    else "<solana_instruction::Instruction as core::clone::Clone>::clone"
  generics := []
  reference := "Solanalib.Specs.SolanaProgram.instruction.Instruction.clone_run"
  decides := ["Solanalib.Specs.SolanaProgram.instruction.Instruction.clone_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgram.instruction.Instruction.clone_run"]
  check := fun c => do
    let source ← instructionOf c.state
    let failAt ← failure c.args
    let required := decide
      ((Solanalib.Specs.SolanaProgram.instruction.Instruction.clone_contract.contract
        cloneTypes).requires
        (cloneBefore source) (cloneArgs failAt))
    let verdict := decideObserved _ (copyFn failAt (sourceValue source) (cloneBefore source))
      (clone_graph source failAt) (observed true) (some c.outcome) (outcomeJson true)
    pure ⟨required && verdict.admitted, verdict.expected⟩

end SolanalibTest.Conformance.Library.Families.InstructionExtensions
