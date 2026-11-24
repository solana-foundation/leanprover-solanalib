/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenBuilders.Execution
import SolanalibTest.Conformance.Library.Families.TokenInterface.Instructions
import Solanalib.Specs.SplToken
import Solanalib.Specs.SplToken2022
import Solanalib.Specs.SplTokenMetadataInterface
import Solanalib.Specs.SplMemo

set_option autoImplicit false

open Lean (Json)

open Solanalib.Specs.SplToken2022

namespace SolanalibTest.Conformance.Library.Families.TokenBuilders

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open SolanalibTest.Conformance.Library.Families.TokenInterface
open Allocated (ST St Out)

theorem observed_iff {Outcome Observation : Type} (relation : Outcome → Prop)
    (computed : Option Outcome) (exact : PGraph relation computed)
    (observe : Outcome → Option Observation) (recorded : Observation) :
    (∃ outcome, relation outcome ∧ observe outcome = some recorded) ↔
      computed.bind observe = some recorded := by
  constructor
  · rintro ⟨outcome, admitted, observed⟩
    rw [(exact outcome).mp admitted]
    exact observed
  · intro observed
    cases computed with
    | none => cases observed
    | some outcome => exact ⟨outcome, (exact outcome).mpr rfl, observed⟩

/-- Decide an actual registered family reference through its proved finite
interpreter. The observed native allocation counters are checked as well. -/
def allocatedChecker {Args : Type} (function name : String) (read : Json → Result Args)
    (reference : St → Args → Out Allocated.Result → Prop)
    (computed : St → Args → Option (Out Allocated.Result))
    (exact : ∀ state args, PGraph (reference state args) (computed state args)) : Checker where
  function := function
  generics := []
  reference := name
  decides := [name]
  check := fun c => do
    let _ ← unitState c.state
    let args ← read c.args
    let result := computed InstructionAllocated.Witness.initialState args
    let expected := result.elim Json.null Instructions.outJson
    if (← (← field c.outcome "exit").getStr?) != "returned" then
      return ⟨false, expected⟩
    let recorded := (← resultOf instruction (← field c.outcome "result"),
      ← Instructions.heap (← field c.outcome "state"))
    have : Decidable (∃ outcome, reference InstructionAllocated.Witness.initialState args outcome ∧
        Allocated.observe? outcome = some recorded) :=
      decidable_of_iff _ (observed_iff _ _ (exact _ args) Allocated.observe? recorded).symm
    return ⟨decide (∃ outcome, reference InstructionAllocated.Witness.initialState args outcome ∧
      Allocated.observe? outcome = some recorded), expected⟩

def amountDecimals (j : Json) : Result Instruction.AmountDecimalsArgs := do
  return ⟨← Instructions.transferArgs j, ← uintField 8 j "decimals"⟩

def setAuthority (count : Nat) (j : Json) : Result (Instruction.SetAuthorityArgs count) := do
  let code ← natField j "authority_type"
  if h : code < count then
    return ⟨← keyField j "program_id", ← keyField j "owned", ← asOption pubkey (← field j
      "new_authority"),
      ⟨code, h⟩, ← keyField j "owner", ← listField j "signers" pubkey⟩
  else throw "authority enum discriminant outside the selected released enum"

def mint2 (j : Json) : Result Instruction.InitializeMint2Args := do
  return ⟨← keyField j "program_id", ← keyField j "mint", ← uintField 8 j "decimals",
    ← keyField j "authority", ← asOption pubkey (← field j "freeze_authority")⟩

def singleAccount (j : Json) : Result Instruction.SingleAccountArgs := do
  return ⟨← keyField j "program_id", ← keyField j "account"⟩

def closeAuthority (j : Json) : Result Instruction.InitializeMintCloseAuthorityArgs := do
  return ⟨← singleAccount j, ← asOption pubkey (← field j "close_authority")⟩

def pointer (j : Json) : Result MetadataPointer.Args := do
  return ⟨← keyField j "program_id", ← keyField j "mint",
    ← asOption pubkey (← field j "authority"), ← asOption pubkey (← field j "metadata_addre\
      ss")⟩

def boolChecker (function name : String) (reference : Unit → Solanalib.Runtime.Pubkey → Bool ×
  Unit) : Checker where
  function := function
  generics := []
  reference := name
  decides := [name]
  check := fun c => do
    decideReturns (returnsOf reference) reference rfl (← unitState c.state) (← pubkey c.args)
      Json.getBool? unitState Lean.toJson (fun _ => Json.null) c.outcome

def legacy : List Checker := [
  allocatedChecker "spl_token::instruction::mint_to"
    "Solanalib.Specs.SplToken.instruction.mint_to_reference"
    Instructions.transferArgs (Solanalib.Specs.SplToken.instruction.mint_to_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.mintToPlan .legacy args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token::instruction::burn_checked"
    "Solanalib.Specs.SplToken.instruction.burn_checked_reference"
    amountDecimals (Solanalib.Specs.SplToken.instruction.burn_checked_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.burnCheckedPlan .legacy args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token::instruction::close_account"
    "Solanalib.Specs.SplToken.instruction.close_account_reference"
    Instructions.authorityArgs (Solanalib.Specs.SplToken.instruction.close_account_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.closeAccountPlan .legacy args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token::instruction::set_authority"
    "Solanalib.Specs.SplToken.instruction.set_authority_reference"
    (setAuthority 4) (Solanalib.Specs.SplToken.instruction.set_authority_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.setAuthorityPlan .legacy args))
    (fun state _ => Allocated.run_fn state _),
  boolChecker "spl_token::native_mint::check_id"
    "Solanalib.Specs.SplToken.native_mint.check_id_reference"
    Solanalib.Specs.SplToken.native_mint.check_id_reference]

def token2022 : List Checker := [
  allocatedChecker "spl_token_2022::instruction::mint_to"
    "Solanalib.Specs.SplToken2022.instruction.mint_to_reference"
    Instructions.transferArgs (instruction.mint_to_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.mintToPlan .either args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token_2022::instruction::burn_checked"
    "Solanalib.Specs.SplToken2022.instruction.burn_checked_reference"
    amountDecimals (instruction.burn_checked_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.burnCheckedPlan .either args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token_2022::instruction::close_account"
    "Solanalib.Specs.SplToken2022.instruction.close_account_reference"
    Instructions.authorityArgs (instruction.close_account_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.closeAccountPlan .either args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token_2022::instruction::freeze_account"
    "Solanalib.Specs.SplToken2022.instruction.freeze_account_reference"
    Instructions.authorityArgs (instruction.freeze_account_reference
      ST)
    (fun state args => Allocated.runF state (InstructionAllocated.freezeAccountPlan .either args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token_2022::instruction::thaw_account"
    "Solanalib.Specs.SplToken2022.instruction.thaw_account_reference"
    Instructions.authorityArgs (instruction.thaw_account_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.thawAccountPlan .either args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token_2022::instruction::transfer_checked"
    "Solanalib.Specs.SplToken2022.instruction.transfer_checked_reference"
    Instructions.transferCheckedArgs
      (instruction.transfer_checked_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.transferCheckedPlan .either args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token_2022::instruction::set_authority"
    "Solanalib.Specs.SplToken2022.instruction.set_authority_reference"
    (setAuthority 17) (instruction.set_authority_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.setAuthorityPlan .either args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token_2022::instruction::initialize_account3"
    "Solanalib.Specs.SplToken2022.instruction.initialize_account3_reference"
    Instructions.initArgs (instruction.initialize_account3_reference
      ST)
    (fun state args => Allocated.runF state (InstructionAllocated.initializeAccount3Plan .either
      args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token_2022::instruction::initialize_mint2"
    "Solanalib.Specs.SplToken2022.instruction.initialize_mint2_reference"
    mint2 (instruction.initialize_mint2_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.initializeMint2Plan .either args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token_2022::instruction::initialize_immutable_owner"
    "Solanalib.Specs.SplToken2022.instruction.initialize_immutable_owner_reference"
    singleAccount (instruction.initialize_immutable_owner_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.initializeImmutableOwnerPlan
      .either args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token_2022::instruction::initialize_mint_close_authority"
    "Solanalib.Specs.SplToken2022.instruction.initialize_mint_close_authority_reference"
    closeAuthority
      (instruction.initialize_mint_close_authority_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.initializeMintCloseAuthorityPlan
      args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token_2022::instruction::initialize_non_transferable_mint"
    "Solanalib.Specs.SplToken2022.instruction.initialize_non_transferable_mint_reference"
    singleAccount
      (instruction.initialize_non_transferable_mint_reference ST)
    (fun state args => Allocated.runF state (InstructionAllocated.initializeNonTransferableMintPlan
      args))
    (fun state _ => Allocated.run_fn state _),
  allocatedChecker "spl_token_2022::extension::metadata_pointer::instruction::initialize"
    "Solanalib.Specs.SplToken2022.extension.metadata_pointer.instruction.initialize_referen\
      ce"
    pointer
      (extension.metadata_pointer.instruction.initialize_reference ST)
    Execution.pointerF Execution.pointer_graph,
  Instructions.idChecker "spl_token_2022::id" "Solanalib.Specs.SplToken2022.id_reference"
    id_reference,
  boolChecker "spl_token_2022::native_mint::check_id"
    "Solanalib.Specs.SplToken2022.native_mint.check_id_reference"
    native_mint.check_id_reference]

namespace Metadata

open MetadataInitialize

def readText (j : Json) : Result Text := do
  return ⟨← (← field j "name").getStr?, ← (← field j "symbol").getStr?, ← (← field j "uri").getStr?⟩

def readArgs (j : Json) : Result (Args Nat) := do
  return ⟨← keyField j "program_id", ← keyField j "metadata", ← keyField j "update_authorit\
    y",
    ← keyField j "mint", ← keyField j "mint_authority", ⟨0, 1, 2⟩⟩

def initial (text : Text) : St := (text.bytes.map some, [])

/-- Empty input Strings have an owned logical slot but no heap allocation.
All other retired input slots and the Borsh temporary count as frees. The
recorded profile counts fresh allocations, not reallocations. -/
def heap (before after : St) : Allocated.Heap :=
  let retiredEmpty := ((List.range before.1.length).filter fun n =>
    before.1.current n == some [] && (after.1.current n).isNone).length
  ⟨after.1.length + after.2.length - (before.1.length + before.2.length),
    Allocated.retired after.1 + Allocated.retired after.2 - retiredEmpty⟩

def observe (before : St) : Out Execution.Metadata.Value → Option (Solanalib.Runtime.CpiInstruction
  × Allocated.Heap)
  | .returned value after =>
    (InstructionAllocated.observe ST after value).map fun instruction => (instruction, heap before
      after)
  | .unwound _ _ | .terminated _ => none

def checker : Checker where
  function := "spl_token_metadata_interface::instruction::initialize"
  generics := []
  reference := "Solanalib.Specs.SplTokenMetadataInterface.instruction.initialize_reference"
  decides := ["Solanalib.Specs.SplTokenMetadataInterface.instruction.initialize_reference"]
  check := fun c => do
    let _ ← unitState c.state
    let text ← readText c.args
    let args ← readArgs c.args
    let before := initial text
    let computed := Execution.Metadata.runF before args
    let expected := (computed.bind (observe before)).elim Json.null fun (instruction, heap) =>
      Json.mkObj [("instruction", instructionJson instruction), ("heap", Instructions.heapJson
        heap)]
    if (← (← field c.outcome "exit").getStr?) != "returned" then return ⟨false, expected⟩
    let recordedResult ← resultOf instruction (← field c.outcome "result")
    match recordedResult with
    | .error _ => return ⟨false, expected⟩
    | .ok instruction =>
      let recorded := (instruction, ← Instructions.heap (← field c.outcome "state"))
      let reference := Solanalib.Specs.SplTokenMetadataInterface.instruction.initialize_reference
        Sample.index before args
      have : Decidable (∃ outcome, reference outcome ∧ observe before outcome = some recorded) :=
        decidable_of_iff _ (observed_iff reference computed (Execution.Metadata.run_graph before
          args)
          (observe before) recorded).symm
      return ⟨decide (∃ outcome, reference outcome ∧ observe before outcome = some recorded),
        expected⟩

end Metadata

end SolanalibTest.Conformance.Library.Families.TokenBuilders
