/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TokenInterface.Common
import SolanalibTest.Conformance.Library.Families.TokenInterface.Allocated
import Solanalib.Specs.SplTokenInterface.Instructions
import Solanalib.Specs.SplToken2022Interface.Instructions

/-!
# Program identities, the program check and the instruction constructors

`id` and `check_spl_token_program_account` are pure references; each record
is decided as the graph of the registered reference.

Each constructor has two registered models observing the same Rust function:
the value observation (`*_value_reference`, the graph of a pure function) and
the operational family (`*_reference`, a relation over vector providers). One
checker decides both on every record:

* the value reference on the recorded `Result<Instruction, ProgramError>`;
* the family reference at its registered sample index `Witness.sampleTypes`
  from the empty ledgers, through `Allocated.run_fn`: it must admit an outcome
  whose returned instruction (read through the `observe` of the model) and
  whose ledger (slots allocated, slots retired) equal the recorded result and
  the recorded fresh allocations and deallocations.
-/

set_option autoImplicit false

open Lean (Json)

open Solanalib.Specs.SplToken2022Interface

namespace SolanalibTest.Conformance.Library.Families.TokenInterface.Instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Token.Instruction
open Solanalib.Specs.Core.Token.InstructionAllocated (Plan observe Witness.initialState)
open SolanalibTest.Conformance.Library.Families.TokenInterface.Allocated

/-! ## Pure references -/

/-- The registered references are the declared program identities and the
either-program check (by definition). -/
theorem legacy_id_evaluated :
    Solanalib.Specs.SplTokenInterface.id_reference = fun _ _ => (legacyProgramId, ()) := rfl

theorem token2022_id_evaluated :
    id_reference = fun _ _ => (token2022ProgramId, ()) := rfl

theorem check_evaluated :
    check_spl_token_program_account_reference =
      fun s k => (checkProgram .either k, s) := rfl

def idChecker (function reference : String) (ref : Unit → Unit → Solanalib.Runtime.Pubkey × Unit) :
  Checker where
  function := function
  generics := []
  reference := reference
  decides := [reference]
  check := fun c => do
    decideReturns (returnsOf ref) ref rfl (← unitState c.state) (← unitState c.args)
      pubkey unitState pubkeyJson (fun _ => Json.null) c.outcome

def checkChecker : Checker where
  function := "spl_token_2022_interface::check_spl_token_program_account"
  generics := []
  reference := "Solanalib.Specs.SplToken2022Interface.check_spl_token_program_account_refer\
    ence"
  decides := ["Solanalib.Specs.SplToken2022Interface.check_spl_token_program_account_refere\
    nce"]
  check := fun c => do
    decideReturns (returnsOf
      check_spl_token_program_account_reference)
      check_spl_token_program_account_reference rfl
      (← unitState c.state) (← keyField c.args "program_id")
      (resultOf unitState) unitState (resultJson fun _ => Json.null) (fun _ => Json.null) c.outcome

/-! ## Arguments -/

def initArgs (j : Json) : Result InitializeAccount3Args := do
  pure ⟨← keyField j "program_id", ← keyField j "account", ← keyField j "mint", ← keyField j
    "owner"⟩

def authorityArgs (j : Json) : Result AuthorityArgs := do
  pure ⟨← keyField j "program_id", ← keyField j "source", ← keyField j "destination",
    ← keyField j "authority", ← listField j "signers" pubkey⟩

def transferArgs (j : Json) : Result TransferArgs := do
  pure ⟨← authorityArgs j, ← uintField 64 j "amount"⟩

def transferCheckedArgs (j : Json) : Result TransferCheckedArgs := do
  pure ⟨← transferArgs j, ← keyField j "mint", ← uintField 8 j "decimals"⟩

def heap (j : Json) : Result Heap := do
  pure ⟨← natField j "allocations", ← natField j "deallocations"⟩

def heapJson (h : Heap) : Json :=
  Json.mkObj [("allocations", Lean.toJson h.allocations), ("deallocations", Lean.toJson
    h.deallocations)]

def outJson : Out Allocated.Result → Json
  | .returned (.ok v) s => Json.mkObj [("exit", "returned"),
      ("result", okJson ((observe ST s v).elim Json.null instructionJson)), ("state", heapJson
        (heapOf s))]
  | .returned (.error e) s => Json.mkObj [("exit", "returned"),
      ("result", errJson (programErrorJson e)), ("state", heapJson (heapOf s))]
  | .unwound r _ => Json.mkObj [("exit", "unwound"), ("reason", Lean.toJson r)]
  | .terminated r => Json.mkObj [("exit", "terminated"), ("reason", Lean.toJson r)]

/-! ## Constructors: one checker, two registered references -/

/-- A constructor with its value reference and its family reference at the
sample index, related to `runF` by `fn`. -/
structure Constructor (Args : Type) where
  function : String
  valueName : String
  familyName : String
  args : Json → Result Args
  value : Unit → Args → Except Token.Error Solanalib.Runtime.CpiInstruction × Unit
  family : St → Args → Out Allocated.Result → Prop
  plan : Args → Plan
  fn : ∀ s a o, family s a o ↔ runF s (plan a) = some o

theorem family_admits_iff {Args : Type} (k : Constructor Args) (a : Args) (recorded : Observation) :
    (∃ o, k.family Witness.initialState a o ∧ observe? o = some recorded) ↔
      (runF Witness.initialState (k.plan a)).bind observe? = some recorded := by
  constructor
  · rintro ⟨o, ho, hobs⟩
    rw [(k.fn _ a o).1 ho]
    exact hobs
  · intro h
    cases hf : runF Witness.initialState (k.plan a) with
    | none => rw [hf] at h; cases h
    | some o =>
      rw [hf] at h
      exact ⟨o, (k.fn _ a o).2 hf, h⟩

def Constructor.checker {Args : Type} (k : Constructor Args) : Checker :=
  pairChecker k.function []
    k.familyName
    k.valueName fun c => do
    let _ ← unitState c.state
    let a ← k.args c.args
    let computed := runF Witness.initialState (k.plan a)
    let expected := Json.mkObj [
      ("family", computed.elim Json.null outJson),
      ("value", resultJson instructionJson (k.value () a).1)]
    match ← (← field c.outcome "exit").getStr? with
    | "returned" =>
      let result ← resultOf instruction (← field c.outcome "result")
      let h ← heap (← field c.outcome "state")
      have : Decidable (∃ o, k.family Witness.initialState a o ∧ observe? o = some (result, h)) :=
        decidable_of_iff _ (family_admits_iff k a (result, h)).symm
      let familyOk := decide (∃ o, k.family Witness.initialState a o ∧ observe? o = some (result,
        h))
      let valueOk := decide (returnsOf k.value () a (Outcome.returned (Unwind := Empty) (Terminal
        := Empty)
        result ()))
      return (familyOk, valueOk, expected)
    | _ => return (false, false, expected)

def legacyInit : Constructor InitializeAccount3Args where
  function := "spl_token_interface::instruction::initialize_account3"
  valueName := "Solanalib.Specs.SplTokenInterface.instruction.initialize_account3_value_ref\
    erence"
  familyName := "Solanalib.Specs.SplTokenInterface.instruction.initialize_account3_referenc\
    e"
  args := initArgs
  value := Solanalib.Specs.SplTokenInterface.instruction.initialize_account3_value_reference
  family := Solanalib.Specs.SplTokenInterface.instruction.initialize_account3_reference ST
  plan := InstructionAllocated.initializeAccount3Plan .legacy
  fn := fun s _ o => run_fn s _ o

def legacyTransfer : Constructor TransferArgs where
  function := "spl_token_interface::instruction::transfer"
  valueName := "Solanalib.Specs.SplTokenInterface.instruction.transfer_value_reference"
  familyName := "Solanalib.Specs.SplTokenInterface.instruction.transfer_reference"
  args := transferArgs
  value := Solanalib.Specs.SplTokenInterface.instruction.transfer_value_reference
  family := Solanalib.Specs.SplTokenInterface.instruction.transfer_reference ST
  plan := InstructionAllocated.transferPlan
  fn := fun s _ o => run_fn s _ o

def tokenInit : Constructor InitializeAccount3Args where
  function := "spl_token_2022_interface::instruction::initialize_account3"
  valueName :=
    "Solanalib.Specs.SplToken2022Interface.instruction.initialize_account3_value_reference"
  familyName := "Solanalib.Specs.SplToken2022Interface.instruction.initialize_account3_refe\
    rence"
  args := initArgs
  value := instruction.initialize_account3_value_reference
  family := instruction.initialize_account3_reference ST
  plan := InstructionAllocated.initializeAccount3Plan .either
  fn := fun s _ o => run_fn s _ o

def tokenClose : Constructor AuthorityArgs where
  function := "spl_token_2022_interface::instruction::close_account"
  valueName := "Solanalib.Specs.SplToken2022Interface.instruction.close_account_value_refer\
    ence"
  familyName := "Solanalib.Specs.SplToken2022Interface.instruction.close_account_reference"
  args := authorityArgs
  value := instruction.close_account_value_reference
  family := instruction.close_account_reference ST
  plan := InstructionAllocated.closeAccountPlan .either
  fn := fun s _ o => run_fn s _ o

def tokenTransferChecked : Constructor TransferCheckedArgs where
  function := "spl_token_2022_interface::instruction::transfer_checked"
  valueName := "Solanalib.Specs.SplToken2022Interface.instruction.transfer_checked_value_re\
    ference"
  familyName := "Solanalib.Specs.SplToken2022Interface.instruction.transfer_checked_referen\
    ce"
  args := transferCheckedArgs
  value := instruction.transfer_checked_value_reference
  family := instruction.transfer_checked_reference ST
  plan := InstructionAllocated.transferCheckedPlan .either
  fn := fun s _ o => run_fn s _ o

def tokenWithdraw : Constructor AuthorityArgs where
  function := "spl_token_2022_interface::instruction::withdraw_excess_lamports"
  valueName :=
    "Solanalib.Specs.SplToken2022Interface.instruction.withdraw_excess_lamports_value_refer\
      ence"
  familyName :=
    "Solanalib.Specs.SplToken2022Interface.instruction.withdraw_excess_lamports_reference"
  args := authorityArgs
  value :=
    instruction.withdraw_excess_lamports_value_reference
  family := instruction.withdraw_excess_lamports_reference ST
  plan := InstructionAllocated.withdrawExcessLamportsPlan
  fn := fun s _ o => run_fn s _ o

def legacyCheckers : List Checker := [
  idChecker "spl_token_interface::id" "Solanalib.Specs.SplTokenInterface.id_reference"
    Solanalib.Specs.SplTokenInterface.id_reference,
  legacyInit.checker, legacyTransfer.checker]

def tokenCheckers : List Checker := [
  idChecker "spl_token_2022_interface::id" "Solanalib.Specs.SplToken2022Interface.id_refere\
    nce"
    id_reference,
  checkChecker, tokenInit.checker, tokenClose.checker, tokenTransferChecked.checker,
  tokenWithdraw.checker]

end SolanalibTest.Conformance.Library.Families.TokenInterface.Instructions
