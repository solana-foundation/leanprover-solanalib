/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Runtime.Common
import SolanalibTest.Conformance.Library.Families.AccountsV2.Projection
import Solanalib.Specs.Pinocchio.RentAccount
import Solanalib.Specs.Pinocchio.Instructions

/-!
# pinocchio 0.11.1 over loader-serialized accounts

States are native input regions with their guards, denoted by the projection of the AccountsV2
family (`SolanalibTest.Conformance.Library.Families.AccountsV2.Projection`:
`parseBefore`, `parseAfter`, `handleArg`, `parseGuard`, `stateJson`,
`parseReturned`, `decideReturnsOpt`), onto `AccountView.State`. Each reference
decided here is registered as a total function (`RealizedBy`) and decided as
`returnsOf` of it (`rfl`):

* `Rent::from_account_view` (`Sysvar.rent111FromAccount`);
* `Instructions::try_from` (`InstructionsSysvar.tryFrom`); its value is the
  acquired guard, `{"guard": [id, generation]}`;
* the Ref-backed observers `load_current_index_run`, `load_instruction_at_run`,
  `get_program_id_run` and `get_instruction_data_run` (the `Ref-support` models of the registry),
  recorded on the `Instructions<Ref<[u8]>>` that
  `try_from` returned. An introspected instruction, program id or data reference
  is its receiver and its offset from the base of the guarded slice, together with its length.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

open Solanalib.Specs.Pinocchio

namespace SolanalibTest.Conformance.Library.Families.Runtime.Accounts

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.InstructionsSysvar
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.AccountsV2 (Native parseBefore parseAfter handleArg
  parseGuard guardJson
  stateJson parseReturned decideReturnsOpt PoolState)

/-! ## Values -/

def someError (j : Json) : Result (Option ProgramError.Value) := do pure (some (← programError j))

def optValue {α : Type} (parse : Json → Result α) (j : Json) : Result (Option α) := do pure (some
  (← parse j))

def exceptOpt {α : Type} (value : Json → Result α) (j : Json) :
    Result (Option (Except ProgramError.Value α)) := do
  pure (some (← asExcept programError value j))

def rent111 (j : Json) : Result Sysvar.Rent111 := do pure ⟨← u64 (← field j "lamports_per_b\
  yte")⟩

def rent111Json (r : Sysvar.Rent111) : Json := Json.mkObj [("lamports_per_byte", u64Json
  r.lamportsPerByte)]

def instructions (j : Json) : Result Instructions := do pure ⟨← parseGuard (← field j
  "guard")⟩

def instructionsJson (i : Instructions) : Json := Json.mkObj [("guard", guardJson i.guard)]

def introspected (j : Json) : Result IntrospectedInstruction := do
  pure ⟨← instructions (← field j "source"), ← nat (← field j "offset")⟩

def introspectedJson (i : IntrospectedInstruction) : Json :=
  Json.mkObj [("source", instructionsJson i.source), ("offset", natJson i.offset)]

def programIdRef (j : Json) : Result ProgramIdRef := do
  pure ⟨← instructions (← field j "source"), ← nat (← field j "offset")⟩

def programIdRefJson (r : ProgramIdRef) : Json :=
  Json.mkObj [("source", instructionsJson r.source), ("offset", natJson r.offset)]

def dataRef (j : Json) : Result DataRef := do
  pure ⟨← instructions (← field j "source"), ← nat (← field j "offset"), ← nat (← field j
    "length")⟩

def dataRefJson (r : DataRef) : Json :=
  Json.mkObj [("source", instructionsJson r.source), ("offset", natJson r.offset), ("length",
    natJson r.length)]

/-! ## Preconditions

`Instructions.Ready` (a live shared guard whose captured view fits the backing) is decided by
`readyB` (`ready_iff`); `tableAligned` by cases on the guard; `State.HasAccount` by the cell
lookup. The `requires` of the contracts (`currentIndexReady`, `instructionAtReady`,
`programIdReady`, `dataReady`, `Sysvar.Rent111ReadReady`) are then decidable from their
definitions. -/

def readyB (source : Instructions) (state : AccountView.State) : Bool :=
  match state.resolve source.guard with
  | none => false
  | some slot => match state.lookupCell slot.cell with
    | none => false
    | some cell => decide (slot.mode = .shared ∧
        slot.view.offset + slot.view.length ≤ cell.value.backing.length ∧
        slot.view.length < ISIZE_LIMIT)

theorem ready_iff (source : Instructions) (state : AccountView.State) :
    source.Ready state ↔ readyB source state = true := by
  unfold Instructions.Ready readyB
  constructor
  · rintro ⟨slot, cell, h1, h2, rest⟩
    simp only [h1, h2]
    exact decide_eq_true rest
  · intro h
    cases h1 : state.resolve source.guard with
    | none => simp [h1] at h
    | some slot =>
      cases h2 : state.lookupCell slot.cell with
      | none => simp [h1, h2] at h
      | some cell =>
        simp only [h1, h2, decide_eq_true_eq] at h
        exact ⟨slot, cell, rfl, h2, h⟩

instance (source : Instructions) (state : AccountView.State) : Decidable (source.Ready state) :=
  decidable_of_iff _ (ready_iff source state).symm

instance (state : AccountView.State) (source : Instructions) (offset : Nat) :
    Decidable (tableAligned state source offset) := by
  unfold tableAligned
  split <;> infer_instance

instance (state : AccountView.State) (handle : AccountView.Handle) :
    Decidable (state.HasAccount handle) :=
  decidable_of_iff ((state.lookupCell handle).isSome = true) (by
    unfold AccountView.State.HasAccount
    cases state.lookupCell handle <;> simp)

instance (state : AccountView.State) (handle : AccountView.Handle) :
    Decidable
      (sysvars.rent.Rent.fixed_rate.from_account_view_contract.requires
      state handle) := by
  show Decidable (Sysvar.Rent111ReadReady state handle)
  unfold Sysvar.Rent111ReadReady
  infer_instance

instance (state : AccountView.State) (source : Instructions) :
    Decidable
      (sysvars.instructions.Instructions.load_current_index_contract.requires
      state source) := by
  show Decidable (currentIndexReady state source)
  unfold currentIndexReady
  infer_instance

instance (state : AccountView.State) (args : Instructions × UInt64) :
    Decidable
      (sysvars.instructions.Instructions.load_instruction_at_contract.requires
      state args) := by
  show Decidable (instructionAtReady state args)
  unfold instructionAtReady
  infer_instance

instance (state : AccountView.State) (i : IntrospectedInstruction) :
    Decidable
      (sysvars.instructions.IntrospectedInstruction.get_program_id_contract.requires
      state i) := by
  show Decidable (programIdReady state i)
  unfold programIdReady
  infer_instance

instance (state : AccountView.State) (i : IntrospectedInstruction) :
    Decidable
      (sysvars.instructions.IntrospectedInstruction.get_instruction_data_contract.requires
      state i) := by
  show Decidable (dataReady state i)
  unfold dataReady
  infer_instance

/-- `constructorReady` decided: the cell of the handle exists and, if it has the Instructions
address and the shared acquisition succeeds, its logical length fits its backing and `isize`. -/
def constructorReadyB (state : AccountView.State) (handle : AccountView.Handle) : Bool :=
  match state.lookupCell handle with
  | none => false
  | some cell =>
    !decide (cell.value.metadata.address = Solanalib.Runtime.Ids.sysvarInstructions) ||
      match AccountView.acquire state handle .shared with
      | (.ok _, _) => decide (cell.value.dataLen ≤ cell.value.backing.length ∧ cell.value.dataLen <
        ISIZE_LIMIT)
      | (.error _, _) => true

theorem constructorReady_iff (state : AccountView.State) (handle : AccountView.Handle) :
    constructorReady state handle ↔ constructorReadyB state handle = true := by
  unfold constructorReady constructorReadyB
  constructor
  · rintro ⟨cell, h, k⟩
    simp only [h]
    by_cases addr : cell.value.metadata.address = Solanalib.Runtime.Ids.sysvarInstructions
    · have k := k addr
      simp only [addr, decide_true, Bool.not_true, Bool.false_or]
      cases e : AccountView.acquire state handle .shared with
      | mk res after =>
        cases res with
        | ok g => exact decide_eq_true (k g after e)
        | error _ => rfl
    · simp [addr]
  · intro hb
    cases h : state.lookupCell handle with
    | none => simp [h] at hb
    | some cell =>
      refine ⟨cell, rfl, fun addr g after e => ?_⟩
      simp only [h, addr, decide_true, Bool.not_true, Bool.false_or, e] at hb
      exact of_decide_eq_true hb

instance (state : AccountView.State) (handle : AccountView.Handle) :
    Decidable
      (sysvars.instructions.Instructions.try_from_contract.requires state
      handle) :=
  decidable_of_iff _ (constructorReady_iff state handle).symm

/-- An Instructions account whose logical length exceeds its backing. The AccountsV2 parser
cannot denote it (it requires `data_len ≤ backing.length`), so no record can break
`constructorReady`; this kernel-checked theorem is the negative control instead. -/
def overlongInstructions : AccountView.State :=
  Sysvar.Witness.singleAccount
    { AccountView.Account.empty with
      metadata := ⟨Solanalib.Runtime.Ids.sysvarInstructions, false, false, false⟩
      dataLen := 5 }

theorem overlong_not_ready :
    ¬ sysvars.instructions.Instructions.try_from_contract.requires
      overlongInstructions ⟨0⟩ := by
  show ¬ constructorReady overlongInstructions ⟨0⟩
  rw [constructorReady_iff]
  decide

/-- The precondition decision of the checker (`decide` of the `requires` of the registered contract,
through the instance above) rejects the overlong account (kernel-checked). -/
theorem overlong_rejected :
    decide (sysvars.instructions.Instructions.try_from_contract.requires
      overlongInstructions ⟨0⟩) = false := by
  decide

/-- A pool checker for a reference registered as a total function. `precondition` decides the
precondition of the contract. -/
def poolChecker {A V : Type} [DecidableEq V] (function reference : String)
    (generics : List (String × String)) (model : PoolState → A → V × PoolState)
    (args : Native → Json → Result A) (value : Json → Result (Option V)) (render : V → Json)
    (precondition : Option (String × (PoolState → A → Bool)) := none) : Checker where
  function := function
  generics := generics
  reference := reference
  decides := [reference]
  decidesRequires := if precondition.isSome then [reference] else []
  check := fun c => do
    let before ← parseBefore c.state
    let a ← args before c.args
    let recorded ← parseReturned value (parseAfter before) c.outcome
    let verdict := decideReturnsOpt (returnsOf model) model rfl before.state a recorded render
      stateJson
    return match precondition with
      | some (name, ready) => withRequires name (ready before.state a) verdict
      | none => verdict

def ref : String := "solana_account_view::Ref<'_, [u8]>"

def fromAccountView : Checker :=
  poolChecker "pinocchio::sysvars::rent::Rent::from_account_view"
    "Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate.from_account_view_run" []
    sysvars.rent.Rent.fixed_rate.from_account_view_run handleArg
      (exceptOpt rent111)
    (exceptJson programErrorJson rent111Json)
    (some ("Rent111ReadReady", fun s h =>
      decide
        (sysvars.rent.Rent.fixed_rate.from_account_view_contract.requires
        s h)))

def tryFrom : Checker :=
  poolChecker
    "<pinocchio::sysvars::instructions::Instructions<solana_account_view::Ref<'a, [u8]>> \
      as core::convert::TryFrom<&'a solana_account_view::AccountView>>::try_from"
    "Solanalib.Specs.Pinocchio.sysvars.instructions.Instructions.try_from_run" []
    sysvars.instructions.Instructions.try_from_run handleArg (exceptOpt
      instructions)
    (exceptJson programErrorJson instructionsJson)
    (some ("constructorReady", fun s h =>
      decide
        (sysvars.instructions.Instructions.try_from_contract.requires s
        h)))

def loadCurrentIndex : Checker :=
  poolChecker "pinocchio::sysvars::instructions::Instructions::<T>::load_current_index"
    "Solanalib.Specs.Pinocchio.sysvars.instructions.Instructions.load_current_index_run" [(
      "T",
      ref)]
    sysvars.instructions.Instructions.load_current_index_run
    (fun _ j => do instructions (← field j "source")) (optValue u16) (fun v => natJson v.toNat)
    (some ("currentIndexReady", fun s a =>
      decide
        (sysvars.instructions.Instructions.load_current_index_contract.requires s a)))

def loadInstructionAt : Checker :=
  poolChecker "pinocchio::sysvars::instructions::Instructions::<T>::load_instruction_at"
    "Solanalib.Specs.Pinocchio.sysvars.instructions.Instructions.load_instruction_at_run" [(
      "T",
      ref)]
    sysvars.instructions.Instructions.load_instruction_at_run
    (fun _ j => do pure (← instructions (← field j "source"), ← u64 (← field j "index")))
    (exceptOpt introspected) (exceptJson programErrorJson introspectedJson)
    (some ("instructionAtReady", fun s a =>
      decide
        (sysvars.instructions.Instructions.load_instruction_at_contract.requires s a)))

def getProgramId : Checker :=
  poolChecker "pinocchio::sysvars::instructions::IntrospectedInstruction::<'_>::get_program\
    _id"
    "Solanalib.Specs.Pinocchio.sysvars.instructions.IntrospectedInstruction.get_program_id_\
      run" []
    sysvars.instructions.IntrospectedInstruction.get_program_id_run
    (fun _ j => do introspected (← field j "instruction")) (optValue programIdRef) programIdRefJson
    (some ("programIdReady", fun s a => decide
      (sysvars.instructions.IntrospectedInstruction.get_program_id_contract.requires s a)))

def getInstructionData : Checker :=
  poolChecker
    "pinocchio::sysvars::instructions::IntrospectedInstruction::<'_>::get_instruction_data"
    "Solanalib.Specs.Pinocchio.sysvars.instructions.IntrospectedInstruction.get_instruction\
      _data_run" []
    sysvars.instructions.IntrospectedInstruction.get_instruction_data_run
    (fun _ j => do introspected (← field j "instruction")) (optValue dataRef) dataRefJson
    (some ("dataReady", fun s a => decide
      (sysvars.instructions.IntrospectedInstruction.get_instruction_data_contract.requires s a)))

def checkers : List Checker :=
  [fromAccountView, tryFrom, loadCurrentIndex, loadInstructionAt, getProgramId, getInstructionData]

end SolanalibTest.Conformance.Library.Families.Runtime.Accounts
