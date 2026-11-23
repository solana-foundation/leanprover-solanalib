/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Utilities.CheckedRuntime
import Solanalib.Specs.SolanaInstructionsSysvar.Checked

set_option autoImplicit false

open Lean (Json toJson)

open Solanalib.Specs.SolanaInstructionsSysvar

namespace SolanalibTest.Conformance.Library.Families.Utilities.Checked

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open InstructionsSysvar
open CheckedRuntime

/-- Every native state field is retained. Guard tombstones are ghost history;
their observable consequence is checked through the actual borrow operations. -/
structure NativeState where
  data : Solanalib.Runtime.Bytes
  readOk : Bool
  writeOk : Bool
  allocations : List Nat
  frees : List Nat
  live : List Nat
  deriving DecidableEq

def naturals (j : Json) : Result (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def nativeState (j : Json) : Result NativeState := do
  pure ⟨← asBytes (← field j "data"), ← bool (← field j "read_ok"),
    ← bool (← field j "write_ok"), ← naturals (← field j "allocations"),
    ← naturals (← field j "frees"), ← naturals (← field j "live")⟩

def stateJson (s : NativeState) : Json := Json.mkObj [
  ("data", bytesJson s.data), ("read_ok", Json.bool s.readOk), ("write_ok", Json.bool s.writeOk),
  ("allocations", toJson s.allocations), ("frees", toJson s.frees), ("live", toJson s.live)]

def info (key : Solanalib.Runtime.Pubkey) : AccountInfo.Value := { AccountInfo.sampleInfo with key
  := key }

def initialBorrows (data : Solanalib.Runtime.Bytes) (held : Nat) : AccountInfo.State :=
  let initial : AccountInfo.State :=
    ⟨[⟨.lamports 73, .refCell 64⟩, ⟨.data data, .refCell 64⟩], []⟩
  if held = 0 then initial
  else (AccountInfo.tryBorrow (if held = 1 then .shared else .exclusive) ⟨1⟩ initial).2

def observeState (borrows : AccountInfo.State) (pool : Pool) : Option NativeState := do
  let cell ← borrows.lookupCell ⟨1⟩
  let data ← match cell.value with | .data bytes => some bytes | _ => none
  pure ⟨data, (AccountInfo.tryBorrow .shared ⟨1⟩ borrows).1.isOk,
    (AccountInfo.tryBorrow .exclusive ⟨1⟩ borrows).1.isOk,
    pool.allocations, pool.frees, pool.live⟩

/-- Decide the real model admission by inspecting the reached identified cell.
Wrong IDs need no data interpretation, exactly as in the source order. -/
def readyDec (before : AccountInfo.State) (account : AccountInfo.Value) :
    Decidable (InstructionsSysvar.Checked.Ready before account) :=
  if same : account.key = Solanalib.Runtime.Ids.sysvarInstructions then
    match present : before.lookupCell account.data with
    | none => isFalse (by
        intro ready
        obtain ⟨bytes, policy, witness⟩ := ready same
        rw [present] at witness
        cases witness)
    | some ⟨.lamports balance, policy⟩ => isFalse (by
        intro ready
        obtain ⟨bytes, actualPolicy, witness⟩ := ready same
        rw [present] at witness
        cases witness)
    | some ⟨.data bytes, policy⟩ => isTrue (fun _ => ⟨bytes, policy, present⟩)
  else isTrue (fun impossible => False.elim (same impossible))

structure InstructionObservation where
  programId : Solanalib.Runtime.Pubkey
  accounts : List Instruction.Meta
  data : Solanalib.Runtime.Bytes
  accountCapacity : Nat
  dataCapacity : Nat
  accountAllocation : Option Nat
  dataAllocation : Option Nat
  deriving DecidableEq

def optionalNat : Json → Result (Option Nat)
  | .null => pure none
  | j => some <$> j.getNat?

def metaValue (j : Json) : Result Instruction.Meta := do
  pure (Instruction.accountMeta (← pubkey (← field j "pubkey")) (← bool (← field j
    "is_signer"))
    (← bool (← field j "is_writable")))

def instruction (j : Json) : Result InstructionObservation := do
  pure ⟨← pubkey (← field j "program_id"), ← (← (← field j "accounts").getArr?).toList.mapM
    metaValue,
    ← asBytes (← field j "data"), ← (← field j "account_capacity").getNat?,
    ← (← field j "data_capacity").getNat?, ← optionalNat (← field j "account_allocation"),
    ← optionalNat (← field j "data_allocation")⟩

def instructionJson (v : InstructionObservation) : Json := Json.mkObj [
  ("program_id", pubkeyJson v.programId),
  ("accounts", Json.arr ((v.accounts.map fun entry => Json.mkObj [
    ("pubkey", pubkeyJson entry.key), ("is_signer", Json.bool (entry.signerByte != 0)),
    ("is_writable", Json.bool (entry.writableByte != 0))]).toArray)),
  ("data", bytesJson v.data), ("account_capacity", toJson v.accountCapacity),
  ("data_capacity", toJson v.dataCapacity), ("account_allocation", toJson v.accountAllocation),
  ("data_allocation", toJson v.dataAllocation)]

def observeInstruction (pool : Pool) (value : CheckedRuntime.Value) : Option InstructionObservation
  := do
  let metas ← metaAt pool value.metas
  let bytes ← byteAt pool value.data
  pure ⟨value.programId, metas.items, bytes.items, metas.capacity, bytes.capacity,
    metas.allocation, bytes.allocation⟩

/-- Interpret owned outputs only through the resources present in the final
allocator world. No output handle is synthesized from the recorded bytes. -/
def observeOutcome {Aux Value Observed Unwind Terminal : Type}
    (pool : Aux → Pool) (observeValue : Aux → Value → Option Observed) :
    Outcome (InstructionsSysvar.Checked.State Aux) (Except ProgramError.Value Value) Unwind
      Terminal →
      Option (Outcome NativeState (Except ProgramError.Value Observed) Unwind Terminal)
  | .returned result after => do
    let state ← observeState after.borrows (pool after.aux)
    let result ← match result with
      | .error error => some (.error error)
      | .ok value => Except.ok <$> observeValue after.aux value
    pure (.returned result state)
  | .unwound reason after => do
    pure (.unwound reason (← observeState after.borrows (pool after.aux)))
  | .terminated reason => some (.terminated reason)

def currentProjection := observeOutcome (Unwind := InstructionsSysvar.Checked.Panic) (Terminal :=
  InstructionsSysvar.Checked.Panic) (fun (_ : Unit) => ({} : Pool))
  (fun (_ : Unit) (value : UInt16) => some value)

def instructionProjection := observeOutcome (Unwind := Empty) (Terminal := Empty) id
  observeInstruction

def panic : String → Option InstructionsSysvar.Checked.Panic
  | "attempt to subtract with overflow" => some .subtractionOverflow
  | reason => if reason.startsWith "range start index" then some .sliceRange else none

def panicJson : InstructionsSysvar.Checked.Panic → Json
  | .subtractionOverflow => "attempt to subtract with overflow"
  | .sliceRange => "range start index exceeds slice length"

def input (c : Case) : Result (NativeState × AccountInfo.Value × AccountInfo.State ×
  Sysvar.ArithmeticProfile) := do
  let before ← nativeState c.state
  let key ← pubkey (← field c.args "key")
  let held ← (← field c.args "held").getNat?
  unless held ≤ 2 do throw "unknown native held-borrow mode"
  let profile ← arithmeticProfile c.args
  pure (before, info key, initialBorrows before.data held, profile)

def current : Checker where
  function := "solana_instructions_sysvar::load_current_index_checked"
  generics := []
  reference := "Solanalib.Specs.SolanaInstructionsSysvar.load_current_index_checked_run"
  decides := ["Solanalib.Specs.SolanaInstructionsSysvar.load_current_index_checked_run"]
  decidesRequires := ["Solanalib.Specs.SolanaInstructionsSysvar.load_current_index_checked_\
    run"]
  check := fun c => do
    let (nativeBefore, account, borrows, profile) ← input c
    asUnit (← field c.args "index")
    let before : InstructionsSysvar.Checked.State Unit := ⟨borrows, ()⟩
    let recorded ← parseOutcome (asExcept programError (fun j => UInt16.ofNat <$> asUInt 16 j))
      nativeState panic panic c.outcome
    let computed := withDataF (InstructionsSysvar.Checked.currentBody profile) before account
    let relation := load_current_index_checked_run
      ⟨profile⟩ before account
    return withRequires "native input interpretation" (observeState borrows {} == some
      nativeBefore) <|
      withRequires "Ready"
        (@decide
          ((load_current_index_checked_contract.contract
          ⟨profile⟩).requires before account)
          (readyDec borrows account)) <|
      decideOptGraph (S := NativeState) (V := Except ProgramError.Value UInt16)
        (U := InstructionsSysvar.Checked.Panic) (T := InstructionsSysvar.Checked.Panic)
        (fun observed => ∃ actual, relation actual ∧ currentProjection actual = some observed)
        (computed.bind currentProjection)
        (projected_graph relation computed (withData_graph (InstructionsSysvar.Checked.currentBody
          profile) before account) currentProjection)
        recorded (outcomeJson stateJson (exceptJson programErrorJson (fun n => toJson n.toNat))
          panicJson panicJson)

theorem instruction_graph (instruction : UInt64) (before : InstructionsSysvar.Checked.State Pool)
    (account : AccountInfo.Value)
    (outcome : Outcome (InstructionsSysvar.Checked.State Pool) CheckedRuntime.DecodeResult Empty
      Empty) :
    load_instruction_at_checked_run index before
      (instruction, account) outcome ↔
      withDataF (fun state data => .returned (decodeF instruction state data).1 (decodeF
        instruction state data).2)
        before account = some outcome := by
  have graph : InstructionsSysvar.Checked.decode index instruction =
      Callback.ofFunction (fun state data => .returned (decodeF instruction state data).1 (decodeF
        instruction state data).2) := by
    funext state data final
    exact propext (decode_graph instruction state data final)
  change InstructionsSysvar.Checked.withData _ before account outcome ↔ _
  rw [graph]
  exact withData_graph _ before account outcome

def atInstruction : Checker where
  function := "solana_instructions_sysvar::load_instruction_at_checked"
  generics := []
  reference := "Solanalib.Specs.SolanaInstructionsSysvar.load_instruction_at_checked_run"
  decides := ["Solanalib.Specs.SolanaInstructionsSysvar.load_instruction_at_checked_run"]
  decidesRequires := ["Solanalib.Specs.SolanaInstructionsSysvar.load_instruction_at_checked\
    _run"]
  check := fun c => do
    let (nativeBefore, account, borrows, _) ← input c
    let instruction ← u64 (← field c.args "index")
    let before : InstructionsSysvar.Checked.State Pool := ⟨borrows, {}⟩
    let recorded ← parseOutcome (asExcept programError Checked.instruction) nativeState noReason
      noReason c.outcome
    let computed := withDataF (fun state data => .returned (decodeF instruction state data).1
      (decodeF instruction state data).2) before account
    let relation := load_instruction_at_checked_run index
      before (instruction, account)
    return withRequires "native input interpretation" (observeState borrows {} == some
      nativeBefore) <|
      withRequires "Ready"
        (@decide
          ((load_instruction_at_checked_contract.contract
          index).requires before (instruction, account))
          (readyDec borrows account)) <|
      decideOptGraph (S := NativeState) (V := Except ProgramError.Value InstructionObservation) (U
        := Empty) (T := Empty)
        (fun observed => ∃ actual, relation actual ∧ instructionProjection actual = some observed)
        (computed.bind instructionProjection)
        (projected_graph relation computed (instruction_graph instruction before account)
          instructionProjection)
        recorded (outcomeJson stateJson (exceptJson programErrorJson instructionJson) emptyJson
          emptyJson)

/-- The exact operational admission decider rejects a missing reached cell.
The JSON native representation always supplies one, so this control exercises
its excluded malformed interpretation directly. -/
theorem missing_cell_rejected :
    @decide
      ((load_instruction_at_checked_contract.contract
      index).requires
      ⟨⟨[], []⟩, {}⟩ (0, info Solanalib.Runtime.Ids.sysvarInstructions))
      (readyDec ⟨[], []⟩ (info Solanalib.Runtime.Ids.sysvarInstructions)) = false := by decide

theorem current_missing_cell_rejected :
    @decide ((load_current_index_checked_contract.contract
      ⟨⟨true, .unwind⟩⟩).requires
      ⟨⟨[], []⟩, ()⟩ (info Solanalib.Runtime.Ids.sysvarInstructions))
      (readyDec ⟨[], []⟩ (info Solanalib.Runtime.Ids.sysvarInstructions)) = false := by decide

end SolanalibTest.Conformance.Library.Families.Utilities.Checked
