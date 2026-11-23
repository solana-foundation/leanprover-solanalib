/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.TransferHookResolution.Index
import SolanalibTest.Conformance.Library.Families.TokenInterface.Common
import SolanalibTest.Conformance.Library.Runtime
import Solanalib.Specs.SplTransferHookInterface.Onchain

set_option autoImplicit false

open Lean (Json toJson)

open Solanalib.Specs.SplTransferHookInterface

namespace SolanalibTest.Conformance.Library.Families.TransferHookResolution

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.TransferHookResolution
open Solanalib.Specs.Core.TransferHookResolution.Sample
open SolanalibTest.Conformance.Library.Families.TokenInterface
open SolanalibTest.Conformance.Library.Families.TokenInterface.Functional

/-- Full AccountInfo value fields, with a separate cell pair per native owner.
Equal keys at distinct positions remain distinct borrow and Rc identities. -/
structure RawAccount where
  key : Solanalib.Runtime.Pubkey
  owner : Solanalib.Runtime.Pubkey
  lamports : UInt64
  data : Solanalib.Runtime.Bytes
  signer : Bool
  writable : Bool
  executable : Bool
  deriving DecidableEq

def rawAccount (j : Json) : Result RawAccount := do
  pure ⟨← keyField j "key", ← keyField j "owner", UInt64.ofNat (← uintField 64 j "lamports"),
    ← asBytes (← field j "data"), ← boolField j "is_signer", ← boolField j "is_writable",
    ← boolField j "executable"⟩

def accountValue (i : Nat) (account : RawAccount) : AccountInfo.Value :=
  ⟨account.key, ⟨2 * i⟩, ⟨2 * i + 1⟩, account.owner, 0,
    account.signer, account.writable, account.executable, ⟨i⟩⟩

def policy : Borrow.Policy := (⟨64, false⟩ : AccountInfo.Profile).policy

def held (j : Json) : Result (Borrow.Handle × Borrow.Mode) := do
  let i ← natField j "account"
  let offset ← match ← (← field j "cell").getStr? with
    | "lamports" => pure 0
    | "data" => pure 1
    | other => throw s!"unknown cell {other}"
  let mode ← match ← (← field j "mode").getStr? with
    | "shared" => pure Borrow.Mode.shared
    | "exclusive" => pure Borrow.Mode.exclusive
    | other => throw s!"unknown borrow {other}"
  pure (⟨2 * i + offset⟩, mode)

def borrowState (raw : List RawAccount) (held : List (Borrow.Handle × Borrow.Mode)) :
  AccountInfo.State :=
  ⟨(raw.flatMap fun a => [AccountInfo.Content.lamports a.lamports, .data a.data]).map
      (fun value => ⟨value, policy⟩),
    held.map fun (handle, mode) => some ⟨handle, mode, 0, .whole⟩⟩

def accountAt {Value : Type} (values : List Value) (position : Nat) : Result Value :=
  match values[position]? with
  | some value => pure value
  | none => throw s!"account index {position} is absent"

def decodeArgs (script : List PdaExit) (raw : List RawAccount) (j : Json) :
    Result (Args (index script) × Solanalib.Runtime.CpiInstruction × List AccountInfo.Value × List
      Nat) := do
  let values := raw.mapIdx accountValue
  let source ← natField j "source"
  let mint ← natField j "mint"
  let destination ← natField j "destination"
  let authority ← natField j "authority"
  let additional ← listField j "additional" Json.getNat?
  let caller ← listField j "caller_infos" Json.getNat?
  let instruction ← instruction (← field j "instruction")
  let args : Args (index script) := {
    instruction := ⟨instruction.programId, (0 : Nat), (0 : Nat)⟩
    infos := (0 : Nat)
    programId := ← keyField j "program_id"
    source := ← accountAt values source
    mint := ← accountAt values mint
    destination := ← accountAt values destination
    authority := ← accountAt values authority
    amount := UInt64.ofNat (← uintField 64 j "amount")
    additional := ← additional.mapM (accountAt values) }
  let multiplicities := (List.range raw.length).flatMap fun i =>
    List.replicate 2 (1 + (additional ++ caller ++ [source, mint, destination, authority]).count i)
  pure (args, instruction, ← caller.mapM (accountAt values), multiplicities)

/-- The source pubkey version zero-initializes all 32 output bytes and starts
bump at 255. A scripted partial write retains exactly that initialized suffix. -/
def pdaExit (reply : Runtime.Reply) : Result PdaExit := do
  unless reply.syscall = "sol_try_find_program_address" do throw "unexpected syscall script"
  unless reply.writes = [] ∧ reply.programId = none ∧ reply.ret < 2^64 do
    throw "unsupported PDA reply fields"
  if reply.terminate.isSome then return .terminal 0
  unless reply.data.length ≤ 32 do throw "PDA output write exceeds 32 bytes"
  let output ← pubkey (bytesJson (reply.data ++ List.replicate (32 - reply.data.length) 0))
  let bump := reply.bump.getD 255
  unless bump < 256 do throw "PDA bump is not a byte"
  pure (.reply ⟨UInt64.ofNat reply.ret, output, UInt8.ofNat bump⟩)

def search (request : Runtime.Request) : Result (List Solanalib.Runtime.Bytes ×
  Solanalib.Runtime.Pubkey) := do
  unless request.syscall = "sol_try_find_program_address" do throw "helper made a non-PDA \
    syscall"
  pure (← request.slices "seeds", ← pubkey (bytesJson (← request.bytes "program_id")))

/-- Bump initialization is a semantic observation of the forced PDA request,
so a well-formed different byte is rejected as a mismatch, not a parse error. -/
def searchBumps (requests : List Runtime.Request) : Result Bool := do
  let bumps ← requests.mapM (fun request => request.nat "bump")
  pure (bumps.all (· == 255))

/-- Both the finite syscall script of this sample and the full local computation
are linked to the exact versioned reference, without duplicating that model. -/
theorem run_iff (script : List PdaExit) (before : Sample.State) (args : Args (index script))
    (outcome : Outcome Sample.State (Except Token.Error Unit) Nat Nat) :
    onchain.add_extra_accounts_for_execute_cpi_reference
        (index script) before args outcome ↔
      fullRunF (prims script) before args = some outcome :=
  fullRun_fn (prims script) before args outcome

inductive Exit where
  | returned (result : Except Token.Error Unit)
  | unwound (message : String)
  deriving DecidableEq

structure Observation where
  exit : Exit
  accounts : List RawAccount
  guards : List (Borrow.Handle × Borrow.Mode)
  instruction : Solanalib.Runtime.CpiInstruction
  infos : List AccountInfo.Value
  counts : List Nat
  searches : List (List Solanalib.Runtime.Bytes × Solanalib.Runtime.Pubkey)
  deriving DecidableEq

/-- The message is determined by a real POD header among the input accounts.
Ambiguous encodings of the panic tag of the finite test index are rejected. -/
def panicMessage (raw : List RawAccount) (code : Nat) : Option String :=
  if code = 102 then some Address.Syscall.panicMessage
  else
    let pairs := raw.filterMap fun account =>
      match findExecuteRange (account.data.length + 1) account.data 0 with
      | .error _ => none
      | .ok (offset, length) =>
        match podHeader (Solanalib.Runtime.slice account.data offset length) with
        | .error _ => none
        | .ok (count, capacity) =>
          if Sample.panicCode (.podSliceBounds count capacity) = code then
            some s!"range end index {count} out of range for slice of length {capacity}"
          else none
    match pairs.eraseDups with
    | [message] => some message
    | _ => none

def afterAccount (state : AccountInfo.State) (i : Nat) (raw : RawAccount) : Option RawAccount := do
  let ⟨.lamports balance, _⟩ ← state.lookupCell ⟨2 * i⟩ | none
  let ⟨.data bytes, _⟩ ← state.lookupCell ⟨2 * i + 1⟩ | none
  pure { raw with lamports := balance, data := bytes }

def observation (script : List PdaExit) (raw : List RawAccount) (args : Args (index script)) :
    Outcome Sample.State (Except Token.Error Unit) Nat Nat → Option Observation
  | .terminated _ => none
  | .returned result after => observe (.returned result) after
  | .unwound reason after => (panicMessage raw reason).bind fun message => observe (.unwound
    message) after
where
  observe (exit : Exit) (after : Sample.State) : Option Observation := do
    let accounts ← (raw.zipIdx).mapM fun (account, i) => afterAccount after.1 i account
    let metas ← Sample.metasOps.current after args.instruction.metas
    let data ← Sample.bytesOps.current after args.instruction.data
    let infos ← Sample.infosOps.current after args.infos
    pure ⟨exit, accounts,
      after.1.slots.filterMap (fun slot => slot.map fun guard => (guard.cell, guard.mode)),
      ⟨args.instruction.programId, metas, data⟩, infos, after.2.rcOwners, after.2.pdaCalls⟩

theorem observed_iff (script : List PdaExit) (raw : List RawAccount) (before : Sample.State)
    (args : Args (index script)) (recorded : Observation) :
    (∃ outcome,
      onchain.add_extra_accounts_for_execute_cpi_reference
        (index script) before args outcome ∧ observation script raw args outcome = some recorded) ↔
      (fullRunF (prims script) before args).bind (observation script raw args) = some recorded := by
  constructor
  · rintro ⟨outcome, called, observed⟩
    rw [(run_iff script before args outcome).mp called]
    exact observed
  · intro admitted
    cases computed : fullRunF (prims script) before args with
    | none => rw [computed] at admitted; cases admitted
    | some outcome =>
      rw [computed] at admitted
      exact ⟨outcome, (run_iff script before args outcome).mpr computed, admitted⟩

/-- The checker decides existence of the actual registered execution, with
exactly the recorded projected state. Its procedure follows the proved full
operational computation rather than a separately asserted output oracle. -/
def accepts (script : List PdaExit) (raw : List RawAccount) (before : Sample.State)
    (args : Args (index script)) (recorded : Observation) : Prop :=
  ∃ outcome,
    onchain.add_extra_accounts_for_execute_cpi_reference
    (index script) before args outcome ∧ observation script raw args outcome = some recorded

instance accepts_decidable (script : List PdaExit) (raw : List RawAccount) (before : Sample.State)
    (args : Args (index script)) (recorded : Observation) :
    Decidable (accepts script raw before args recorded) :=
  decidable_of_iff
    ((fullRunF (prims script) before args).bind (observation script raw args) = some recorded)
    (observed_iff script raw before args recorded).symm

/-- A terminal fixture decides the actual terminal outcome of the same reference.
The separately checked request is forced before any account lookup. -/
def firstPdaTerminal (script : List PdaExit) (before : Sample.State)
    (args : Args (index script)) : Prop :=
  onchain.add_extra_accounts_for_execute_cpi_reference
    (index script) before args (.terminated (0 : Nat))

def terminalFlag : Option (Outcome Sample.State (Except Token.Error Unit) Nat Nat) → Bool
  | some (.terminated reason) => reason == 0
  | _ => false

theorem terminalFlag_iff (outcome : Option (Outcome Sample.State (Except Token.Error Unit) Nat
  Nat)) :
    outcome = some (.terminated 0) ↔ terminalFlag outcome = true := by
  cases outcome with
  | none => simp [terminalFlag]
  | some outcome =>
    cases outcome <;> simp [terminalFlag]

instance firstPdaTerminal_decidable (script : List PdaExit) (before : Sample.State)
    (args : Args (index script)) : Decidable (firstPdaTerminal script before args) :=
  decidable_of_iff (terminalFlag (fullRunF (prims script) before args) = true)
    ((run_iff script before args (.terminated (0 : Nat))).trans (terminalFlag_iff _)).symm

def recordedInfo (j : Json) : Result AccountInfo.Value := do
  let i ← natField j "cells"
  pure ⟨← keyField j "key", ⟨2 * i⟩, ⟨2 * i + 1⟩, ← keyField j "owner", 0,
    ← boolField j "is_signer", ← boolField j "is_writable", ← boolField j "executable", ⟨i⟩⟩

def recordedObservation (outcome : Json) : Result (Observation × Runtime.SyscallState) := do
  let exit ← match ← (← field outcome "exit").getStr? with
    | "returned" => pure (Exit.returned (← resultOf asUnit (← field outcome "result")))
    | "unwound" => pure (Exit.unwound (← (← field outcome "reason").getStr?))
    | other => throw s!"unexpected finite exit {other}"
  let state ← field outcome "state"
  let syscalls ← Runtime.syscallsOf state
  pure (⟨exit, ← listField state "accounts" rawAccount, ← listField state "borrows" held,
    ← instruction (← field state "instruction"), ← listField state "caller_infos" recordedInfo,
    ← listField state "counts" Json.getNat?, ← syscalls.log.mapM search⟩, syscalls)

def observationJson (observed : Observation) : Json := Json.mkObj [
  ("exit", match observed.exit with
    | .returned result => resultJson (fun _ => Json.null) result
    | .unwound message => Json.mkObj [("unwound", Json.str message)]),
  ("instruction", instructionJson observed.instruction),
  ("info_cells", toJson (observed.infos.map (fun info => info.data.cell))),
  ("counts", toJson observed.counts), ("pda_count", toJson observed.searches.length)]

/-- Compare the registered full operational model on ordinary and unwind
exits. Terminal cases here cover the first mandatory PDA call only; their
exact forced request and leftover replies are checked separately. -/
def check (case : Case) : Result Verdict := do
  let raw ← listField case.state "accounts" rawAccount
  let held ← listField case.state "borrows" held
  let syscallBefore ← Runtime.syscallsOf case.state
  unless syscallBefore.log.isEmpty do throw "initial syscall log is not empty"
  let script ← syscallBefore.replies.mapM pdaExit
  let (args, instruction, caller, counts) ← decodeArgs script raw case.args
  let before : Sample.State := (borrowState raw held, {
    bytes := [some instruction.data], metas := [some instruction.metas], infos := [some caller],
      rcOwners := counts })
  let requires := Solanalib.Contracts.Model.requires
    (onchain.add_extra_accounts_for_execute_cpi_contract.contract (index script)) before args
  have : Decidable requires := instDecidableTrue
  unless decide requires do throw "outside model precondition"
  if (← (← field case.outcome "exit").getStr?) = "terminated" then
    let first ← accountAt syscallBefore.replies 0
    unless first.terminate.isSome do throw "terminal fixture requires a stopping first PDA \
      reply"
    let after ← Runtime.syscallsOf case.outcome
    let calls ← after.log.mapM search
    let expectedCall := hookPdaInputs args args.programId
    let admitted := decide (firstPdaTerminal script before args) && (← searchBumps after.log) &&
      (calls == [(expectedCall.seeds, args.programId)]) &&
      (after.replies == syscallBefore.replies.drop 1) &&
      ((← (← field case.outcome "reason").getStr?) == "sol_try_find_program_address") &&
      ((← (← field case.outcome "detail").getStr?) == first.terminate.getD "")
    pure ⟨admitted, Json.str "terminated at the first actual PDA request"⟩
  else
    let recordedCounts ← listField case.state "counts" Json.getNat?
    let (recorded, syscallAfter) ← recordedObservation case.outcome
    let computed := (fullRunF (prims script) before args).bind (observation script raw args)
    let admitted := recordedCounts == counts && decide (accepts script raw before args recorded) &&
      syscallAfter.replies == syscallBefore.replies.drop recorded.searches.length &&
      (← searchBumps syscallAfter.log)
    pure ⟨admitted, (computed.map observationJson).getD (Json.str "no represented finite \
      outcome")⟩

end SolanalibTest.Conformance.Library.Families.TransferHookResolution
