/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Core

/-!
# Readers for syscall, CPI and loader-input records

The Rust side is `rust/shim` (syscall requests and scripted replies, terminal exits) and
`rust/accounts` (the serialized input region of the loader). These readers turn their JSON into
plain Lean data; a family checker maps that data to the state, provider and outcome types of its
model. Nothing here is a model.

* `syscallState`: `{"replies": [...], "log": [...]}`, the `"syscalls"` field of a state (before:
  the script and an empty log; after: the unconsumed replies and every request).
* `terminated?`: the shim format `{"exit": "terminated", "reason", "detail", "syscalls"}`.
* `loaderInput`: the account list a case serializes (`Input::to_json`).
* `region`: the input region read back after the call (`Region::read_back`). -/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Runtime

/-! ## Syscalls -/

/-- The memory effect of a CPI on one C-ABI account info, applied before
`sol_invoke_signed_c` returns. -/
structure AccountWrite where
  account : Nat
  lamports : Option Nat
  data : Option Solanalib.Runtime.Bytes
  owner : Option Solanalib.Runtime.Bytes
  deriving DecidableEq, Repr

/-- One scripted reply, consumed by the next call of `syscall`. -/
structure Reply where
  syscall : String
  ret : Nat
  data : Solanalib.Runtime.Bytes
  programId : Option Solanalib.Runtime.Bytes
  bump : Option Nat
  terminate : Option String
  writes : List AccountWrite
  deriving DecidableEq, Repr

/-- One request: the syscall name and its other fields, as recorded
(see the README section on "Syscalls" table for the fields of each syscall). -/
structure Request where
  syscall : String
  fields : Json
  deriving Inhabited

structure SyscallState where
  replies : List Reply
  log : List Request

def optField {α : Type} (j : Json) (key : String) (parse : Json → Result α) : Result (Option α) :=
  match j.getObjVal? key with
  | .ok v => do pure (some (← parse v))
  | .error _ => pure none

def accountWrite (j : Json) : Result AccountWrite := do
  pure ⟨← (← field j "account").getNat?, ← optField j "lamports" Json.getNat?,
    ← optField j "data" asBytes, ← optField j "owner" asBytes⟩

def reply (j : Json) : Result Reply := do
  let writes ← match j.getObjVal? "writes" with
    | .ok w => do (← w.getArr?).toList.mapM accountWrite
    | .error _ => pure []
  pure ⟨← (← field j "syscall").getStr?, ← (← field j "return").getNat?, ← asBytes (← field j
    "data"),
    ← optField j "program_id" asBytes, ← optField j "bump" Json.getNat?,
    ← optField j "terminate" Json.getStr?, writes⟩

def request (j : Json) : Result Request := do
  pure ⟨← (← field j "syscall").getStr?, j⟩

def syscallState (j : Json) : Result SyscallState := do
  pure ⟨← (← (← field j "replies").getArr?).toList.mapM reply,
    ← (← (← field j "log").getArr?).toList.mapM request⟩

/-- The `"syscalls"` field of a record state. -/
def syscallsOf (state : Json) : Result SyscallState := do syscallState (← field state
  "syscalls")

namespace Request

def bytes (r : Request) (key : String) : Result Solanalib.Runtime.Bytes := do asBytes (← field
  r.fields key)

def nat (r : Request) (key : String) : Result Nat := do (← field r.fields key).getNat?

def bool (r : Request) (key : String) : Result Bool := do (← field r.fields key).getBool?

/-- A list of byte strings (`sol_log_data` fields, hash inputs, seeds). -/
def slices (r : Request) (key : String) : Result (List Solanalib.Runtime.Bytes) := do
  (← (← field r.fields key).getArr?).toList.mapM asBytes

end Request

/-- An instruction as prepared for `sol_invoke_signed_c`. -/
structure CpiMeta where
  pubkey : Solanalib.Runtime.Bytes
  isSigner : Bool
  isWritable : Bool
  deriving DecidableEq, Repr

structure CpiInstruction where
  programId : Solanalib.Runtime.Bytes
  accounts : List CpiMeta
  data : Solanalib.Runtime.Bytes
  deriving DecidableEq, Repr

structure CpiAccountInfo where
  key : Solanalib.Runtime.Bytes
  lamports : Nat
  data : Solanalib.Runtime.Bytes
  owner : Solanalib.Runtime.Bytes
  rentEpoch : Nat
  isSigner : Bool
  isWritable : Bool
  executable : Bool
  deriving DecidableEq, Repr

structure CpiCall where
  instruction : CpiInstruction
  accountInfos : List CpiAccountInfo
  signersSeeds : List (List Solanalib.Runtime.Bytes)
  deriving DecidableEq, Repr

def cpiMeta (j : Json) : Result CpiMeta := do
  pure ⟨← asBytes (← field j "pubkey"), ← (← field j "is_signer").getBool?, ← (← field j
    "is_writable").getBool?⟩

def cpiAccountInfo (j : Json) : Result CpiAccountInfo := do
  pure ⟨← asBytes (← field j "key"), ← (← field j "lamports").getNat?, ← asBytes (← field j
    "data"),
    ← asBytes (← field j "owner"), ← (← field j "rent_epoch").getNat?, ← (← field j
      "is_signer").getBool?,
    ← (← field j "is_writable").getBool?, ← (← field j "executable").getBool?⟩

/-- A `sol_invoke_signed_c` request. -/
def cpiCall (r : Request) : Result CpiCall := do
  unless r.syscall == "sol_invoke_signed_c" do throw s!"not a C-ABI CPI request: \
    {r.syscall}"
  let ix ← field r.fields "instruction"
  let instruction : CpiInstruction := ⟨← asBytes (← field ix "program_id"),
    ← (← (← field ix "accounts").getArr?).toList.mapM cpiMeta, ← asBytes (← field ix "data")⟩
  let infos ← (← (← field r.fields "account_infos").getArr?).toList.mapM cpiAccountInfo
  let seeds ← (← (← field r.fields "signers_seeds").getArr?).toList.mapM fun s => do
    (← s.getArr?).toList.mapM asBytes
  pure ⟨instruction, infos, seeds⟩

/-- The raw header bytes `[is_signer, is_writable, executable, padding]` of each
account info of a `sol_invoke_signed_c` request, as logged when the driver
turned on `shim::log_cpi_raw_header` (`none` for an account info without
them). The booleans of `cpiCall` mean "byte is nonzero". -/
def cpiRawHeaders (r : Request) : Result (List (Option (List Nat))) := do
  unless r.syscall == "sol_invoke_signed_c" do throw s!"not a C-ABI CPI request: \
    {r.syscall}"
  (← (← field r.fields "account_infos").getArr?).toList.mapM fun info =>
    optField info "header" fun h => do (← h.getArr?).toList.mapM Json.getNat?

/-- A shim terminal exit: reason (`sol_panic_`, `abort`, a syscall whose reply
was marked `terminate`, or `process`), detail and the syscall state at that
point; `none` for any other exit. -/
structure Terminated where
  reason : String
  detail : Json
  syscalls : Option SyscallState

def terminated? (outcome : Json) : Result (Option Terminated) := do
  match ← (← field outcome "exit").getStr? with
  | "terminated" =>
    let detail := (outcome.getObjVal? "detail").toOption.getD Json.null
    pure (some ⟨← (← field outcome "reason").getStr?, detail, ← optField outcome "syscalls"
      syscallState⟩)
  | _ => pure none

/-! ## Loader input region -/

structure InputAccount where
  key : Solanalib.Runtime.Bytes
  owner : Solanalib.Runtime.Bytes
  lamports : Nat
  data : Solanalib.Runtime.Bytes
  isSigner : Bool
  isWritable : Bool
  executable : Bool
  rentEpoch : Nat
  deriving DecidableEq, Repr

inductive InputEntry where
  | account (account : InputAccount)
  | duplicate (index : Nat)
  deriving DecidableEq, Repr

/-- The account list a case serializes into the input region. -/
structure LoaderInput where
  entries : List InputEntry
  instructionData : Solanalib.Runtime.Bytes
  programId : Solanalib.Runtime.Bytes
  deriving DecidableEq, Repr

def inputEntry (j : Json) : Result InputEntry := do
  match j.getObjVal? "duplicate_of" with
  | .ok i => pure (.duplicate (← i.getNat?))
  | .error _ => pure (.account ⟨← asBytes (← field j "key"), ← asBytes (← field j "owner"),
      ← (← field j "lamports").getNat?, ← asBytes (← field j "data"), ← (← field j
        "is_signer").getBool?,
      ← (← field j "is_writable").getBool?, ← (← field j "executable").getBool?,
      ← (← field j "rent_epoch").getNat?⟩)

def loaderInput (j : Json) : Result LoaderInput := do
  pure ⟨← (← (← field j "accounts").getArr?).toList.mapM inputEntry,
    ← asBytes (← field j "instruction_data"), ← asBytes (← field j "program_id")⟩

/-- A non-duplicate account in the region after the call. `marker` is the
first byte (`0xff` at entry; the account-view borrow state), `padding` the
4-byte field after the flags (the resize delta of the account-view as unsigned;
the deserialize of solana-program writes the original data length there),
`spareNonzeroAt` the first nonzero byte offset after `dataLen` within the
original length plus 10 KiB, computed from the recorded spare bytes (`spare`),
which must agree with the recorded `spare_nonzero_at`. The flag bytes are raw. -/
structure RegionAccount where
  marker : Nat
  isSigner : Nat
  isWritable : Nat
  executable : Nat
  padding : Nat
  key : Solanalib.Runtime.Bytes
  owner : Solanalib.Runtime.Bytes
  lamports : Nat
  dataLen : Nat
  data : Solanalib.Runtime.Bytes
  rentEpoch : Nat
  spareNonzeroAt : Option Nat
  deriving DecidableEq, Repr

inductive RegionEntry where
  | account (account : RegionAccount)
  | duplicate (index : Nat)
  deriving DecidableEq, Repr

structure Region where
  entries : List RegionEntry
  instructionData : Solanalib.Runtime.Bytes
  programId : Solanalib.Runtime.Bytes
  deriving DecidableEq, Repr

def regionEntry (j : Json) : Result RegionEntry := do
  match j.getObjVal? "duplicate_of" with
  | .ok i => pure (.duplicate (← i.getNat?))
  | .error _ =>
    let n (k : String) : Result Nat := do (← field j k).getNat?
    let data ← asBytes (← field j "data")
    let spare := ((← asBytes (← field j "spare")).findIdx? (· != 0)).map (data.length + ·)
    let recorded ← match ← field j "spare_nonzero_at" with
      | .null => pure none
      | v => do pure (some (← v.getNat?))
    unless spare == recorded do
      throw
        s!"spare_nonzero_at {recorded} disagrees with the spare bytes (first nonzero at \
          {spare})"
    pure (.account ⟨← n "marker", ← n "is_signer", ← n "is_writable", ← n "executable", ← n
      "padding",
      ← asBytes (← field j "key"), ← asBytes (← field j "owner"), ← n "lamports", ← n
        "data_len",
      data, ← n "rent_epoch", spare⟩)

def region (j : Json) : Result Region := do
  pure ⟨← (← (← field j "accounts").getArr?).toList.mapM regionEntry,
    ← asBytes (← field j "instruction_data"), ← asBytes (← field j "program_id")⟩

/-- The region an untouched input reads back as: markers `0xff`, padding 0,
everything else as given. Useful for a state before the call. -/
def LoaderInput.fresh (input : LoaderInput) : Region :=
  ⟨input.entries.map fun
      | .duplicate i => .duplicate i
      | .account a => .account ⟨255, if a.isSigner then 1 else 0, if a.isWritable then 1 else 0,
          if a.executable then 1 else 0, 0, a.key, a.owner, a.lamports, a.data.length, a.data,
          a.rentEpoch, none⟩,
    input.instructionData, input.programId⟩

end SolanalibTest.Conformance.Library.Runtime
