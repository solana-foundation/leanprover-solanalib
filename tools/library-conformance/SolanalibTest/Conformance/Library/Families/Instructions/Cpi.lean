/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Runtime
import SolanalibTest.Conformance.Library.Families.Instructions.Common
import Solanalib.Specs.SolanaInstructionView.Capabilities
import Solanalib.Specs.PinocchioSystem.Capabilities
import Solanalib.Specs.PinocchioAssociatedTokenAccount.Capabilities

/-!
# Family `Instructions`: checked CPI preparation

The slice entries of InstructionView 1.0.0, the InstructionView 2.1.0 fixed-array
`invoke_signed` at `A = &AccountView`, and the pinocchio-system and associated-token-account
wrappers above it. Each case runs over a loader input region (`rust/accounts`) with chosen
accounts, duplicates and live borrows, and the `sol_invoke_signed_c` of the shim, which logs the
prepared request and answers from the script of the case (normal return, callee account writes,
or a terminal failure).

## The checked index

`World` is the state of the record: the input region as read back, the unconsumed shim replies
and the CPI requests logged so far. From it:

- `pool`: the AccountView pool. Cells are the non-duplicate accounts of the region, in order; a
  duplicate entry denotes the cell of its target. The account of each cell is its region header
  and data; its live leases are read from the borrow byte (255 free, 0 one exclusive, otherwise
  `255 - b` shared), each a whole-data slot.
- `rawHeader`: the signer, writable and executable bytes of the region and the first padding
  byte.
- the invocation provider `invokeFn`: the next reply must be for `sol_invoke_signed_c`; it logs
  the request as the shim observes it (each descriptor read through the pool: key, lamports, the
  copied data length of bytes, owner, rent epoch and flags; with the raw header option of the
  shim, also the flag bytes of the descriptor and copied padding byte) and applies the writes of
  the reply to the region, or terminates. The library ignores the return value of the syscall,
  as the unit-returning invocation of the model does.
- The temporary boxed array of v1: allocation and drop are not observable and change nothing.

The registered relations are decided through the reductions of the models (`directV2_iff`) and
the graph lemmas below for function-form providers. -/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Instructions.Cpi

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.CpiRequest
  Solanalib.Specs.Core.CpiRequest.Checked
open SolanalibTest.Conformance.Library.Borsh

/-! ## World and projections -/

/-- A logged CPI request, with the raw header bytes of each account info
`[is_signer, is_writable, executable, padding]` when the case logs them. -/
structure LoggedCall where
  call : Runtime.CpiCall
  headers : List (Option (List Nat))
  deriving DecidableEq

structure World where
  region : Runtime.Region
  replies : List Runtime.Reply
  log : List LoggedCall
  /-- Whether the case turned on the raw header logging of the shim (`"raw_header": true`). -/
  rawHeader : Bool
  deriving DecidableEq

abbrev Entries := List Runtime.RegionEntry

/-- The non-duplicate accounts of the region: the cells, in order. -/
def accounts (entries : Entries) : List Runtime.RegionAccount :=
  entries.filterMap fun
    | .account a => some a
    | .duplicate _ => none

/-- The cell of entry `i`: the number of non-duplicate entries before its target. -/
def cellOf (entries : Entries) (i : Nat) : Nat :=
  let target := match entries[i]? with
    | some (.duplicate j) => j
    | _ => i
  (accounts (entries.take target)).length

def handleOf (entries : Entries) (i : Nat) : Borrow.Handle := ⟨cellOf entries i⟩

def pubkeyOf (b : Solanalib.Runtime.Bytes) : Solanalib.Runtime.Pubkey :=
  Solanalib.Runtime.Pubkey.ofBytes b

def accountOf (a : Runtime.RegionAccount) : AccountView.Account :=
  ⟨⟨pubkeyOf a.key, a.isSigner != 0, a.isWritable != 0, a.executable != 0⟩, pubkeyOf a.owner,
    a.lamports, a.dataLen, a.dataLen, a.data, 0, 0⟩

/-- Live leases of cell `k` from its borrow byte. -/
def slotsOf (k : Nat) (a : Runtime.RegionAccount) : List (Option (Borrow.Slot AccountView.Slice)) :=
  let whole : AccountView.Slice := ⟨0, a.dataLen⟩
  if a.marker = 255 then []
  else if a.marker = 0 then [some ⟨⟨k⟩, .exclusive, 0, whole⟩]
  else List.replicate (255 - a.marker) (some ⟨⟨k⟩, .shared, 0, whole⟩)

def slotsFrom : Nat → List Runtime.RegionAccount → List (Option (Borrow.Slot AccountView.Slice))
  | _, [] => []
  | k, a :: rest => slotsOf k a ++ slotsFrom (k + 1) rest

/-- A shim terminal exit, as recorded: the reason (the syscall whose reply terminates, or
`shim` for a script error), its detail and the syscall state at that point (the unconsumed
replies and every logged request, including the request of the failing call). -/
structure Terminal where
  reason : String
  detail : String
  replies : List Runtime.Reply
  log : List LoggedCall
  deriving DecidableEq

def poolOf (region : Runtime.Region) : AccountView.State :=
  let cells := accounts region.entries
  ⟨cells.map fun a => ⟨accountOf a, Borrow.Policy.accountView⟩, slotsFrom 0 cells⟩

def pool (w : World) : AccountView.State := poolOf w.region

def rawHeader (w : World) (h : Borrow.Handle) : RawHeader :=
  match (accounts w.region.entries)[h.cell]? with
  | some a => ⟨UInt8.ofNat a.isSigner, UInt8.ofNat a.isWritable, UInt8.ofNat a.executable,
      UInt8.ofNat (a.padding % 256)⟩
  | none => ⟨0, 0, 0, 0⟩

/-! ## The invocation provider -/

/-- A prepared descriptor as the shim reads it through its pointers. -/
def infoOf (p : AccountView.State) (d : Descriptor) : Runtime.CpiAccountInfo :=
  let a := p.account d.account
  ⟨a.metadata.address.bytes, a.lamports, a.backing.take d.dataLen, a.owner.bytes, d.rentEpoch,
    d.isSigner != 0, d.isWritable != 0, d.executable != 0⟩

def instructionOf (i : Solanalib.Runtime.CpiInstruction) : Runtime.CpiInstruction :=
  ⟨i.programId.bytes, i.metas.map fun m => ⟨m.key.bytes, m.signerByte != 0, m.writableByte != 0⟩,
    i.data⟩

/-- The four header bytes the shim reads from a prepared descriptor: its flag bytes and its
copied padding byte (v1 copies none; such a case does not log headers). -/
def headerOf (d : Descriptor) : List Nat :=
  [d.isSigner.toNat, d.isWritable.toNat, d.executable.toNat, (d.copiedPadding.getD 0).toNat]

def callOf (p : AccountView.State) (raw : Bool) (req : Request Descriptor) : LoggedCall :=
  ⟨⟨instructionOf req.instruction, req.accounts.map (infoOf p), req.signers⟩,
    req.accounts.map fun d => if raw then some (headerOf d) else none⟩

/-- Update the `k`-th non-duplicate account of the region. -/
def updateCell (f : Runtime.RegionAccount → Runtime.RegionAccount) : Nat → Entries → Entries
  | _, [] => []
  | k, .duplicate j :: rest => .duplicate j :: updateCell f k rest
  | 0, .account a :: rest => .account (f a) :: rest
  | k + 1, .account a :: rest => .account a :: updateCell f k rest

/-- A callee write to the `account`-th prepared account (shim `AccountWrite`). -/
def applyWrite (prepared : List Descriptor) (entries : Entries) (w : Runtime.AccountWrite) :
  Entries :=
  match prepared[w.account]? with
  | none => entries
  | some d => updateCell (fun a => { a with
      lamports := w.lamports.getD a.lamports
      data := match w.data with
        | some bytes => bytes ++ a.data.drop bytes.length
        | none => a.data
      owner := w.owner.getD a.owner }) d.account.cell entries

def cpiSyscall : String := "sol_invoke_signed_c"

/-- The `sol_invoke_signed_c` of the shim under the script of the case. -/
def invokeFn (w : World) (req : Request Descriptor) : Outcome World Unit String Terminal :=
  let logged := w.log ++ [callOf (pool w) w.rawHeader req]
  match w.replies with
  | r :: rest =>
    if r.syscall = cpiSyscall then
      match r.terminate with
      | some detail => .terminated ⟨cpiSyscall, detail, rest, logged⟩
      | none => .returned ()
          ⟨{ w.region with entries := r.writes.foldl (applyWrite req.accounts) w.region.entries },
            rest, logged, w.rawHeader⟩
    else .terminated ⟨"shim", s!"script error: {cpiSyscall} called, next reply is for \
      {r.syscall}",
      w.replies, logged⟩
  | [] => .terminated ⟨"shim", s!"script error: {cpiSyscall} called, no reply left", [], logged⟩

/-! ## Graph lemmas for function-form providers -/

abbrev Out := Outcome World (Except Error Unit) String Terminal

/-- The checked v2 path at the identity `AsRef`, with a function-form invocation. -/
def directFn (f : World → Request Descriptor → Outcome World Unit String Terminal)
    (before : World) (request : Request AccountView.Handle) : Out :=
  if request.accounts.length < request.instruction.metas.length then
    .returned (.error .NotEnoughAccountKeys) before
  else match prepareDirectV2 (pool before) (rawHeader before) request.instruction.metas
    request.accounts with
    | .error error => .returned (.error error) before
    | .ok prepared => Outcome.map (fun _ => .ok ()) (f before ⟨request.instruction, prepared,
      request.signers⟩)

theorem directV2_fn_iff (f : World → Request Descriptor → Outcome World Unit String Terminal)
    (before : World) (request : Request AccountView.Handle) (o : Out) :
    directV2 pool rawHeader (Callback.ofFunction f) before request o ↔ directFn f before request =
      o := by
  rw [directV2_iff]
  unfold directFn
  split
  · exact eq_comm
  · cases prepareDirectV2 (pool before) (rawHeader before) request.instruction.metas
      request.accounts with
    | error e => exact eq_comm
    | ok prepared => exact Callback.map_ofFunction _ f before _ o

/-- The checked v1 inner path, with a function-form invocation. -/
def innerV1Fn (f : World → Request Descriptor → Outcome World Unit String Terminal)
    (before : World) (request : Request AccountView.Handle) : Out :=
  if request.accounts.length < request.instruction.metas.length then
    .returned (.error .NotEnoughAccountKeys) before
  else match prepareV1 (pool before) request.instruction.metas request.accounts with
    | .error error => .returned (.error error) before
    | .ok prepared => Outcome.map (fun _ => .ok ()) (f before ⟨request.instruction, prepared,
      request.signers⟩)

theorem innerV1_fn_iff (f : World → Request Descriptor → Outcome World Unit String Terminal)
    (before : World) (request : Request AccountView.Handle) (o : Out) :
    innerV1 pool (Callback.ofFunction f) before request o ↔ innerV1Fn f before request = o := by
  unfold innerV1 innerV1Fn
  split
  · exact eq_comm
  · cases prepareV1 (pool before) request.instruction.metas request.accounts with
    | error e => exact eq_comm
    | ok prepared => exact Callback.map_ofFunction _ f before _ o

/-- Rust aborts when a destructor panics during unwinding (never reached: the drop returns). -/
def doublePanic : Terminal := ⟨"abort", "panic in a destructor during cleanup", [], []⟩

/-- The allocation and drop of the boxed array: unobservable, no effect. -/
def boxStorage : Storage World Unit String Terminal where
  allocate := Callback.ofFunction fun s _ => .returned () s
  drop := Callback.ofFunction fun s _ => .returned () s
  doubleUnwind := fun _ _ _ terminal => terminal = doublePanic

def sliceFn (f : World → Request Descriptor → Outcome World Unit String Terminal)
    (before : World) (request : Request AccountView.Handle) : Out :=
  if 128 < request.instruction.metas.length then .returned (.error .InvalidArgument) before
  else innerV1Fn f before request

theorem cleanup_box (pending final : Out) :
    Owned.cleanup boxStorage.doubleUnwind [fun current => boxStorage.drop current ()] pending final
      ↔
      pending = final := by
  cases pending with
  | returned v s =>
    simp only [Owned.cleanup, boxStorage, Callback.ofFunction]
    constructor
    · rintro ⟨d, hd, hm⟩; subst hd; exact hm.symm
    · intro h; exact ⟨_, rfl, h.symm⟩
  | unwound r s =>
    simp only [Owned.cleanup, boxStorage, Callback.ofFunction]
    constructor
    · rintro ⟨d, hd, hm⟩; subst hd; exact hm.symm
    · intro h; exact ⟨_, rfl, h.symm⟩
  | terminated t => exact eq_comm

theorem sliceV1_fn_iff (f : World → Request Descriptor → Outcome World Unit String Terminal)
    (before : World) (request : Request AccountView.Handle) (o : Out) :
    sliceV1 pool boxStorage (Callback.ofFunction f) before request o ↔ sliceFn f before request = o
      := by
  unfold sliceV1 sliceFn
  split
  · exact eq_comm
  · simp only [Callback.bind, boxStorage, Callback.ofFunction]
    constructor
    · rintro ⟨i, hi, hm⟩
      subst hi
      obtain ⟨pending, hbody, hclean⟩ := hm
      rw [innerV1_fn_iff] at hbody
      rw [← (cleanup_box pending o).mp hclean, hbody]
    · intro h
      exact ⟨_, rfl, _, (innerV1_fn_iff f before request _).mpr rfl, (cleanup_box _ o).mpr h⟩

/-! ## Records -/

def loggedCalls (log : List Runtime.Request) : Result (List LoggedCall) :=
  log.mapM fun r => do pure (⟨← Runtime.cpiCall r, ← Runtime.cpiRawHeaders r⟩ : LoggedCall)

def world (state : Json) : Result World := do
  let region ← Runtime.region (← field state "region")
  let syscalls ← Runtime.syscallsOf state
  let log ← loggedCalls syscalls.log
  let raw ← match state.getObjVal? "raw_header" with
    | .ok v => v.getBool?
    | .error _ => pure false
  pure ⟨region, syscalls.replies, log, raw⟩

def errorName : Error → String
  | .NotEnoughAccountKeys => "NotEnoughAccountKeys"
  | .InvalidArgument => "InvalidArgument"
  | .AccountBorrowFailed => "AccountBorrowFailed"
  | _ => "other"

def errorOf (j : Json) : Result Error := do
  match ← j.getStr? with
  | "NotEnoughAccountKeys" => pure .NotEnoughAccountKeys
  | "InvalidArgument" => pure .InvalidArgument
  | "AccountBorrowFailed" => pure .AccountBorrowFailed
  | other => throw s!"error {other} is not a checked-helper error"

/-- The terminated outcome of the shim: reason, detail and syscall state, all compared. -/
def terminalOf (j : Json) : Result (Option Terminal) := do
  match ← Runtime.terminated? j with
  | none => pure none
  | some t =>
    let detail ← t.detail.getStr?
    let some syscalls := t.syscalls | throw "terminated outcome without its syscall state"
    pure (some ⟨t.reason, detail, syscalls.replies, ← loggedCalls syscalls.log⟩)

/-- A recorded outcome; `state` parses the state of a returned or unwound outcome. -/
def recordedWith {W V : Type} (value : Json → Result V) (state : Json → Result W) (j : Json) :
    Result (Option (Outcome W V String Terminal)) := do
  match ← terminalOf j with
  | some t => pure (some (.terminated t))
  | none => parseOutcome value state (fun r => some r) noReason j

def recorded (j : Json) : Result (Option Out) := recordedWith (asExcept errorOf asUnit) world j

def terminalJson (t : Terminal) : Json :=
  Json.mkObj [("exit", "terminated"), ("reason", Json.str t.reason), ("detail", Json.str t.detail),
    ("syscalls", Json.mkObj [("replies_left", toJson t.replies.length), ("cpi_calls", toJson
      t.log.length)])]

/-- A summary of the computed outcome for the report. -/
def outJson : Out → Json
  | .returned r w => returnedJson (exceptJson (fun e => Json.str (errorName e)) (fun _ =>
    Json.null) r)
      (Json.mkObj [("cpi_calls", toJson w.log.length), ("replies_left", toJson w.replies.length)])
  | .unwound reason w => Json.mkObj [("exit", "unwound"), ("reason", Json.str reason),
      ("state", Json.mkObj [("cpi_calls", toJson w.log.length)])]
  | .terminated t => terminalJson t

def entryIndex (j : Json) : Result Nat := j.getNat?

def handleField (entries : Entries) (j : Json) (k : String) : Result Borrow.Handle := do
  pure (handleOf entries (← entryIndex (← field j k)))

def handles (entries : Entries) (j : Json) : Result (List Borrow.Handle) := do
  pure ((← asList entryIndex (← field j "accounts")).map (handleOf entries))

def signersOf (j : Json) : Result (List (List Solanalib.Runtime.Bytes)) := do
  asList (asList asBytes) (← field j "signers")

/-- Decide `relation before args recorded` through `graph : relation o ↔ computed = o`. -/
def decideCpi (c : Case) (k : World → Result (Σ' (relation : Out → Prop) (computed : Out),
    ∀ o, relation o ↔ computed = o)) : Result Verdict := do
  let before ← world c.state
  let ⟨relation, computed, graph⟩ ← k before
  pure (decideGraph relation computed graph (← recorded c.outcome) outJson)

/-! ## pinocchio-system 0.6.0 and pinocchio-associated-token-account 0.4.0 -/

def headerTypes : HeaderTypes := ⟨⟨World, pool, String, Terminal⟩, rawHeader⟩

abbrev invoke : Syscall World String Terminal := Callback.ofFunction invokeFn

namespace PSystem
open Solanalib.Specs.PinocchioSystem.instructions

theorem transfer_evaluated (before : World) (args : transfer.Transfer.Args headerTypes)
    (h : args.invoke = invoke) (o : Out) :
    transfer.Transfer.invoke_run headerTypes before args o ↔
      directFn invokeFn before (transfer.Transfer.request before args) = o := by
  show directV2 pool rawHeader args.invoke before _ o ↔ _
  rw [h]; exact directV2_fn_iff invokeFn before _ o

theorem allocate_evaluated (before : World) (args : allocate.Allocate.Args headerTypes)
    (h : args.invoke = invoke) (o : Out) :
    allocate.Allocate.invoke_signed_run headerTypes before args o ↔
      directFn invokeFn before (allocate.Allocate.request before args) = o := by
  show directV2 pool rawHeader args.invoke before _ o ↔ _
  rw [h]; exact directV2_fn_iff invokeFn before _ o

theorem assign_evaluated (before : World) (args : assign.Assign.Args headerTypes)
    (h : args.invoke = invoke) (o : Out) :
    assign.Assign.invoke_signed_run headerTypes before args o ↔
      directFn invokeFn before (assign.Assign.request before args) = o := by
  show directV2 pool rawHeader args.invoke before _ o ↔ _
  rw [h]; exact directV2_fn_iff invokeFn before _ o

def transferChecker : Checker where
  function := "pinocchio_system::instructions::transfer::Transfer::<'_>::invoke"
  generics := []
  reference := "Solanalib.Specs.PinocchioSystem.instructions.transfer.Transfer.invoke_run"
  decides := ["Solanalib.Specs.PinocchioSystem.instructions.transfer.Transfer.invoke_run"]
  check := fun c => decideCpi c fun before => do
    let e := before.region.entries
    let args : transfer.Transfer.Args headerTypes :=
      ⟨← handleField e c.args "from", ← handleField e c.args "to", ← natField c.args
        "lamports" 64,
        invoke⟩
    pure ⟨_, _, transfer_evaluated before args rfl⟩

def allocateChecker : Checker where
  function := "pinocchio_system::instructions::allocate::Allocate::<'_>::invoke_signed"
  generics := []
  reference := "Solanalib.Specs.PinocchioSystem.instructions.allocate.Allocate.invoke_signe\
    d_run"
  decides := ["Solanalib.Specs.PinocchioSystem.instructions.allocate.Allocate.invoke_signed\
    _run"]
  check := fun c => decideCpi c fun before => do
    let e := before.region.entries
    let args : allocate.Allocate.Args headerTypes :=
      ⟨← handleField e c.args "account", ← natField c.args "space" 64, ← signersOf c.args, invoke⟩
    pure ⟨_, _, allocate_evaluated before args rfl⟩

def assignChecker : Checker where
  function := "pinocchio_system::instructions::assign::Assign::<'_, '_>::invoke_signed"
  generics := []
  reference := "Solanalib.Specs.PinocchioSystem.instructions.assign.Assign.invoke_signed_ru\
    n"
  decides := ["Solanalib.Specs.PinocchioSystem.instructions.assign.Assign.invoke_signed_run"]
  check := fun c => decideCpi c fun before => do
    let e := before.region.entries
    let args : assign.Assign.Args headerTypes :=
      ⟨← handleField e c.args "account", ← keyField c.args "owner", ← signersOf c.args, invoke⟩
    pure ⟨_, _, assign_evaluated before args rfl⟩

end PSystem

namespace Ata
open Solanalib.Specs.PinocchioAssociatedTokenAccount.instructions.create_idempotent

theorem create_idempotent_evaluated (before : World) (args : CreateIdempotent.Args headerTypes)
    (h : args.invoke = invoke) (o : Out) :
    CreateIdempotent.invoke_run headerTypes before args o ↔
      directFn invokeFn before (CreateIdempotent.request before args) = o := by
  show directV2 pool rawHeader args.invoke before _ o ↔ _
  rw [h]; exact directV2_fn_iff invokeFn before _ o

def checker : Checker where
  function :=
    "pinocchio_associated_token_account::instructions::create_idempotent::CreateIdempotent:\
      :<'_>::invoke"
  generics := []
  reference :=
    "Solanalib.Specs.PinocchioAssociatedTokenAccount.instructions.create_idempotent.CreateI\
      dempotent.invoke_run"
  decides :=
    ["Solanalib.Specs.PinocchioAssociatedTokenAccount.instructions.create_idempotent.Create\
      Idempotent.invoke_run"]
  check := fun c => decideCpi c fun before => do
    let e := before.region.entries
    let h (k : String) := handleField e c.args k
    let args : CreateIdempotent.Args headerTypes :=
      ⟨← h "funding_account", ← h "account", ← h "wallet", ← h "mint", ← h "system_program",
        ← h "token_program", invoke⟩
    pure ⟨_, _, create_idempotent_evaluated before args rfl⟩

end Ata

/-! ## solana-instruction-view 2.1.0 `invoke_signed` at `A = &AccountView` -/

namespace V2

def arrayTypes : ArrayTypes := ⟨headerTypes, AccountView.Handle, identityAsRef⟩

theorem invoke_signed_evaluated (before : World) (args : ArrayCall arrayTypes) (h : args.invoke =
  invoke)
    (o : Out) :
    Solanalib.Specs.SolanaInstructionView.cpi.invoke_signed_run arrayTypes before args o ↔
      directFn invokeFn before ⟨args.instruction, args.accounts.values, args.signers⟩ = o := by
  show directV2 pool rawHeader args.invoke before _ o ↔ _
  rw [h]; exact directV2_fn_iff invokeFn before _ o

def staticAccounts {α : Type} (size : Nat) (values : List α) : Result (StaticAccounts α) :=
  if h : values.length = size then pure ⟨size, values, h⟩
  else throw s!"{values.length} accounts recorded at ACCOUNTS = {size}"

def checker (size : Nat) : Checker where
  function := "solana_instruction_view::cpi::invoke_signed"
  generics := [("ACCOUNTS", toString size), ("A", "&solana_account_view::AccountView")]
  reference := "Solanalib.Specs.SolanaInstructionView.cpi.invoke_signed_run"
  decides := ["Solanalib.Specs.SolanaInstructionView.cpi.invoke_signed_run"]
  check := fun c => decideCpi c fun before => do
    let args : ArrayCall arrayTypes := ⟨← instructionOf' c.args, ← staticAccounts size (← handles
      before.region.entries c.args),
      ← signersOf c.args, invoke⟩
    pure ⟨_, _, invoke_signed_evaluated before args rfl⟩
where
  instructionOf' (j : Json) : Result Solanalib.Runtime.CpiInstruction := do
    Instructions.instructionOf (← field j "instruction")

end V2

/-! ## solana-instruction-view 1.0.0 slice entries -/

namespace V1

def sliceTypes : SliceTypes := ⟨⟨World, pool, String, Terminal⟩, Unit, boxStorage⟩

theorem invoke_signed_with_slice_evaluated (before : World) (args : SignedCall sliceTypes)
    (h : args.invoke = invoke) (o : Out) :
    Solanalib.Specs.SolanaInstructionView.cpi.invoke_signed_with_slice_run sliceTypes before args o
      ↔
      sliceFn invokeFn before args.request = o := by
  show sliceV1 pool boxStorage args.invoke before args.request o ↔ _
  rw [h]; exact sliceV1_fn_iff invokeFn before _ o

theorem invoke_with_slice_evaluated (before : World) (args : UnsignedCall sliceTypes)
    (h : args.invoke = invoke) (o : Out) :
    Solanalib.Specs.SolanaInstructionView.cpi.invoke_with_slice_run sliceTypes before args o ↔
      sliceFn invokeFn before ⟨args.instruction, args.accounts, []⟩ = o := by
  show sliceV1 pool boxStorage args.invoke before _ o ↔ _
  rw [h]; exact sliceV1_fn_iff invokeFn before _ o

def instruction (j : Json) : Result Solanalib.Runtime.CpiInstruction := do
  Instructions.instructionOf (← field j "instruction")

def signedChecker : Checker where
  function := "solana_instruction_view::cpi::invoke_signed_with_slice"
  generics := []
  reference := "Solanalib.Specs.SolanaInstructionView.cpi.invoke_signed_with_slice_run"
  decides := ["Solanalib.Specs.SolanaInstructionView.cpi.invoke_signed_with_slice_run"]
  check := fun c => decideCpi c fun before => do
    let args : SignedCall sliceTypes :=
      ⟨⟨← instruction c.args, ← handles before.region.entries c.args, ← signersOf c.args⟩, invoke⟩
    pure ⟨_, _, invoke_signed_with_slice_evaluated before args rfl⟩

def unsignedChecker : Checker where
  function := "solana_instruction_view::cpi::invoke_with_slice"
  generics := []
  reference := "Solanalib.Specs.SolanaInstructionView.cpi.invoke_with_slice_run"
  decides := ["Solanalib.Specs.SolanaInstructionView.cpi.invoke_with_slice_run"]
  check := fun c => decideCpi c fun before => do
    let args : UnsignedCall sliceTypes :=
      ⟨← instruction c.args, ← handles before.region.entries c.args, invoke⟩
    pure ⟨_, _, invoke_with_slice_evaluated before args rfl⟩

end V1

end SolanalibTest.Conformance.Library.Families.Instructions.Cpi
