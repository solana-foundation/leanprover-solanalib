/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Runtime
import Solanalib.Specs.SolanaAccountView

/-!
# solana-account-view 2.0.0: projection of a native input region

The driver `rust/accounts-v2` serializes accounts exactly as the loader does
(`rust/accounts`, ABI v1 aligned input region), makes an `AccountView` of each
instruction account from the address of its first occurrence (as the
entrypoint does; a duplicate entry aliases the earlier account), and calls the
unmodified library. The state of a record is

```
{"input": <Region::read_back>, "backing": [hex], "guards": [entry], "owner_epochs": [n]}
```

and denotes the model state (`Borrow.State Account Slice`) below.

* Cell `c` is the `c`-th non-duplicate entry of the region. Its metadata are
  `key` and the nonzero observation of the three flag bytes; `owner`,
  `lamports` and `data_len` are the header fields read back after the call.
  Its backing is the data area of the account up to the length serialized at entry
  (`entryLen`), so it includes bytes beyond `data_len`; the driver also records
  it as `backing[c]`.
* `guards[k]` is the live guard with ghost identity `k`, as
  `[cell, mode, generation, offset, length]`, or `null` once dropped. `cell` is
  the account whose `borrow_state` byte the private `state` pointer of the guard addresses, `mode`
  its type (`Ref` shared, `RefMut` exclusive), `offset` and
  `length` its private `value` pointer relative to the data of that account and the length of the
  referent, read from the guard object itself (not through `Deref`).
  A guard leaked by an unwinding `try_map` closure keeps its entry.
* An argument `{"account": i}` is the `AccountView` of instruction account `i`;
  it denotes the cell of the first occurrence of `i`.

Ghost components, fixed by projection rules rather than observed: guard
identities count acquisitions in order; a generation starts at 0 and advances
on every move through `try_map` (each exit with a state); `owner_epochs[c]`
counts successful `close` calls on cell `c`; `resizeDelta` is 0 (2.0.0 has no
resize counter); every cell has the AccountView policy (254 shared guards).

A native state is denoted only if (a) the `marker` of each account (the `borrow_state` of
account-view) is the source encoding of its live guards (255 free, `255 - n`
for `n` shared, 0 exclusive), and (b) its whole data area, the read-back `data`
followed by every `spare` byte, is the backing (the first `entryLen` bytes, of
which `data_len` are read back as `data`) followed by the 10 KiB realloc
reserve, all of whose bytes are zero; `spare_nonzero_at` must be the first nonzero byte of the area
at or after `data_len`. The recorded `backing` must equal the
backing read back. An after-state is denoted only if, moreover, every byte of
the region the model does not represent (`Frame`: flag bytes, the 4-byte
padding, key, rent epoch, the realloc reserve and alignment padding of each
account, each duplicate entry with its padding, the account count, instruction
data and program id) equals the state before the call. So every byte of the
read-back region is either projected onto the model state or compared. A
record whose after-state is not denoted is rejected.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.AccountsV2

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Runtime (Region RegionEntry RegionAccount)

abbrev PoolState := AccountView.State
abbrev ObsState := AccountViewObservation.State
abbrev Account := AccountView.Account
abbrev Slice := AccountView.Slice
abbrev Handle := Borrow.Handle
abbrev Guard := Borrow.Guard
abbrev Slot := Borrow.Slot Slice
abbrev Mode := Borrow.Mode

/-! ## Values -/

def pubkey (j : Json) : Result Solanalib.Runtime.Pubkey := do
  let b ← asBytes j
  if h : b.length = 32 then pure ⟨b, h⟩ else throw s!"address must have 32 bytes, got \
    {b.length}"

def pubkeyOf (b : Solanalib.Runtime.Bytes) : Result Solanalib.Runtime.Pubkey :=
  if h : b.length = 32 then pure ⟨b, h⟩ else throw s!"address must have 32 bytes, got \
    {b.length}"

def pubkeyJson (k : Solanalib.Runtime.Pubkey) : Json := bytesJson k.bytes

def flagJson (b : Bool) : Json := toJson (if b then 1 else 0 : Nat)

def natField (j : Json) (key : String) : Result Nat := do (← field j key).getNat?

def parseMode : String → Result Mode
  | "shared" => pure .shared
  | "exclusive" => pure .exclusive
  | other => throw s!"unknown guard mode {other}"

def modeJson : Mode → Json
  | .shared => "shared"
  | .exclusive => "exclusive"

/-- A guard token `[id, generation]`. -/
def parseGuard (j : Json) : Result Guard := do
  match (← j.getArr?).toList with
  | [i, g] => return ⟨← i.getNat?, ← g.getNat?⟩
  | _ => throw s!"guard must be [id, generation], got {j.compress}"

def guardJson (g : Guard) : Json := Json.arr #[toJson g.id, toJson g.generation]

/-! ## States -/

/-- The source `borrow_state` byte of the live guards of a cell, if it has one. -/
def leaseByte (state : PoolState) (handle : Handle) : Option Nat :=
  let x := state.exclusiveCount handle
  let s := state.sharedCount handle
  if x = 0 then (if s ≤ 254 then some (255 - s) else none)
  else if x = 1 ∧ s = 0 then some 0 else none

def parseSlot (j : Json) : Result (Option Slot) :=
  match j with
  | .null => pure none
  | _ => do
    match (← j.getArr?).toList with
    | [c, m, g, o, l] =>
      return some ⟨⟨← c.getNat?⟩, ← parseMode (← m.getStr?), ← g.getNat?, ⟨← o.getNat?, ←
        l.getNat?⟩⟩
    | _ => throw s!"guard entry must be [cell, mode, generation, offset, length], got \
      {j.compress}"

def isAccount : RegionEntry → Bool
  | .account _ => true
  | .duplicate _ => false

def regionAccounts (r : Region) : List RegionAccount :=
  r.entries.filterMap fun
    | .account a => some a
    | .duplicate _ => none

/-- The cell of instruction account `i`: the position of its first occurrence
among the non-duplicate entries. -/
def cellOf (r : Region) (i : Nat) : Option Nat :=
  let position (j : Nat) : Option Nat := match r.entries[j]? with
    | some (.account _) => some ((r.entries.take j).countP isAccount)
    | _ => none
  match r.entries[i]? with
  | some (.account _) => position i
  | some (.duplicate j) => if j < i then position j else none
  | none => none

/-- The realloc reserve after the serialized data of each account (`MAX_PERMITTED_DATA_INCREASE`).
-/
def reserveLen : Nat := 10 * 1024

/-- The bytes of one region entry that the model does not represent: the raw
flag bytes, the 4-byte padding, the key, the rent epoch, the realloc reserve
(the data area beyond the serialized length) and the alignment padding of an
account; the index and padding bytes of a duplicate. -/
inductive FrameEntry where
  | account (isSigner isWritable executable padding : Nat) (key : Solanalib.Runtime.Bytes)
    (rentEpoch : Nat)
      (reserve alignment : Solanalib.Runtime.Bytes)
  | duplicate (index : Nat) (padding : Solanalib.Runtime.Bytes)
  deriving DecidableEq

/-- Every byte of the region the model does not represent. -/
structure Frame where
  entries : List FrameEntry
  count : Nat
  instructionData : Solanalib.Runtime.Bytes
  programId : Solanalib.Runtime.Bytes
  deriving DecidableEq

/-- The read-back fields beyond `Runtime.RegionEntry`: the `spare` bytes of an account (its data
area after `data_len`, up to the serialized length plus the
reserve) and `alignment_padding`; the 7 padding bytes of a duplicate. -/
inductive Extra where
  | account (spare alignment : Solanalib.Runtime.Bytes)
  | duplicate (padding : Solanalib.Runtime.Bytes)

def parseExtra (j : Json) : Result Extra := do
  match j.getObjVal? "duplicate_of" with
  | .ok _ => return .duplicate (← asBytes (← field j "padding"))
  | .error _ => return .account (← asBytes (← field j "spare")) (← asBytes (← field j
    "alignment_padding"))

def firstNonzero (bytes : Solanalib.Runtime.Bytes) (start : Nat) : Option Nat :=
  ((bytes.drop start).findIdx? (· ≠ 0)).map (· + start)

/-- The whole data area of an account, `data ++ spare`, split at the serialized
length into the backing and the reserve, if the read-back denotes them:
the area has room for the reserve, the logical length is within the backing
and read back in full, `spare_nonzero_at` is the first nonzero byte of the area at
or after `data_len`, and the reserve is zero. -/
def splitArea (a : RegionAccount) (spare : Solanalib.Runtime.Bytes) : Option
  (Solanalib.Runtime.Bytes × Solanalib.Runtime.Bytes) :=
  let area := a.data ++ spare
  let entryLen := area.length - reserveLen
  let backing := area.take entryLen
  let reserve := area.drop entryLen
  if reserveLen ≤ area.length ∧ a.data.length = a.dataLen ∧ a.dataLen ≤ entryLen ∧
      a.spareNonzeroAt = firstNonzero area a.dataLen ∧ reserve.all (· == 0) then
    some (backing, reserve)
  else none

/-- A native state: its unrepresented bytes and the model state it denotes. -/
structure Native where
  region : Region
  frame : Frame
  state : PoolState

def account (a : RegionAccount) (backing : Solanalib.Runtime.Bytes) (epoch : Nat) : Result Account
  := do
  return {
    metadata := ⟨← pubkeyOf a.key, a.isSigner != 0, a.isWritable != 0, a.executable != 0⟩
    owner := ← pubkeyOf a.owner
    lamports := a.lamports
    dataLen := a.dataLen
    entryLen := backing.length
    backing
    resizeDelta := 0
    ownerEpoch := epoch }

/-- One region entry: its frame entry and, for an account, its backing; `none`
if the data area of the entry denotes no backing. -/
def entryParts : RegionEntry × Extra → Result (Option (FrameEntry × Option (RegionAccount ×
  Solanalib.Runtime.Bytes)))
  | (.duplicate i, .duplicate padding) => return some (.duplicate i padding, none)
  | (.account a, .account spare alignment) =>
    return (splitArea a spare).map fun (backing, reserve) =>
      (.account a.isSigner a.isWritable a.executable a.padding a.key a.rentEpoch reserve alignment,
        some (a, backing))
  | _ => throw "region entry and its read-back fields disagree"

/-- The model state denoted by a native state, or `none` if it denotes none. -/
def parseNative (j : Json) : Result (Option Native) := do
  let input ← field j "input"
  let r ← Runtime.region input
  let extras ← (← (← field input "accounts").getArr?).toList.mapM parseExtra
  let backings ← (← (← field j "backing").getArr?).toList.mapM asBytes
  let epochs ← (← (← field j "owner_epochs").getArr?).toList.mapM Json.getNat?
  let slots ← (← (← field j "guards").getArr?).toList.mapM parseSlot
  let parts ← (r.entries.zip extras).mapM entryParts
  match parts.mapM id with
  | none => return none
  | some parts =>
    let frame : Frame := ⟨parts.map (·.1), ← natField input "count", r.instructionData, r.programId⟩
    let raw := parts.filterMap (·.2)
    unless raw.length = backings.length ∧ raw.length = epochs.length do
      throw s!"{raw.length} accounts, {backings.length} backings and {epochs.length} owner \
        epochs"
    let accounts ← (raw.zip epochs).mapM fun ((a, b), e) => account a b e
    let state : PoolState := ⟨accounts.map fun a => ⟨a, Borrow.Policy.accountView⟩, slots⟩
    let inRange := slots.all fun
      | none => true
      | some slot => decide (slot.cell.cell < accounts.length)
    let markers := (raw.zipIdx).all fun ((a, _), i) => leaseByte state ⟨i⟩ == some a.marker
    -- The recorded `backing` is that of the region: it adds no information, only agreement.
    let recorded := (raw.zip backings).all fun ((_, b), recorded) => b == recorded
    return if inRange && markers && recorded then some ⟨r, frame, state⟩ else none

/-- A state before the call must be denoted; otherwise the record is malformed. -/
def parseBefore (j : Json) : Result Native := do
  match ← parseNative j with
  | some n => pure n
  | none => throw s!"the state before the call denotes no model state: {j.compress}"

/-- The model state denoted by the state after the call, if any; every byte of
the region it does not represent must equal the state before. -/
def parseAfter (before : Native) (j : Json) : Result (Option PoolState) := do
  return (← parseNative j).bind fun n =>
    if n.frame = before.frame then some n.state else none

def cellJson (state : PoolState) (cell : Borrow.Cell Account × Nat) : Json :=
  let a := cell.1.value
  Json.mkObj [
    ("key", pubkeyJson a.metadata.address), ("is_signer", toJson a.metadata.signer),
    ("is_writable", toJson a.metadata.writable), ("executable", toJson a.metadata.executable),
    ("owner", pubkeyJson a.owner), ("lamports", toJson a.lamports), ("data_len", toJson a.dataLen),
    ("backing", bytesJson a.backing), ("owner_epoch", toJson a.ownerEpoch),
    ("marker", match leaseByte state ⟨cell.2⟩ with | some b => toJson b | none => Json.null)]

def slotJson : Option Slot → Json
  | none => Json.null
  | some s => Json.arr #[toJson s.cell.cell, modeJson s.mode, toJson s.generation,
      toJson s.view.offset, toJson s.view.length]

/-- A model state, for reports (`model:` lines); not a corpus format. -/
def stateJson (state : PoolState) : Json :=
  Json.mkObj [("cells", Json.arr (state.cells.zipIdx.map (cellJson state)).toArray),
    ("guards", Json.arr (state.slots.map slotJson).toArray)]

def obsStateJson (s : ObsState) : Json :=
  let leaseJson : Solanalib.Runtime.Lease → Json
    | .free => "free"
    | .shared n => Json.mkObj [("shared", toJson n)]
    | .exclusive => "exclusive"
  Json.mkObj [
    ("key", pubkeyJson s.metadata.address), ("is_signer", toJson s.metadata.signer),
    ("owner", pubkeyJson s.account.owner), ("lamports", toJson s.account.lamports),
    ("data_len", toJson s.account.dataLen), ("lease", leaseJson s.account.lease),
    ("data", match s.account.data with | some b => bytesJson b | none => Json.null)]

/-! ## Arguments and results -/

/-- The cell of an instruction account named in a record. -/
def cellArg (before : Native) (i : Nat) : Result Nat :=
  match cellOf before.region i with
  | some c => pure c
  | none => throw s!"instruction account {i} denotes no account"

def handleArg (before : Native) (args : Json) : Result Handle := do
  return ⟨← cellArg before (← natField args "account")⟩

def guardArg (args : Json) : Result Guard := do parseGuard (← field args "guard")

/-- `ProgramError` by its `Debug` name; names the model has no value for are `none`. -/
def programError (j : Json) : Result (Option AccountView.Error) := do
  match ← j.getStr? with
  | "AccountBorrowFailed" => return some .accountBorrowFailed
  | "InvalidRealloc" => return some .invalidRealloc
  | _ => return none

def errorJson : AccountView.Error → Json
  | .accountBorrowFailed => "AccountBorrowFailed"
  | .invalidRealloc => "InvalidRealloc"

/-- `{"ok": v}` or `{"err": e}` where either side may denote no model value. -/
def optExcept {ε α : Type} (error : Json → Result (Option ε)) (value : Json → Result (Option α))
    (j : Json) : Result (Option (Except ε α)) :=
  match j.getObjVal? "ok", j.getObjVal? "err" with
  | .ok v, .error _ => return (← value v).map .ok
  | .error _, .ok e => return (← error e).map .error
  | _, _ => throw s!"expected {"{"}\"ok\": …} or {"{"}\"err\": …}, got {j.compress}"

def some' {α : Type} (parse : Json → Result α) (j : Json) : Result (Option α) := do
  return some (← parse j)

/-! ## Deciding a recorded outcome -/

/-- A registered precondition (`requires`) with its decision, and what it says
for the report. A record outside it fails. -/
structure Pre (S A : Type) where
  requires : S → A → Prop
  dec : ∀ s a, Decidable (requires s a)
  says : S → A → String

def Pre.check {S A : Type} (pre : Pre S A) (s : S) (a : A) : Result Unit :=
  if @decide _ (pre.dec s a) then pure ()
  else throw s!"outside the registered precondition: {pre.says s a}"


/-- A recorded outcome of a family without unwinding or terminal exits; `none`
if no model outcome denotes it (an unwind, or an undenoted value or state). -/
def parseReturned {S V : Type} (value : Json → Result (Option V)) (state : Json → Result (Option S))
    (j : Json) : Result (Option (Outcome S V Empty Empty)) := do
  match ← (← field j "exit").getStr? with
  | "returned" =>
    let v ← value (← field j "result")
    let s ← state (← field j "state")
    return (do return .returned (← v) (← s))
  | "unwound" | "terminated" => return none
  | other => throw s!"unknown exit {other}"

/-- Decide a reference registered as the graph of `model` on a recorded
outcome. `evaluated` is the proof, by `rfl`, that the decided relation is that
graph; an undenoted recording is rejected. -/
def decideReturnsOpt {S A V : Type} [DecidableEq S] [DecidableEq V]
    (relation : S → A → Outcome S V Empty Empty → Prop) (model : S → A → V × S)
    (evaluated : relation = returnsOf model) (before : S) (args : A)
    (recorded : Option (Outcome S V Empty Empty)) (renderValue : V → Json) (renderState : S → Json)
      :
    Verdict :=
  let computed := model before args
  let expected := returnedJson (renderValue computed.1) (renderState computed.2)
  match recorded with
  | some o =>
    have : Decidable (relation before args o) := by
      rw [evaluated]; exact instDecidableReturnsOf model before args o
    ⟨decide (relation before args o), expected⟩
  | none => ⟨false, expected⟩

def both (pool observation : Verdict) : Verdict :=
  ⟨pool.admitted && observation.admitted,
    Json.mkObj [("pool", pool.expected), ("observation", observation.expected)]⟩

end SolanalibTest.Conformance.Library.Families.AccountsV2
