/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AccountsV1.Common
import SolanalibTest.Conformance.Library.Families.AccountsV1.Requires
import Solanalib.Specs.SolanaAccountInfo

/-!
# solana-account-info 3.1.1 checkers

Corpus `solana_account_info`, written by `rust/accounts-v1/src/info.rs`
over input regions that the `deserialize` of solana-program-entrypoint 3.1.1 turns
into AccountInfos (`AccountInfo::new`, and `AccountInfo::clone` for a
duplicate).

**Projection.** The model state `Borrow.State Content View` is read from the
record as follows.

* Cells `2k` and `2k + 1` are the lamports and data `RefCell`s of the `k`-th
  non-duplicate account, identified by their `Rc` (a duplicate shares them).
  The contents are the current `u64` and bytes. The policy is that of the profile
  (`Profile.policy`, `isize::MAX` shares at 64 bits).
* Slot `i` is the guard object `i` of the driver (creation order), live while the
  driver holds it, on the cell its pointer addresses, with the mode of its type;
  its view is `whole` (a `Ref<&mut [u8]>` derefs to the whole cell).
* The lease kind of each cell (free, shared, exclusive), probed natively, must be
  the kind of the lease observation of the model in both states; the shared count
  itself is the number of live slots.
* Ghost components come from the state before: the slot count and the
  generations. The state after is compared without them, so the tombstone the temporary guard of a
  getter leaves is not compared.
* `args.info` is the AccountInfo value: key and owner bytes, the two cell
  handles (by `Rc` identity), the owner reference (by address: the account
  whose owner field it addresses), `_unused` and the flags. `args.profile` is
  the word size and panic strategy of the target (64 bits, unwinding).

The derived `Clone` family is decided at the index whose state adds the `Rc` strong count of each
cell to the borrow world and whose Rc clone increments the
count of its cell; `clone_observation` is decided on the same records.
-/

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.AccountsV1.Info

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AccountInfo
open SolanalibTest.Conformance.Library.Families.AccountsV1

abbrev State := Solanalib.Specs.Core.AccountInfo.State

/-! ## Native state -/

inductive LeaseKind where
  | free
  | shared
  | exclusive
  deriving DecidableEq

def leaseKind : Solanalib.Runtime.Lease → LeaseKind
  | .free => .free
  | .shared _ => .shared
  | .exclusive => .exclusive

def leaseKindOf (s : String) : Result LeaseKind :=
  match s with
  | "free" => pure .free
  | "shared" => pure .shared
  | "exclusive" => pure .exclusive
  | other => throw s!"unknown lease {other}"

def leaseKindJson : LeaseKind → Json
  | .free => "free"
  | .shared => "shared"
  | .exclusive => "exclusive"

structure NativeCell where
  content : Content
  lease : LeaseKind

structure Native where
  cells : List NativeCell
  rc : List Nat
  guards : List (GuardEntry View)
  /-- The region outside the lamports fields and the current data. -/
  frame : Solanalib.Runtime.Bytes

def viewOf (j : Json) : Result View :=
  match j with
  | .str "whole" => pure .whole
  | other => do pure (.bytesRange (← natField other "offset") (← natField other "length"))

def viewJson : View → Json
  | .whole => "whole"
  | .bytesRange o l => Json.mkObj [("offset", o), ("length", l)]

def cellOf (j : Json) : Result NativeCell := do
  let lease ← leaseKindOf (← strField j "lease")
  match j.getObjVal? "lamports", j.getObjVal? "data" with
  | .ok v, .error _ => return ⟨.lamports (UInt64.ofNat (← asUInt 64 v)), lease⟩
  | .error _, .ok d => return ⟨.data (← asBytes d), lease⟩
  | _, _ => throw s!"a cell holds lamports or data: {j.compress}"

def contentJson : Content → Json
  | .lamports v => Json.mkObj [("lamports", v.toNat)]
  | .data b => Json.mkObj [("data", bytesJson b)]

def nativeOf (j : Json) : Result Native := do
  let cells ← (← arrField j "cells").mapM cellOf
  let rc ← (← arrField j "rc").mapM (·.getNat?)
  let guards ← guardsOf viewOf j
  return ⟨cells, rc, guards, ← asBytes (← field j "frame")⟩

def leasesFit (n : Native) (s : State) : Bool :=
  n.cells.zipIdx.all fun (c, k) => c.lease == leaseKind (s.lease ⟨k⟩)

/-- The recorded native state is the projection of the model state. -/
def stateFits (n : Native) (s : State) : Bool :=
  n.cells.length == s.cells.length &&
  (n.cells.zip s.cells).all (fun (c, m) => decide (c.content = m.value)) &&
  leasesFit n s && guardsMatch n.guards [] s

/-- A call keeps the region outside the projection. -/
def frameKept (before after : Native) : Bool := decide (before.frame = after.frame)

/-- A call other than `clone` keeps every `Rc` strong count. -/
def rcKept (before after : Native) : Bool := before.rc == after.rc

/-- The header fields an AccountInfo copies, read back from the frame: key,
owner and the three flag bytes of each non-duplicate account, in order. The
frame is the region without the lamports fields and the current data, so after
the 88-byte header (less lamports) it holds the rest of the data area
(`data_len - current length` plus the 10 KiB reserve and padding to 8) and the
rent epoch; a duplicate entry is 8 bytes. -/
structure FrameAccount where
  key : Solanalib.Runtime.Bytes
  owner : Solanalib.Runtime.Bytes
  flags : Solanalib.Runtime.Bytes

def frameAccounts : Nat → Solanalib.Runtime.Bytes → List Nat → Option (List FrameAccount)
  | 0, _, _ => some []
  | _ + 1, [], _ => none
  | n + 1, marker :: rest, lens =>
    if marker = 0xff then
      match lens with
      | [] => none
      | current :: lens =>
        let dataLen := Solanalib.Runtime.leNat ((rest.drop 71).take 8)
        let pad := (8 - dataLen % 8) % 8
        let skip := (dataLen - current) + 10240 + pad + 8
        (frameAccounts n ((rest.drop 79).drop skip) lens).map
          (⟨(rest.drop 7).take 32, (rest.drop 39).take 32, rest.take 3⟩ :: ·)
    else frameAccounts n (rest.drop 7) lens

def flagByte (b : Option UInt8) : Bool := b.getD 0 != 0

/-- `args.info` is the AccountInfo of one account of the region: its two cells
are those of that account, its owner reference names it, and its key, owner and flags
are the header bytes of that account. -/
def infoFits (frame : Solanalib.Runtime.Bytes) (cells : List NativeCell) (info : Value) : Bool :=
  let lens := (List.range (cells.length / 2)).map fun k =>
    match (cells[2 * k + 1]?).map NativeCell.content with
    | some (.data bytes) => bytes.length
    | _ => 0
  match frameAccounts (Solanalib.Runtime.leNat (frame.take 8)) (frame.drop 8) lens with
  | none => false
  | some accounts =>
    let k := info.lamports.cell / 2
    match accounts[k]? with
    | none => false
    | some a =>
      info.lamports.cell % 2 == 0 && info.data.cell == info.lamports.cell + 1 &&
      info.ownerRef.id == k && accounts.length * 2 == cells.length &&
      decide (a.key = info.key.bytes ∧ a.owner = info.owner.bytes) &&
      info.isSigner == flagByte a.flags[0]? && info.isWritable == flagByte a.flags[1]? &&
      info.executable == flagByte a.flags[2]?

def stateJson (s : State) : Json := Json.mkObj [
  ("cells", Json.arr (s.cells.zipIdx.map fun (c, k) =>
    Json.mkObj [("content", contentJson c.value), ("lease", leaseKindJson (leaseKind (s.lease
      ⟨k⟩)))]).toArray),
  ("guards", liveSlotsJson viewJson s)]

/-! ## Arguments and the state before -/

def infoOf (j : Json) : Result Value := do
  return {
    key := ← pubkeyOf (← field j "key")
    lamports := ⟨← natField j "lamports"⟩
    data := ⟨← natField j "data"⟩
    owner := ← pubkeyOf (← field j "owner")
    unused := UInt64.ofNat (← asUInt 64 (← field j "unused"))
    isSigner := ← boolField j "is_signer"
    isWritable := ← boolField j "is_writable"
    executable := ← boolField j "executable"
    ownerRef := ⟨← natField j "owner_ref"⟩ }

def infoJson (v : Value) : Json := Json.mkObj [
  ("key", pubkeyJson v.key), ("lamports", v.lamports.cell), ("data", v.data.cell),
  ("owner", pubkeyJson v.owner), ("unused", v.unused.toNat), ("is_signer", v.isSigner),
  ("is_writable", v.isWritable), ("executable", v.executable), ("owner_ref", v.ownerRef.id)]

def argsOf (j : Json) : Result Args := do
  let p ← field j "profile"
  return ⟨⟨← natField p "word_bits", ← boolField p "aborts"⟩, ← infoOf (← field j "info")⟩

structure Before where
  native : Native
  args : Args
  state : State

def beforeOf (state args : Json) : Result Before := do
  let n ← nativeOf state
  let a ← argsOf args
  let g ← field state "ghost"
  let cells := n.cells.map fun c => (⟨c.content, a.profile.policy⟩ : Borrow.Cell Content)
  let gens ← (← arrField g "generations").mapM (·.getNat?)
  let slots ← slotsOf n.guards (← natField g "slots") gens
  let s : State := ⟨cells, slots⟩
  unless n.guards.all (fun x => x.cell < cells.length) do throw "guard on an unknown cell"
  unless a.info.lamports.cell < cells.length ∧ a.info.data.cell < cells.length do
    throw "the AccountInfo names unknown cells"
  unless n.rc.length = cells.length do throw "one strong count per cell"
  unless a.profile.wordBits = 64 do throw s!"the host usize has 64 bits, not \
    {a.profile.wordBits}"
  unless infoFits n.frame n.cells a.info do
    throw "the AccountInfo cells, owner reference, key, owner or flags do not belong to one \
      account"
  unless leasesFit n s do throw "probed leases disagree with the guards held before the \
    call"
  return ⟨n, a, s⟩

/-! ## Getters: relations with panics, decided through their graph -/

/-- The single outcome of the getter reference, if the model path is not malformed. -/
def observeComputed (o : Observation) (state : State) (args : Args) :
    Option (Outcome State Nat Panic Panic) :=
  match observe o state args.info with
  | (.malformed, _) => none
  | (.value v, after) => some (.returned v after)
  | (.borrowFailed, after) =>
    some (if args.profile.aborts then .terminated .borrowFailed else .unwound .borrowFailed after)

theorem observe_evaluated (o : Observation) (state : State) (args : Args)
    (out : Outcome State Nat Panic Panic) :
    observeReference o state args out ↔ observeComputed o state args = some out := by
  unfold observeReference observePost observeComputed
  rcases observe o state args.info with ⟨r, after⟩
  cases r with
  | value v => simp only [Option.some.injEq]; exact eq_comm
  | malformed => simp
  | borrowFailed =>
    cases args.profile.aborts <;> simp only [Option.some.injEq] <;> exact eq_comm

/-- The RefCell borrow panic of this toolchain. -/
def panicOf (reason : String) (p : Panic) : Bool :=
  match p with
  | .borrowFailed => reason == "RefCell already mutably borrowed"

def renderOutcome {S V U T : Type} (value : V → Json) (state : S → Json) : Outcome S V U T → Json
  | .returned v s => Json.mkObj [("exit", "returned"), ("result", value v), ("state", state s)]
  | .unwound _ s => Json.mkObj [("exit", "unwound"), ("reason", "borrowFailed"), ("state", state s)]
  | .terminated _ => Json.mkObj [("exit", "terminated"), ("reason", "borrowFailed")]

/-! ### The registered preconditions

`ObservationReady`: the cell of the getter exists and holds its type.
`DataBorrowReady`: a protocol-valid world (`Borrow.State.Valid`) and a data cell. -/

theorem observationReady_iff (o : Observation) (state : State) (info : Value) :
    ObservationReady o state info ↔
      ∃ cell, state.lookupCell (o.handle info) = some cell ∧ ∃ value, o.project cell.value = some
        value :=
  ⟨fun ⟨cell, value, present, typed⟩ => ⟨cell, present, value, typed⟩,
    fun ⟨cell, present, value, typed⟩ => ⟨cell, value, present, typed⟩⟩

instance observationReadyDecidable (o : Observation) (state : State) (info : Value) :
    Decidable (ObservationReady o state info) :=
  decidable_of_iff _ (observationReady_iff o state info).symm

instance dataCellDecidable (state : State) (h : Borrow.Handle) :
    Decidable (∃ bytes policy, state.lookupCell h = some ⟨.data bytes, policy⟩) :=
  match state.lookupCell h with
  | some ⟨.data bytes, policy⟩ => isTrue ⟨bytes, policy, rfl⟩
  | some ⟨.lamports _, _⟩ => isFalse fun ⟨_, _, found⟩ => by cases found
  | none => isFalse fun ⟨_, _, found⟩ => by cases found

instance dataBorrowReadyDecidable (state : State) (info : Value) :
    Decidable (DataBorrowReady state info) := by
  unfold DataBorrowReady; infer_instance

def getterCheck (o : Observation) (contract : Solanalib.Contracts.Model State Args Nat Panic Panic)
    (same : ∀ s a, contract.requires s a = ObservationReady o s a.info)
    (relation : State → Args → Outcome State Nat Panic Panic → Prop)
    (evaluated : relation = observeReference o) (c : Case) : Result Verdict := do
  let b ← beforeOf c.state c.args
  have : Decidable (contract.requires b.state b.args) := by rw [same]; infer_instance
  unless decide (contract.requires b.state b.args) do
    throw "the input is outside the registered precondition"
  let recorded ← parseRecorded (fun j => j.getNat?) nativeOf c.outcome
  let fits := matchOutcome (fun r (v : Nat) _ => r == v)
    (fun n s => stateFits n s && frameKept b.native n && rcKept b.native n) panicOf panicOf recorded
  return admits (relation b.state b.args) (observeComputed o b.state b.args)
    (fun out => by rw [evaluated]; exact observe_evaluated o b.state b.args out) fits
    (renderOutcome (fun (v : Nat) => v) stateJson)

def lamportsChecker : Checker where
  function := "solana_account_info::AccountInfo::<'a>::lamports"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.lamports_reference"
  check := getterCheck .lamports Solanalib.Specs.SolanaAccountInfo.AccountInfo.lamports_contract
    (fun _ _ => rfl)
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.lamports_reference rfl
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.lamports_reference"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.lamports_reference"]

def dataLenChecker : Checker where
  function := "solana_account_info::AccountInfo::<'a>::data_len"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_len_reference"
  check := getterCheck .dataLen Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_len_contract
    (fun _ _ => rfl)
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_len_reference rfl
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_len_reference"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.data_len_reference"]

/-! ## Checked data borrows: total references -/

def programErrorOf (s : String) : Result ProgramError.Value :=
  match s with
  | "AccountBorrowFailed" => pure .accountBorrowFailed
  | other => throw s!"unexpected ProgramError {other}"

def borrowCheck (contract : Solanalib.Contracts.Model State Args (Except ProgramError.Value
  Borrow.Guard))
    (same : ∀ s a, contract.requires s a = DataBorrowReady s a.info)
    (relation : State → Args → Outcome State (Except ProgramError.Value Borrow.Guard) Empty Empty →
      Prop)
    (model : State → Args → Except ProgramError.Value Borrow.Guard × State)
    (evaluated : relation = returnsOf model) (c : Case) : Result Verdict := do
  let b ← beforeOf c.state c.args
  have : Decidable (contract.requires b.state b.args) := by rw [same]; infer_instance
  unless decide (contract.requires b.state b.args) do
    throw "the input is outside the registered precondition"
  let recorded ← parseRecorded
    (asExcept (fun e => do programErrorOf (← e.getStr?)) (fun j => natField j "guard")) nativeOf
      c.outcome
  let fits := matchOutcome (U := Empty) (T := Empty)
    (fun r v _ => match r, v with
      | .ok id, .ok g => id == g.id
      | .error e, .error e' => decide (e = e')
      | _, _ => false)
    (fun n s => stateFits n s && frameKept b.native n && rcKept b.native n) noMatch noMatch recorded
  return admits (relation b.state b.args) _
    (fun out => by rw [evaluated]; exact returnsOf_graph model b.state b.args out) fits
    (renderOutcome (exceptJson (fun e => Json.str (toString (repr e)))
      (fun g => Json.mkObj [("guard", g.id), ("generation", g.generation)])) stateJson)

def tryBorrowDataChecker : Checker where
  function := "solana_account_info::AccountInfo::<'a>::try_borrow_data"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_data_reference"
  check := borrowCheck Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_data_contract (fun
    _ _ => rfl)
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_data_reference tryBorrowData rfl
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_data_reference"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_data_refere\
    nce"]

def tryBorrowMutDataChecker : Checker where
  function := "solana_account_info::AccountInfo::<'a>::try_borrow_mut_data"
  generics := []
  reference := "Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_mut_data_reference"
  check := borrowCheck Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_mut_data_contract
    (fun _ _ => rfl)
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_mut_data_reference tryBorrowMutData rfl
  decides := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_mut_data_reference"]
  decidesRequires := ["Solanalib.Specs.SolanaAccountInfo.AccountInfo.try_borrow_mut_data_re\
    ference"]

/-! ## Derived `Clone`: the Rc family and the value observation -/

/-- Add `delta` to the strong count of the `Rc` of a cell. -/
def bump (counts : List Nat) (h : Borrow.Handle) : List Nat := counts.modify h.cell (· + 1)
def unbump (counts : List Nat) (h : Borrow.Handle) : List Nat := counts.modify h.cell (· - 1)

/-- The test index of the clone family: the borrow world with the `Rc` strong count of each cell;
`Rc::clone` increments, `Rc` drop decrements the count of
its cell; no terminal exit. -/
def rcOps : AccountInfoRc.Ops (State × List Nat) Empty where
  cloneRc := Callback.ofFunction fun w (_, h) => .returned () (w.1, bump w.2 h)
  dropRc := Callback.ofFunction fun w (_, h) => .returned () (w.1, unbump w.2 h)

def cloneIndex : AccountInfoRc.Types := ⟨State × List Nat, Empty, rcOps⟩

/-- At this index the registered clone reference is the graph of: lamports Rc
clone, then data Rc clone, returning the same value. -/
theorem clone_evaluated (before : State × List Nat) (info : Value)
    (out : Outcome (State × List Nat) Value Empty Empty) :
    Solanalib.Specs.SolanaAccountInfo.AccountInfo.clone_reference cloneIndex before info out ↔
      some (Outcome.returned (AccountInfo.clone info)
        (before.1, bump (bump before.2 info.lamports) info.data)) = some out := by
  simp only [Solanalib.Specs.SolanaAccountInfo.AccountInfo.clone_reference, AccountInfoRc.cloneRun,
    AccountInfoRc.cloneCall, cloneIndex, rcOps, Callback.bind, Callback.map, Callback.ofFunction,
    Option.some.injEq]
  constructor
  · rintro ⟨i, rfl, i2, rfl, rfl⟩
    rfl
  · rintro rfl
    exact ⟨_, rfl, _, rfl, rfl⟩

/-- The Rc family at `cloneIndex`, with the strong counts. -/
def cloneFamilyCheck (c : Case) : Result Verdict := do
  let b ← beforeOf c.state c.args
  let recorded ← parseRecorded infoOf nativeOf c.outcome
  let fits := matchOutcome (U := Empty) (T := Empty) (fun r v (_ : State × List Nat) => decide (r =
    v))
    (fun n (w : State × List Nat) => stateFits n w.1 && n.rc == w.2 && frameKept b.native n)
    noMatch noMatch recorded
  return admits
    (Solanalib.Specs.SolanaAccountInfo.AccountInfo.clone_reference cloneIndex (b.state,
      b.native.rc) b.args.info) _
    (clone_evaluated (b.state, b.native.rc) b.args.info) fits
    (renderOutcome infoJson fun (w : State × List Nat) => Json.mkObj [("world", stateJson w.1),
      ("rc", toJson w.2)])

/-- The value observation, without the Rc lifecycle. -/
def cloneObservationCheck (c : Case) : Result Verdict := do
  let b ← beforeOf c.state c.args
  let recorded ← parseRecorded infoOf nativeOf c.outcome
  let fits := matchOutcome (U := Empty) (T := Empty) (fun r v (_ : State) => decide (r = v))
    (fun n s => stateFits n s && frameKept b.native n) noMatch noMatch recorded
  return admits (Solanalib.Specs.SolanaAccountInfo.AccountInfo.clone_observation_reference b.state
    b.args) _
    (fun out => returnsOf_graph cloneReference b.state b.args out) fits (renderOutcome infoJson
      stateJson)

def cloneModels : List (String × (Case → Result Verdict)) := [
  ("Solanalib.Specs.SolanaAccountInfo.AccountInfo.clone_reference", cloneFamilyCheck),
  ("Solanalib.Specs.SolanaAccountInfo.AccountInfo.clone_observation_reference",
    cloneObservationCheck)]

def cloneCheck (c : Case) : Result Verdict := do
  let family ← cloneFamilyCheck c
  let observation ← cloneObservationCheck c
  return ⟨family.admitted && observation.admitted,
    Json.mkObj [("clone_reference", family.expected), ("clone_observation_reference",
      observation.expected)]⟩

def cloneChecker : Checker where
  function := "<solana_account_info::AccountInfo<'a> as core::clone::Clone>::clone"
  generics := []
  reference :=
    "Solanalib.Specs.SolanaAccountInfo.AccountInfo.clone_reference + \
      Solanalib.Specs.SolanaAccountInfo.AccountInfo.clone_observation_reference"
  check := cloneCheck
  decides := cloneModels.map (·.1)
  checkModels := some (perModel cloneModels)

def checkers : List Checker :=
  [lamportsChecker, dataLenChecker, tryBorrowDataChecker, tryBorrowMutDataChecker, cloneChecker]

end SolanalibTest.Conformance.Library.Families.AccountsV1.Info
