/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AccountsV1.Info
import Solanalib.Specs.Core.AccountInfoResize

/-!
Native projections for the SDK AccountInfo operations. Cell identities, live
guard objects, lease probes and Rc counts use the established AccountsV1
fixture. This extension observes owner storage, every backing byte, both
lengths, all AccountInfo aliases and actual memset calls. The unchanged frame
contains all bytes outside those modeled mutable fields. Guard tombstones
and generations remain ghost data, supplied only by the state before.
-/

set_option autoImplicit false

open Lean (Json)

namespace SolanalibTest.Conformance.Library.Families.SdkAccounts

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AccountInfoSdk
open SolanalibTest.Conformance.Library.Families.AccountsV1

structure Memset where
  cell : Nat
  offset : Nat
  byte : UInt8
  length : Nat
  deriving DecidableEq

structure Native where
  base : Info.Native
  owners : List Solanalib.Runtime.Pubkey
  buffers : List Buffer
  infos : List AccountInfo.Value
  memsets : List Memset

def sparseOf (j : Json) : Result Solanalib.Runtime.Bytes := do
  return (← asBytes (← field j "prefix")) ++ List.replicate (← natField j "zeros") 0

def bufferOf (j : Json) : Result Buffer := do
  return ⟨← asUInt 32 (← field j "original_len"),
    ← asUInt 64 (← field j "serialized_len"), ← sparseOf (← field j "spare")⟩

def memsetOf (j : Json) : Result Memset := do
  return ⟨← natField j "cell", ← natField j "offset",
    UInt8.ofNat (← asUInt 8 (← field j "byte")), ← natField j "length"⟩

def nativeOf (j : Json) : Result Native := do
  return ⟨← Info.nativeOf j, ← (← arrField j "owners").mapM pubkeyOf,
    ← (← arrField j "buffers").mapM bufferOf,
    ← (← arrField j "infos").mapM Info.infoOf,
    ← (← arrField j "memsets").mapM memsetOf⟩

def modelBuffers (buffers : List Buffer) : List (Option Buffer) :=
  buffers.flatMap fun buffer => [none, some buffer]

structure Before where
  native : Native
  args : AccountInfo.Args
  state : State
  reference : Reference

/-- Parse before checking model admission. Source fixture consistency is
checked separately, so malformed model inputs exercise the real precondition. -/
def beforeOf (state args : Json) : Result Before := do
  let native ← nativeOf state
  let arguments ← Info.argsOf args
  let ghost ← field state "ghost"
  let generations ← (← arrField ghost "generations").mapM (·.getNat?)
  let slots ← slotsOf native.base.guards (← natField ghost "slots") generations
  let cells := native.base.cells.map fun c => (⟨c.content, arguments.profile.policy⟩ : Borrow.Cell
    AccountInfo.Content)
  return ⟨native, arguments, ⟨⟨cells, slots⟩, native.owners, modelBuffers native.buffers⟩,
    ⟨← natField args "reference"⟩⟩

structure FrameHeader where
  key : Solanalib.Runtime.Bytes
  flags : Solanalib.Runtime.Bytes
  originalLen : Nat

/-- The frame retains the marker, flags, original length, key, alignment and
rent epoch. It removes owner, lamports, serialized length and complete backing.
Duplicate entries keep their eight bytes and share the earlier identities. -/
def headersOf : Nat → Solanalib.Runtime.Bytes → Option (List FrameHeader)
  | 0, _ => some []
  | _ + 1, [] => none
  | count + 1, marker :: rest =>
    if marker = 0xff then
      let original := Solanalib.Runtime.leNat ((rest.drop 3).take 4)
      let padding := (8 - original % 8) % 8
      (headersOf count (rest.drop (39 + padding + 8))).map
        (⟨(rest.drop 7).take 32, rest.take 3, original⟩ :: ·)
    else headersOf count (rest.drop 7)

def infoFits (native : Native) (headers : List FrameHeader) (info : AccountInfo.Value) : Bool :=
  let k := info.ownerRef.id
  match headers[k]?, native.owners[k]? with
  | some header, some owner =>
    info.lamports.cell == 2 * k && info.data.cell == 2 * k + 1 &&
    decide (info.key.bytes = header.key ∧ info.owner = owner) &&
    info.isSigner == Info.flagByte header.flags[0]? &&
    info.isWritable == Info.flagByte header.flags[1]? &&
    info.executable == Info.flagByte header.flags[2]?
  | _, _ => false

def validateBefore (b : Before) : Result Unit := do
  unless b.args.profile.wordBits = 64 do throw "native usize has 64 bits"
  unless b.native.infos[b.reference.id]? = some b.args.info do
    throw "argument is not the selected existing AccountInfo reference"
  unless b.native.base.guards.all (fun g => g.cell < b.state.borrow.cells.length) do
    throw "guard addresses an unknown cell"
  unless Info.leasesFit b.native.base b.state.borrow do
    throw "probed leases disagree with held guards"
  unless b.native.base.rc.length = b.state.borrow.cells.length do
    throw "expected one Rc count per represented cell"
  unless b.native.base.cells.length = 2 * b.native.buffers.length ∧
      b.native.owners.length = b.native.buffers.length do
    throw "owner/buffer stores disagree with independent cell identities"
  let count := Solanalib.Runtime.leNat (b.native.base.frame.take 8)
  unless count = b.native.infos.length do throw "AccountInfo count disagrees with the frame"
  let some headers := headersOf count (b.native.base.frame.drop 8)
    | throw "invalid loader frame"
  unless headers.length = b.native.buffers.length do
    throw "unique header count disagrees with buffers"
  unless (headers.zip b.native.buffers).all (fun (h, buffer) => h.originalLen ==
    buffer.originalLen) do
    throw "original-length words disagree with the immutable frame"
  unless b.native.infos.all (infoFits b.native headers) do
    throw "AccountInfo metadata or reference identities disagree with storage"
  unless b.native.memsets.isEmpty do throw "call trace was not reset before recording"

/-- Read current owner storage through the same retained reference. -/
def currentInfo (state : State) (info : AccountInfo.Value) : AccountInfo.Value :=
  { info with owner := (state.owner info.ownerRef).getD info.owner }

def stateFits (before : Native) (observed : Native) (state : State)
    (counts : List Nat) (memsets : List Memset := []) : Bool :=
  Info.stateFits observed.base state.borrow &&
  decide (observed.owners = state.owners) &&
  decide (modelBuffers observed.buffers = state.buffers) &&
  decide (observed.infos = before.infos.map (currentInfo state)) &&
  observed.base.rc == counts && Info.frameKept before.base observed.base &&
  decide (observed.memsets = memsets)

def borrowFits (before : Before) (observed : Native) (state : AccountInfo.State) : Bool :=
  stateFits before.native observed { before.state with borrow := state } before.native.base.rc

def stateJson (state : State) : Json := Json.mkObj [
  ("borrow", Info.stateJson state.borrow),
  ("owners", Json.arr (state.owners.map pubkeyJson).toArray),
  ("buffers", Json.arr (state.buffers.map fun buffer => match buffer with
    | none => Json.null
    | some b => Json.mkObj [("original_len", b.originalLen), ("serialized_len", b.serializedLen),
        ("spare", bytesJson b.spare)]).toArray)]

def expectedMemsets (state : State) (args : ResizeArgs) : List Memset :=
  match prepareResize state args with
  | .zero _ offset length _ => [⟨args.info.data.cell, offset, 0, length⟩]
  | _ => []

instance lamportsCellDecidable (state : AccountInfo.State) (handle : Borrow.Handle) :
    Decidable (∃ amount policy, state.lookupCell handle = some ⟨.lamports amount, policy⟩) :=
  match state.lookupCell handle with
  | some ⟨.lamports value, policy⟩ => isTrue ⟨value, policy, rfl⟩
  | some ⟨.data _, _⟩ => isFalse fun ⟨_, _, present⟩ => by cases present
  | none => isFalse fun ⟨_, _, present⟩ => by cases present

instance lamportsBorrowReadyDecidable (state : AccountInfo.State) (info : AccountInfo.Value) :
    Decidable (LamportsBorrowReady state info) := by
  unfold LamportsBorrowReady
  infer_instance

theorem resizeReady_iff (state : State) (args : ResizeArgs) :
    ResizeReady state args ↔ state.borrow.Valid ∧
      match state.borrow.lookupCell args.info.data with
      | none | some ⟨.lamports _, _⟩ => False
      | some ⟨.data bytes, _⟩ =>
        (state.borrow.exclusiveCount args.info.data = 0 →
          state.borrow.sharedCount args.info.data = 0 → args.newLen ≠ bytes.length →
          ∃ buffer, state.buffer args.info.data = some buffer ∧
            (args.newLen - buffer.originalLen ≤ 10240 →
              args.newLen ≤ bytes.length + buffer.spare.length)) := by
  unfold ResizeReady
  cases found : state.borrow.lookupCell args.info.data with
  | none => simp
  | some cell =>
    cases cell with
    | mk content policy => cases content <;> simp

instance resizeReadyDecidable (state : State) (args : ResizeArgs) :
    Decidable (ResizeReady state args) := by
  cases found : state.borrow.lookupCell args.info.data with
  | none =>
    have equivalence := resizeReady_iff state args
    simp only [found] at equivalence
    exact decidable_of_iff _ equivalence.symm
  | some cell =>
    cases cell with
    | mk content policy =>
      cases content <;>
        (have equivalence := resizeReady_iff state args
         simp only [found] at equivalence
         exact decidable_of_iff _ equivalence.symm)

def programErrorOf (j : Json) : Result ProgramError.Value := do
  match ← j.getStr? with
  | "AccountBorrowFailed" => return .accountBorrowFailed
  | "InvalidRealloc" => return .invalidRealloc
  | name => throw s!"unexpected program error {name}"

def programErrorJson : ProgramError.Value → Json
  | .accountBorrowFailed => "AccountBorrowFailed"
  | .invalidRealloc => "InvalidRealloc"
  | other => Json.str (toString (repr other))

end SolanalibTest.Conformance.Library.Families.SdkAccounts
