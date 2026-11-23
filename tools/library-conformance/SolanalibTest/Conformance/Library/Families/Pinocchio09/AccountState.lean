/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Pinocchio09.Common
import SolanalibTest.Conformance.Library.Runtime

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.Pinocchio09

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.PinocchioAccount
open AccountsV1

structure Before where
  native : Json
  state : State
  aux : Aux
  aliases : List Handle

def fieldOf (s : String) : Result Field :=
  match s with
  | "data" => pure .data
  | "lamports" => pure .lamports
  | other => throw s!"unknown account field {other}"

def fieldName : Field → String
  | .data => "data"
  | .lamports => "lamports"

def signedDelta (word : Nat) : Int :=
  if word < 2^31 then word else (word : Int) - 2^32

def rawDelta (delta : Int) : Nat := (delta % (2^32 : Int)).toNat

def slotOf (state : State) (j : Json) : Result (Option (Borrow.Slot View)) := do
  if j == Json.null then return none
  let field ← fieldOf (← strField j "field")
  let handle := state.field ⟨0⟩ field
  let offset ← natField j "offset"
  let length ← natField j "len"
  let wholeLength := match field with | .data => (state.data ⟨0⟩).dataLen | .lamports => 8
  let view := if offset = 0 ∧ length = wholeLength then View.whole else .bytes offset length
  return some ⟨handle, ← modeOf (← strField j "mode"), ← natField j "generation", view⟩

/-- One physical unique account and its duplicate, exactly as the driver
allocates them. The input reader verifies every native integer and spare byte.
The aliases point into one state; no duplicate allocation or lease reset occurs. -/
def beforeOf (j : Json) : Result Before := do
  let input ← field j "input"
  let _ ← SolanalibTest.Conformance.Library.Runtime.region input
  let entries ← arrField input "accounts"
  let account ← match entries with
    | [account, duplicate] => do
      unless (← natField duplicate "duplicate_of") = 0 do throw "duplicate must alias \
        account 0"
      pure account
    | _ => throw "expected one unique account and one duplicate"
  let data ← asBytes (← field account "data")
  let spare ← asBytes (← field account "spare")
  let length ← natField account "data_len"
  let delta := signedDelta (← asUInt 32 (← field account "padding"))
  unless data.length = length do throw "data length differs from the recorded bytes"
  let item : Input := {
    key := ← pubkeyOf (← field account "key")
    owner := ← pubkeyOf (← field account "owner")
    isSigner := UInt8.ofNat (← asUInt 8 (← field account "is_signer"))
    isWritable := UInt8.ofNat (← asUInt 8 (← field account "is_writable"))
    executable := UInt8.ofNat (← asUInt 8 (← field account "executable"))
    lamports := UInt64.ofNat (← asUInt 64 (← field account "lamports"))
    data := ⟨data ++ spare, length, ((length : Int) - delta).toNat, delta⟩ }
  let state := (State.empty.insert item).2
  let slots ← (← arrField j "guards").mapM (slotOf state)
  let state : State := ({ state.1 with slots := slots }, state.2)
  unless decide state.1.Valid do throw "invalid guard ledger"
  unless (← natField account "marker") = borrowByte state ⟨0⟩ do
    throw "guard ledger disagrees with the account borrow byte"
  return ⟨j, state, ← auxOf j, [⟨0⟩, ⟨0⟩]⟩

def Before.handle (before : Before) (j : Json) : Result Handle := do
  let index ← natField j "account"
  return before.aliases.getD index ⟨index⟩

def viewRange (state : State) (slot : Borrow.Slot View) : Nat × Nat :=
  match slot.view with
  | .bytes offset length => (offset, length)
  | .whole => (0, match (state.1.lookupCell slot.cell).map Borrow.Cell.value with
      | some (.data data) => data.dataLen
      | some (.lamports _) => 8
      | none => 0)

def slotJson (state : State) (slot : Borrow.Slot View) : Json :=
  let range := viewRange state slot
  Json.mkObj [("field", toJson (if slot.cell = state.field ⟨0⟩ .data then "data" else
    "lamports")),
    ("mode", modeJson slot.mode), ("generation", toJson slot.generation),
    ("offset", toJson range.1), ("len", toJson range.2)]

/-- `consumed` is fixed by the interpreted call, never supplied by an output
record. It hides the object consumed by a map while its lease remains in the
model and therefore remains visible in the borrow byte. -/
def stateJson (before : Before) (state : State) (aux : Aux) (consumed : List Nat := []) : Json :=
  let input := before.native.getObjValD "input"
  let entries := (input.getObjValAs? (Array Json) "accounts").toOption.getD #[]
  let old := entries[0]?.getD Json.null
  let header := state.header ⟨0⟩
  let data := state.data ⟨0⟩
  let spare := data.backing.drop data.dataLen
  let nonzero := (spare.findIdx? (· != 0)).map (· + data.dataLen)
  let current := puts old [
    ("marker", toJson (borrowByte state ⟨0⟩)),
    ("is_signer", toJson header.isSigner.toNat), ("is_writable", toJson header.isWritable.toNat),
    ("executable", toJson header.executable.toNat), ("key", pubkeyJson header.key),
    ("owner", pubkeyJson header.owner), ("lamports", toJson (state.lamports ⟨0⟩).toNat),
    ("padding", toJson (rawDelta data.resizeDelta)), ("data_len", toJson data.dataLen),
    ("data", bytesJson data.bytes), ("spare", bytesJson spare),
    ("spare_nonzero_at", match nonzero with | some n => toJson n | none => Json.null)]
  let guards := state.1.slots.zipIdx |>.map fun (slot, index) =>
    if consumed.contains index then Json.null else slot.map (slotJson state) |>.getD Json.null
  withAux (puts before.native [("input", put input "accounts" (.arr (entries.set! 0 current))),
    ("guards", arrayJson guards)]) aux

abbrev World := State × Aux

abbrev guardProfile : GuardProfile := ⟨View, List Header × Aux⟩
def guardWorld (before : Before) : guardProfile.World := (before.state.1, before.state.2,
  before.aux)
def guardState (world : guardProfile.World) : State := (world.1, world.2.1)
def guardWorldJson (before : Before) (world : guardProfile.World) (consumed : List Nat := []) :
  Json :=
  stateJson before (guardState world) world.2.2 consumed

def referenceJson (reference : Reference) (world : guardProfile.World) : Json :=
  let state := guardState world
  match world.1.resolve reference.guard with
  | none => Json.mkObj [("unresolved", guardJson reference.guard)]
  | some slot =>
    let range := viewRange state slot
    let bytes := match (state.1.lookupCell slot.cell).map Borrow.Cell.value with
      | some (.data data) => data.backing.drop range.1 |>.take range.2
      | some (.lamports balance) => Solanalib.Runtime.leBytes 8 balance.toNat
      | none => []
    puts (guardJson reference.guard) [("offset", toJson range.1), ("len", toJson range.2),
      ("writable", toJson reference.writable), ("bytes", bytesJson bytes)]

end SolanalibTest.Conformance.Library.Families.Pinocchio09
