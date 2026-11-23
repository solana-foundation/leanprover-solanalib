/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Runtime.Common
import Solanalib.Specs.SolanaProgramEntrypoint.EntryDeserialize
import Solanalib.Specs.Pinocchio.EntryDeserialize

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.EntryDeserialize

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.EntryDeserialize

def nat (j : Json) : Result Nat := asUInt 64 j
def natJson (n : Nat) : Json := toJson n
def boolJson (b : Bool) : Json := toJson b

def byteArray (j : Json) : Result Solanalib.Runtime.Pubkey := do
  let bytes ← asBytes j
  if h : bytes.length = 32 then pure ⟨bytes, h⟩
  else throw "public key must have exactly 32 bytes"

def array {α : Type} (read : Json → Result α) (j : Json) : Result (List α) := do
  (← j.getArr?).toList.mapM read

def nullableNat (j : Json) : Result (Option Nat) :=
  match j with
  | .null => pure none
  | _ => some <$> nat j

def views (j : Json) : Result Views := do
  pure ⟨← nat (← field j "program_offset"), ← byteArray (← field j "program_id"),
    ← nat (← field j "instruction_offset"), ← asBytes (← field j "instruction_data")⟩

def viewsJson (value : Views) : Json := Json.mkObj [
  ("program_offset", natJson value.programOffset), ("program_id", bytesJson value.programId.bytes),
  ("instruction_offset", natJson value.instructionOffset),
  ("instruction_data", bytesJson value.instructionData)]

def stateBytes (j : Json) : Result Solanalib.Runtime.Bytes := do asBytes (← field j "bytes")

/-- The shared recorder emits both raw bytes and a decoded account-region readback. Every
field of that readback must agree; otherwise a corrupted redundant observation could pass. -/
def regionAccountJson (slot : Slot) : Json :=
  match slot.duplicate with
  | some earlier => Json.mkObj [("duplicate_of", natJson earlier),
      ("padding", bytesJson slot.duplicatePadding)]
  | none =>
    let account := slot.account
    let nonzero := account.spare.findIdx? (fun byte => byte != 0)
    Json.mkObj [("marker", natJson 255), ("is_signer", natJson account.signer.toNat),
      ("is_writable", natJson account.writable.toNat),
      ("executable", natJson account.executable.toNat),
      ("padding", natJson account.reserved.toNat), ("key", bytesJson account.key.bytes),
      ("owner", bytesJson account.owner.bytes), ("lamports", natJson account.lamports.toNat),
      ("data_len", natJson account.data.length), ("data", bytesJson account.data),
      ("rent_epoch", natJson account.rentEpoch.toNat),
      ("spare_nonzero_at", match nonzero with
        | none => Json.null | some offset => natJson (account.data.length + offset)),
      ("spare", bytesJson account.spare), ("alignment_padding", bytesJson account.padding)]

def regionJson (parsed : Parsed) : Json := Json.mkObj [
  ("accounts", Json.arr (parsed.slots.map regionAccountJson).toArray),
  ("count", natJson parsed.slots.length), ("instruction_data", bytesJson parsed.instructionData),
  ("program_id", bytesJson parsed.programId.bytes)]

def regionConsistent (j : Json) : Result Unit := do
  let bytes ← stateBytes j
  let some parsed := parse bytes | throw "account region is not a complete loader input"
  unless (← field j "input") == regionJson parsed do
    throw "account region readback differs from the recorded raw input bytes"

def readRange (bytes : Solanalib.Runtime.Bytes) (offset length : Nat) : Result
  Solanalib.Runtime.Bytes :=
  match slice? bytes offset length with
  | some value => pure value
  | none => throw "recorded byte range is outside the input allocation"

def readWord (bytes : Solanalib.Runtime.Bytes) (offset width : Nat) : Result Nat :=
  Solanalib.Runtime.leNat <$> readRange bytes offset width

def pinReady (maximum : Nat) (before : Pinocchio.State) : Prop :=
  maximum ≤ 254 ∧ before.outputs.length = maximum ∧
    match parse before.bytes with
    | none => False
    | some parsed => parsed.slots.length ≤ 254 ∧ (parsed.slots = [] ∨ 0 < maximum)

instance (maximum : Nat) (before : Pinocchio.State) : Decidable (pinReady maximum before) := by
  unfold pinReady
  split <;> infer_instance

theorem pinReady_iff (maximum : Nat) (before : Pinocchio.State) :
    Pinocchio.Admitted maximum before ↔ pinReady maximum before := by
  cases parsed : parse before.bytes <;> simp [Pinocchio.Admitted, pinReady, parsed]

def pinRequires (maximum : Nat) (before : Pinocchio.State) : Bool :=
  have : Decidable (requires
      (Solanalib.Specs.Pinocchio.entrypoint.deserialize_contract.contract ⟨maximum⟩) before ()) :=
    decidable_of_iff _ (pinReady_iff maximum before).symm
  decide (requires (Solanalib.Specs.Pinocchio.entrypoint.deserialize_contract.contract ⟨maximum⟩)
    before ())

def sdkReady {Aux : Type} (before : SDK.State Aux) : Prop :=
  SDK.Coherent before ∧ match parse before.bytes with
    | none => False
    | some parsed => parsed.slots.length * 48 < 2^63

instance {Aux : Type} (before : SDK.State Aux) : Decidable (sdkReady before) := by
  unfold sdkReady SDK.Coherent
  split <;> infer_instance

theorem sdkReady_iff {Aux : Type} (before : SDK.State Aux) :
    SDK.Admitted before ↔ sdkReady before := by
  cases parsed : parse before.bytes <;> simp [SDK.Admitted, sdkReady, parsed]

def sdkRequires (index : SDK.Index) (before : SDK.State index.Aux) : Bool :=
  have : Decidable (requires
      (Solanalib.Specs.SolanaProgramEntrypoint.deserialize_contract.contract index) before ()) :=
    decidable_of_iff _ (sdkReady_iff before).symm
  decide (requires (Solanalib.Specs.SolanaProgramEntrypoint.deserialize_contract.contract index)
    before ())

/-- Native addresses are normalized by first occurrence. Repeated occurrences must retain
their content and Rc count; a fresh identity is appended, never inferred from key equality. -/
def mergeAt {α : Type} [DecidableEq α] (values : List α) (index : Nat) (value : α) :
    Result (List α) :=
  if index = values.length then pure (values ++ [value])
  else if values[index]? = some value then pure values
  else throw "conflicting content or noncanonical alias identity"

end SolanalibTest.Conformance.Library.Families.EntryDeserialize
