/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.EntryDeserialize.Common

/-! The size, alignment of the actual allocator and first recorded-length observation instantiate
the explicit allocator provider of the model. Rc pointers and owner addresses are normalized by
identity in the native recorder, independently of key equality. The reader reconstructs each
unique shared cell once and rejects conflicting observations of any duplicate. -/

set_option autoImplicit false
open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.EntryDeserialize

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.EntryDeserialize

structure AllocationObservation where
  size : Nat
  align : Nat
  firstOriginalLength : Nat
  deriving DecidableEq, Repr

def allocationObservation (request : SDK.AllocationRequest) : AllocationObservation :=
  ⟨match request.site with | .vector n => 48 * n | .lamports _ => 32 | .data _ => 40,
    8, (word? request.input 12 4).getD 0⟩

def nativeIndex (failAt : Option Nat) : SDK.Index where
  Aux := List AllocationObservation
  Terminal := Unit
  allocate := fun before request =>
    if failAt = some before.length then some (.terminated ())
    else some (.returned () (before ++ [allocationObservation request]))

def sdkInitial (bytes : Solanalib.Runtime.Bytes) : SDK.State (List AllocationObservation) :=
  ⟨bytes, ⟨⟨[], []⟩, [], []⟩, [], [], []⟩

def readAllocation (j : Json) : Result AllocationObservation := do
  pure ⟨← nat (← field j "size"), ← nat (← field j "align"),
    ← asUInt 32 (← field j "first_original_length")⟩

def allocationJson (value : AllocationObservation) : Json := Json.mkObj [
  ("size", natJson value.size), ("align", natJson value.align),
  ("first_original_length", natJson value.firstOriginalLength)]

structure ObservedInfo where
  info : SDK.Info
  lamports : UInt64
  data : Solanalib.Runtime.Bytes
  buffer : AccountInfoSdk.Buffer
  lamportsStrong : Nat
  dataStrong : Nat
  deriving DecidableEq, Repr

def readInfo (bytes : Solanalib.Runtime.Bytes) (j : Json) : Result ObservedInfo := do
  let offset ← nat (← field j "header_offset")
  unless (← nat (← field j "lamports_offset")) = offset + 72 do
    throw "lamports pointer no longer designates its serialized header"
  unless (← nat (← field j "data_offset")) = offset + 88 do
    throw "data pointer no longer designates its serialized header"
  let data ← asBytes (← field j "data")
  let buffer : AccountInfoSdk.Buffer := ⟨← readWord bytes (offset + 4) 4,
    ← readWord bytes (offset + 80) 8, ← readRange bytes (offset + 88 + data.length) growth⟩
  let value : AccountInfo.Value := ⟨← byteArray (← field j "key"),
    ⟨← nat (← field j "lamports_cell")⟩, ⟨← nat (← field j "data_cell")⟩,
    ← byteArray (← field j "owner"), UInt64.ofNat (← asUInt 64 (← field j "rent_epoch")),
    ← (← field j "signer").getBool?, ← (← field j "writable").getBool?,
    ← (← field j "executable").getBool?, ⟨← nat (← field j "owner_ref")⟩⟩
  pure ⟨⟨value, offset⟩, UInt64.ofNat (← asUInt 64 (← field j "lamports")), data, buffer,
    ← nat (← field j "lamports_strong"), ← nat (← field j "data_strong")⟩

abbrev CellObservation := AccountInfo.Content × Nat × Option AccountInfoSdk.Buffer

def collectInfos (infos : List ObservedInfo) :
    Result (List CellObservation × List Solanalib.Runtime.Pubkey) :=
  infos.foldlM (fun (cells, owners) observed => do
    let cells ← mergeAt cells observed.info.value.lamports.cell
      (.lamports observed.lamports, observed.lamportsStrong, none)
    let cells ← mergeAt cells observed.info.value.data.cell
      (.data observed.data, observed.dataStrong, some observed.buffer)
    let owners ← mergeAt owners observed.info.value.ownerRef.id observed.info.value.owner
    pure (cells, owners)) ([], [])

abbrev SDKOutcome := Outcome (SDK.State (List AllocationObservation)) SDK.Result Empty Unit

/-- Every returned state is reconstructed from native readback, including the mutated input,
reserve bytes, Rc identities/counts and allocation observations. Ghost lease history is empty:
the deserializer constructs fresh RefCells and performs no checked acquisition. -/
def sdkRecorded (outcome : Json) : Result (Option SDKOutcome) := do
  match ← (← field outcome "exit").getStr? with
  | "returned" =>
    let state ← field outcome "state"
    regionConsistent state
    asUnit (← field state "outputs")
    let bytes ← stateBytes state
    let result ← field outcome "result"
    let infos ← array (readInfo bytes) (← field result "accounts")
    unless (← nat (← field result "capacity")) = infos.length do
      throw "vector capacity differs from the requested exact fixture capacity"
    let (cells, owners) ← collectInfos infos
    let after : SDK.State (List AllocationObservation) := ⟨bytes,
      ⟨⟨cells.map (fun cell => ⟨cell.1, .refCell 64⟩), []⟩, owners,
        cells.map (fun cell => cell.2.2)⟩,
      cells.map (fun cell => cell.2.1), [infos.map (·.info)],
      ← array readAllocation (← field result "allocations")⟩
    pure (some (.returned ⟨← views (← field result "views"), 0⟩ after))
  | "terminated" =>
    if (← (← field outcome "reason").getStr?) = "allocation-failure" then
      pure (some (.terminated ()))
    else pure none
  | "unwound" => pure none
  | other => throw s!"unknown exit {other}"

def sdkOutcomeJson : SDKOutcome → Json
  | .terminated () => Json.mkObj [("exit", "terminated"), ("reason", "allocation-failure")]
  | .unwound impossible _ => nomatch impossible
  | .returned result after => returnedJson
    (Json.mkObj [("views", viewsJson result.views), ("vector", natJson result.vector)])
    (Json.mkObj [("bytes", bytesJson after.bytes),
      ("rc_strong", toJson after.rcStrong),
      ("allocations", Json.arr (after.allocator.map allocationJson).toArray)])

theorem sdk_graph (failAt : Option Nat) (before : SDK.State (List AllocationObservation))
    (outcome : SDKOutcome) :
    Solanalib.Specs.SolanaProgramEntrypoint.deserialize_run (nativeIndex failAt) before () outcome ↔
      SDK.execute (nativeIndex failAt) before = some outcome := Iff.rfl

def sdkChecker : Checker where
  function := "solana_program_entrypoint::deserialize"
  generics := []
  reference := "Solanalib.Specs.SolanaProgramEntrypoint.deserialize_run"
  decides := ["Solanalib.Specs.SolanaProgramEntrypoint.deserialize_run"]
  decidesRequires := ["Solanalib.Specs.SolanaProgramEntrypoint.deserialize_run"]
  check := fun c => do
    asUnit (← field c.state "outputs")
    let before := sdkInitial (← stateBytes c.state)
    let failAt ← nullableNat (← field c.args "fail_at")
    unless sdkRequires (nativeIndex failAt) before do
      throw "the input is outside the registered precondition"
    regionConsistent c.state
    let recorded ← sdkRecorded c.outcome
    pure (Runtime.decideOptGraph (S := SDK.State (List AllocationObservation))
      (V := SDK.Result) (U := Empty) (T := Unit)
      (Solanalib.Specs.SolanaProgramEntrypoint.deserialize_run (nativeIndex failAt) before ())
      (SDK.execute (nativeIndex failAt) before) (sdk_graph failAt before)
      recorded sdkOutcomeJson)

end SolanalibTest.Conformance.Library.Families.EntryDeserialize
