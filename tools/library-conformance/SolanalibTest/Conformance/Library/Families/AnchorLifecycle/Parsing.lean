/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.CollectionGraph
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.ExitGraph
import SolanalibTest.Conformance.Library.Families.AnchorLifecycle.PayloadGraph

/-! The records describe concrete script inputs, original record identities,
caller-owned Rc references and the complete serialized account region. Host
unwind observations are separate from production release/abort applicability. -/

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.AnchorLifecycle

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor

def asStep (json : Json) : Result Step := do
  pure ⟨← keyField json "key", ← asOption asPubkey (← field json "assign"),
    ← asOption (asUInt 64) (← field json "lamports"), ← asUInt 64 (← field json "value"),
    ← asUInt 32 (← field json "error"), ← boolField json "panic", ← asBytes (← field json
      "bytes")⟩

def asScript (json : Json) : Result Script := do
  pure ⟨← asList asStep (← field json "owner"), ← asList asStep (← field json "check_owner"),
    ← asList asStep (← field json "id"), ← asList asStep (← field json "check_id"),
    ← asList asStep (← field json "decode"), ← asList asStep (← field json "serialize"),
    ← asList asStep (← field json "drop_payload"), ← asList asStep (← field json "sysvar"),
    ← asList asStep (← field json "inner"), "Account discriminator did not match what was \
      expected"⟩

def parseCounts (json : Json) : Result (List Nat) := do
  let pairs ← asList (asList (asUInt 64)) json
  unless pairs.all (fun pair => pair.length == 2 && pair.all (· > 0)) do
    throw "each live AccountInfo must have two positive Rc counts"
  return pairs.flatten

def parseAfterCounts (json : Json) : Result (List Nat) := do
  let pairs ← asList (asList (asUInt 64)) json
  unless pairs.all (fun pair => pair.length == 2) do
    throw "each AccountInfo count record has two fields"
  return pairs.flatten

def expectedCounts (owned : Bool) (object method : String) (input : LoaderInput) (target
  destination : Nat) :
    List Nat :=
  let numbers := entryNumbers input.entries
  let raw := (List.range (distinctOf input.entries).length).map fun k => numbers.count (some k)
  let increment := fun counts record => match numbers[record]?.join with
    | none => counts
    | some k => counts.set k (counts.getD k 0 + 1)
  let raw := if owned && ["account", "interface_account"].contains object && ["reload",
    "exit",
    "close"].contains method
      then increment raw target else raw
  let raw := if owned && object == "unchecked_account" && method == "try_from" then increment raw
    target else raw
  let raw := if method == "close" then increment raw destination else raw
  raw.flatMap fun count => [count, count]

def referenceAt (legacyRent : Bool) (input : LoaderInput) (index : Nat) : Result AccountReference
  := do
  let info ← infoAt input index
  let some (some k) := (entryNumbers input.entries)[index]? | throw "invalid record \
    identity"
  let some account := (distinctOf input.entries)[k]? | throw "invalid distinct account \
    identity"
  return ⟨index, { info with unused := if legacyRent then UInt64.ofNat account.rentEpoch else 0 }⟩

def parseBumps (legacy : Bool) (json : Json) : Result Nat := do
  if legacy then
    let pairs ← asArray json
    match pairs with
    | [pair] =>
      match ← asArray pair with
      | [name, value] =>
        unless (← name.getStr?) == "seed" do throw "unexpected scripted bump key"
        asUInt 8 value
      | _ => throw "expected the concrete bump map entry"
    | _ => throw "expected the concrete one-entry bump map"
  else asUInt 64 json

structure Inputs where
  input : LoaderInput
  world : W
  reference : AccountReference
  destination : Option AccountReference
  accounts : AccountsState Nat
  args : AccountsArgs
  script : Script
  savedOwner : Solanalib.Runtime.Pubkey
  optionalSome : Bool
  innerValue : Nat

def inputs (legacyRent owned : Bool) (object method : String) (record : Case) : Result Inputs := do
  let (input, borrow) ← asWorld record.state
  unless (← field record.state "syscalls").compress ==
      (Json.mkObj [("replies", Json.arr #[]), ("log", Json.arr #[])]).compress do
    throw "input syscall state must have no replies and an empty log"
  let target ← natField record.args "account"
  let destination ← natField record.args "destination"
  let counts ← parseCounts (← field record.state "ref_counts")
  unless counts == expectedCounts owned object method input target destination do
    throw "the input Rc counts disagree with the exact caller-owned records"
  let reference ← if input.entries.isEmpty then pure ⟨target, AccountInfo.sampleInfo⟩ else
    referenceAt legacyRent input target
  let destination ← if method == "close" then pure (some (← referenceAt legacyRent input
    destination)) else pure none
  let innerValue ← asUInt 64 (← field record.args "inner_value")
  let payload ← match record.state.getObjVal? "payload" with
    | .ok value => asUInt 64 value
    | .error _ => pure innerValue
  let buffers := (distinctOf input.entries).flatMap fun account =>
    [none, some (⟨account.data.length, account.data.length, List.replicate 10240 0⟩ :
      AccountInfoSdk.Buffer)]
  let world : W := (borrow, {
    owners := inputOwners input, counts := counts, log := [], strings := [], boxes := [], payload
      := payload,
    extraLive := 0, programString := none, buffers := buffers, payloadBoxes := [some innerValue] })
  unless (← asArray (← field record.state "log")).isEmpty do
    throw "input callback log must be empty"
  unless (← natField record.state "fresh_live") == 0 do
    throw "input measured allocation count must be zero"
  unless (← field record.state "program_string_dropped") == .null do
    throw "input decoder String has not been created"
  let accounts ← if method == "try_accounts" then do
      let remaining ← asList (asUInt 64) (← field record.state "remaining")
      unless remaining == (List.range input.entries.length).drop target do
        throw "remaining accounts must denote the actual input suffix"
      pure (⟨← remaining.mapM (referenceAt legacyRent input), ← parseBumps owned (← field
        record.state "bumps"),
        ← asList asPubkey (← field record.state "reallocs")⟩ : AccountsState Nat)
    else pure ⟨[], 0, []⟩
  return ⟨input, world, reference, destination, accounts,
    ⟨profile, ← keyField record.args "program_id", ← asBytes (← field record.args
      "instruction_data")⟩,
    { ← asScript (← field record.args "script") with discriminatorMessage :=
        if ["anchor_lifecycle_0_27_0", "anchor_lifecycle_0_29_0"].contains record.corpus then
          "8 byte discriminator did not match what was expected"
        else "Account discriminator did not match what was expected" }, ← keyField record.args
          "saved_owner",
    ← boolField record.args "optional_some", innerValue⟩

def currentInfo (state : W) (info : AccountInfo.Value) : AccountInfo.Value :=
  { info with owner := ownerAt state.2 info.ownerRef }

def eventJson : Event → Json × Json
  | .owner => ("owner", .null)
  | .id => ("id", .null)
  | .checkOwner reference => ("check_owner", toJson reference)
  | .checkId key => ("check_id", pubkeyJson key)
  | .decode checked bytes => (if checked then "deserialize" else "deserialize_unchecked", bytesJson
    bytes)
  | .serialize value => ("serialize", toJson value)
  | .write count => ("write", toJson count)
  | .dropPayload value => ("drop_payload", toJson value)
  | .sysvar reference => ("from_account_info", toJson reference)
  | .innerAccounts program bytes remaining => ("inner_accounts", Json.mkObj [
      ("program_id", pubkeyJson program), ("instruction_data", bytesJson bytes), (
        "remaining",
        toJson remaining)])
  | .innerExit value program => ("inner_exit", Json.mkObj [("value", toJson value), (
    "program_id",
    pubkeyJson program)])
  | .innerClose value destination => ("inner_close", Json.mkObj [("value", toJson value),
    ("destination", infoJson destination)])

def loggedJson (logged : Logged) : Json :=
  let (call, argument) := eventJson logged.event
  Json.mkObj [("call", call), ("argument", argument), ("ref_counts", toJson logged.counts),
    ("leases", listJson leaseJson logged.leases)]

structure StateObs where
  world : WorldObs
  spare : List Solanalib.Runtime.Bytes
  padding : List Solanalib.Runtime.Bytes
  count : Nat
  counts : List Nat
  log : List String
  freshLive : Nat
  programStringDropped : Option Bool
  payload : Option Nat
  accounts : Option (List Nat × Nat × List Solanalib.Runtime.Pubkey)
  syscalls : String
  deriving DecidableEq

def stateObs (input : LoaderInput) (includePayload : Bool) (accounts : Option (AccountsState Nat))
  (after : W) : StateObs :=
  let plain := observeWorld input after.2.owners after.1
  let update := fun (acc : List RegionEntry × Nat) (entry : RegionEntry) =>
    match entry with
    | .duplicate _ => (acc.1 ++ [entry], acc.2)
    | .account account =>
      let buffer := (after.2.buffers[2 * acc.2 + 1]?.join).getD ⟨account.padding, account.dataLen,
        []⟩
      let updated : RegionAccount := { account with
        padding := buffer.originalLen,
        dataLen := buffer.serializedLen,
        spareNonzeroAt := (buffer.spare.findIdx? (· != 0)).map (account.data.length + ·) }
      (acc.1 ++ [.account updated], acc.2 + 1)
  { world := { plain with region := { plain.region with entries := (plain.region.entries.foldl
    update ([], 0)).1 } },
    spare := (List.range (distinctOf input.entries).length).map fun k =>
      ((after.2.buffers[2 * k + 1]?.join).getD ⟨0, 0, []⟩).spare,
    padding := input.entries.map fun
      | .account account => List.replicate ((8 - account.data.length % 8) % 8) 0
      | .duplicate _ => List.replicate 7 0,
    count := input.entries.length, counts := after.2.counts, log := after.2.log.map (Json.compress
      ∘ loggedJson),
    freshLive := freshLive after, programStringDropped := programStringDropped after,
    payload := if includePayload then some after.2.payload else none,
    accounts := accounts.map fun state => (state.remaining.map AccountReference.identity,
      state.bumps, state.reallocs),
    syscalls := (Json.mkObj [("replies", Json.arr #[]), ("log", listJson (fun bytes =>
      Json.mkObj [("syscall", "sol_memcpy_"), ("bytes", bytesJson bytes)])
        after.2.memoryCopies)]).compress }

def asStateObs (legacyBumps : Bool) (json : Json) : Result StateObs := do
  let entries ← asArray (← field (← field json "input") "accounts")
  let spare ← entries.filterMapM fun entry => do
    match entry.getObjVal? "duplicate_of" with
    | .ok _ => return none
    | .error _ => return some (← asBytes (← field entry "spare"))
  let padding ← entries.mapM fun entry => do
    match entry.getObjVal? "duplicate_of" with
    | .ok _ => asBytes (← field entry "padding")
    | .error _ => asBytes (← field entry "alignment_padding")
  let payload ← match json.getObjVal? "payload" with
    | .ok value => pure (some (← asUInt 64 value))
    | .error _ => pure none
  let accounts ← match json.getObjVal? "remaining" with
    | .error _ => pure none
    | .ok value => pure (some (← asList (asUInt 64) value, ← parseBumps legacyBumps (← field json
      "bumps"),
        ← asList asPubkey (← field json "reallocs")))
  return ⟨← asWorldObs json, spare, padding, ← natField (← field json "input") "count",
    ← parseAfterCounts (← field json "ref_counts"), (← asArray (← field json "log")).map
      Json.compress,
    ← natField json "fresh_live", ← asOption (fun value => value.getBool?) (← field json
      "program_string_dropped"),
    payload, accounts, (← field json "syscalls").compress⟩

end SolanalibTest.Conformance.Library.Families.AnchorLifecycle
