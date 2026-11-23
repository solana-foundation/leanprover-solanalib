/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.BorshCommon
import Solanalib.Specs.Core.AnchorSplTokenOperations.ReferenceObservation
import Solanalib.Specs.Core.AnchorSplTokenOperations.Sample

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

open Lean (Json toJson)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTokenOperations
open SolanalibTest.Conformance.Library.Borsh (asList listJson)

def keyOf (value : Json) : Result Solanalib.Runtime.Pubkey := do
  let bytes ← asBytes value
  unless bytes.length = 32 do throw "a source Pubkey has exactly 32 bytes"
  pure (.ofBytes bytes)

def optionalKey : Json → Result (Option Solanalib.Runtime.Pubkey)
  | .null => pure none
  | value => return some (← keyOf value)

def fixtureKey (number : Nat) : Solanalib.Runtime.Pubkey := .ofBytes (Solanalib.Runtime.leBytes 32
  number)

def infoOf (identity : Nat) (value : Json) : Result AccountInfo.Value := do
  pure {
    key := ← keyOf (← field value "key")
    owner := ← keyOf (← field value "owner")
    lamports := ⟨2 * identity⟩
    data := ⟨2 * identity + 1⟩
    ownerRef := ⟨identity⟩
    unused := 0
    isSigner := ← (← field value "signer").getBool?
    isWritable := ← (← field value "writable").getBool?
    executable := ← (← field value "executable").getBool? }

def parametersOf (operation : Operation) (args : Json) : Result (Parameters operation) :=
  match operation with
  | .transfer | .burn | .mintTo => return UInt64.ofNat (← asUInt 64 (← field args "amount"))
  | .transferChecked | .burnChecked | .mintToChecked => return {
      amount := UInt64.ofNat (← asUInt 64 (← field args "amount")),
      decimals := UInt8.ofNat (← asUInt 8 (← field args "decimals")) }
  | .setAuthority => do
      let authority ← asUInt 8 (← field args "authority_type")
      if bounded : authority < 17 then
        pure ⟨⟨authority, bounded⟩, ← optionalKey (← field args "option1")⟩
      else throw "unavailable AuthorityType discriminant"
  | .initializeMint2 => return ⟨UInt8.ofNat (← asUInt 8 (← field args "decimals")),
      ← keyOf (← field args "mint_authority"), ← optionalKey (← field args "option2")⟩
  | .getAccountDataSize => do asList (fun value => do
      let tag ← asUInt 16 value
      if bounded : tag < 28 then pure ⟨tag, bounded⟩
      else throw "unavailable production ExtensionType") (← field args "extensions")
  | .mintCloseAuthority => do optionalKey (← field args "option1")
  | .permanentDelegate => return (← optionalKey (← field args "option1")).getD .zero
  | .metadataPointer | .groupPointer | .groupMemberPointer | .transferHook =>
      return ⟨← optionalKey (← field args "option1"), ← optionalKey (← field args "option2")⟩
  | .closeAccount | .initializeAccount3 | .initializeImmutableOwner | .nonTransferableMint => pure
    ()

def contextProgram (release : Release) (info : AccountInfo.Value) : release.Program :=
  match release with
  | .v027 | .v029 | .v0321 => info
  | .v102 | .v112 => info.key

def cpiError (release : Release) (borsh : Bool) : release.ProgramError Nat :=
  match release with
  | .v027 | .v029 | .v0321 => if borsh then .borshIoError 0 else .custom 77
  | .v102 | .v112 => .custom 77

def scriptOf (binding : Binding) (args : Json) (expected : Solanalib.Runtime.Pubkey) :
    Result (Reference.Script binding.release) := do
  let mode ← (← field args "mode").getStr?
  let getter ← (← field args "getter").getStr?
  let borsh ← (← field args "borsh").getBool?
  unless !borsh || (binding.release ∈ [.v027, .v029, .v0321] && mode == "error") do
    throw "the selected dependency has no owned Borsh error here"
  let reply ← match mode with
    | "ok" => pure .success
    | "error" => pure (.error (cpiError binding.release borsh))
    | "unwind" => pure (.unwind 23)
    | "terminal" => pure (.terminal 71)
    | _ => throw "unknown whole-invocation script"
  let returned ← match getter with
    | "good" => pure (.present expected (Solanalib.Runtime.u64le 165))
    | "none" => pure .absent
    | "wrong" => pure (.present (fixtureKey 99) [1])
    | "short" => pure (.present expected (List.replicate 7 1))
    | "long" => pure (.present expected (List.replicate 9 1))
    | "unwind" => pure (.unwind 29)
    | "terminal" => pure (.terminal 91)
    | _ => throw "unknown whole-getter script"
  let enumSize ← asUInt 64 (← field args "enum_size")
  pure { reply, returned, enumSize, writeFirst := true }

structure Prepared (binding : Binding) where
  before : Reference.State binding.release
  args : Args binding Nat Nat
  script : Reference.Script binding.release
  identities : List AccountInfo.Value

/-- The record carries actual input aliases, counts, cells and borrowed seed
bytes. Validity of the source pointers is a separate Rust-binding obligation. -/
def prepare (binding : Binding) (record : Case) : Result (Prepared binding) := do
  let rawInfos ← (← field record.state "infos").getArr?
  let infos ← rawInfos.toList.zipIdx.mapM fun (value, index) => infoOf index value
  unless infos.length = 5 do throw "the native fixture has five input identities"
  let indices ← asList (asUInt 64) (← field record.args "account_ids")
  unless indices.length = binding.operation.accountCount do
    throw "wrong source account aggregate arity"
  let accounts ← indices.mapM fun index => match infos[index]? with
    | some info => pure info
    | none => throw "account identity is not in the input table"
  let remainingIndices ← asList (asUInt 64) (← field record.args "remaining")
  let remaining ← remainingIndices.mapM fun index => match infos[index]? with
    | some info => pure info
    | none => throw "remaining account identity is not in the input table"
  let programIndex ← asUInt 64 (← field record.args "program_index")
  let program ← match infos[programIndex]? with
    | some info => pure info
    | none => throw "context program identity is not in the input table"
  let seeds ← asList (asList asBytes) (← field record.args "seeds")
  let counts ← asList (asList (asUInt 64)) (← field record.state "counts")
  unless counts.length = infos.length && counts.all (fun pair => pair.length == 2) do
    throw "one actual pair of Rc counts is required per input identity"
  let cells : List (Nat × Solanalib.Runtime.Bytes) ← asList (fun cell => do
    let lamports ← asUInt 64 (← field cell "lamports")
    let data ← asBytes (← field cell "data")
    pure (lamports, data)) (← field record.state "cells")
  unless cells.length = infos.length do throw "one cell pair is required per input identity"
  let args : Args binding Nat Nat := {
    context := {
      accounts := fun index => accounts[index.val]?.getD (Sample.info 0)
      program := contextProgram binding.release program
      remainingAccounts := 0
      signerSeeds := 0 }
    parameters := ← parametersOf binding.operation record.args }
  let before : Reference.State binding.release := {
    remaining := [some remaining], seeds := [some seeds], strings := [some "owned \
      dependency error"]
    counts := counts.zipIdx.flatMap fun (pair, index) =>
      [((.lamports, ⟨2 * index⟩), pair[0]?.getD 0), ((.data, ⟨2 * index + 1⟩), pair[1]?.getD 0)]
    lamports := cells.zipIdx.map fun (cell, index) => (⟨2 * index⟩, cell.1)
    dataCells := cells.zipIdx.map fun (cell, index) => (⟨2 * index + 1⟩, cell.2) }
  pure ⟨before, args, ← scriptOf binding record.args (selectedProgram args), infos⟩

end SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations
