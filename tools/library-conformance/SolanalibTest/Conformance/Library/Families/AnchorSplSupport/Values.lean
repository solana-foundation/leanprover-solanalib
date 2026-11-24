/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Core
import Solanalib.Specs.Core.AnchorSplSupport.Values
import Solanalib.Specs.Core.Callback

/-!
Native borrowed-value observations at the same existing wrapper. Wire decoding
is only the value transport of the recorder; it is not part of the deref contract.
The returned current pointee is checked as the after-state of the registered
field-reference model, and the native parent-address observation is retained.
-/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport

open Lean (Json toJson)
open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AnchorSplSupport

private def keyAt (bytes : Solanalib.Runtime.Bytes) (offset : Nat) : Solanalib.Runtime.Pubkey :=
  .ofBytes (Solanalib.Runtime.slice bytes offset 32)

private def u64At (bytes : Solanalib.Runtime.Bytes) (offset : Nat) : UInt64 :=
  UInt64.ofNat (Solanalib.Runtime.leNat (Solanalib.Runtime.slice bytes offset 8))

/-- Complete legacy stake fields, including the stored binary64 bits. -/
def stakeFromBytes (bytes : Solanalib.Runtime.Bytes) : Result LegacyStake.State := do
  let tag := Solanalib.Runtime.leNat (bytes.take 4)
  let metadata : StakeState.Meta := ⟨u64At bytes 4, ⟨keyAt bytes 12, keyAt bytes 44⟩,
    ⟨Int64.ofInt (Int.ofNat (u64At bytes 76).toNat), u64At bytes 84, keyAt bytes 92⟩⟩
  let active : StakeState.Stake :=
    ⟨⟨keyAt bytes 124, u64At bytes 156, u64At bytes 164, u64At bytes 172,
      u64At bytes 180⟩, u64At bytes 188⟩
  match tag, bytes.length with
  | 0, 4 => pure .uninitialized
  | 1, 124 => pure (.initialized metadata)
  | 2, 196 => pure (.stake metadata active)
  | 3, 4 => pure .rewardsPool
  | _, _ => throw "invalid legacy stake value transport"

/-- This renderer serializes the complete pointee rather than retaining a copy
of the input transport bytes. Short variants have no flags or padding. -/
def stakeBytes : LegacyStake.State → Solanalib.Runtime.Bytes
  | .uninitialized => Solanalib.Runtime.u32le 0
  | .initialized metadata => Solanalib.Runtime.u32le 1 ++ metadata.encode
  | .stake metadata active => Solanalib.Runtime.u32le 2 ++ metadata.encode ++ active.encode
  | .rewardsPool => Solanalib.Runtime.u32le 3

private def keyOption : Option Solanalib.Runtime.Pubkey → Solanalib.Runtime.Bytes
  | none => List.replicate 36 0
  | some key => Solanalib.Runtime.u32le 1 ++ key.bytes

private def amountOption : Option Nat → Solanalib.Runtime.Bytes
  | none => List.replicate 12 0
  | some amount => Solanalib.Runtime.u32le 1 ++ Solanalib.Runtime.u64le amount

/-- SPL Pack output into the initially zeroed buffer of the recorder. COption::None
writes its tag and leaves the zero payload of that buffer unchanged. -/
def accountBytes (account : Token.Account) : Solanalib.Runtime.Bytes :=
  account.mint.bytes ++ account.owner.bytes ++ Solanalib.Runtime.u64le account.amount ++
    keyOption account.delegate ++ [(match account.state with
      | .uninitialized => 0 | .initialized => 1 | .frozen => 2 : UInt8)] ++
    amountOption account.nativeAmount ++ Solanalib.Runtime.u64le account.delegatedAmount ++
    keyOption account.closeAuthority

def pointee : (wrapper : Wrapper) → Json → Result wrapper.Pointee
  | .stakeAccount, json => do stakeFromBytes (← asBytes json)
  | .tokenAccount, json | .interfaceTokenAccount, json => do
    let bytes ← asBytes json
    match Token.unpackAccountUnchecked bytes with
    | .ok value => pure value
    | .error _ => throw "invalid account value transport"

def pointeeJson : (wrapper : Wrapper) → wrapper.Pointee → Json
  | .stakeAccount, value => bytesJson (stakeBytes value)
  | .tokenAccount, value | .interfaceTokenAccount, value => bytesJson (accountBytes value)

private instance (wrapper : Wrapper) : DecidableEq wrapper.Pointee := by
  cases wrapper <;> unfold Wrapper.Pointee <;> infer_instance

private instance (wrapper : Wrapper) : DecidableEq (DerefResult (derefSample wrapper)) :=
  inferInstanceAs (DecidableEq (FieldReference Unit Unit))

/-- The native transport contains an existing borrowed wrapper. Its parsed
slot is present; the general family still rejects missing or expired parents. -/
theorem deref_requires (wrapper : Wrapper)
    (contract : Solanalib.Contracts.Model (Option wrapper.Pointee) Unit
      (DerefResult (derefSample wrapper)))
    (contract_eq : contract = (derefFamily wrapper).contract (derefSample wrapper))
    (input : wrapper.Pointee) : Solanalib.Contracts.Model.requires contract (some input) () := by
  rw [contract_eq]
  exact ⟨input, rfl, rfl⟩

/-- The exact registered reference is evaluated at a live existing slot. Its
state is the current pointee, so an altered returned field is a model mismatch. -/
def derefChecker (wrapper : Wrapper) (function contractName runName : String)
    (contract : Solanalib.Contracts.Model (Option wrapper.Pointee) Unit
      (DerefResult (derefSample wrapper)))
    (contract_eq : contract = (derefFamily wrapper).contract (derefSample wrapper))
    (relation : Callback.Run (Option wrapper.Pointee) Unit
      (DerefResult (derefSample wrapper)) Empty Empty)
    (evaluated : relation = returnsOf (deref (derefSample wrapper))) : Checker where
  function := function
  generics := []
  reference := runName
  decides := [contractName, runName]
  decidesRequires := [contractName, runName]
  check := fun c => do
    asUnit c.state
    let input ← pointee wrapper c.args
    let expected := returnedJson (Json.mkObj [("value", pointeeJson wrapper input),
      ("same_parent", Json.bool true)]) Json.null
    unless (← field c.outcome "exit").getStr? == .ok "returned" do return ⟨false, expected⟩
    asUnit (← field c.outcome "state")
    let result ← field c.outcome "result"
    unless (← field result "same_parent").getBool? == .ok true do return ⟨false, expected⟩
    let output ← pointee wrapper (← field result "value")
    have required := deref_requires wrapper contract contract_eq input
    let _ : Decidable (Solanalib.Contracts.Model.requires contract (some input) ()) := isTrue
      required
    let check ← decideReturns relation (deref (derefSample wrapper)) evaluated (some input) ()
      (fun _ => pure ⟨(), ()⟩) (fun _ => pure (some output))
      (fun _ => Json.mkObj [("value", pointeeJson wrapper input), ("same_parent", Json.bool true)])
      (fun _ => Json.null) c.outcome
    pure ⟨decide (Solanalib.Contracts.Model.requires contract (some input) ()) && check.admitted &&
      c.outcome == expected, expected⟩

private def pubkey (json : Json) : Result Solanalib.Runtime.Pubkey := do
  let bytes ← asBytes json
  if h : bytes.length = 32 then pure ⟨bytes, h⟩ else throw "key must have 32 bytes"

/-- The copied Pubkey result uses the exact reference of the selected version. -/
def idChecker (program : Program) (function contractName runName : String)
    (contract : Solanalib.Contracts.Model Unit Unit Solanalib.Runtime.Pubkey)
    (contract_eq : contract = idContract program Unit)
    (relation : Callback.Run Unit Unit Solanalib.Runtime.Pubkey Empty Empty)
    (evaluated : relation = returnsOf (idReference program)) : Checker where
  function := function
  generics := []
  reference := runName
  decides := [contractName, runName]
  decidesRequires := [contractName, runName]
  check := fun c => do
    asUnit c.state; asUnit c.args
    have required : Solanalib.Contracts.Model.requires contract () () := by
      rw [contract_eq]; trivial
    let _ : Decidable (Solanalib.Contracts.Model.requires contract () ()) := isTrue required
    let checked ← decideReturns relation (idReference program) evaluated () ()
      (fun value => do
        asUnit (← field value "same_parent")
        pubkey (← field value "value")) asUnit
      (fun key => Json.mkObj [("value", bytesJson key.bytes), ("same_parent", Json.null)])
      (fun _ => Json.null) c.outcome
    pure ⟨decide (Solanalib.Contracts.Model.requires contract () ()) && checked.admitted,
      checked.expected⟩

/-- Static IDs retain one repeated address and the exact ordered slice. -/
def idsChecker (contractName runName : String)
    (contract : Solanalib.Contracts.Model Unit Unit InterfaceIdsRef)
    (contract_eq : contract = idsContract Unit)
    (relation : Callback.Run Unit Unit InterfaceIdsRef Empty Empty)
    (evaluated : relation = returnsOf idsReference) : Checker where
  function := "<anchor_spl::token_interface::TokenInterface as anchor_lang::Ids>::ids"
  generics := []
  reference := runName
  decides := [contractName, runName]
  decidesRequires := [contractName, runName]
  check := fun c => do
    asUnit c.state; asUnit c.args
    let expected := returnedJson (Json.mkObj [
      ("value", Json.arr (InterfaceIdsRef.ids.read.map (fun key => bytesJson key.bytes)).toArray),
      ("same_parent", Json.bool true)]) Json.null
    unless (← field c.outcome "exit").getStr? == .ok "returned" do return ⟨false, expected⟩
    asUnit (← field c.outcome "state")
    let result ← field c.outcome "result"
    let output ← (← (← field result "value").getArr?).toList.mapM pubkey
    let same ← (← field result "same_parent").getBool?
    have required : Solanalib.Contracts.Model.requires contract () () := by
      rw [contract_eq]; trivial
    let _ : Decidable (Solanalib.Contracts.Model.requires contract () ()) := isTrue required
    let check ← decideReturns relation idsReference evaluated () () (fun _ => pure .ids) asUnit
      (fun reference => Json.mkObj [("value", Json.arr (reference.read.map (fun key => bytesJson
        key.bytes)).toArray),
        ("same_parent", Json.bool true)]) (fun _ => Json.null) c.outcome
    pure ⟨decide (Solanalib.Contracts.Model.requires contract () ()) && check.admitted &&
      same && decide (output = InterfaceIdsRef.ids.read), expected⟩

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport
