/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.Values
import Solanalib.Specs.Core.AnchorViewsContracts

/-! Native observations of wrapper fields and actual callback arguments.
Reference equality is observed separately from equality of the Rc aliases.
The wrapper store and its loan identities are ghost; payloads, account fields,
Rc multiplicities, callback events and syscall messages are all compared. -/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.AnchorViews

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorViews
open SolanalibTest.Conformance.Library.Families.Anchor

structure AccountObs where
  key : Solanalib.Runtime.Pubkey
  owner : Solanalib.Runtime.Pubkey
  signer : Bool
  writable : Bool
  executable : Bool
  lamports : Nat
  data : Solanalib.Runtime.Bytes
  deriving DecidableEq

structure Effects where
  account : AccountObs
  counts : List Nat
  trace : List String
  messages : List Solanalib.Runtime.Bytes
  deriving DecidableEq

structure Snapshot where
  payload : Option Nat
  effects : Effects
  deriving DecidableEq

def asMessages (j : Json) : Result (List Solanalib.Runtime.Bytes) := do
  let s ← field j "syscalls"
  unless (← asArray (← field s "replies")).isEmpty do
    throw "wrapper fixture has no scripted syscall replies"
  (← asArray (← field s "log")).mapM fun request => do
    unless (← strField request "syscall") = "sol_log_" do
      throw "unexpected wrapper syscall"
    asBytes (← field request "bytes")

def messagesJson (xs : List Solanalib.Runtime.Bytes) : Json := Json.mkObj [
  ("replies", .arr #[]), ("log", listJson (fun bytes =>
    Json.mkObj [("syscall", "sol_log_"), ("bytes", bytesJson bytes)]) xs)]

def asAccount (j : Json) : Result AccountObs := do
  pure ⟨← keyField j "key", ← keyField j "owner", ← boolField j "signer",
    ← boolField j "writable", ← boolField j "executable",
    ← asUInt 64 (← field j "lamports"), ← asBytes (← field j "data")⟩

def accountJson (a : AccountObs) : Json := Json.mkObj [
  ("key", pubkeyJson a.key), ("owner", pubkeyJson a.owner),
  ("signer", toJson a.signer), ("writable", toJson a.writable),
  ("executable", toJson a.executable), ("lamports", toJson a.lamports),
  ("data", bytesJson a.data)]

def asSnapshot (j : Json) : Result Snapshot := do
  let counts ← asList (asUInt 64) (← field j "counts")
  unless counts.length = 2 do throw "expected both AccountInfo Rc counts"
  pure ⟨← asOption (asUInt 64) (← field j "payload"),
    ⟨← asAccount (← field j "account"), counts,
      ← asList (fun s => s.getStr?) (← field j "trace"), ← asMessages j⟩⟩

def snapshotJson (s : Snapshot) : Json := Json.mkObj [
  ("payload", optionJson toJson s.payload), ("account", accountJson s.effects.account),
  ("counts", listJson toJson s.effects.counts),
  ("trace", listJson Json.str s.effects.trace), ("syscalls", messagesJson s.effects.messages)]

def toInfo (a : AccountObs) : AccountInfo.Value :=
  ⟨a.key, ⟨0⟩, ⟨1⟩, a.owner, 0, a.signer, a.writable, a.executable, ⟨0⟩⟩

def policy : Borrow.Policy := .refCell 64
def guard : Borrow.Guard := ⟨0, 0⟩
def handle : Borrow.Handle := ⟨0⟩

def makeWrapper {P : Type} (value : P) (s : Snapshot) (savedOwner : Bool) : Wrapper P :=
  ⟨⟨value, toInfo s.effects.account⟩, 19,
    if savedOwner then some s.effects.account.owner else none⟩

def makeWorld {P : Type} (value : P) (s : Snapshot) (mode : Option Borrow.Mode)
    (savedOwner : Bool) : World P Effects :=
  (⟨[⟨some (makeWrapper value s savedOwner), policy⟩],
    mode.toList.map fun m => some ⟨handle, m, 0, ()⟩⟩, s.effects)

def observeWorld {P : Type} (display : P → Option Nat) (s : World P Effects) : Snapshot :=
  ⟨(s.1.lookupCell handle).bind fun cell => cell.value.bind fun w => display w.account.value, s.2⟩

def project {P V R U T : Type} (display : P → Option Nat)
    (value : World P Effects → V → R) (unwind : U → String) (terminal : T → String) :
    Outcome (World P Effects) V U T → Outcome Snapshot R String String
  | .returned v s => .returned (value s v) (observeWorld display s)
  | .unwound r s => .unwound (unwind r) (observeWorld display s)
  | .terminated t => .terminated (terminal t)

def impossible : Empty → String := fun e => nomatch e

def outcomeJson {S V : Type} (state : S → Json) (value : V → Json) :
    Outcome S V String String → Json
  | .returned v s => returnedJson (value v) (state s)
  | .unwound r s => Json.mkObj [("exit", "unwound"), ("reason", r), ("state", state s)]
  | .terminated t => Json.mkObj [("exit", "terminated"), ("reason", t)]

def render {V : Type} (value : V → Json) : Option (Outcome Snapshot V String String) → Json :=
  optionJson (outcomeJson snapshotJson value)

structure InfoObs where
  sameInput : Bool
  inReceiver : Bool
  deriving DecidableEq

def asInfoObs (j : Json) : Result InfoObs :=
  return ⟨← boolField j "same_input", ← boolField j "in_receiver"⟩

def infoObsJson (i : InfoObs) : Json := Json.mkObj [
  ("same_input", toJson i.sameInput), ("in_receiver", toJson i.inReceiver)]

def observeInfo {P : Type} (storage : InfoStorage) (s : World P Effects) (r : InfoRef) : InfoObs :=
  let live := (readInfo storage s.1 r).isSome
  ⟨live && decide (r.location = .external 19), live && decide (r.location = .field handle)⟩

structure PayloadObs where
  sameField : Bool
  mutable : Bool
  value : Option Nat
  deriving DecidableEq

def asPayloadObs (j : Json) : Result PayloadObs :=
  return ⟨← boolField j "same_field", ← boolField j "mutable", some (← asUInt 64 (← field j
    "value"))⟩

def payloadObsJson (p : PayloadObs) : Json := Json.mkObj [
  ("same_field", toJson p.sameField), ("mutable", toJson p.mutable), ("value", optionJson toJson
    p.value)]

def observePayload (s : World Nat Effects) (r : PayloadRef) : PayloadObs :=
  ⟨decide (payloadLocation s.1 r = some handle), r.mutable, readPayload s.1 r⟩

structure CloneObs where
  value : Option Nat
  infoSame : Bool
  infoAliases : Bool
  payloadDistinct : Bool
  deriving DecidableEq

def asCloneObs (payload : Bool) (j : Json) : Result CloneObs := do
  let value ← if payload then do pure (some (← asUInt 64 (← field j "value"))) else pure none
  let distinct ← if payload then boolField j "payload_distinct" else pure true
  pure ⟨value, ← boolField j "info_same", ← boolField j "info_aliases", distinct⟩

def cloneObsJson (payload : Bool) (c : CloneObs) : Json := Json.mkObj
  ([("info_same", toJson c.infoSame), ("info_aliases", toJson c.infoAliases)] ++
    if payload then [("value", optionJson toJson c.value), ("payload_distinct", toJson
      c.payloadDistinct)] else [])

def observeClone {P : Type} (storage : InfoStorage) (display : P → Option Nat)
    (s : World P Effects) (h : Borrow.Handle) : CloneObs :=
  match (s.1.lookupCell handle).bind (·.value), (s.1.lookupCell h).bind (·.value) with
  | some original, some result =>
    ⟨display result.account.value,
      match storage with
      | .owned => decide (h = handle)
      | .borrowed => decide (result.infoIdentity = original.infoIdentity),
      decide (result.account.info.lamports = original.account.info.lamports ∧
        result.account.info.data = original.account.info.data), decide (h ≠ handle)⟩
  | _, _ => ⟨none, false, false, false⟩

end SolanalibTest.Conformance.Library.Families.AnchorViews
