/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.AnchorLang.system_program
import SolanalibTest.Conformance.Library.Families.AnchorSystem.Graph
import SolanalibTest.Conformance.Library.BorshCommon

/-! The native projection records current instruction bytes, ordered account
identities/seeds, Rc counts, caller-visible mutation and resource retirement.
The complete registered relation is decided through `run_graph`; the only
source behavior replaced in the native fixture is the whole CPI signature. -/

set_option autoImplicit false

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorSystem

open Lean (Json toJson)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSystem
open SolanalibTest.Conformance.Library.Families.Anchor
open SolanalibTest.Conformance.Library.Borsh (asList listJson)

def identity (account : AccountInfo.Value) : Nat :=
  match account.lamports.cell with
  | 2 => 0 | 4 => 1 | 6 => 2 | 18 => 3 | _ => 4

def requestJson (counts : List (List Nat)) (request : CpiRequest.Request AccountInfo.Value) : Json
  :=
  Json.mkObj [
    ("instruction", Json.mkObj [
      ("program", bytesJson request.instruction.programId.bytes),
      ("metas", listJson (fun entry => Json.mkObj [("key", bytesJson entry.key.bytes),
        ("signer", toJson (entry.signerByte != 0)), ("writable", toJson (entry.writableByte !=
          0))]) request.instruction.metas),
      ("data", bytesJson request.instruction.data)]),
    ("accounts", listJson (fun account => toJson (identity account)) request.accounts),
    ("signers", listJson (listJson bytesJson) request.signers),
    ("counts", listJson (fun account => toJson (counts[identity account]?.getD []))
      request.accounts)]

def countDrops (counts : List (List Nat)) (events : List AccountInfoRc.Event) : List (List Nat) :=
  events.foldl (fun counts event => match event with
    | .drop field handle =>
      let i := match handle.cell / 2 with | 1 => 0 | 2 => 1 | 3 => 2 | 9 => 3 | _ => 4
      let j := match field with | .lamports => 0 | .data => 1
      counts.modify i (fun pair => pair.modify j (· - 1))
    | .clone field handle =>
      let i := match handle.cell / 2 with | 1 => 0 | 2 => 1 | 3 => 2 | 9 => 3 | _ => 4
      let j := match field with | .lamports => 0 | .data => 1
      counts.modify i (fun pair => pair.modify j (· + 1))) counts

def cellsJson : List Nat → List Json
  | lamports :: first :: second :: third :: rest =>
    Json.mkObj [("lamports", toJson lamports),
      ("data", bytesJson [UInt8.ofNat first, UInt8.ofNat second, UInt8.ofNat third])] :: cellsJson
        rest
  | _ => []

def readCells (value : Json) : Result (List Nat) := do
  let cells ← asList (fun entry => do
    let lamports ← asUInt 64 (← field entry "lamports")
    let bytes ← asBytes (← field entry "data")
    unless bytes.length = 3 do throw "fixture cell must contain three bytes"
    pure (lamports :: bytes.map UInt8.toNat)) value
  unless cells.length = 4 do throw "fixture has four stable account identities"
  pure cells.flatten

def programError (profile : Profile) (borsh : Bool) : profile.Program Nat :=
  match profile with
  | .inlineLegacy | .boxedLegacy => if borsh then .borshIoError 0 else .custom 77
  | .boxedModern => .custom 77

def provider (profile : Profile) (mode : String) (borsh : Bool)
    (before : State profile) (request : CpiRequest.Request AccountInfo.Value) : InvokeOut profile :=
  let after := { before with
    calls := before.calls ++ [request]
    effects := (before.effects.modify 0 (· + 101)).modify 1 (· + 7) }
  if mode = "ok" then .returned (.ok ()) after
  else if mode = "error" then .returned (.error (programError profile borsh)) after
  else if mode = "unwind" then .unwound 91 after
  else .terminated 92

/-- The opaque provider receives this request and these Rc counts at entry.
Its terminal result carries no state, so retain the entry observation separately. -/
structure ProviderObservation (profile : Profile) where
  request : CpiRequest.Request AccountInfo.Value
  counts : List (List Nat)
  exit : InvokeOut profile

def observeProvider (profile : Profile) (counts : List (List Nat)) (mode : String) (borsh : Bool)
    (before : State profile) (current : CpiRequest.Request AccountInfo.Value) : ProviderObservation
      profile :=
  ⟨current, countDrops counts before.rcEvents, provider profile mode borsh before current⟩

def observedInvoke (profile : Profile) (counts : List (List Nat)) (mode : String) (borsh : Bool)
    (before : State profile) (current : CpiRequest.Request AccountInfo.Value) : InvokeOut profile :=
  (observeProvider profile counts mode borsh before current).exit

/-- Recording the input changes no provider outcome or shared-state effect. -/
theorem observedInvoke_eq_provider (profile : Profile) (counts : List (List Nat))
    (mode : String) (borsh : Bool) :
    observedInvoke profile counts mode borsh = provider profile mode borsh := rfl

/-- Read the current allocated instruction at the same point as `invokeFn`,
then capture the exact input of the provider used by the registered run. -/
def observeInvocation (profile : Profile) (counts : List (List Nat)) (mode : String) (borsh : Bool)
    {operation : Operation} (args : Args (Sample.index profile).resources profile.context operation)
    (value : InstructionBuilder.Value (Sample.index profile).resources.types.builder)
    (before : State profile) : Option (ProviderObservation profile) :=
  (request before args value).map (observeProvider profile counts mode borsh before)

/-- This is the actual finite construction prefix, not a successful replacement
run. In particular, terminal detail never rebuilds an instruction from entry args. -/
def observedInvocation (profile : Profile) (counts : List (List Nat)) (mode : String) (borsh : Bool)
    {operation : Operation} (before : State profile)
    (args : Args (Sample.index profile).resources profile.context operation) :
    Option (ProviderObservation profile) :=
  observeInvocation profile counts mode borsh args (Sample.builtValue before)
    (Sample.afterBuild before args)

/-- Every actual construction return gives this same provider observation.
The equality uses the complete build result, including its state and resources. -/
theorem observedInvocation_after_build (profile : Profile) (counts : List (List Nat))
    (mode : String) (borsh : Bool) {operation : Operation} (before : State profile)
    (args : Args (Sample.index profile).resources profile.context operation)
    (value : InstructionBuilder.Value (Sample.index profile).resources.types.builder)
    (after : State profile) (built : build before args (.returned value after)) :
    observedInvocation profile counts mode borsh before args =
      observeInvocation profile counts mode borsh args value after := by
  have exactBuild := (Sample.build_exact before args (.returned value after)).mp built
  cases exactBuild
  rfl

theorem observedInvocation_actual (profile : Profile) (counts : List (List Nat))
    (mode : String) (borsh : Bool) {operation : Operation} (before : State profile)
    (args : Args (Sample.index profile).resources profile.context operation)
    (seen : ProviderObservation profile)
    (found : observedInvocation profile counts mode borsh before args = some seen) :
    ∃ (after : State profile) (current : CpiRequest.Request AccountInfo.Value),
      build before args (.returned (Sample.builtValue before) after) ∧
      request after args (Sample.builtValue before) = some current ∧
      observeProvider profile counts mode borsh after current = seen := by
  cases requested : request (Sample.afterBuild before args) args (Sample.builtValue before) with
  | none => simp [observedInvocation, observeInvocation, requested] at found
  | some current =>
    have same : observeProvider profile counts mode borsh (Sample.afterBuild before args) current =
      seen :=
      Option.some.inj (by simpa only [observedInvocation, observeInvocation, requested,
        Option.map_some] using found)
    exact ⟨Sample.afterBuild before args, current, Sample.build_returns before args, requested,
      same⟩

/-- A captured terminal input is a reached provider call of the complete
registered relation. No after-state is supplied for that terminal exit. -/
theorem observedInvocation_terminal (profile : Profile) (counts : List (List Nat))
    (mode : String) (borsh : Bool) {operation : Operation} (before : State profile)
    (args : Args (Sample.index profile).resources profile.context operation)
    (seen : ProviderObservation profile) (reason : Nat)
    (found : observedInvocation profile counts mode borsh before args = some seen)
    (terminal : seen.exit = .terminated reason) :
    Solanalib.Specs.Core.AnchorSystem.run
      (recordedIndex profile (observedInvoke profile counts mode borsh)) before args (.terminated
        reason) := by
  obtain ⟨after, current, built, requested, same⟩ :=
    observedInvocation_actual profile counts mode borsh before args seen found
  have called : (recordedIndex profile (observedInvoke profile counts mode borsh)).invoke
      after current (.terminated reason) := by
    change (observeProvider profile counts mode borsh after current).exit = .terminated reason
    rw [same]
    exact terminal
  exact run_after_build (recordedIndex profile (observedInvoke profile counts mode borsh))
    args before after (Sample.builtValue before) (.terminated reason) (.terminated reason) built
    (invokeAndConvert_terminal (recordedIndex profile (observedInvoke profile counts mode borsh))
      args (Sample.builtValue before) after current reason requested called) rfl
/-- The native fixture puts its sentinel in the first byte. `Pubkey.ofNat`
uses the opposite byte order and is deliberately not used for this input. -/
def fixtureKey (number : Nat) : _root_.Solanalib.Runtime.Pubkey :=
  _root_.Solanalib.Runtime.Pubkey.ofBytes (_root_.Solanalib.Runtime.leBytes 32 number)

def fixtureInfo (number : Nat) : AccountInfo.Value :=
  { Sample.info number with key := fixtureKey number }

def modelArgs (profile : Profile) (operation : Operation) (alias : Bool) (amount : UInt64) :
    Args (Sample.index profile).resources profile.context operation :=
  { Sample.args profile operation with
    accounts := match operation with
      | .allocate | .assign => fixtureInfo 1
      | .createAccount | .transfer => (fixtureInfo 1, fixtureInfo (if alias then 1 else 2))
    parameters := match operation with
      | .allocate | .transfer => amount
      | .assign => fixtureKey 23
      | .createAccount => (amount, (4097 : UInt64), fixtureKey 23) }

def expectedCounts (profile : Profile) (operation : Operation) (alias : Bool) : List (List Nat) :=
  let pair := operation == .createAccount || operation == .transfer
  let first := 3 + if pair && alias then 1 else 0
  let second := 1 + if pair && !alias then 1 else 0
  let program := if profile == .boxedModern then 1 else 2
  [[first, first], [second, second], [3, 3], [program, program]]

def errorJson (profile : Profile) (state : State profile) (error : Error (Sample.index profile)) :
  Json :=
  match AnchorErrorOperations.currentPayload profile.storage (Sample.errors profile) state error
    with
  | some (.program payload) =>
    let program := match profile, payload.error with
      | .inlineLegacy, .custom value | .boxedLegacy, .custom value | .boxedModern, .custom value =>
        Json.mkObj [("custom", toJson value.toNat)]
      | .inlineLegacy, .borshIoError resource | .boxedLegacy, .borshIoError resource =>
        Json.mkObj [("borsh", toJson ((state.strings[resource]?.join).getD "<missing>"))]
      | _, _ => Json.str "<unexpected-error>"
    Json.mkObj [("program_error", program),
      ("origin", (payload.origin.map fun value => toJson (reprStr value)).getD Json.null),
      ("compared", (payload.compared.map fun value => toJson (reprStr value)).getD Json.null),
      ("boxed", toJson (profile != .inlineLegacy))]
  | _ => Json.str "<missing-program-error>"

/-- Resource identity is independent of equal String contents. The owned Borsh resource of the
provider is 0; non-String errors have no identity observation. -/
def sameString (profile : Profile) (state : State profile) : Except (Error (Sample.index profile))
  Unit → Json
  | .ok () => Json.null
  | .error error =>
    match AnchorErrorOperations.currentPayload profile.storage (Sample.errors profile) state error
      with
    | some (.program payload) =>
      match Sample.programStrings profile payload.error with
      | [] => Json.null
      | resources => toJson (resources == [0])
    | _ => Json.null

def stateJson (profile : Profile) (counts : List (List Nat))
    (callCounts : Option (List (List Nat))) (sameString : Json) (state : State profile) : Json :=
  Json.mkObj [("cells", toJson (cellsJson state.effects)),
    ("counts", toJson (countDrops counts state.rcEvents)),
    ("calls", (callCounts.map fun current => listJson (requestJson current) state.calls).getD
      Json.null),
    ("freed", toJson ((state.construction.events.filterMap fun event =>
        if event = 40 then some "metas" else if event = 41 then some "data" else none) ++
      if state.remaining.current 0 = none then ["remaining"] else [])),
    ("fresh_boxes", toJson (state.boxes.filterMap id).length), ("same_string", sameString)]

/-- Only the known terminal provider exposes this captured request. An
unrecognized reason cannot borrow the label or request of that provider. -/
def terminalDetail {profile : Profile} (seen : Option (ProviderObservation profile)) (reason : Nat)
  : Json :=
  if reason != 92 then Json.null else
    match seen with
    | some observed => match observed.exit with
      | .terminated actual =>
        if actual == reason then requestJson observed.counts observed.request else Json.null
      | _ => Json.null
    | none => Json.null

def project (profile : Profile) (counts : List (List Nat))
    (seen : Option (ProviderObservation profile)) : Out profile → Json
  | .returned value state => returnedJson
      (exceptJson (errorJson profile state) (fun _ => Json.null) value)
      (stateJson profile counts (seen.map (·.counts)) (sameString profile state value) state)
  | .unwound reason state => Json.mkObj [("exit", toJson "unwound"),
      ("reason", if reason == 91 then toJson "opaque invoke unwind" else toJson reason),
      ("state", stateJson profile counts (seen.map (·.counts)) Json.null state)]
  | .terminated reason => Json.mkObj [("exit", toJson "terminated"),
      ("reason", if reason == 92 then toJson "opaque invoke terminal" else toJson reason),
      ("request", terminalDetail seen reason)]

abbrev Contract (profile : Profile) (operation : Operation) :=
  (index : Index profile) → Solanalib.Contracts.Model index.resources.types.State
    (Args index.resources profile.context operation) (Except (Error index) Unit)
    index.resources.types.Unwind index.resources.types.Terminal

/-- At the resource interpretation construction of this fixture always creates
readable current vectors; the opaque invocation still has all finite exits. -/
def fixtureReady (profile : Profile) (operation : Operation)
    (contract : Contract profile operation) (exactContract : contract = (family profile
      operation).contract)
    (invoke : State profile → CpiRequest.Request AccountInfo.Value → InvokeOut profile)
    (before : State profile) (args : Args (Sample.index profile).resources profile.context
      operation) :
    Decidable ((contract (recordedIndex profile invoke)).requires before args) :=
  .isTrue (by rw [exactContract]; exact Sample.build_ready before args)

def checker (profile : Profile) (operation : Operation) (sourceName referenceName : String)
    (selected : FamilyRun (family profile operation)) (referenceExact : selected = reference
      profile operation)
    (contract : Contract profile operation) (contractExact : contract = (family profile
      operation).contract) : Checker where
  function := sourceName
  generics := []
  reference := referenceName ++ " (projected wrapper; explicit whole-signature invocation \
    provider)"
  decides := [referenceName]
  decidesRequires := [referenceName]
  check := fun record => do
    let actualOperation ← (← field record.args "operation").getStr?
    let expectedOperation := match operation with
      | .allocate => "allocate" | .assign => "assign"
      | .createAccount => "create_account" | .transfer => "transfer"
    unless actualOperation = expectedOperation do throw "operation does not match selected \
      function"
    let mode ← (← field record.args "mode").getStr?
    unless mode ∈ ["ok", "error", "unwind", "terminal"] do throw "unknown provider script"
    let alias ← (← field record.args "alias").getBool?
    let borsh ← (← field record.args "borsh").getBool?
    unless !borsh || (profile != .boxedModern && mode == "error") do
      throw "unavailable Borsh error script"
    let amount := UInt64.ofNat (← asUInt 64 (← field record.args "amount"))
    let counts ← asList (asList Json.getNat?) (← field record.state "counts")
    unless counts = expectedCounts profile operation alias do
      throw "invalid prepared Rc multiplicity"
    let effects ← readCells (← field record.state "cells")
    let before : State profile := { Sample.before profile with effects, strings := [some
      "owned provider error"] }
    let args := modelArgs profile operation alias amount
    let invoke := observedInvoke profile counts mode borsh
    let index := recordedIndex profile invoke
    let seen := observedInvocation profile counts mode borsh before args
    have : Decidable ((contract index).requires before args) :=
      fixtureReady profile operation contract contractExact _ before args
    unless decide ((contract index).requires before args) do
      throw "unreadable constructed resources"
    have graph : PGraph (selected index before args) (runFn profile invoke before args) := by
      rw [referenceExact]
      exact run_graph profile _ before args
    pure (decideProjected (selected index before args) _ graph
      (fun outcome => (project profile counts seen outcome).compress)
      (some record.outcome.compress) (fun value => match value with
        | none => Json.null
        | some text => (Json.parse text).toOption.getD (Json.str text)))

def checkers : List Checker := [
    checker .boxedLegacy .allocate "anchor_lang::system_program::allocate"
      "Solanalib.Specs.AnchorLang.system_program.allocate_run"
        system_program.allocate_run rfl
      system_program.allocate_contract.contract rfl,
    checker .boxedLegacy .assign "anchor_lang::system_program::assign"
      "Solanalib.Specs.AnchorLang.system_program.assign_run"
        system_program.assign_run rfl
      system_program.assign_contract.contract rfl,
    checker .boxedLegacy .createAccount "anchor_lang::system_program::create_account"
      "Solanalib.Specs.AnchorLang.system_program.create_account_run"
        system_program.create_account_run rfl
      system_program.create_account_contract.contract rfl,
    checker .boxedLegacy .transfer "anchor_lang::system_program::transfer"
      "Solanalib.Specs.AnchorLang.system_program.transfer_run"
        system_program.transfer_run rfl
      system_program.transfer_contract.contract rfl]

def idChecker : Checker where
  function := "<anchor_lang::system_program::System as anchor_lang::Id>::id"
  generics := []
  reference := "Solanalib.Specs.AnchorLang.system_program.System.id_run"
  decides := ["Solanalib.Specs.AnchorLang.system_program.System.id_run"]
  check := fun record => do
    let _ ← asUnit record.state
    let _ ← asUnit record.args
    pure (decideProjected (returnsOf (Unwind := Empty) (Terminal := Empty)
        system_program.System.id_run () ())
      (some (.returned Instruction.systemProgramId ()))
      (fun outcome => by
        cases outcome with
        | returned value state =>
          cases state
          simp [returnsOf, system_program.System.id_run, eq_comm]
        | unwound impossible _ => cases impossible
        | terminated impossible => cases impossible)
      (fun outcome => match outcome with
        | .returned value _ => (returnedJson (bytesJson value.bytes) Json.null).compress
        | .unwound impossible _ => nomatch impossible
        | .terminated impossible => nomatch impossible)
      (some record.outcome.compress) (fun value => match value with
        | none => Json.null
        | some text => (Json.parse text).toOption.getD (Json.str text)))


end SolanalibTest.Conformance.Library.Families.AnchorSystem

namespace SolanalibTest.Conformance.Library.Families.AnchorSystem

def modernCheckers : List Checker := [
  checker .boxedModern .allocate "anchor_lang::system_program::allocate"
      "Solanalib.Specs.AnchorLang.system_program.allocate_unit_borsh_run"
        system_program.allocate_unit_borsh_run rfl
      system_program.allocate_unit_borsh_contract.contract rfl,
  checker .boxedModern .assign "anchor_lang::system_program::assign"
      "Solanalib.Specs.AnchorLang.system_program.assign_unit_borsh_run"
        system_program.assign_unit_borsh_run rfl
      system_program.assign_unit_borsh_contract.contract rfl,
  checker .boxedModern .createAccount "anchor_lang::system_program::create_account"
      "Solanalib.Specs.AnchorLang.system_program.create_account_unit_borsh_run"
        system_program.create_account_unit_borsh_run rfl
      system_program.create_account_unit_borsh_contract.contract rfl,
  checker .boxedModern .transfer "anchor_lang::system_program::transfer"
      "Solanalib.Specs.AnchorLang.system_program.transfer_unit_borsh_run"
        system_program.transfer_unit_borsh_run rfl
      system_program.transfer_unit_borsh_contract.contract rfl]

end SolanalibTest.Conformance.Library.Families.AnchorSystem

namespace SolanalibTest.Conformance.Library.Families.AnchorSystem

open Lean (Json toJson)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSystem
open SolanalibTest.Conformance.Library.Families.Anchor
open SolanalibTest.Conformance.Library.Borsh (asList listJson)

def inlineLegacyCheckers : List Checker :=
  [
    checker .inlineLegacy .allocate "anchor_lang::system_program::allocate"
      "Solanalib.Specs.AnchorLang.system_program.allocate_inline_borsh_run"
        system_program.allocate_inline_borsh_run rfl
      system_program.allocate_inline_borsh_contract.contract rfl,
    checker .inlineLegacy .assign "anchor_lang::system_program::assign"
      "Solanalib.Specs.AnchorLang.system_program.assign_inline_borsh_run"
        system_program.assign_inline_borsh_run rfl
      system_program.assign_inline_borsh_contract.contract rfl,
    checker .inlineLegacy .createAccount "anchor_lang::system_program::create_account"
      "Solanalib.Specs.AnchorLang.system_program.create_account_inline_borsh_run"
        system_program.create_account_inline_borsh_run rfl
      system_program.create_account_inline_borsh_contract.contract rfl,
    checker .inlineLegacy .transfer "anchor_lang::system_program::transfer"
      "Solanalib.Specs.AnchorLang.system_program.transfer_inline_borsh_run"
        system_program.transfer_inline_borsh_run rfl
      system_program.transfer_inline_borsh_contract.contract rfl]

end SolanalibTest.Conformance.Library.Families.AnchorSystem
