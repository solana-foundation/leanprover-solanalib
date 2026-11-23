/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck
import Solanalib.Specs.AnchorLang.account_loader

/-! Executable graphs of the registered unchecked and account-slice loader
references. The existing Owner script and owned error heap are reused; record
identity and the mutable slice are observed independently of aliased cells. -/

set_option autoImplicit false

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorLoader.Construct

open Lean (Json toJson)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor
open Anchor.Construct (Script W Out OErr ownedTypes ownedFn ownedGraph ownedOps heap0
  ownedOwnerCheckFn ownedOwnerCheck_graph ownedLoaderFn ownedLoader_graph resultK effectsBind_graph)
open Anchor.RequiresAccounts

def types (script : Script) : AnchorLoader.ConstructorTypes :=
  AnchorLoader.ConstructorTypes.ofConstructor (ownedTypes script)

def uncheckedFn (script : Script) (before : W) (args : AnchorLoader.UncheckedArgs) :
    Option (Out (Except OErr (AnchorLoader.Value UInt64))) :=
  (ownedOwnerCheckFn script before args.info).bind
    (Anchor.PGraph.bindK (resultK fun _ after => some (.returned (.ok ⟨args.account⟩) after)))

theorem unchecked_graph (script : Script) (before : W) (args : AnchorLoader.UncheckedArgs) :
    Anchor.PGraph (AnchorLoader.unchecked (types script) before args) (uncheckedFn script before
      args) := by
  apply effectsBind_graph
  · exact ownedOwnerCheck_graph script before args.info
  · intro _ after
    exact Anchor.PGraph.eq_left _

theorem ownerReady_iff (script : Script) (before : W) (args : AccountInfo.Args)
    (discriminator : Solanalib.Runtime.Bytes) :
    AnchorConstructOwned.OwnerCheckReady (ownedTypes script) before args ↔
      AnchorConstructOwned.OwnerCheckReady ((types script).constructor discriminator) before args
        := by
  constructor <;>
    intro ready expected after called mismatch name afterName copied message afterMessage formatted
      resource afterBox boxed
  all_goals
    have admitted := ready expected after called mismatch name afterName copied message
      afterMessage formatted resource afterBox boxed
    refine ⟨admitted.1, ?_⟩
    intro produced second
    cases produced <;> exact admitted.2 _ second

theorem uncheckedReady_iff (script : Script) (before : W) (args : AnchorLoader.UncheckedArgs) :
    ownerCheckReadyB script before args.info = true ↔ AnchorLoader.UncheckedReady (types script)
      before args := by
  exact (ownerCheckReadyB_iff script before args.info).trans (ownerReady_iff script before
    args.info [])

def accountsTypes (script : Script) : AnchorLoader.AccountsTypes :=
  ⟨types script, Nat, Anchor.Loading.disc⟩

def emptyFn (before : W) : Option (Out (Except OErr (AnchorLoader.Value UInt64))) :=
  (Anchor.Construct.depFn (OwnedFn.buildCodeFn ownedFn before
    ⟨AnchorLifecycle.Code.notEnoughKeys.payload.name,
      AnchorLifecycle.Code.notEnoughKeys.payload.code,
      AnchorLifecycle.Code.notEnoughKeys.payload.message⟩)).map (Outcome.map Except.error)

theorem empty_graph (script : Script) (before : W) :
    Anchor.PGraph (AnchorLifecycle.fail (types script).toBase .notEnoughKeys before ()) (emptyFn
      before) :=
  Anchor.PGraph.map _ (Anchor.Construct.dep_graph script (OwnedFn.buildCode_graph ownedGraph before
    _))

def accountsFn (script : Script) (before : AnchorLoader.AccountsState (accountsTypes script))
    (args : AnchorLifecycle.AccountsArgs) :
    Option (Outcome (AnchorLoader.AccountsState (accountsTypes script))
      (Except OErr (AnchorLoader.Value UInt64)) (ConstructorUnwind String) (ConstructorTerminal
        Anchor.Construct.Failure)) :=
  match before.remaining with
  | [] => (emptyFn before.world).map ((AnchorLoader.accountsFocus (accountsTypes
    script)).liftOutcome before)
  | account :: rest =>
    ((ownedLoaderFn script before.world ⟨args.profile, account.info⟩).map
      (Outcome.map (Except.map fun _ => (⟨account⟩ : AnchorLoader.Value UInt64)))).map
        ((AnchorLoader.accountsFocus (accountsTypes script)).liftOutcome { before with remaining :=
          rest })

theorem accounts_graph (script : Script) (before : AnchorLoader.AccountsState (accountsTypes
  script))
    (args : AnchorLifecycle.AccountsArgs) :
    Anchor.PGraph (AnchorLoader.tryAccounts (accountsTypes script) before args) (accountsFn script
      before args) := by
  unfold AnchorLoader.tryAccounts accountsFn
  cases remaining : before.remaining with
  | nil =>
    exact Anchor.PGraph.focusLift (AnchorLoader.accountsFocus (accountsTypes script))
      (b := before) (a := ()) (empty_graph script before.world)
  | cons account rest =>
    exact Anchor.PGraph.focusLift (AnchorLoader.accountsFocus (accountsTypes script))
      (b := { before with remaining := rest })
      (Anchor.PGraph.map (Except.map fun _ => (⟨account⟩ : AnchorLoader.Value UInt64))
        (ownedLoader_graph script before.world ⟨args.profile, account.info⟩))

def accountsReadyB (script : Script) (before : AnchorLoader.AccountsState (accountsTypes script))
    (args : AnchorLifecycle.AccountsArgs) : Bool :=
  match before.remaining with
  | [] => true
  | account :: _ => ownedReadyB .loader script before.world ⟨args.profile, account.info⟩

theorem accountsReadyB_iff (script : Script) (before : AnchorLoader.AccountsState (accountsTypes
  script))
    (args : AnchorLifecycle.AccountsArgs) :
    accountsReadyB script before args = true ↔ AnchorLoader.AccountsReady (accountsTypes script)
      before args := by
  cases remaining : before.remaining with
  | nil => simp only [accountsReadyB, AnchorLoader.AccountsReady, remaining, eq_self, iff_self]
  | cons account rest =>
    simp only [accountsReadyB, AnchorLoader.AccountsReady, remaining]
    apply (ownedReadyB_iff .loader script before.world ⟨args.profile, account.info⟩).trans
    unfold AnchorConstructOwned.Ready
    apply and_congr (ownerReady_iff script before.world ⟨args.profile, account.info⟩
      Anchor.Loading.disc)
    constructor <;> intro ready checked called <;> exact ready checked called

abbrev RefObs := Outcome Anchor.Construct.StateObs (Except (Option ErrorValue) Nat)
  Anchor.Construct.Reason Unit

def project (input : LoaderInput) : Out (Except OErr (AnchorLoader.Value UInt64)) → RefObs
  | .returned result after => .returned
      (result.mapError (AnchorErrorOwned.current ownedOps after) |>.map (·.account.id))
      ⟨observeWorld input after.2.2.owners after.1, after.2.2.log⟩
  | .unwound reason after => .unwound reason
      ⟨observeWorld input after.2.2.owners after.1, after.2.2.log⟩
  | .terminated _ => .terminated ()

def refResult (json : Json) : Result (Except (Option ErrorValue) Nat) :=
  asExcept (fun error => return some (← asErrorValue error)) (fun value => natField value
    "record")
    json

def asRefObs (json : Json) : Result (Option RefObs) :=
  parseOutcome refResult Anchor.Construct.asStateObs Anchor.Construct.asReason noReason json

def refObsJson : Option RefObs → Json
  | none => "<no outcome>"
  | some (.returned result state) => returnedJson
      (exceptJson (optionJson errorValueJson) (fun id => Json.mkObj [("record", toJson id)]) result)
      (Anchor.Construct.stateObsJson state)
  | some (.unwound reason state) => Json.mkObj [("exit", "unwound"),
      ("reason", Anchor.Construct.reasonJson reason), ("state", Anchor.Construct.stateObsJson
        state)]
  | some (.terminated _) => Json.mkObj [("exit", "terminated")]

def uncheckedInputs (record : Case) := do
  let parsed ← Anchor.Construct.inputs record
  let args : AnchorLoader.UncheckedArgs :=
    ⟨profile, ← keyField record.args "program_id", ⟨← natField record.args "account",
      parsed.args.info⟩⟩
  return (parsed, args)

def uncheckedRequires (record : Case) : Result Bool := do
  let (parsed, args) ← uncheckedInputs record
  return Anchor.RequiresCheck.decideBy
    (p :=
      (accounts.account_loader.AccountLoader.try_from_unchecked_contract.contract
      (types parsed.script)).requires (parsed.world, (heap0, parsed.aux)) args) _
    (uncheckedReady_iff parsed.script (parsed.world, (heap0, parsed.aux)) args)

def uncheckedChecker : Checker :=
  let model :=
    "Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_unchecked_ru\
      n"
  withFrame [("no syscalls", noSyscalls)] <| withRequires [
    ("Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_unchecked_r\
      un",
      uncheckedRequires)] <|
    ofModel "anchor_lang::accounts::account_loader::AccountLoader::<'info, \
      T>::try_from_unchecked"
      [("T", "conformance_anchor_loader::script::Zc")] model fun record => do
        let (parsed, args) ← uncheckedInputs record
        let before : W := (parsed.world, (heap0, parsed.aux))
        return decideProjected
          (accounts.account_loader.AccountLoader.try_from_unchecked_run
            (types parsed.script) before args) _ (unchecked_graph parsed.script before args)
          (project parsed.input) (← asRefObs record.outcome) refObsJson

structure AccountsObs where
  world : Anchor.Construct.StateObs
  remaining : List Nat
  bumps : Nat
  reallocs : List Solanalib.Runtime.Pubkey
  deriving DecidableEq

abbrev AccountsOutcome := Outcome AccountsObs (Except (Option ErrorValue) Nat)
  Anchor.Construct.Reason Unit

def accountsStateObs (input : LoaderInput) {script : Script}
    (state : AnchorLoader.AccountsState (accountsTypes script)) : AccountsObs :=
  ⟨⟨observeWorld input state.world.2.2.owners state.world.1, state.world.2.2.log⟩,
    state.remaining.map (·.id), state.bumps, state.reallocs⟩

def projectAccounts (input : LoaderInput) {script : Script} :
    Outcome (AnchorLoader.AccountsState (accountsTypes script)) (Except OErr (AnchorLoader.Value
      UInt64))
      (ConstructorUnwind String) (ConstructorTerminal Anchor.Construct.Failure) → AccountsOutcome
  | .returned result after => .returned
      (result.mapError (AnchorErrorOwned.current ownedOps after.world) |>.map (·.account.id))
      (accountsStateObs input after)
  | .unwound reason after => .unwound reason (accountsStateObs input after)
  | .terminated _ => .terminated ()

def parseAccountsState (json : Json) : Result AccountsObs := do
  return ⟨← Anchor.Construct.asStateObs json, ← asList Json.getNat? (← field json
    "remaining"),
    ← natField json "bumps", ← asList asPubkey (← field json "reallocs")⟩

def accountsObsJson (outcome : Option AccountsOutcome) : Json :=
  Json.str (reprStr (outcome.map fun
    | .returned value state => ("returned", state.remaining, state.bumps, value.toOption)
    | .unwound _ state => ("unwound", state.remaining, state.bumps, none)
    | .terminated _ => ("terminated", [], 0, none)))

def accountsInputs (record : Case) : Result (Σ script : Script,
    LoaderInput × AnchorLoader.AccountsState (accountsTypes script) × AnchorLifecycle.AccountsArgs)
      := do
  let (input, world) ← asWorld record.state
  let indices ← asList Json.getNat? (← field record.state "remaining")
  let remaining ← indices.mapM fun id => do return (⟨id, ← infoAt input id⟩ :
    AnchorLoader.Reference)
  let info := remaining.headD ⟨0, AccountInfo.sampleInfo⟩
  let script ← Anchor.Construct.asScript (← field record.args "script") info.info
  let owners ← (distinctOf input.entries).mapM fun account => toPubkey account.owner
  let before : AnchorLoader.AccountsState (accountsTypes script) :=
    ⟨(world, (heap0, ⟨owners, []⟩)), remaining, ← natField record.state "bumps",
      ← asList asPubkey (← field record.state "reallocs")⟩
  let args : AnchorLifecycle.AccountsArgs :=
    ⟨profile, ← keyField record.args "program_id", ← asBytes (← field record.args
      "instruction_data")⟩
  return ⟨script, input, before, args⟩

def accountsRequires (record : Case) : Result Bool := do
  let ⟨script, _, before, args⟩ ← accountsInputs record
  return Anchor.RequiresCheck.decideBy
    (p :=
      (accounts.account_loader.AccountLoader.try_accounts_contract.contract
      (accountsTypes script)).requires before args) _ (accountsReadyB_iff script before args)

def accountsChecker : Checker :=
  let model := "Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_accoun\
    ts_run"
  withFrame [("no syscalls", noSyscalls)] <| withRequires [
    ("Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_accounts_run",
      accountsRequires)] <|
    ofModel
      "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as \
        anchor_lang::Accounts<'info, B>>::try_accounts"
      [("T", "conformance_anchor_loader::script::Zc"), ("B", "u64")] model fun record => do
        let ⟨script, input, before, args⟩ ← accountsInputs record
        let recorded ← parseOutcome refResult parseAccountsState Anchor.Construct.asReason noReason
          record.outcome
        return decideProjected
          (accounts.account_loader.AccountLoader.try_accounts_run
            (accountsTypes script) before args)
          _ (accounts_graph script before args) (projectAccounts input) recorded accountsObsJson

end SolanalibTest.Conformance.Library.Families.AnchorLoader.Construct
