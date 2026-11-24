/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.Construct

/-!
# Checkers of `Account`/`InterfaceAccount`/`AccountLoader::try_from`

See `Construct.lean` for the scripted instantiations and graph lemmas. Each
checker decides the registered primary model `<..>.try_from_run` (owned
errors) and `<..>.try_from_observation_run` on the record, through the same
observation.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean (Json ToJson toJson)

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.Anchor.Construct

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
  SolanalibTest.Conformance.Library.Runtime

inductive ResultObs where
  | account (value : UInt64) (info : AccountInfo.Value)
  | loader (info : AccountInfo.Value)
  deriving DecidableEq

/-- The whole region and leases after the call (owners included), and the callback log. -/
structure StateObs where
  world : WorldObs
  log : List Event
  deriving DecidableEq

abbrev Reason := AccountInfo.Panic ⊕ String

abbrev CtorObs := Outcome StateObs (Except (Option ErrorValue) ResultObs) Reason Unit

def asReason (r : String) : Option Reason :=
  if r = "RefCell already mutably borrowed" then some (.inl .borrowFailed) else some (.inr r)

def reasonJson : Reason → Json
  | .inl .borrowFailed => "RefCell already mutably borrowed"
  | .inr r => Json.str r

def asResultObs (account : Bool) (j : Json) : Result ResultObs := do
  if account then pure (.account (← asU64 (← field j "value")) (← asInfo (← field j "info")))
  else pure (.loader (← asInfo (← field j "info")))

def resultObsJson : ResultObs → Json
  | .account v i => Json.mkObj [("value", toJson v.toNat), ("info", infoJson i)]
  | .loader i => Json.mkObj [("info", infoJson i)]

def asStateObs (j : Json) : Result StateObs := do
  pure ⟨← asWorldObs j, ← asList asEvent (← field j "log")⟩

def stateObsJson (s : StateObs) : Json := Json.mkObj [("world", worldObsJson s.world),
  ("log", listJson eventJson s.log)]

def ctorObsJson : Option CtorObs → Json
  | none => "<no outcome>"
  | some (.returned v s) => returnedJson (match v with
      | .ok r => okJson (resultObsJson r)
      | .error e => errJson (optionJson errorValueJson e)) (stateObsJson s)
  | some (.unwound r s) => Json.mkObj [("exit", "unwound"), ("reason", reasonJson r), (
    "state",
    stateObsJson s)]
  | some (.terminated _) => Json.mkObj [("exit", "terminated")]

def asCtorObs (account : Bool) (j : Json) : Result (Option CtorObs) :=
  parseOutcome (asExcept (fun e => do pure (some (← asErrorValue e))) (asResultObs account))
    asStateObs
    asReason noReason j

def currentInfo (aux : CAux) (i : AccountInfo.Value) : AccountInfo.Value :=
  { i with owner := aux.ownerAt i.ownerRef }

def current (aux : CAux) : ResultObs → ResultObs
  | .account v i => .account v (currentInfo aux i)
  | .loader i => .loader (currentInfo aux i)

/-- Project a constructor outcome: `err` reads the value of an error in the state.
A returned AccountInfo is observed with its owner read through its owner
reference in the state after the call, as the source reads `*info.owner`; the `owner` field of the
model is an entry snapshot, not a native observation. -/
def project {S V E U T : Type} (input : LoaderInput) (cells : S → AccountInfo.State) (aux : S →
  CAux)
    (err : S → E → Option ErrorValue) (result : V → ResultObs) (reason : U → Reason) :
    Outcome S (Except E V) U T → CtorObs
  | .returned v s => .returned (match v with
      | .ok r => .ok (current (aux s) (result r))
      | .error e => .error (err s e)) ⟨observeWorld input (aux s).owners (cells s), (aux s).log⟩
  | .unwound r s => .unwound (reason r) ⟨observeWorld input (aux s).owners (cells s), (aux s).log⟩
  | .terminated _ => .terminated ()

def obsProject {V : Type} (input : LoaderInput) (result : V → ResultObs) : OOut (Except Error V) →
  CtorObs :=
  project (S := OW) input Prod.fst Prod.snd (fun _ e => some e) result id

def ownedProject {V : Type} (input : LoaderInput) (result : V → ResultObs) : Out (Except OErr V) →
  CtorObs :=
  project (S := W) input Prod.fst (fun s => s.2.2) (fun s e => AnchorErrorOwned.current ownedOps s
    e) result id

def heap0 : Heap := ⟨[], [], Owned.budget, []⟩

structure Inputs where
  input : LoaderInput
  world : AccountInfo.State
  aux : CAux
  args : AccountInfo.Args
  script : Script

def inputs (c : Case) : Result Inputs := do
  let (input, world) ← asWorld c.state
  let info ← infoAt input (← natField c.args "account")
  let owners ← (distinctOf input.entries).mapM fun a => toPubkey a.owner
  pure ⟨input, world, ⟨owners, []⟩, ⟨profile, info⟩, ← asScript (← field c.args "script") info⟩

def both (owned observation : Verdict) : Verdict :=
  ⟨owned.admitted && observation.admitted,
    Json.mkObj [("model", owned.expected), ("observation_model", observation.expected)]⟩

def accountResult (a : Account UInt64) : ResultObs := .account a.value a.info
def interfaceResult (a : InterfaceAccount UInt64) : ResultObs := .account a.account.value
  a.account.info
def loaderResult (l : Loader UInt64) : ResultObs := .loader l.info

def accountChecker : Checker := ofModels
  ("anchor_lang::accounts::account::Account::<'a, T>::try_from") ([("T",
  "conformance_anchor::script::Scripted")])
  ("Solanalib.Specs.AnchorLang.accounts.account.Account.try_from_run (scripted traits, \
    reference heap) " ++
    "+ Solanalib.Specs.AnchorLang.accounts.account.Account.try_from_observation_run \
      (scripted traits)")
  ["Solanalib.Specs.AnchorLang.accounts.account.Account.try_from_run",
    "Solanalib.Specs.AnchorLang.accounts.account.Account.try_from_observation_run"]
  fun c => do
    let i ← inputs c
    let recorded ← asCtorObs true c.outcome
    let owned := decideProjected (O := Out (Except OErr (Account UInt64)))
      (accounts.account.Account.try_from_run (ownedTypes i.script)
        (i.world, (heap0, i.aux)) i.args)
      _ (ownedAccount_graph i.script (i.world, (heap0, i.aux)) i.args) (ownedProject i.input
        accountResult) recorded ctorObsJson
    let observation := decideProjected (O := OOut (Except Error (Account UInt64)))
      (accounts.account.Account.try_from_observation_run (obsIndex
        i.script) (i.world, i.aux) i.args)
      _ (obsAccount_graph i.script (i.world, i.aux) i.args) (obsProject i.input accountResult)
        recorded ctorObsJson
    return [owned, observation]

def interfaceChecker : Checker := ofModels
  ("anchor_lang::accounts::interface_account::InterfaceAccount::<'a, T>::try_from") ([("T",
  "conformance_anchor::script::Scripted")])
  ("Solanalib.Specs.AnchorLang.accounts.interface_account.InterfaceAccount.try_from_run \
    (scripted traits, reference heap) " ++
    "+ \
      Solanalib.Specs.AnchorLang.accounts.interface_account.InterfaceAccount.try_from_obser\
      vation_run (scripted traits)")
  ["Solanalib.Specs.AnchorLang.accounts.interface_account.InterfaceAccount.try_from_run",
    "Solanalib.Specs.AnchorLang.accounts.interface_account.InterfaceAccount.try_from_observ\
      ation_run"]
  fun c => do
    let i ← inputs c
    let recorded ← asCtorObs true c.outcome
    let owned := decideProjected (O := Out (Except OErr (InterfaceAccount UInt64)))
      (accounts.interface_account.InterfaceAccount.try_from_run
        (ownedTypes i.script)
        (i.world, (heap0, i.aux)) i.args)
      _ (ownedInterface_graph i.script (i.world, (heap0, i.aux)) i.args) (ownedProject i.input
        interfaceResult) recorded
      ctorObsJson
    let observation := decideProjected (O := OOut (Except Error (InterfaceAccount UInt64)))
      (accounts.interface_account.InterfaceAccount.try_from_observation_run (obsIndex i.script)
        (i.world, i.aux) i.args)
      _ (obsInterface_graph i.script (i.world, i.aux) i.args) (obsProject i.input interfaceResult)
        recorded ctorObsJson
    return [owned, observation]

def loaderChecker : Checker := ofModels
  ("anchor_lang::accounts::account_loader::AccountLoader::<'info, T>::try_from") ([("T",
  "conformance_anchor::script::Zc")])
  ("Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_run \
    (scripted Owner, reference heap) " ++
    "+ \
      Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_observation\
      _run (scripted Owner)")
  ["Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_run",
    "Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader.try_from_observation_\
      run"]
  fun c => do
    let i ← inputs c
    let recorded ← asCtorObs false c.outcome
    let owned := decideProjected (O := Out (Except OErr (Loader UInt64)))
      (accounts.account_loader.AccountLoader.try_from_run (ownedTypes
        i.script)
        (i.world, (heap0, i.aux)) i.args)
      _ (ownedLoader_graph i.script (i.world, (heap0, i.aux)) i.args) (ownedProject i.input
        loaderResult) recorded
      ctorObsJson
    let observation := decideProjected (O := OOut (Except Error (Loader UInt64)))
      (accounts.account_loader.AccountLoader.try_from_observation_run
        (obsIndex i.script)
        (i.world, i.aux) i.args)
      _ (obsLoader_graph i.script (i.world, i.aux) i.args) (obsProject i.input loaderResult)
        recorded ctorObsJson
    return [owned, observation]

def checkers : List Checker :=
  [accountChecker, interfaceChecker, loaderChecker].map (withFrame [("no syscalls", noSyscalls)])

end SolanalibTest.Conformance.Library.Families.Anchor.Construct
