/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.World
import SolanalibTest.Conformance.Library.Families.Anchor.Errors
import Solanalib.Specs.AnchorLang.construct
import Solanalib.Specs.AnchorLang.context
import Solanalib.Specs.AnchorLang.log
import Solanalib.Specs.Core.AnchorSpl

/-!
# `ToAccountInfo::to_account_info`, `CpiContext::new_with_signer`, `sol_log_data`

* `to_account_info` at a scripted `AsRef<AccountInfo>` (`Holder`: logs, then
  panics or returns its account). The primary model (`AnchorToInfo.run`) also
  clones both `Rc` fields; its `Rc` provider is instantiated by the strong
  counts of the `Rc`s of the cells, observed natively (`Rc::strong_count`) before and
  after the call. The observation model (`Callback.map clone asRef`) has no
  `Rc` effects and is decided on the log alone.
* `new_with_signer` at `T = anchor_spl::token::Transfer` (three AccountInfos).
  The primary model creates the empty remaining-account vector through the
  registered vector ledger (`Owned.vectorReference`, as its own sample); the
  context is observed through `AnchorContextOwned.observe`.
* `sol_log_data` at the registered sample index (`AnchorLog.sample`, a trace
  sink), with the `sol_log_data` request log of the shim as the trace.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Anchor.Misc

open Solanalib.Contracts.Model Solanalib.Specs.Core SolanalibTest.Conformance.Library.Runtime
open SolanalibTest.Conformance.Library.Families.Anchor.Errors (both outcomeJson renderOpt emptyJson)

/-! ## to_account_info -/

structure HolderArgs where
  info : AccountInfo.Value
  panics : Bool

structure TState where
  counts : List Nat
  log : List String
  deriving DecidableEq

def asRefFn (s : TState) (h : HolderArgs) : Outcome TState AccountInfo.Value String Empty :=
  let s' := { s with log := s.log ++ ["as_ref"] }
  if h.panics then .unwound "script as_ref" s' else .returned h.info s'

def bump (s : TState) (cell : Nat) : TState :=
  { s with counts := s.counts.modify cell (· + 1) }

def toInfoTypes : AnchorToInfo.Types where
  State := TState
  Input := HolderArgs
  Unwind := String
  Terminal := Empty
  asRef := Callback.ofFunction asRefFn
  rc := {
    cloneRc := Callback.ofFunction fun s (_, handle) => .returned () (bump s handle.cell)
    dropRc := Callback.ofFunction fun s (_, handle) => .returned () s }

def cloneFn (s : TState) (info : AccountInfo.Value) : Outcome TState AccountInfo.Value Empty Empty
  :=
  .returned (AccountInfo.clone info) (bump (bump s info.lamports.cell) info.data.cell)

def cloneG (s : TState) (x : AccountInfoRc.Field × Borrow.Handle) : Outcome TState Unit Empty Empty
  :=
  .returned () (bump s x.2.cell)

theorem clone_graph (after : TState) (info : AccountInfo.Value) :
    PGraph (AccountInfoRc.lift (Unwind := String) (AccountInfoRc.cloneCall toInfoTypes.rc) after
      info)
      (some (AccountInfoRc.liftOutcome (cloneFn after info))) := by
  have h : PGraph (AccountInfoRc.cloneCall toInfoTypes.rc after info) (some (cloneFn after info)) :=
    PGraph.bind (run := fun state (_ : Unit) => toInfoTypes.rc.cloneRc state (.lamports,
      info.lamports))
      (PGraph.ofFunction cloneG after (.lamports, info.lamports))
      (fun _ mid => PGraph.map (run := fun state (_ : Unit) => toInfoTypes.rc.cloneRc state (.data,
        info.data))
        (fun _ => AccountInfo.clone info) (PGraph.ofFunction cloneG mid (.data, info.data)))
  exact PGraph.exists_eq _ h

theorem toInfo_graph (before : TState) (h : HolderArgs) :
    PGraph (AnchorToInfo.run toInfoTypes before h)
      ((some (asRefFn before h)).bind (PGraph.bindK fun info after =>
        some (AccountInfoRc.liftOutcome (cloneFn after info)))) :=
  PGraph.bind (PGraph.ofFunction asRefFn before h) fun info after => clone_graph after info

def obsAsRef (log : List String) (h : HolderArgs) : Outcome (List String) AccountInfo.Value String
  Empty :=
  match asRefFn ⟨[], log⟩ h with
  | .returned v s => .returned v s.log
  | .unwound r s => .unwound r s.log
  | .terminated t => .terminated t

def obsIndex : Solanalib.Specs.Core.AnchorAccount.ToInfoIndex :=
  ⟨List String, HolderArgs, String, Empty, Callback.ofFunction obsAsRef⟩

def asTState (j : Json) : Result TState := do
  pure ⟨← asList (fun x => x.getNat?) (← field j "counts"), ← asList (fun x => x.getStr?) (← field
    j "log")⟩

def tstateJson (s : TState) : Json :=
  Json.mkObj [("counts", listJson toJson s.counts), ("log", listJson Json.str s.log)]

def toInfoChecker : Checker := ofModels
  ("<T as anchor_lang::ToAccountInfo<'info>>::to_account_info") ([("T",
  "conformance_anchor::accounts::Holder")])
  ("Solanalib.Specs.AnchorLang.ToAccountInfo.to_account_info_run (scripted AsRef, Rc \
    strong counts) " ++
    "+ Solanalib.Specs.AnchorLang.ToAccountInfo.to_account_info_observation_run (scripted \
      AsRef)")
  ["Solanalib.Specs.AnchorLang.ToAccountInfo.to_account_info_run",
    "Solanalib.Specs.AnchorLang.ToAccountInfo.to_account_info_observation_run"]
  fun c => do
    let input ← loaderInput (← field c.state "input")
    let info ← infoAt input (← natField c.args "account")
    let h : HolderArgs := ⟨info, ← boolField c.args "panics"⟩
    let before ← asTState c.state
    let recorded ← parseOutcome asInfo asTState (fun r => some r) noReason c.outcome
    let owned := decideProjected (O := Outcome TState AccountInfo.Value String Empty)
      (Solanalib.Specs.AnchorLang.ToAccountInfo.to_account_info_run toInfoTypes before h) _
        (toInfo_graph before h) id recorded
      (renderOpt (outcomeJson tstateJson infoJson Json.str emptyJson))
    let obsRecorded : Option (Outcome (List String) AccountInfo.Value String Empty) := recorded.map
      fun
      | .returned v s => .returned v s.log
      | .unwound r s => .unwound r s.log
      | .terminated t => .terminated t
    let observation := decideProjected (O := Outcome (List String) AccountInfo.Value String Empty)
      (Solanalib.Specs.AnchorLang.ToAccountInfo.to_account_info_observation_run obsIndex before.log
        h) _
      (PGraph.map AccountInfo.clone (PGraph.ofFunction obsAsRef before.log h)) id obsRecorded
      (renderOpt (outcomeJson (listJson Json.str) infoJson Json.str emptyJson))
    return [owned, observation]

/-! ## new_with_signer -/

abbrev Accounts := AnchorSpl.TransferAccounts

def ownedTypes : AnchorContextOwned.Types where
  State := Owned.VectorState AccountInfo.Value
  Accounts := Accounts
  Resource := Nat
  Unwind := Empty
  Terminal := Empty
  remaining := Owned.vectorReference

def obsIdx : Solanalib.Specs.AnchorLang.context.CpiContext.ObservationIndex := ⟨Unit, Accounts,
  AccountInfo.Value⟩

abbrev Ctx := AnchorContext.Value Accounts AccountInfo.Value

def asSeeds (j : Json) : Result AnchorContext.SignerSeeds := asList (asList asBytes) j

def seedsJson (s : AnchorContext.SignerSeeds) : Json := listJson (listJson bytesJson) s

def asCtx (j : Json) : Result Ctx := do
  let a ← field j "accounts"
  pure ⟨⟨← asInfo (← field a "from"), ← asInfo (← field a "to"), ← asInfo (← field a
    "authority")⟩,
    ← asList asInfo (← field j "remaining_accounts"), ← keyField j "program_id", ← asSeeds (← field
      j "signer_seeds")⟩

def ctxJson (x : Ctx) : Json := Json.mkObj [
  ("accounts", Json.mkObj [("from", infoJson x.accounts.source), ("to", infoJson
    x.accounts.destination),
    ("authority", infoJson x.accounts.authority)]),
  ("remaining_accounts", listJson infoJson x.remainingAccounts), ("program_id", pubkeyJson
    x.programId),
  ("signer_seeds", seedsJson x.signerSeeds)]

def contextChecker : Checker := ofModels
  ("anchor_lang::context::CpiContext::<'a, 'b, 'c, 'info, T>::new_with_signer") ([("T",
  "anchor_spl::token::Transfer<'_>")])
  ("Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_run (vector ledger) " ++
    "+ Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_observation_run")
  ["Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_run",
    "Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_observation_run"]
  fun c => do
    let input ← loaderInput (← field c.state "input")
    let a ← field c.args "accounts"
    let accounts : Accounts := ⟨← infoAt input (← natField a "from"), ← infoAt input (← natField a
      "to"),
      ← infoAt input (← natField a "authority")⟩
    let args : AnchorContext.NewWithSignerArgs Accounts :=
      ⟨← keyField c.args "program_id", accounts, ← asSeeds (← field c.args "signer_seeds")⟩
    let recorded ← parseOutcome asCtx (fun _ => pure ()) noReason noReason c.outcome
    -- Primary: the vector ledger is ghost state; the context is observed through `observe`.
    let ownedRel := Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_run ownedTypes []
      args
    have ownedGraph : PGraph ownedRel (some (.returned (AnchorContextOwned.newWithSigner ownedTypes
      [] args).1
        (AnchorContextOwned.newWithSigner ownedTypes [] args).2)) := by
      intro o
      exact (returnsOf_iff _ _ _ o).trans (by
        constructor
        · intro h; rw [← h]
        · intro h; exact Option.some.inj h)
    let project : Outcome (Owned.VectorState AccountInfo.Value)
        (AnchorContextOwned.Value Accounts Nat) Empty Empty → Option (Outcome Unit Ctx Empty Empty)
          := fun
      | .returned v s => (AnchorContextOwned.observe ownedTypes s v).map fun x => .returned x ()
      | _ => none
    let owned := decideProjected ownedRel _ ownedGraph project (recorded.map some)
      (fun o => match o with
        | some (some x) => outcomeJson (fun _ => .null) ctxJson emptyJson emptyJson x
        | _ => "<no outcome>")
    let observation := Errors.decideRet (S := Unit) (V := Ctx)
      (Solanalib.Specs.AnchorLang.context.CpiContext.new_with_signer_observation_run obsIdx)
      AnchorContext.newWithSignerReference rfl () args recorded
      (outcomeJson (fun _ => .null) ctxJson emptyJson emptyJson)
    return [owned, observation]

/-! ## sol_log_data -/

def asLogEvents (state : Json) : Result (List Log.Event) := do
  let s ← syscallsOf state
  s.log.mapM fun r => do
    unless r.syscall = "sol_log_data" do throw s!"unexpected syscall {r.syscall}"
    pure (.data (← r.slices "fields"))

def eventJson : Log.Event → Json
  | .data fs => tagged "data" (listJson bytesJson fs)
  | _ => "other"

def logChecker : Checker := ofModel ("anchor_lang::solana_program::log::sol_log_data") ([])
  "Solanalib.Specs.AnchorLang.solana_program.log.sol_log_data_run"
  fun c => do
    let before ← asLogEvents c.state
    let fields ← asList asBytes (← field c.args "fields")
    let recorded ← parseOutcome (Unwind := String) (Terminal := String) asUnit asLogEvents noReason
      noReason c.outcome
    let rel := Solanalib.Specs.AnchorLang.solana_program.log.sol_log_data_run
      Solanalib.Specs.AnchorLang.solana_program.log.sol_log_data_sample
      before fields
    pure (decideProjected (O := Outcome (List Log.Event) Unit String String) rel _
      (PGraph.ofFunction Log.appendEvent before (.data fields)) id recorded
      (renderOpt (outcomeJson (listJson eventJson) (fun _ => .null) Json.str Json.str)))

/-- Replies unchanged (sol_log_data consumes none; its log is the trace of the model). -/
def repliesUnchanged (c : Case) : Result Bool := do
  pure (decide ((← syscallsOf (← outcomeState c)).replies = (← syscallsOf c.state).replies))

def checkers : List Checker := [
  withFrame [("no syscalls", noSyscalls), ("accounts unchanged", accountsUnchanged)] toInfoChecker,
  withFrame [("no syscalls", noSyscalls), ("accounts unchanged", accountsUnchanged)] contextChecker,
  withFrame [("replies unchanged", repliesUnchanged)] logChecker]

end SolanalibTest.Conformance.Library.Families.Anchor.Misc
