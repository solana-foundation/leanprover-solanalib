/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Anchor.RequiresCheck
import Solanalib.Specs.AnchorLang.account_loader

/-! Initialization conformance decides the registered owned reference and
its observation facet. The error heap is the existing finite reference heap;
the typed data and every reached allocation admission are decided separately. -/

set_option autoImplicit false

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorLoader.Init

open Lean (Json toJson)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor
open Anchor.Decide Anchor.RequiresAccounts
open Anchor.Construct (pgraph_ite withGuard_graph)
open Anchor.Loading (W Out types ownedFn ownedGraph heap0 depFn dep_graph mapLoadedFn
  mapLoaded_graph)

def buildFn (before : W) (code : AnchorErrorOwned.Code) :=
  depFn (OwnedFn.buildCodeFn ownedFn before code)

theorem build_graph (l : LoadIndex) (before : W) (code : AnchorErrorOwned.Code) :
    Anchor.PGraph (AnchorLoaderInitOwned.build (types l) code before ()) (buildFn before code) :=
  dep_graph l (OwnedFn.buildCode_graph ownedGraph before code)

def panicFn (l : LoadIndex) (args : LoadArgs l) (before : W) (guard : Borrow.Guard) : Option (Out
  l) :=
  if args.profile.aborts then some (.terminated (.inl .sliceBounds))
  else match Borrow.release before.1 guard with
    | (.error _, _) => none
    | (.ok (), after) => some (.unwound .sliceBounds (after, before.2))

theorem panic_graph (l : LoadIndex) (args : LoadArgs l) (before : W) (guard : Borrow.Guard) :
    Anchor.PGraph (AnchorLoaderInitOwned.panic (types l) args before guard .sliceBounds)
      (panicFn l args before guard) := by
  unfold AnchorLoaderInitOwned.panic panicFn
  apply pgraph_ite
  · exact Anchor.PGraph.eq_left _
  · rcases Borrow.release before.1 guard with ⟨released, after⟩
    cases released with
    | error _ => exact Anchor.PGraph.false
    | ok value => cases value; exact Anchor.PGraph.eq_left _

def runFn (l : LoadIndex) (before : W) (args : LoadArgs l) : Option (Out l) :=
  if args.loader.info.isWritable = false then
    (Anchor.Loading.codeFn before .notMutable).map (Outcome.map Except.error)
  else match AccountInfo.tryBorrow .exclusive args.loader.info.data before.1 with
    | (.error failure, during) =>
      (Anchor.Loading.programFn (during, before.2) failure).map (Outcome.map Except.error)
    | (.ok guard, during) => match Borrow.current during guard with
      | .error _ | .ok (_, .lamports _) => none
      | .ok (_, .data bytes) =>
        if bytes.length < l.discriminator.length then panicFn l args (during, before.2) guard
        else if AnchorLoaderInit.hasDiscriminator l.discriminator bytes then
          ((buildFn (during, before.2) AnchorLoaderInitOwned.alreadySet).map
            (Outcome.map Except.error)).bind (AccountInfo.GuardCallback.releaseOutcome guard)
        else mapLoadedFn l args (during, before.2) guard bytes

theorem run_graph (l : LoadIndex) (before : W) (args : LoadArgs l) :
    Anchor.PGraph (AnchorLoaderInitOwned.run (types l) before args) (runFn l before args) := by
  unfold AnchorLoaderInitOwned.run runFn
  apply pgraph_ite
  · exact Anchor.PGraph.map _ (Anchor.Loading.code_graph l before _)
  · rcases AccountInfo.tryBorrow .exclusive args.loader.info.data before.1 with ⟨borrowed, during⟩
    cases borrowed with
    | error failure => exact Anchor.PGraph.map _ (Anchor.Loading.program_graph l _ _)
    | ok guard =>
      dsimp only
      rcases Borrow.current during guard with _ | ⟨_, content⟩
      · exact Anchor.PGraph.false
      · cases content with
        | lamports _ => exact Anchor.PGraph.false
        | data bytes =>
          dsimp only [types]
          apply pgraph_ite
          · exact panic_graph l args _ guard
          · apply pgraph_ite
            · exact withGuard_graph guard (Anchor.PGraph.map _ (build_graph l _ _))
            · exact mapLoaded_graph l args _ guard bytes

def codeReadyB (before : W) (guard : Borrow.Guard) (code : AnchorErrorOwned.Code) : Bool :=
  allExitsB (ownedFn.copy before code.name) (exitLiveB guard) &&
    onReturnedB (ownedFn.copy before code.name) (fun _ afterName =>
      allExitsB (ownedFn.format afterName code.message) (exitLiveB guard)) &&
    onReturnedB (ownedFn.copy before code.name) (fun name afterName =>
      onReturnedB (ownedFn.format afterName code.message) fun message afterMessage =>
        allExitsB (ownedFn.newBox afterMessage (.anchor ⟨name, code.number, message, none, none⟩))
          (exitLiveB guard))

theorem codeReadyB_iff (l : LoadIndex) (before : W) (guard : Borrow.Guard) (code :
  AnchorErrorOwned.Code) :
    codeReadyB before guard code = true ↔ AnchorLoaderInitOwned.CodeReady (types l) before guard
      code := by
  unfold codeReadyB
  rw [Bool.and_eq_true, Bool.and_eq_true, liveAt_iff (ownedGraph.copy before _),
    onReturned_iff (ownedGraph.copy before _) _ _ fun _ afterName =>
      liveAt_iff (ownedGraph.format afterName _),
    onReturned_iff (ownedGraph.copy before _) _ _ fun _ afterName =>
      onReturned_iff (ownedGraph.format afterName _) _ _ fun _ afterMessage =>
        liveAt_iff (ownedGraph.newBox afterMessage _)]
  exact ⟨fun ⟨⟨name, message⟩, boxed⟩ => ⟨name, message, boxed⟩,
    fun ⟨name, message, boxed⟩ => ⟨⟨name, message⟩, boxed⟩⟩

def observationReadyB (l : LoadIndex) (before : AccountInfo.State) (args : LoadArgs l) : Bool :=
  if args.loader.info.isWritable = false then true else dataReadyB .exclusive before
    args.loader.info.data

theorem observationReadyB_iff (l : LoadIndex) (before : AccountInfo.State) (args : LoadArgs l) :
    observationReadyB l before args = true ↔ AnchorLoaderInit.Ready before args := by
  unfold observationReadyB AnchorLoaderInit.Ready
  split
  · simp
  · exact dataReadyB_iff _ _ _

def readyB (l : LoadIndex) (before : W) (args : LoadArgs l) : Bool :=
  observationReadyB l before.1 args &&
    if args.loader.info.isWritable = false then true
    else match AccountInfo.tryBorrow .exclusive args.loader.info.data before.1 with
      | (.error _, _) => true
      | (.ok guard, during) => match Borrow.current during guard with
        | .error _ | .ok (_, .lamports _) => true
        | .ok (_, .data bytes) =>
          if bytes.length < l.discriminator.length then true
          else if AnchorLoaderInit.hasDiscriminator l.discriminator bytes then
            codeReadyB (during, before.2) guard AnchorLoaderInitOwned.alreadySet
          else true

theorem readyB_iff (l : LoadIndex) (before : W) (args : LoadArgs l) :
    readyB l before args = true ↔ AnchorLoaderInitOwned.Ready (types l) before args := by
  unfold readyB AnchorLoaderInitOwned.Ready
  rw [Bool.and_eq_true, observationReadyB_iff]
  apply and_congr_right; intro _
  split
  · simp
  · rcases AccountInfo.tryBorrow .exclusive args.loader.info.data before.1 with ⟨borrowed, during⟩
    cases borrowed with
    | error _ => simp
    | ok guard =>
      dsimp only
      rcases Borrow.current during guard with _ | ⟨_, content⟩
      · simp
      · cases content with
        | lamports _ => simp
        | data bytes =>
          dsimp only [types]
          by_cases short : bytes.length < l.discriminator.length
          · simp [short]
          · by_cases nonzero : AnchorLoaderInit.hasDiscriminator l.discriminator bytes = true
            · simpa [short, nonzero, types] using
                codeReadyB_iff l (during, before.2) guard AnchorLoaderInitOwned.alreadySet
            · simp [short, nonzero]

def reason (size dataLength : Nat) (text : String) : Option LoadPanic :=
  if text = sliceFailMessage 0 8 dataLength then some .sliceBounds
  else Anchor.Loading.asLoadPanic size dataLength text

def parseOutcome (size dataLength : Nat) (json : Json) : Result (Option Anchor.Loading.LoadObs) :=
  SolanalibTest.Conformance.Library.parseOutcome (asExcept (fun value => return some (←
    asErrorValue value)) Anchor.Loading.asMappedObs)
    asWorldObs (reason size dataLength) noReason json

def inputs (size alignment : Nat) (record : Case) := do
  let (input, world) ← asWorld record.state
  let info ← infoAt input (← natField record.args "account")
  let layout := Anchor.Loading.layout size alignment
  let args : LoadArgs layout := ⟨profile, ⟨info⟩, ← natField record.args "data_address"⟩
  return (world, args)

def ownedRequires (size alignment : Nat) (record : Case) : Result Bool := do
  let (world, args) ← inputs size alignment record
  return Anchor.RequiresCheck.decideBy
    (p :=
      (accounts.account_loader.AccountLoader.load_init_contract.contract
      (types (Anchor.Loading.layout size alignment))).requires (world, heap0) args)
    _ (readyB_iff _ (world, heap0) args)

def observationRequires (size alignment : Nat) (record : Case) : Result Bool := do
  let (world, args) ← inputs size alignment record
  return Anchor.RequiresCheck.decideBy
    (p :=
      (accounts.account_loader.AccountLoader.load_init_observation_contract.contract
      (Anchor.Loading.layout size alignment)).requires world args)
    _ (observationReadyB_iff _ world args)

def checker (name : String) (size alignment : Nat) : Checker :=
  let root := "Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader."
  let raw := ofModels "anchor_lang::accounts::account_loader::AccountLoader::<'info, \
    T>::load_init"
    [("T", name)]
    "Owned initialization and current mapped byte range, with its observation facet"
    [root ++ "load_init_run", root ++ "load_init_observation_run"] fun record => do
      let (input, world) ← asWorld record.state
      let info ← infoAt input (← natField record.args "account")
      let layout := Anchor.Loading.layout size alignment
      let args : LoadArgs layout := ⟨profile, ⟨info⟩, ← natField record.args "data_address"⟩
      let observed ← parseOutcome size (dataLength world info.data) record.outcome
      let ownedRel :=
        accounts.account_loader.AccountLoader.load_init_run (types
        layout) (world, heap0) args
      let observationRel :=
        accounts.account_loader.AccountLoader.load_init_observation_run
        layout world args
      return [
        decideProjected ownedRel _ (run_graph layout (world, heap0) args)
          (Anchor.Loading.project input Prod.fst (fun state error =>
            AnchorErrorOwned.current Anchor.Loading.ownedOps state error)) observed
              Anchor.Loading.loadObsJson,
        decideProjected observationRel _ (Anchor.PGraph.ofOption (AnchorLoaderInit.run layout world
          args))
          (Anchor.Loading.project input id (fun _ error => some error)) observed
            Anchor.Loading.loadObsJson]
  withFrame [("no syscalls", noSyscalls), ("no Owner callback", fun record => do
    return (← field (← outcomeState record) "log") == (← field record.state "log"))] <|
      withRequires [
    (root ++ "load_init_run", ownedRequires size alignment),
    (root ++ "load_init_observation_run", observationRequires size alignment)] raw

def checkers : List Checker := [checker "conformance_anchor_loader::script::Zc" 16 8,
  checker "conformance_anchor_loader::script::Zc16" 32 16]

end SolanalibTest.Conformance.Library.Families.AnchorLoader.Init
