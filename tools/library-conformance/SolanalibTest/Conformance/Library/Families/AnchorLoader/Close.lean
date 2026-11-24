/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLoader.CloseReady
import SolanalibTest.Conformance.Library.Families.AnchorLoader.Identity

/-! The native close comparison retains the exact shared backing, original
and current length words, balances, owners, leases and moved Rc counts.
The common-close definition supplies the executable local core; the owned
error heap and destination destructor remain explicit primitive providers. -/

set_option autoImplicit false

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorLoader.Close

open Lean (Json toJson)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor
open Anchor.Construct (Heap OErr Failure StringId BoxId heap0)

structure Aux where
  owners : List Solanalib.Runtime.Pubkey
  buffers : List (Option AccountInfoSdk.Buffer)
  counts : List Nat
  heap : Heap

abbrev W := World Aux
abbrev Out (Value : Type) := Outcome W Value
  (AnchorLifecycle.ClosePanic ⊕ ConstructorUnwind String)
  (AnchorLifecycle.ClosePanic ⊕ ConstructorTerminal Failure)

def sdk : Owned.Focus W AccountInfoSdk.State where
  get := fun state => ⟨state.1, state.2.owners, state.2.buffers⟩
  set := fun state next => (next.borrow, { state.2 with owners := next.owners, buffers :=
    next.buffers })
  get_set := by intro _ next; cases next; rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def heap : Owned.Focus W Heap where
  get := fun state => state.2.heap
  set := fun state next => (state.1, { state.2 with heap := next })
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

def ops := AnchorErrorOwned.Reference.ops.focus heap
def fn := RefFn.fn.focus heap
theorem graph : OpsGraph ops fn := RefFn.graph.focus heap

def dropRc (before : W) (input : AccountInfoRc.Field × Borrow.Handle) :
    Option (Outcome W Unit Empty Failure) :=
  match before.2.counts[input.2.cell]? with
  | some (count + 1) => some (.returned ()
      (before.1, { before.2 with counts := before.2.counts.set input.2.cell count }))
  | _ => none

def rc : AccountInfoRc.Ops W Failure where
  cloneRc := fun _ _ _ => False
  dropRc := fun before input outcome => dropRc before input = some outcome

def types : AnchorLoaderClose.Types where
  Aux := Aux
  Payload := Unit
  Unwind := String
  Terminal := Failure
  StringResource := StringId
  BoxResource := BoxId
  errors := ops
  sdk := sdk
  borrow_eq := fun _ => rfl
  rc := rc

abbrev Args := AnchorLoaderClose.Args types

def lifted {Value : Type} (outcome : Outcome W Value Empty Failure) : Out Value :=
  AnchorLifecycle.closeLift (AnchorAccount.widen (AccountInfoRc.liftOutcome (Unwind := String)
    outcome))

def errorFn (before : W) (failure : ProgramError.Value) : Option (Out (Except OErr Unit)) :=
  (((OwnedFn.fromProgramFn fn before failure).map (AccountInfoRc.liftOutcome (Unwind :=
    String))).map AnchorAccount.widen
    |>.map (Outcome.map (Except.error (α := Unit)))).map AnchorLifecycle.closeLift

theorem error_graph (before : W) (failure : ProgramError.Value) :
    Anchor.PGraph (AnchorLifecycle.closeLiftCall
      (Callback.map Except.error (AnchorLifecycle.programError types.core.toBase failure)) before
        ())
      (errorFn before failure) := by
  exact Anchor.PGraph.exists_eq AnchorLifecycle.closeLift
    (Anchor.PGraph.map Except.error (Anchor.Construct.widen_graph
      (Anchor.Construct.rcLift_graph (U := String) (OwnedFn.fromProgram_graph graph before
        failure))))

def commonFn (before : W) (args : Args) : Option (Out (Except OErr Unit)) :=
  match AnchorLifecycle.commonCloseCore .legacy (sdk.get before) args.core with
  | none => none
  | some (.returned (.ok ()) after) => some (.returned (.ok ()) (sdk.set before after))
  | some (.returned (.error failure) after) => errorFn (sdk.set before after) failure
  | some (.unwound reason after) => some (.unwound (.inl reason) (sdk.set before after))
  | some (.terminated reason) => some (.terminated (.inl reason))

theorem common_graph (before : W) (args : Args) :
    Anchor.PGraph (AnchorLifecycle.commonClose .legacy types.core before args.core) (commonFn
      before args) := by
  unfold AnchorLifecycle.commonClose commonFn
  change Anchor.PGraph (fun outcome => match AnchorLifecycle.commonCloseCore .legacy (sdk.get
    before) args.core with
    | none => False
    | some (.unwound reason after) => _
    | some (.terminated reason) => _
    | some (.returned (.ok ()) after) => _
    | some (.returned (.error failure) after) => _) _
  cases AnchorLifecycle.commonCloseCore .legacy (sdk.get before) args.core with
  | none => exact Anchor.PGraph.false
  | some outcome =>
    cases outcome with
    | unwound _ _ => exact Anchor.PGraph.eq_left _
    | terminated _ => exact Anchor.PGraph.eq_left _
    | returned result after =>
      cases result with
      | ok value => cases value; exact Anchor.PGraph.eq_left _
      | error failure => exact error_graph (sdk.set before after) failure

def dropRawFn (before : W) (info : AccountInfo.Value) : Option (Outcome W Unit Empty Failure) :=
  (dropRc before (.lamports, info.lamports)).bind
    (Anchor.PGraph.bindK fun _ after => dropRc after (.data, info.data))

theorem dropRaw_graph (before : W) (info : AccountInfo.Value) :
    Anchor.PGraph (AccountInfoRc.dropCall rc before info) (dropRawFn before info) :=
  Anchor.PGraph.bind (Anchor.PGraph.ofOption _) (fun _ _ => Anchor.PGraph.ofOption _)

def dropFn (info : AccountInfo.Value) (before : W) : Option (Out Unit) :=
  (((dropRawFn before info).map (AccountInfoRc.liftOutcome (Unwind := String))).map
    AnchorAccount.widen).map
    AnchorLifecycle.closeLift

theorem drop_graph (info : AccountInfo.Value) (before : W) :
    Anchor.PGraph (AnchorLifecycle.closeLiftCall
      (fun state (_ : Unit) => AnchorLifecycle.dropInfo types.core.toBase rc info state) before ())
      (dropFn info before) :=
  Anchor.PGraph.exists_eq AnchorLifecycle.closeLift (Anchor.Construct.widen_graph
    (Anchor.Construct.rcLift_graph (U := String) (dropRaw_graph before info)))

def runFn (before : W) (args : Args) : Option (Out (Except OErr Unit)) :=
  (commonFn before args).bind (Anchor.PGraph.cleanupFn (fun _ _ _ => none) [dropFn
    args.destination.info])

theorem run_graph (before : W) (args : Args) :
    Anchor.PGraph (AnchorLoaderClose.run types before args) (runFn before args) := by
  exact Anchor.PGraph.scope (fun _ _ _ => Anchor.PGraph.false)
    (Anchor.PGraph.DropsGraph.cons (drop_graph args.destination.info) Anchor.PGraph.DropsGraph.nil)
    (common_graph before args)

structure StateObs where
  world : WorldObs
  spare : List Solanalib.Runtime.Bytes
  counts : List Nat
  deriving DecidableEq

abbrev Obs := Outcome StateObs (Except (Option ErrorValue) Unit)
  (AnchorLifecycle.ClosePanic ⊕ ConstructorUnwind String) Unit

def observe (input : LoaderInput) (after : W) : StateObs :=
  let plain := observeWorld input after.2.owners after.1
  let update := fun (acc : List RegionEntry × Nat) (entry : RegionEntry) =>
    match entry with
    | .duplicate _ => (acc.1 ++ [entry], acc.2)
    | .account account =>
      let buffer := (after.2.buffers[2 * acc.2 + 1]?.join).getD ⟨account.padding, account.dataLen,
        []⟩
      let updated : RegionAccount := { account with
        padding := buffer.originalLen
        dataLen := buffer.serializedLen
        spareNonzeroAt := (buffer.spare.findIdx? (· != 0)).map (account.data.length + ·) }
      (acc.1 ++ [.account updated], acc.2 + 1)
  { world := { plain with region := { plain.region with entries := (plain.region.entries.foldl
    update ([], 0)).1 } },
    spare := (List.range (distinctOf input.entries).length).map fun index =>
      ((after.2.buffers[2 * index + 1]?.join).getD ⟨0, 0, []⟩).spare,
    counts := after.2.counts }

def project (input : LoaderInput) : Out (Except OErr Unit) → Obs
  | .returned result after => .returned (result.mapError (AnchorErrorOwned.current ops after))
    (observe input after)
  | .unwound reason after => .unwound reason (observe input after)
  | .terminated _ => .terminated ()

def asState (json : Json) : Result StateObs := do
  let entries ← asArray (← field (← field json "input") "accounts")
  let spare ← entries.filterMapM fun entry => do
    match entry.getObjVal? "duplicate_of" with
    | .ok _ => return none
    | .error _ => return some (← asBytes (← field entry "spare"))
  return ⟨← asWorldObs json, spare, (← Identity.counts (← field json "ref_counts")).flatten⟩

def reason (message : String) : Option (AnchorLifecycle.ClosePanic ⊕ ConstructorUnwind String) :=
  if message = "RefCell already borrowed" || message = "RefCell already mutably borrowed" then some
    (.inl .borrowFailed)
  else if message = "called `Option::unwrap()` on a `None` value" then some (.inl
    .arithmeticOverflow)
  else none

def obsJson : Option Obs → Json
  | none => "<no outcome>"
  | some (.returned result after) => returnedJson
      (exceptJson (optionJson errorValueJson) (fun _ => Json.null) result)
      (Json.mkObj [("counts", toJson after.counts), ("leases", toJson (after.world.leases.map
        reprStr)),
        ("spare", listJson bytesJson after.spare)])
  | some (.unwound failure after) => Json.mkObj [("exit", "unwound"), ("reason", reprStr failure),
      ("counts", toJson after.counts), ("spare", listJson bytesJson after.spare)]
  | some (.terminated _) => Json.mkObj [("exit", "terminated")]

def inputs (record : Case) : Result (LoaderInput × W × Args) := do
  let (input, borrow) ← asWorld record.state
  let source ← natField record.args "account"
  let destination ← natField record.args "destination"
  let args : Args := ⟨profile, ⟨⟨source, ← infoAt input source⟩⟩, ⟨destination, ← infoAt input
    destination⟩⟩
  let buffers := (distinctOf input.entries).flatMap fun account =>
    [none, some (⟨account.data.length, account.data.length, List.replicate 10240 0⟩ :
      AccountInfoSdk.Buffer)]
  let counts := (← Identity.counts (← field record.state "ref_counts")).flatten
  return (input, (borrow, ⟨inputOwners input, buffers, counts, heap0⟩), args)

def noOwnerCall (record : Case) : Result Bool := do
  return (← field (← outcomeState record) "log") == toJson ([] : List Json)

def requires (record : Case) : Result Bool := do
  let (_, before, args) ← inputs record
  return Anchor.RequiresCheck.decideBy
    (p := (accounts.account_loader.AccountLoader.close_contract.contract
      types).requires before args) _ (CloseReady.coreB_iff (sdk.get before) args.core)

def checker : Checker :=
  let root := "Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader."
  withFrame [("no syscalls", noSyscalls), ("no Owner callback", noOwnerCall)] <| withRequires [
    (root ++ "close_run", requires)] <|
    ofModel
      "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as \
        anchor_lang::AccountsClose<'info>>::close"
      [("T", "conformance_anchor_loader::script::Zc")] (root ++ "close_run") fun record => do
        let (input, before, args) ← inputs record
        let recorded ← parseOutcome (asExcept (fun error => return some (← asErrorValue error))
          asUnit)
          asState reason noReason record.outcome
        return decideProjected
          (accounts.account_loader.AccountLoader.close_run types before
            args)
          _ (run_graph before args) (project input) recorded obsJson

end SolanalibTest.Conformance.Library.Families.AnchorLoader.Close
