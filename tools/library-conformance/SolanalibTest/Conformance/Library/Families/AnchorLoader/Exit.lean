/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.AnchorLoader.Construct

/-! Exit comparison follows actual Owner, is_closed, checked borrowing and
partial BpfWriter writes. The recorded copy syscall is checked separately
against the reached write prefix; it is not treated as an opaque no-op. -/

set_option autoImplicit false

open Solanalib.Specs.AnchorLang

namespace SolanalibTest.Conformance.Library.Families.AnchorLoader.Exit

open Lean (Json toJson)
open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorAccount
open SolanalibTest.Conformance.Library.Runtime SolanalibTest.Conformance.Library.Families.Anchor
open Anchor.Decide Anchor.RequiresAccounts
open Anchor.Construct (Script W Out OErr ownedTypes ownedFn ownedGraph ownedOps heap0
  ownerFn ownedShape widen_graph pgraph_ite)

/-- The historical corpus observes account bytes, leases, Owner logs and
panic text, but not diagnostic allocation events. This concrete index erases
those events; effectful contract tests separately check state threading. -/
def types (script : Script) : AnchorLoaderExit.Types where
  toConstructorTypes := Construct.types script
  discriminator := Anchor.Loading.disc
  IoError := Borsh.IoError
  makeError := Callback.ofFunction fun before error => .returned error before
  unwrapError := Callback.ofFunction fun before (aborts, _) =>
    if aborts then .terminated (.inl .writeZero) else .unwound (.inl .writeZero) before
  dropError := Callback.ofFunction fun before _ => .returned () before
  doubleUnwind := fun _ _ _ reason => reason = .inl .writeZero

abbrev Args (script : Script) := AnchorLoaderExit.Args (types script)
abbrev XOut (Value : Type) := Outcome W Value (AnchorLoaderExit.Panic ⊕ String)
  (AnchorLoaderExit.Panic ⊕ Anchor.Construct.Failure)

def observeFn (before : W) (args : AccountInfo.Args) : Option (Out Nat) :=
  match AccountInfo.observe .dataLen before.1 args.info with
  | (.malformed, _) => none
  | (.value value, after) => some (.returned value (after, before.2))
  | (.borrowFailed, after) => if args.profile.aborts then some (.terminated (.inl .borrowFailed))
      else some (.unwound (.inl .borrowFailed) (after, before.2))

theorem observe_graph (before : W) (args : AccountInfo.Args) :
    Anchor.PGraph (AnchorLifecycle.observe .dataLen before args) (observeFn before args) := by
  unfold AnchorLifecycle.observe observeFn
  rcases AccountInfo.observe .dataLen before.1 args.info with ⟨read, after⟩
  cases read with
  | malformed => exact Anchor.PGraph.false
  | value _ => exact Anchor.PGraph.eq_left _
  | borrowFailed => apply pgraph_ite <;> exact Anchor.PGraph.eq_left _

def closedFn (script : Script) (before : W) (args : AccountInfo.Args) : Option (Out Bool) :=
  if (types script).ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId then
    (observeFn before args).map (Outcome.map fun length => length == 0)
  else some (.returned false before)

theorem closed_graph (script : Script) (before : W) (args : AccountInfo.Args) :
    Anchor.PGraph (AnchorLifecycle.isClosed (types script).ownerAt before args) (closedFn script
      before args) := by
  unfold AnchorLifecycle.isClosed closedFn
  apply pgraph_ite
  · exact Anchor.PGraph.map _ (observe_graph before args)
  · exact Anchor.PGraph.eq_left _

theorem lift_graph (script : Script) {A V : Type}
    {run : (types script).toBase.Run A V} {before : W} {args : A} {result : Option (Out V)}
    (graph : Anchor.PGraph (run before args) result) :
    Anchor.PGraph (AnchorLoaderExit.lift (types := types script) run before args)
      (result.map (AnchorLoaderExit.widen (types := types script))) := Anchor.PGraph.exists_eq _
        graph

def writeZeroFn (script : Script) (before : (types script).Aux) (aborts : Bool) :
    Outcome (types script).Aux Empty (AnchorLoaderExit.Unwind (types script))
      (AnchorLoaderExit.Terminal (types script)) :=
  if aborts then .terminated (.inl .writeZero) else .unwound (.inl .writeZero) before

theorem writeZero_graph (script : Script) (before : (types script).Aux) (aborts : Bool) :
    Anchor.PGraph (AnchorLoaderExit.writeZero (types script) before aborts)
      (some (writeZeroFn script before aborts)) := by
  intro outcome
  dsimp only [types, AnchorLoaderExit.Unwind, AnchorLoaderExit.Terminal] at before outcome
  cases aborts <;>
    simp [AnchorLoaderExit.writeZero, types, writeZeroFn, Callback.ofFunction,
      Owned.scope, Owned.cleanup] <;> exact eq_comm

def writeFn (script : Script) (args : Args script) (before : W) (guard : Borrow.Guard)
    (bytes : Solanalib.Runtime.Bytes) : Option (XOut (Except OErr Unit)) :=
  match Borrow.write before.1 guard (.data (AnchorLoaderExit.writtenBytes (types
    script).discriminator bytes)) with
  | (.error _, _) => none
  | (.ok (), written) =>
    if bytes.length < (types script).discriminator.length then
      (some (writeZeroFn script before.2 args.profile.aborts)).map
        (Owned.Focus.snd.liftOutcome (written, before.2)) |>.bind fun failed =>
          match failed with
          | .returned impossible _ => nomatch impossible
          | .unwound reason during =>
            match Borrow.release during.1 guard with
            | (.error _, _) => none
            | (.ok (), after) => some (.unwound reason (after, during.2))
          | .terminated reason => some (.terminated reason)
    else match Borrow.release written guard with
      | (.error _, _) => none
      | (.ok (), after) => some (.returned (.ok ()) (after, before.2))

theorem write_graph (script : Script) (args : Args script) (before : W) (guard : Borrow.Guard)
    (bytes : Solanalib.Runtime.Bytes) :
    Anchor.PGraph (AnchorLoaderExit.writeDiscriminator (types script) args before guard bytes)
      (writeFn script args before guard bytes) := by
  unfold AnchorLoaderExit.writeDiscriminator writeFn
  rcases Borrow.write before.1 guard (.data (AnchorLoaderExit.writtenBytes (types
    script).discriminator bytes))
    with ⟨result, written⟩
  cases result with
  | error _ => exact Anchor.PGraph.false
  | ok value =>
    cases value
    dsimp only
    split
    · apply Anchor.PGraph.exists_step (Anchor.PGraph.focusLift Owned.Focus.snd
        (b := (written, before.2)) (writeZero_graph script before.2 args.profile.aborts))
      intro failed
      cases failed with
      | returned impossible _ => nomatch impossible
      | terminated _ => exact Anchor.PGraph.eq_left _
      | unwound reason during =>
        dsimp only
        rcases Borrow.release during.1 guard with ⟨result, after⟩
        cases result with
        | error _ => exact Anchor.PGraph.false
        | ok value => cases value; exact Anchor.PGraph.eq_left _
    · rcases Borrow.release written guard with ⟨result, after⟩
      cases result with
      | error _ => exact Anchor.PGraph.false
      | ok value => cases value; exact Anchor.PGraph.eq_left _

def persistFn (script : Script) (before : W) (args : Args script) : Option (XOut (Except OErr
  Unit)) :=
  match AccountInfo.tryBorrow .exclusive args.loader.account.info.data before.1 with
  | (.error failure, during) =>
    ((Anchor.Construct.programFn (during, before.2) failure).map (Outcome.map (Except.error (α :=
      Unit)))).map
      (AnchorLoaderExit.widen (types := types script))
  | (.ok guard, during) => match Borrow.current during guard with
    | .error _ | .ok (_, .lamports _) => none
    | .ok (_, .data bytes) => writeFn script args (during, before.2) guard bytes

theorem persist_graph (script : Script) (before : W) (args : Args script) :
    Anchor.PGraph (AnchorLoaderExit.persist (types script) before args) (persistFn script before
      args) := by
  unfold AnchorLoaderExit.persist persistFn
  rcases AccountInfo.tryBorrow .exclusive args.loader.account.info.data before.1 with ⟨borrowed,
    during⟩
  cases borrowed with
  | error failure =>
    exact lift_graph script (Anchor.PGraph.map _ (Anchor.Construct.program_graph script (during,
      before.2) failure))
  | ok guard =>
    dsimp only
    rcases Borrow.current during guard with _ | ⟨_, content⟩
    · exact Anchor.PGraph.false
    · cases content with
      | lamports _ => exact Anchor.PGraph.false
      | data bytes => exact write_graph script args (during, before.2) guard bytes

def runFn (script : Script) (before : W) (args : Args script) : Option (XOut (Except OErr Unit)) :=
  (some (ownerFn ownedShape script before ())).map (AnchorLoaderExit.widen (types := types script)
    ∘ widen) |>.bind
    (Anchor.PGraph.bindK fun owner afterOwner =>
      if owner = args.programId then
        ((closedFn script afterOwner args.info).map (AnchorLoaderExit.widen (types := types
          script))).bind
          (Anchor.PGraph.bindK fun closed afterRead => if closed then some (.returned (.ok ())
            afterRead)
            else persistFn script afterRead args)
      else some (.returned (.ok ()) afterOwner))

theorem run_graph (script : Script) (before : W) (args : Args script) :
    Anchor.PGraph (AnchorLoaderExit.run (types script) before args) (runFn script before args) := by
  unfold AnchorLoaderExit.run runFn
  apply Anchor.PGraph.bind
  · exact lift_graph script (widen_graph (Anchor.PGraph.ofFunction (ownerFn ownedShape script)
    before ()))
  · intro owner afterOwner
    apply pgraph_ite
    · apply Anchor.PGraph.bind (lift_graph script (closed_graph script afterOwner args.info))
      intro closed afterRead
      apply pgraph_ite
      · exact Anchor.PGraph.eq_left _
      · exact persist_graph script afterRead args
    · exact Anchor.PGraph.eq_left _

def closedReadyB (script : Script) (before : W) (args : AccountInfo.Args) : Bool :=
  if (types script).ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId then
    decide ((AccountInfo.observe .dataLen before.1 args.info).1 ≠ .malformed) else true

theorem closedReadyB_iff (script : Script) (before : W) (args : AccountInfo.Args) :
    closedReadyB script before args = true ↔ AnchorLifecycle.IsClosedReady (types script).ownerAt
      before args := by
  unfold closedReadyB AnchorLifecycle.IsClosedReady AnchorLifecycle.ObserveReady
  split <;> simp_all

def readyB (script : Script) (before : W) (args : Args script) : Bool :=
  onReturnedB (some (ownerFn ownedShape script before ())) fun owner afterOwner =>
    if owner = args.programId then closedReadyB script afterOwner args.info &&
      onReturnedB (closedFn script afterOwner args.info) (fun closed afterRead =>
        if closed then true else dataReadyB .exclusive afterRead.1 args.loader.account.info.data)
    else true

theorem readyB_iff (script : Script) (before : W) (args : Args script) :
    readyB script before args = true ↔ AnchorLoaderExit.Ready (types script) before args := by
  unfold readyB AnchorLoaderExit.Ready
  apply onReturned_iff (Anchor.PGraph.ofFunction (ownerFn ownedShape script) before ())
  intro owner afterOwner
  by_cases same : owner = args.programId
  · simp only [same, ↓reduceIte, true_implies, Bool.and_eq_true]
    apply and_congr (closedReadyB_iff script afterOwner args.info)
    have all := onReturned_iff (closed_graph script afterOwner args.info)
      (fun closed afterRead => if closed then True else
        AccountInfo.DataBorrow.Ready .exclusive afterRead.1 args.loader.account.info.data)
      (fun closed afterRead => if closed then true else
        dataReadyB .exclusive afterRead.1 args.loader.account.info.data) fun closed afterRead => by
      cases closed with
      | true => simp
      | false => exact dataReadyB_iff .exclusive afterRead.1 args.loader.account.info.data
    exact all.trans ⟨fun h after called => h false after called,
      fun h closed after called => by cases closed with
      | true => trivial
      | false => exact h after called⟩
  · simp only [same, ↓reduceIte, false_implies, iff_self]

abbrev Obs := Outcome Anchor.Construct.StateObs (Except (Option ErrorValue) Unit)
  (AnchorLoaderExit.Panic ⊕ String) Unit

def project (input : LoaderInput) : XOut (Except OErr Unit) → Obs
  | .returned value after => .returned (value.mapError (AnchorErrorOwned.current ownedOps after))
      ⟨observeWorld input after.2.2.owners after.1, after.2.2.log⟩
  | .unwound reason after => .unwound reason
      ⟨observeWorld input after.2.2.owners after.1, after.2.2.log⟩
  | .terminated _ => .terminated ()

def asReason (reason : String) : Option (AnchorLoaderExit.Panic ⊕ String) :=
  if reason = "RefCell already mutably borrowed" then some (.inl .borrowFailed)
  else if reason =
    "called `Result::unwrap()` on an `Err` value: Custom { kind: WriteZero, error: \
      \"failed to write whole buffer\" }" then
    some (.inl .writeZero)
  else some (.inr reason)

def reasonJson : AnchorLoaderExit.Panic ⊕ String → Json
  | .inl .borrowFailed => "borrow panic"
  | .inl .writeZero => "short discriminator write"
  | .inr reason => Json.str reason

def obsJson : Option Obs → Json
  | none => "<no outcome>"
  | some (.returned result state) => returnedJson (exceptJson (optionJson errorValueJson) (fun _ =>
    Json.null) result)
      (Anchor.Construct.stateObsJson state)
  | some (.unwound reason state) => Json.mkObj [("exit", "unwound"), ("reason", reasonJson reason),
      ("state", Anchor.Construct.stateObsJson state)]
  | some (.terminated _) => Json.mkObj [("exit", "terminated")]

def inputs (record : Case) : Result (Σ parsed : Anchor.Construct.Inputs, Args parsed.script) := do
  let parsed ← Anchor.Construct.inputs record
  let args : Args parsed.script := ⟨profile, ⟨⟨← natField record.args "account", parsed.args.info⟩⟩,
    ← keyField record.args "program_id"⟩
  return ⟨parsed, args⟩

/-- This is the reached source write prefix, not an inference from final
byte equality: unchanged initial bytes can still cause a real memcpy call. -/
def copiedBytes (script : Script) (before : W) (args : Args script) : Option
  Solanalib.Runtime.Bytes := do
  let .returned owner afterOwner := ownerFn ownedShape script before () | none
  if owner ≠ args.programId then none else do
    let .returned false afterRead ← closedFn script afterOwner args.info | none
    let (.ok guard, during) := AccountInfo.tryBorrow .exclusive args.loader.account.info.data
      afterRead.1 | none
    let .ok (_, .data bytes) := Borrow.current during guard | none
    let copied := Anchor.Loading.disc.take bytes.length
    if copied.isEmpty then none else some copied

def syscallFrame (record : Case) : Result Bool := do
  let ⟨parsed, args⟩ ← inputs record
  let before ← field record.state "syscalls"
  let after ← field (← outcomeState record) "syscalls"
  let copied := copiedBytes parsed.script (parsed.world, (heap0, parsed.aux)) args
  let expected := copied.toList.map fun bytes => Json.mkObj [("syscall", "sol_memcpy_"), (
    "bytes",
    bytesJson bytes)]
  return (← field after "replies") == (← field before "replies") &&
    (← field after "log") == toJson expected

def requires (record : Case) : Result Bool := do
  let ⟨parsed, args⟩ ← inputs record
  return Anchor.RequiresCheck.decideBy
    (p := (accounts.account_loader.AccountLoader.exit_contract.contract
      (types parsed.script)).requires (parsed.world, (heap0, parsed.aux)) args)
    _ (readyB_iff parsed.script (parsed.world, (heap0, parsed.aux)) args)

def checker : Checker :=
  let root := "Solanalib.Specs.AnchorLang.accounts.account_loader.AccountLoader."
  withFrame [("exact reached discriminator copy", syscallFrame)] <| withRequires [
    (root ++ "exit_run", requires)] <|
    ofModel
      "<anchor_lang::accounts::account_loader::AccountLoader<'info, T> as \
        anchor_lang::AccountsExit<'info>>::exit"
      [("T", "conformance_anchor_loader::script::Zc")] (root ++ "exit_run") fun record => do
        let ⟨parsed, args⟩ ← inputs record
        let before : W := (parsed.world, (heap0, parsed.aux))
        let recorded ← parseOutcome (asExcept (fun error => return some (← asErrorValue error))
          asUnit)
          Anchor.Construct.asStateObs asReason noReason record.outcome
        return decideProjected
          (accounts.account_loader.AccountLoader.exit_run (types
            parsed.script) before args)
          _ (run_graph parsed.script before args) (project parsed.input) recorded obsJson

end SolanalibTest.Conformance.Library.Families.AnchorLoader.Exit
