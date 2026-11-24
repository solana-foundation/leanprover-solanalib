/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLoaderInit
public import Solanalib.Specs.Core.AnchorLoadingOwned
public import Solanalib.Specs.Core.AnchorOwnedSamples

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLoaderInitOwned

abbrev Types := AnchorLoadingOwned.Types
abbrev Args (types : Types) := AnchorAccount.LoadArgs types.layout
abbrev Result (types : Types) := AnchorLoadingOwned.Result types
abbrev Terminal (types : Types) := AnchorLoadingOwned.Terminal types

/-- The exact declared error fields used by initialization. -/
def alreadySet : AnchorErrorOwned.Code :=
  ⟨"AccountDiscriminatorAlreadySet", 3000,
    "The account discriminator was already set on this account"⟩

/-- Allocate the name, message and Box using the established owned factory. -/
def build (types : Types) (code : AnchorErrorOwned.Code) :
    Callback.Run (AnchorAccount.World types.Aux) Unit (AnchorLoadingOwned.Error types)
      AnchorAccount.LoadPanic (Terminal types) :=
  fun before _ => AnchorLoadingOwned.dependency types
    (AnchorErrorOwned.buildCode types.errors) before code

/-- Minimal token availability at every reached error-allocation primitive.
The constraints precede the complete factory result, so a missing later
provider result cannot hide an earlier finite exit that destroys the guard. -/
structure CodeReady (types : Types) (before : AnchorAccount.World types.Aux)
    (guard : Borrow.Guard) (code : AnchorErrorOwned.Code) : Prop where
  name : AnchorLoadingOwned.LiveAt guard types.errors.copyLiteral before code.name
  message : ∀ name afterName,
    types.errors.copyLiteral before code.name (.returned name afterName) →
      AnchorLoadingOwned.LiveAt guard types.errors.formatLiteral afterName code.message
  boxed : ∀ name afterName,
    types.errors.copyLiteral before code.name (.returned name afterName) →
    ∀ message afterMessage,
    types.errors.formatLiteral afterName code.message (.returned message afterMessage) →
      AnchorLoadingOwned.LiveAt guard types.errors.newBox afterMessage
        (.anchor ⟨name, code.number, message, none, none⟩)

/-- Each actual primitive exit supports checked release at its own returned
state. Terminal exits have no fabricated cleanup state. -/
theorem CodeReady.checkpoints {types : Types} {before : AnchorAccount.World types.Aux}
    {guard : Borrow.Guard} {code : AnchorErrorOwned.Code}
    (ready : CodeReady types before guard code) :
    (∀ produced, types.errors.copyLiteral before code.name produced →
      AnchorLoadingOwned.Releasable guard produced) ∧
    (∀ name afterName, types.errors.copyLiteral before code.name (.returned name afterName) →
      ∀ produced, types.errors.formatLiteral afterName code.message produced →
        AnchorLoadingOwned.Releasable guard produced) ∧
    (∀ name afterName, types.errors.copyLiteral before code.name (.returned name afterName) →
      ∀ message afterMessage,
      types.errors.formatLiteral afterName code.message (.returned message afterMessage) →
        ∀ produced, types.errors.newBox afterMessage
          (.anchor ⟨name, code.number, message, none, none⟩) produced →
            AnchorLoadingOwned.Releasable guard produced) := by
  refine ⟨fun produced called => (ready.name produced called).releasable,
    fun name afterName named produced called =>
      (ready.message name afterName named produced called).releasable,
    fun name afterName named message afterMessage formatted produced called =>
      (ready.boxed name afterName named message afterMessage formatted produced called).releasable⟩

/-- The final factory return retains the guard needed by the enclosing data
scope. Earlier primitive returns are covered separately by `checkpoints`. -/
theorem CodeReady.live {types : Types} {before : AnchorAccount.World types.Aux}
    {guard : Borrow.Guard} {code : AnchorErrorOwned.Code}
    (ready : CodeReady types before guard code) :
    AnchorLoadingOwned.LiveAt guard (build types code) before () := by
  rintro produced ⟨original, built, lifted⟩
  obtain ⟨nameExit, named, continued⟩ := built
  cases nameExit with
  | terminated reason => cases continued; cases lifted; trivial
  | unwound impossible _ => nomatch impossible
  | returned name afterName =>
    obtain ⟨messageExit, formatted, continued⟩ := continued
    cases messageExit with
    | terminated reason => cases continued; cases lifted; trivial
    | unwound impossible _ => nomatch impossible
    | returned message afterMessage =>
      obtain ⟨boxExit, allocated, mapped⟩ := continued
      have live := ready.boxed name afterName named message afterMessage formatted boxExit allocated
      cases boxExit with
      | returned resource after => cases mapped; cases lifted; exact live
      | unwound impossible _ => nomatch impossible
      | terminated reason => cases mapped; cases lifted; trivial

/-- Lift the existing checked panic/release operation without changing the
auxiliary world. Only the local panic branch is added to terminal reasons. -/
def panic (types : Types) (args : Args types) (before : AnchorAccount.World types.Aux)
    (guard : Borrow.Guard) (reason : AnchorAccount.LoadPanic) :
    Outcome (AnchorAccount.World types.Aux) (Result types)
      AnchorAccount.LoadPanic (Terminal types) → Prop :=
  fun outcome =>
    if args.profile.aborts then outcome = .terminated (.inl reason)
    else match Borrow.release before.1 guard with
      | (.error _, _) => False
      | (.ok (), after) => outcome = .unwound reason (after, before.2)

/-- Exact initialization sequence, including diagnostic allocation while
the guard is held. A short discriminator slice panics before inspecting it;
success transfers the guard and leaves every data byte unchanged. -/
def run (types : Types) : Callback.Run (AnchorAccount.World types.Aux) (Args types)
    (Result types) AnchorAccount.LoadPanic (Terminal types) :=
  fun before args outcome =>
    if args.loader.info.isWritable = false then
      Callback.map Except.error (AnchorLoadingOwned.code types .notMutable) before () outcome
    else
      let (borrowed, during) := AccountInfo.tryBorrow .exclusive args.loader.info.data before.1
      match borrowed with
      | .error failure => Callback.map Except.error (AnchorLoadingOwned.program types failure)
          (during, before.2) () outcome
      | .ok guard => match Borrow.current during guard with
        | .error _ | .ok (_, .lamports _) => False
        | .ok (_, .data bytes) =>
          if bytes.length < types.layout.discriminator.length then
            panic types args (during, before.2) guard .sliceBounds outcome
          else if AnchorLoaderInit.hasDiscriminator types.layout.discriminator bytes then
            AnchorEffects.withGuard guard (Callback.map Except.error (build types alreadySet))
              (during, before.2) () outcome
          else AnchorLoadingOwned.mapLoaded types args (during, before.2) guard bytes outcome

/-- The only reached-data and cleanup requirements. No owner, zero-prefix,
payload-size or alignment success is demanded by admission. -/
def Ready (types : Types) (before : AnchorAccount.World types.Aux) (args : Args types) : Prop :=
  AnchorLoaderInit.Ready before.1 args ∧
    if args.loader.info.isWritable = false then True
    else match AccountInfo.tryBorrow .exclusive args.loader.info.data before.1 with
      | (.error _, _) => True
      | (.ok guard, during) => match Borrow.current during guard with
        | .error _ | .ok (_, .lamports _) => True
        | .ok (_, .data bytes) =>
          if bytes.length < types.layout.discriminator.length then True
          else if AnchorLoaderInit.hasDiscriminator types.layout.discriminator bytes then
            CodeReady types (during, before.2) guard alreadySet
          else True

/-- At every actual successful acquisition the typed read is available.
Each finite already-set error-factory exit executes its exact source-required
release. The other branch has an actual mapping or panic continuation. -/
theorem local_continuations {types : Types} {before : AnchorAccount.World types.Aux}
    {args : Args types} (ready : Ready types before args)
    (writable : ¬ args.loader.info.isWritable = false)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrow .exclusive args.loader.info.data before.1 = (.ok guard,
      during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) ∧
      if bytes.length < types.layout.discriminator.length then
        ∃ outcome, panic types args (during, before.2) guard .sliceBounds outcome ∧
          run types before args outcome
      else if AnchorLoaderInit.hasDiscriminator types.layout.discriminator bytes then
        CodeReady types (during, before.2) guard alreadySet ∧
          ∀ produced, Callback.map Except.error (build types alreadySet) (during, before.2) ()
            produced →
            AccountInfo.GuardCallback.releaseOutcome guard produced =
              some (AnchorLoadingOwned.cleanupExit guard produced) ∧
                run types before args (AnchorLoadingOwned.cleanupExit guard produced)
      else ∃ outcome, AnchorLoadingOwned.mapLoaded types args (during, before.2) guard bytes
        outcome ∧
        run types before args outcome := by
  have typed : AccountInfo.DataBorrow.Ready .exclusive before.1 args.loader.info.data := by
    simpa only [AnchorLoaderInit.Ready, ite_eq_right writable] using ready.1
  obtain ⟨bytes, current⟩ := AccountInfo.DataBorrow.ready_current typed acquired
  refine ⟨bytes, current, ?_⟩
  split
  next short =>
    have live := AccountInfo.GuardCallback.tryBorrow_live acquired
    have existsExit : ∃ outcome, panic types args (during, before.2) guard .sliceBounds outcome :=
      by
      unfold panic
      split
      · exact ⟨_, rfl⟩
      · rw [Borrow.release_live live]
        exact ⟨_, rfl⟩
    obtain ⟨outcome, called⟩ := existsExit
    exact ⟨outcome, called, by
      simpa only [run, ite_eq_right writable, acquired, current, ite_eq_left short] using called⟩
  next enough =>
    split
    next set =>
      have codeReady : CodeReady types (during, before.2) guard alreadySet := by
        simpa only [Ready, ite_eq_right writable, acquired, current,
          ite_eq_right enough, ite_eq_left set] using ready.2
      refine ⟨codeReady, ?_⟩
      rintro produced ⟨original, called, rfl⟩
      have live := codeReady.live original called
      have mappedLive : AnchorLoadingOwned.ExitLive guard (Outcome.map
          (Except.error (α := AnchorAccount.Mapped types.layout.Payload)) original) := by
        cases original <;> exact live
      have released := mappedLive.releasable
      refine ⟨released.1, ?_⟩
      simp only [run, ite_eq_right writable, acquired, current, ite_eq_right enough,
        ite_eq_left set, AnchorEffects.withGuard]
      exact ⟨_, ⟨original, called, rfl⟩, released.1⟩
    next zero =>
      obtain ⟨outcome, mapped⟩ := AnchorLoadingOwned.mapLoaded_complete
        (before := (during, before.2)) args current
      exact ⟨outcome, mapped, by
        simpa only [run, ite_eq_right writable, acquired, current,
          ite_eq_right enough, ite_eq_right zero] using mapped⟩

def family : Family where
  Index := Types
  State := fun types => AnchorAccount.World types.Aux
  Args := Args
  Value := Result
  Unwind := fun _ => AnchorAccount.LoadPanic
  Terminal := Terminal
  contract := fun types => { requires := Ready types, post := run types }

def reference : FamilyRun family := run
theorem reference_holds : FamilyReference family reference := by
  intro _ _ _ _ _ step
  exact step

def sample : Types := { AnchorOwnedSamples.loading with layout := AnchorLoaderInit.sample }

theorem has_execution : FamilyHasExecution family reference sample := by
  refine ⟨(AnchorLoaderInit.sampleState, AnchorOwnedSamples.auxiliary), AnchorLoaderInit.sampleArgs,
    .returned (.ok ⟨⟨0, 1⟩⟩)
      ((Borrow.transfer (AccountInfo.tryBorrow .exclusive AccountInfo.sampleInfo.data
        AnchorLoaderInit.sampleState).2 ⟨0, 0⟩ (.bytesRange 1 2)).2,
          AnchorOwnedSamples.auxiliary), ⟨trivial, trivial⟩, rfl⟩

end Solanalib.Specs.Core.AnchorLoaderInitOwned
