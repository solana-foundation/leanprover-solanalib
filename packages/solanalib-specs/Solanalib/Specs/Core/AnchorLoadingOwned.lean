/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorConstructOwned

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLoadingOwned

/-- Loader layout parameters remain explicit; error resources live in the
same world as the two independently borrowed AccountInfo cells. -/
structure Types where
  /-- Captured dependency state alongside the account borrow store. -/
  Aux : Type
  /-- Terminal reasons of the fixed error dependencies. -/
  Terminal : Type
  /-- Stable logical identities of owned diagnostic strings. -/
  StringResource : Type
  /-- Stable logical identities of owned error boxes. -/
  BoxResource : Type
  /-- Actual primitive error-resource relations in the shared current world. -/
  errors : AnchorErrorOwned.Ops (AnchorAccount.World Aux) StringResource BoxResource Terminal
  /-- Associated discriminator and payload layout. -/
  layout : AnchorAccount.LoadIndex

/-- An owned diagnostic box returned by the selected error factory. -/
abbrev Error (types : Types) := AnchorErrorOwned.Error types.BoxResource
/-- Local mapping abort and dependency termination remain distinct. -/
abbrev Terminal (types : Types) := AnchorAccount.LoadPanic ⊕ types.Terminal
/-- Ordinary SDK errors versus a successfully transferred data guard. -/
abbrev Result (types : Types) := Except (Error types) (AnchorAccount.Mapped types.layout.Payload)

/-- Fixed-source error dependencies cannot unwind. They may terminate, and
that reason remains distinct from a local mapping panic configured to abort. -/
def dependency (types : Types) {Args Value : Type}
    (run : Callback.Run (AnchorAccount.World types.Aux) Args Value Empty types.Terminal) :
    Callback.Run (AnchorAccount.World types.Aux) Args Value AnchorAccount.LoadPanic (Terminal
      types) :=
  fun before args outcome => ∃ produced, run before args produced ∧
    (match produced with
      | .returned value after => outcome = .returned value after
      | .unwound impossible _ => nomatch impossible
      | .terminated reason => outcome = .terminated (.inr reason))

/-- The actual name, message and Box sequence for an Anchor error code. -/
def code (types : Types) (failure : AnchorAccount.Code) :
    Callback.Run (AnchorAccount.World types.Aux) Unit (Error types)
      AnchorAccount.LoadPanic (Terminal types) :=
  fun before _ => dependency types (AnchorErrorOwned.buildCode types.errors) before
    ⟨failure.payload.name, failure.payload.code, failure.payload.message⟩

/-- Guarded factory admission follows from its three source-ordered primitive
allocation obligations, with the exact terminal vocabulary retained. -/
theorem code_admissible {types : Types} {before : AnchorAccount.World types.Aux}
    {guard : Borrow.Guard} {failure : AnchorAccount.Code}
    (admitted : AnchorGuardEffects.BuildCodeAdmissible types.errors before guard
      ⟨failure.payload.name, failure.payload.code, failure.payload.message⟩) :
    AccountInfo.GuardCallback.Admissible guard (code types failure) before () := by
  rintro outcome ⟨produced, called, lifted⟩
  have frame := admitted.admissible produced called
  cases produced with
  | returned value after => cases lifted; exact frame
  | unwound impossible _ => nomatch impossible
  | terminated _ => cases lifted; trivial

/-- Box the original AccountInfo borrow error without diagnostic strings. -/
def program (types : Types) (failure : ProgramError.Value) :
    Callback.Run (AnchorAccount.World types.Aux) Unit (Error types)
      AnchorAccount.LoadPanic (Terminal types) :=
  fun before _ => dependency types (AnchorErrorOwned.fromProgram types.errors) before failure

/-- Mapping has no heap-error branch. This adapter lifts its successful guard
transfer and its source-local panic cleanup without changing auxiliary state. -/
def mapLoaded (types : Types) (args : AnchorAccount.LoadArgs types.layout)
    (before : AnchorAccount.World types.Aux) (guard : Borrow.Guard) (bytes :
      _root_.Solanalib.Runtime.Bytes)
    (outcome : Outcome (AnchorAccount.World types.Aux) (Result types)
      AnchorAccount.LoadPanic (Terminal types)) : Prop :=
  match AnchorAccount.mapLoaded types.layout args before.1 guard bytes with
  | none => False
  | some (.returned (.error _) _) => False
  | some (.returned (.ok mapped) after) => outcome = .returned (.ok mapped) (after, before.2)
  | some (.unwound reason after) => outcome = .unwound reason (after, before.2)
  | some (.terminated reason) => outcome = .terminated (.inl reason)

/-- Mutable loading checks writable metadata before borrowing. Discriminator
errors allocate while the acquired data guard is held, then release it.
Successful mapping transfers the guard instead of dropping it. No path checks
the account owner or silently substitutes a decoded payload. -/
def run (mode : Borrow.Mode) (types : Types) :
    Callback.Run (AnchorAccount.World types.Aux) (AnchorAccount.LoadArgs types.layout)
      (Result types) AnchorAccount.LoadPanic (Terminal types) :=
  fun before args outcome =>
    if mode = .exclusive ∧ args.loader.info.isWritable = false then
      Callback.map Except.error (code types .notMutable) before () outcome
    else
      let (borrowed, during) := AccountInfo.tryBorrow mode args.loader.info.data before.1
      match borrowed with
      | .error failure => Callback.map Except.error (program types failure) (during, before.2) ()
        outcome
      | .ok guard => match Borrow.current during guard with
        | .error _ | .ok (_, .lamports _) => False
        | .ok (_, .data bytes) =>
          match AnchorConstructOwned.discriminatorFailure types.layout.discriminator bytes with
          | some failure => AnchorEffects.withGuard guard (Callback.map Except.error (code types
            failure))
            (during, before.2) () outcome
          | none => mapLoaded types args (during, before.2) guard bytes outcome

/-- Every state-bearing callback exit leaves this exact token usable at its
current generation. No unrelated store validity, history, policy, or cell
footprint is imposed. Source permissions and resource interpretations remain
separate from this minimal local cleanup condition. -/
def ExitLive {Aux Value Unwind ExitTerminal : Type} (guard : Borrow.Guard) :
    Outcome (AnchorAccount.World Aux) Value Unwind ExitTerminal → Prop
  | .returned _ after | .unwound _ after => ∃ slot, after.1.resolve guard = some slot
  | .terminated _ => True

/-- Universal token availability at one actual provider input, including all
nondeterministic returns and unwinds. A terminal has no state to constrain. -/
def LiveAt {Aux Args Value Unwind ExitTerminal : Type} (guard : Borrow.Guard)
    (callback : Callback.Run (AnchorAccount.World Aux) Args Value Unwind ExitTerminal)
    (before : AnchorAccount.World Aux) (args : Args) : Prop :=
  ∀ produced, callback before args produced → ExitLive guard produced

/-- The candidate cleanup retains the exact pending value/reason and all
effects in the state of the provider except the consumed guard slot. Its legality
is established by `ExitLive.releasable`, not assumed by this definition. -/
def cleanupExit {Aux Value Unwind ExitTerminal : Type} (guard : Borrow.Guard) :
    Outcome (AnchorAccount.World Aux) Value Unwind ExitTerminal →
      Outcome (AnchorAccount.World Aux) Value Unwind ExitTerminal
  | .returned value after => .returned value ((Borrow.release after.1 guard).2, after.2)
  | .unwound reason after => .unwound reason ((Borrow.release after.1 guard).2, after.2)
  | .terminated reason => .terminated reason

/-- The actual checked local release exists with its exact pending exit and
retires the token. This is availability of cleanup at a primitive prefix;
it does not assert that successful error construction drops its guard early. -/
def Releasable {Aux Value Unwind ExitTerminal : Type} (guard : Borrow.Guard)
    (produced : Outcome (AnchorAccount.World Aux) Value Unwind ExitTerminal) : Prop :=
  AccountInfo.GuardCallback.releaseOutcome guard produced = some (cleanupExit guard produced) ∧
    match cleanupExit guard produced with
    | .returned _ after | .unwound _ after => after.1.resolve guard = none
    | .terminated _ => True

/-- Token availability supplies actual successful cleanup on every finite
state-bearing exit, without rolling back callback effects or inventing a
post-state for a terminal. -/
theorem ExitLive.releasable {Aux Value Unwind ExitTerminal : Type} {guard : Borrow.Guard}
    {produced : Outcome (AnchorAccount.World Aux) Value Unwind ExitTerminal}
    (live : ExitLive guard produced) : Releasable guard produced := by
  cases produced with
  | returned value after =>
    obtain ⟨slot, live⟩ := live
    exact ⟨by simp only [AccountInfo.GuardCallback.releaseOutcome, cleanupExit,
      Borrow.release_live live], Borrow.release_consumes live⟩
  | unwound reason after =>
    obtain ⟨slot, live⟩ := live
    exact ⟨by simp only [AccountInfo.GuardCallback.releaseOutcome, cleanupExit,
      Borrow.release_live live], Borrow.release_consumes live⟩
  | terminated reason => exact ⟨rfl, trivial⟩

/-- Minimal held-token obligations at each source-ordered error allocation.
Earlier returns are checked even if a later provider has no finite outcome.
The fixed error provider has Empty unwind; terminal allocation exits remain
unconstrained, while `LiveAt` itself also handles state-bearing unwind. -/
structure FactoryReady (types : Types) (before : AnchorAccount.World types.Aux)
    (guard : Borrow.Guard) (failure : AnchorAccount.Code) : Prop where
  /-- Every actual name-allocation return retains the token of the caller. -/
  name : LiveAt guard types.errors.copyLiteral before failure.payload.name
  /-- Message allocation is checked at every reached name-return state. -/
  message : ∀ name afterName,
    types.errors.copyLiteral before failure.payload.name (.returned name afterName) →
      LiveAt guard types.errors.formatLiteral afterName failure.payload.message
  /-- Box allocation is checked after every actual name/message return pair. -/
  boxed : ∀ name afterName,
    types.errors.copyLiteral before failure.payload.name (.returned name afterName) →
    ∀ message afterMessage,
    types.errors.formatLiteral afterName failure.payload.message (.returned message afterMessage) →
      LiveAt guard types.errors.newBox afterMessage
        (.anchor ⟨name, failure.payload.code, message, none, none⟩)

/-- Concrete local cleanup is available after every reached allocation exit.
These three conclusions concern different actual provider inputs; none is
inferred from the existence of a later whole-factory execution. -/
structure FactoryCheckpoints (types : Types) (before : AnchorAccount.World types.Aux)
    (guard : Borrow.Guard) (failure : AnchorAccount.Code) : Prop where
  /-- Release succeeds and retires the guard after every name exit. -/
  name : ∀ produced, types.errors.copyLiteral before failure.payload.name produced →
    Releasable guard produced
  /-- Release succeeds at every reached message exit. -/
  message : ∀ name afterName,
    types.errors.copyLiteral before failure.payload.name (.returned name afterName) →
    ∀ produced, types.errors.formatLiteral afterName failure.payload.message produced →
      Releasable guard produced
  /-- Release succeeds at every reached Box exit. -/
  boxed : ∀ name afterName,
    types.errors.copyLiteral before failure.payload.name (.returned name afterName) →
    ∀ message afterMessage,
    types.errors.formatLiteral afterName failure.payload.message (.returned message afterMessage) →
    ∀ produced, types.errors.newBox afterMessage
      (.anchor ⟨name, failure.payload.code, message, none, none⟩) produced →
        Releasable guard produced

/-- Each primitive assumption establishes an actual checked release and
retirement at the current exit state of that primitive. -/
theorem FactoryReady.checkpoints {types : Types} {before : AnchorAccount.World types.Aux}
    {guard : Borrow.Guard} {failure : AnchorAccount.Code}
    (ready : FactoryReady types before guard failure) :
    FactoryCheckpoints types before guard failure := by
  refine ⟨?_, ?_, ?_⟩
  · intro produced called
    exact (ready.name produced called).releasable
  · intro name afterName named produced called
    exact (ready.message name afterName named produced called).releasable
  · intro name afterName named message afterMessage formatted produced called
    exact (ready.boxed name afterName named message afterMessage formatted produced
      called).releasable

/-- The final state-bearing exit of a completed factory comes from its Box
allocation. This conclusion needs only that actual final-site capability;
the earlier sites have their separate checkpoint conclusions above. -/
theorem code_live {types : Types} {before : AnchorAccount.World types.Aux}
    {guard : Borrow.Guard} {failure : AnchorAccount.Code}
    (boxed : ∀ name afterName,
      types.errors.copyLiteral before failure.payload.name (.returned name afterName) →
      ∀ message afterMessage,
      types.errors.formatLiteral afterName failure.payload.message (.returned message afterMessage)
        →
        LiveAt guard types.errors.newBox afterMessage
          (.anchor ⟨name, failure.payload.code, message, none, none⟩)) :
    LiveAt guard (code types failure) before () := by
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
      have live := boxed name afterName named message afterMessage formatted boxExit allocated
      cases boxExit with
      | returned resource after => cases mapped; cases lifted; exact live
      | unwound impossible _ => nomatch impossible
      | terminated reason => cases mapped; cases lifted; trivial

/-- Source admission supplies only the actual current-data read and the primitive token obligations
of the reached discriminator factory. Writable and borrow errors need no held-guard factory;
mapping panics remain admitted. -/
def Admission (mode : Borrow.Mode) (types : Types) (before : AnchorAccount.World types.Aux)
    (args : AnchorAccount.LoadArgs types.layout) : Prop :=
  AnchorAccount.LoadReady mode before.1 args ∧
    if mode = .exclusive ∧ args.loader.info.isWritable = false then True
    else
      match AccountInfo.tryBorrow mode args.loader.info.data before.1 with
      | (.error _, _) => True
      | (.ok guard, during) =>
        match Borrow.current during guard with
        | .error _ | .ok (_, .lamports _) => True
        | .ok (_, .data bytes) =>
          match AnchorConstructOwned.discriminatorFailure types.layout.discriminator bytes with
          | none => True
          | some failure => FactoryReady types (during, before.2) guard failure

/-- The owned adapter retains the actual successful transfer of the common mapping,
unwind cleanup or abort. Its error variant cannot be fabricated by mapping. -/
theorem mapLoaded_complete {types : Types} (args : AnchorAccount.LoadArgs types.layout)
    {before : AnchorAccount.World types.Aux} {guard : Borrow.Guard}
    {view : AccountInfo.View} {bytes : _root_.Solanalib.Runtime.Bytes}
    (current : Borrow.current before.1 guard = .ok (view, .data bytes)) :
    ∃ outcome, mapLoaded types args before guard bytes outcome := by
  obtain ⟨produced, mapped, complete⟩ := AnchorAccount.mapLoaded_complete args current
  cases produced with
  | returned result after =>
    cases result with
    | error _ => cases complete
    | ok value => exact ⟨.returned (.ok value) (after, before.2), by simp only [mapLoaded, mapped]⟩
  | unwound reason after => exact ⟨.unwound reason (after, before.2), by simp only [mapLoaded,
    mapped]⟩
  | terminated reason => exact ⟨.terminated (.inl reason), by simp only [mapLoaded, mapped]⟩

/-- Admission establishes actual current data at each successful acquisition.
Every reached primitive checkpoint supports checked cleanup, and every finite
whole error-factory exit has its exact outer continuation. If no discriminator
error occurs, the local mapping has a real finite result instead. This theorem
does not assume an outcome or termination for any dependency. -/
theorem local_continuations {mode : Borrow.Mode} {types : Types}
    {before : AnchorAccount.World types.Aux} {args : AnchorAccount.LoadArgs types.layout}
    (admitted : Admission mode types before args)
    (allowed : ¬ (mode = .exclusive ∧ args.loader.info.isWritable = false))
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrow mode args.loader.info.data before.1 = (.ok guard, during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) ∧
      match AnchorConstructOwned.discriminatorFailure types.layout.discriminator bytes with
      | some failure =>
        FactoryCheckpoints types (during, before.2) guard failure ∧
          ∀ produced, Callback.map Except.error (code types failure) (during, before.2) () produced
            →
            AccountInfo.GuardCallback.releaseOutcome guard produced = some (cleanupExit guard
              produced) ∧
              run mode types before args (cleanupExit guard produced)
      | none => ∃ outcome, mapLoaded types args (during, before.2) guard bytes outcome ∧
          run mode types before args outcome := by
  have typed : AccountInfo.DataBorrow.Ready mode before.1 args.loader.info.data := by
    simpa only [AnchorAccount.LoadReady, ite_eq_right allowed] using admitted.1
  obtain ⟨bytes, current⟩ := AccountInfo.DataBorrow.ready_current typed acquired
  refine ⟨bytes, current, ?_⟩
  cases failed : AnchorConstructOwned.discriminatorFailure types.layout.discriminator bytes with
  | none =>
    obtain ⟨outcome, mapped⟩ := mapLoaded_complete (before := (during, before.2)) args current
    exact ⟨outcome, mapped, by
      simpa only [run, ite_eq_right allowed, acquired, current, failed] using mapped⟩
  | some failure =>
    have ready : FactoryReady types (during, before.2) guard failure := by
      simpa only [Admission, ite_eq_right allowed, acquired, current, failed] using admitted.2
    refine ⟨ready.checkpoints, ?_⟩
    rintro produced ⟨original, called, rfl⟩
    have live := code_live ready.boxed original called
    have mappedLive : ExitLive guard
        (Outcome.map (fun error => (Except.error error : Result types)) original) := by
      cases original <;> exact live
    have released := mappedLive.releasable
    exact ⟨released.1, by
      simp only [run, ite_eq_right allowed, acquired, current, failed, AnchorEffects.withGuard]
      exact ⟨Outcome.map Except.error original, ⟨original, called, rfl⟩, released.1⟩⟩

/-- Only a reached discriminator-error factory has held-guard obligations.
Each of its primitive calls is universally admitted at the actual input;
the writable rejection, failed borrow, and mapping paths have no such call. -/
def Ready (mode : Borrow.Mode) (types : Types) (before : AnchorAccount.World types.Aux)
    (args : AnchorAccount.LoadArgs types.layout) : Prop :=
  ¬ (mode = .exclusive ∧ args.loader.info.isWritable = false) →
    ∀ guard during, AccountInfo.tryBorrow mode args.loader.info.data before.1 = (.ok guard, during)
      →
      ∀ view bytes, Borrow.current during guard = .ok (view, .data bytes) →
        ∀ failure, AnchorConstructOwned.discriminatorFailure types.layout.discriminator bytes =
          some failure →
          AnchorGuardEffects.BuildCodeAdmissible types.errors (during, before.2) guard
            ⟨failure.payload.name, failure.payload.code, failure.payload.message⟩

/-- Every actual guarded error-factory exit has the same cleanup and whole-load
exit under the primitive preconditions, including exact terminal forwarding. -/
theorem Ready.retain {mode : Borrow.Mode} {types : Types}
    {before : AnchorAccount.World types.Aux} {args : AnchorAccount.LoadArgs types.layout}
    (ready : Ready mode types before args)
    (allowed : ¬ (mode = .exclusive ∧ args.loader.info.isWritable = false))
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrow mode args.loader.info.data before.1 = (.ok guard, during))
    {view : AccountInfo.View} {bytes : _root_.Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes))
    {failure : AnchorAccount.Code}
    (failed : AnchorConstructOwned.discriminatorFailure types.layout.discriminator bytes = some
      failure)
    {produced : Outcome (AnchorAccount.World types.Aux) (Result types) AnchorAccount.LoadPanic
      (Terminal types)}
    (called : Callback.map Except.error (code types failure) (during, before.2) () produced) :
    ∃ outcome, AnchorAccount.releaseOutcome guard produced = some outcome ∧
      run mode types before args outcome := by
  have admitted := (code_admissible
    (ready allowed guard during acquired view bytes current failure failed)).map
      (fun error => (Except.error error : Result types))
  have live : during.resolve guard = some ⟨args.loader.info.data, mode, 0, .whole⟩ :=
    AccountInfo.GuardCallback.tryBorrow_live acquired
  obtain ⟨outcome, released, retained⟩ := admitted.retain live called
  exact ⟨outcome, released, by
    simpa only [run, ite_eq_right allowed, acquired, current, failed, AnchorEffects.withGuard]
      using retained⟩

/-- The raw load relation keeps every modeled exit. Its source domain supplies
the selected read and reached allocator obligations consumed by
`local_continuations`; it does not promise provider termination. -/
def family (mode : Borrow.Mode) : Family where
  Index := Types
  State := fun types => AnchorAccount.World types.Aux
  Args := fun types => AnchorAccount.LoadArgs types.layout
  Value := Result
  Unwind := fun _ => AnchorAccount.LoadPanic
  Terminal := Terminal
  contract := fun types => {
    requires := Admission mode types
    post := run mode types }

/-- The same raw load relation at every source-domain family index. -/
def reference (mode : Borrow.Mode) : FamilyRun (family mode) := run mode

theorem reference_holds (mode : Borrow.Mode) : FamilyReference (family mode) (reference mode) := by
  intro _ _ _ _ _ step
  exact step

end Solanalib.Specs.Core.AnchorLoadingOwned
