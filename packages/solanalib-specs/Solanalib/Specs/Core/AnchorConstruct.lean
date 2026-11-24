/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLoading
public import Solanalib.Specs.Core.AccountInfoGuardCallback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorAccount

abbrev World (Aux : Type) := Borrow.World AccountInfo.Content AccountInfo.View Aux

/-- Local getter panics remain distinct from an unwind from a supplied callback or
termination reason. -/
abbrev ConstructorUnwind (Unwind : Type) := AccountInfo.Panic ⊕ Unwind
abbrev ConstructorTerminal (Terminal : Type) := AccountInfo.Panic ⊕ Terminal

/-- Preserve all callback effects and tag its nonlocal exit reason. -/
def widen {State Value Unwind Terminal : Type} :
    Outcome State Value Unwind Terminal →
      Outcome State Value (ConstructorUnwind Unwind) (ConstructorTerminal Terminal)
  | .returned value after => .returned value after
  | .unwound reason after => .unwound (.inr reason) after
  | .terminated reason => .terminated (.inr reason)

def widenCallback {State Args Value Unwind Terminal : Type}
    (callback : Callback.Run State Args Value Unwind Terminal) :
    Callback.Run State Args Value (ConstructorUnwind Unwind) (ConstructorTerminal Terminal) :=
  fun before args outcome => ∃ produced, callback before args produced ∧ widen produced = outcome

/-- Widening the exit vocabulary changes neither the guard frame nor the
actual callback state. -/
theorem widen_frame {Aux Value Unwind Terminal : Type} {before : World Aux}
    {guard : Borrow.Guard} {produced : Outcome (World Aux) Value Unwind Terminal}
    (frame : AccountInfo.GuardCallback.Frame before guard produced) :
    AccountInfo.GuardCallback.Frame before guard (widen produced) := by
  cases produced <;> exact frame

/-- Universal admission survives the explicit exit tags of the constructor. -/
theorem widenCallback_admissible {Aux Args Value Unwind Terminal : Type}
    {callback : Callback.Run (World Aux) Args Value Unwind Terminal}
    {before : World Aux} {args : Args} {guard : Borrow.Guard}
    (admitted : AccountInfo.GuardCallback.Admissible guard callback before args) :
    AccountInfo.GuardCallback.Admissible guard (widenCallback callback) before args := by
  rintro _ ⟨produced, called, rfl⟩
  exact widen_frame (admitted produced called)

/-- Sequencing for the `?` operator in the source: a returned error short-circuits with the current
state of the callback, whereas success continues in that same state. -/
def resultBind {State Args First Last Unwind Terminal : Type}
    (first : Callback.Run State Args (Except Error First) Unwind Terminal)
    (next : First → State → Outcome State (Except Error Last) Unwind Terminal → Prop) :
    Callback.Run State Args (Except Error Last) Unwind Terminal :=
  Callback.bind first fun result after outcome => match result with
    | .error error => outcome = .returned (.error error) after
    | .ok value => next value after outcome

/-- The trait may replace its local `&[u8]` cursor on either return branch.
The cursor is not required to be a suffix: that is a law of a particular codec. -/
structure Decoded (Payload : Type) where
  result : Except Error Payload
  cursor : _root_.Solanalib.Runtime.Bytes

structure DecodeArgs where
  info : AccountInfo.Value
  guard : Borrow.Guard
  bytes : _root_.Solanalib.Runtime.Bytes

/-- The generic traits are explicit relations over the whole modeled world.
Owner and CheckOwner need not be pure, deterministic or total. Deserialization
has a separate held-borrow frame at each state-bearing finite exit. Current
owners are read through an explicit projection from mutable auxiliary state;
CheckOwner receives the reference identity, as the source passes `&Pubkey`. -/
structure ConstructorIndex where
  Aux : Type
  Payload : Type
  Unwind : Type
  Terminal : Type
  discriminator : _root_.Solanalib.Runtime.Bytes
  ownerAt : AccountInfo.OwnerAt Aux
  owner : Callback.Run (World Aux) Unit _root_.Solanalib.Runtime.Pubkey Unwind Terminal
  checkOwner : Callback.Run (World Aux) AccountInfo.OwnerRef (Except Error Unit) Unwind Terminal
  deserialize : Callback.Run (World Aux) DecodeArgs (Decoded Payload) Unwind Terminal

/-- A shared data codec may affect captured auxiliary state and other cells,
but it cannot modify the contents protected by its held shared data guard. -/
def sharedDataFootprint : Borrow.Footprint AccountInfo.Content AccountInfo.View :=
  AccountInfo.GuardCallback.footprint

theorem sharedDataFrame_refl (state : AccountInfo.State) (guard : Borrow.Guard)
    (valid : state.Valid) : Borrow.CallbackFrame sharedDataFootprint state state guard := by
  exact Borrow.CallbackFrame.refl state guard valid sharedDataFootprint (fun _ _ _ => rfl)

/-- Frame every normal or unwinding decoder exit, while retaining all effects
outside the protected cell. A terminal exit supplies no state to constrain. -/
def decodeFrame {Aux Payload Unwind Terminal : Type}
    (before : World Aux) (guard : Borrow.Guard)
    (produced : Outcome (World Aux) (Decoded Payload) Unwind Terminal) : Prop :=
  AccountInfo.GuardCallback.Frame before guard produced

/-- Cleanup acts on the actual callback state, so an error or panic does not
undo its writes to other cells or captured state. -/
abbrev releaseOutcome {Aux Value Unwind Terminal : Type} (guard : Borrow.Guard) :
    Outcome (World Aux) Value Unwind Terminal →
      Option (Outcome (World Aux) Value Unwind Terminal) :=
  AccountInfo.GuardCallback.releaseOutcome guard

/-- The all-zero 32-byte address is the declared address of the system program. -/
def systemProgramId : _root_.Solanalib.Runtime.Pubkey := .zero

/-- The short-circuit condition of the source calls lamports only for a system-owned
account. Non-system-owned accounts do not acquire the lamports cell here. -/
def initialized {Aux Unwind Terminal : Type} (ownerAt : AccountInfo.OwnerAt Aux)
    (before : World Aux) (args : AccountInfo.Args) :
    Option (Outcome (World Aux) (Except Error Unit)
      (ConstructorUnwind Unwind) (ConstructorTerminal Terminal)) :=
  if ownerAt before.2 args.info.ownerRef = systemProgramId then
    match AccountInfo.observe .lamports before.1 args.info with
    | (.malformed, _) => none
    | (.value balance, after) =>
      some (.returned (if balance = 0 then .error (error .notInitialized) else .ok ())
        (after, before.2))
    | (.borrowFailed, after) =>
      if args.profile.aborts then some (.terminated (.inl .borrowFailed))
      else some (.unwound (.inl .borrowFailed) (after, before.2))
  else some (.returned (.ok ()) before)

/-- Only the system-owner branch reads lamports. Its actual observation must
not be malformed; zero balances and checked borrow failures remain admitted.
No unrelated account field, target width or whole representation is required. -/
def InitReady {Aux : Type} (ownerAt : AccountInfo.OwnerAt Aux)
    (before : World Aux) (args : AccountInfo.Args) : Prop :=
  ownerAt before.2 args.info.ownerRef = systemProgramId →
    (AccountInfo.observe .lamports before.1 args.info).1 ≠ .malformed

/-- The branch-local read domain supplies the actual finite
observation of the initializer, including zero balance, unwind, abort and non-system bypass. -/
theorem InitReady.hasOutcome {Aux Unwind Terminal : Type}
    {ownerAt : AccountInfo.OwnerAt Aux} {before : World Aux} {args : AccountInfo.Args}
    (ready : InitReady ownerAt before args) :
    ∃ outcome, initialized (Unwind := Unwind) (Terminal := Terminal)
      ownerAt before args = some outcome := by
  by_cases system : ownerAt before.2 args.info.ownerRef = systemProgramId
  · have represented := ready system
    cases observed : AccountInfo.observe .lamports before.1 args.info with
    | mk result after =>
      cases result with
      | malformed => simp [observed] at represented
      | value balance =>
        exact ⟨.returned (if balance = 0 then .error (error .notInitialized) else .ok ())
          (after, before.2), by simp only [initialized, system, observed, ↓reduceIte]⟩
      | borrowFailed =>
        cases strategy : args.profile.aborts with
        | false => exact ⟨.unwound (.inl .borrowFailed) (after, before.2),
            by simp only [initialized, system, observed, strategy, ↓reduceIte, Bool.false_eq_true]⟩
        | true => exact ⟨.terminated (.inl .borrowFailed),
            by simp only [initialized, system, observed, strategy, ↓reduceIte]⟩
  · exact ⟨.returned (.ok ()) before, by simp only [initialized, system, ↓reduceIte]⟩

/-- This is exactly the domain of the raw initializer, rather than a stronger
well-formedness bundle imposed on paths that never read lamports. -/
theorem initReady_iff_hasOutcome {Aux Unwind Terminal : Type}
    (ownerAt : AccountInfo.OwnerAt Aux) (before : World Aux) (args : AccountInfo.Args) :
    InitReady ownerAt before args ↔
      ∃ outcome, initialized (Unwind := Unwind) (Terminal := Terminal)
        ownerAt before args = some outcome := by
  constructor
  · exact InitReady.hasOutcome
  · rintro ⟨outcome, actual⟩ system malformed
    cases observed : AccountInfo.observe .lamports before.1 args.info with
    | mk result after =>
      have same : result = .malformed := by simpa only [observed] using malformed
      cases same
      simp only [initialized, system, observed, ↓reduceIte] at actual
      cases actual

/-- The left comparison operand is an owner reference: its pointed value is
read after the first `T::owner()` callback. A mismatch then copies that value
before calling `T::owner()` again for the diagnostic. Both callback effects
remain, while the copied diagnostic key survives a second owner assignment. -/
def ownerCheck (index : ConstructorIndex) (before : World index.Aux) (args : AccountInfo.Args) :
    Outcome (World index.Aux) (Except Error Unit)
      (ConstructorUnwind index.Unwind) (ConstructorTerminal index.Terminal) → Prop :=
  Callback.bind (widenCallback index.owner)
    (fun expected after outcome =>
      let observed := index.ownerAt after.2 args.info.ownerRef
      if observed = expected then outcome = .returned (.ok ()) after
      else Callback.map
        (fun diagnostic => Except.error
          ((error .ownedByWrongProgram).replaceCompared (.pubkeys observed diagnostic)))
        (widenCallback index.owner) after () outcome)
    before ()

/-- Deserialization is called while the acquired shared guard is live. Every
callback exit with checked cleanup is retained, including a nonadmitted frame
violation. The source interpretation supplies `DecodeReady` separately. -/
def decodeAccount (index : ConstructorIndex) (before : World index.Aux) (args : AccountInfo.Args) :
    Outcome (World index.Aux) (Except Error index.Payload)
      (ConstructorUnwind index.Unwind) (ConstructorTerminal index.Terminal) → Prop :=
  let (borrowed, during) := AccountInfo.tryBorrowData before.1 args
  match borrowed with
  | .error failure => fun outcome => outcome = .returned (.error (programError failure)) (during,
    before.2)
  | .ok guard => match Borrow.current during guard with
    | .error _ | .ok (_, .lamports _) => fun _ => False
    | .ok (_, .data bytes) => fun outcome => ∃ produced,
      index.deserialize (during, before.2) ⟨args.info, guard, bytes⟩ produced ∧
      releaseOutcome guard (Outcome.map Decoded.result (widen produced)) = some outcome

/-- The selected data cell exists before borrowing. Every actual codec exit at
the acquired guard must frame that guard and its current shared bytes. This is
universal call admission, never a filter on individual outcomes. -/
def DecodeReady (index : ConstructorIndex) (before : World index.Aux) (args : AccountInfo.Args) :
  Prop :=
  (∃ bytes policy, before.1.lookupCell args.info.data = some ⟨.data bytes, policy⟩) ∧
    ∀ guard during, AccountInfo.tryBorrowData before.1 args = (.ok guard, during) →
      ∀ view bytes, Borrow.current during guard = .ok (view, .data bytes) →
        AccountInfo.GuardCallback.Admissible guard index.deserialize (during, before.2)
          ⟨args.info, guard, bytes⟩

/-- Selected data-cell typing rules out a malformed read after successful
acquisition. The actual bytes and universal codec admission exist. -/
theorem DecodeReady.callback_input {index : ConstructorIndex} {before : World index.Aux}
    {args : AccountInfo.Args} (ready : DecodeReady index before args)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) ∧
      AccountInfo.GuardCallback.Admissible guard index.deserialize (during, before.2)
        ⟨args.info, guard, bytes⟩ := by
  obtain ⟨bytes, current⟩ := AccountInfo.GuardCallback.data_current ready.1 acquired
  exact ⟨bytes, current, ready.2 guard during acquired .whole bytes current⟩

/-- Admission consumes an actual codec execution and proves an exact decoder
exit exists, including returned errors, unwinds, and terminal exits. -/
theorem DecodeReady.retain {index : ConstructorIndex} {before : World index.Aux}
    {args : AccountInfo.Args} (ready : DecodeReady index before args)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during))
    {view : AccountInfo.View} {bytes : _root_.Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes))
    {produced : Outcome (World index.Aux) (Decoded index.Payload) index.Unwind index.Terminal}
    (called : index.deserialize (during, before.2) ⟨args.info, guard, bytes⟩ produced) :
    ∃ outcome, releaseOutcome guard (Outcome.map Decoded.result (widen produced)) = some outcome ∧
      decodeAccount index before args outcome := by
  have frame := (widen_frame (ready.2 guard during acquired view bytes current produced called)).map
    Decoded.result
  have live : during.resolve guard = some ⟨args.info.data, .shared, 0, .whole⟩ :=
    AccountInfo.GuardCallback.tryBorrow_live acquired
  obtain ⟨outcome, released⟩ := frame.release_exists live
  refine ⟨outcome, released, ?_⟩
  simpa only [decodeAccount, acquired, current] using ⟨produced, called, released⟩

/-- Loader construction checks a shared borrow and the discriminator only. It
releases its temporary guard on either checked branch and never decodes `T`. -/
def checkLoaderData (index : ConstructorIndex) (before : World index.Aux) (args : AccountInfo.Args)
  :
    Outcome (World index.Aux) (Except Error Unit)
      (ConstructorUnwind index.Unwind) (ConstructorTerminal index.Terminal) → Prop :=
  let (borrowed, during) := AccountInfo.tryBorrowData before.1 args
  match borrowed with
  | .error failure => fun outcome => outcome = .returned (.error (programError failure)) (during,
    before.2)
  | .ok guard => match Borrow.current during guard with
    | .error _ | .ok (_, .lamports _) => fun _ => False
    | .ok (_, .data bytes) => fun outcome =>
      releaseOutcome guard
        (.returned (discriminatorCheck index.discriminator bytes) (during, before.2)) = some outcome

inductive Constructor where
  | account
  | interfaceAccount
  | loader
  deriving DecidableEq, Repr

def Constructor.Result (kind : Constructor) (Payload : Type) : Type :=
  match kind with
  | .account => Account Payload
  | .interfaceAccount => InterfaceAccount Payload
  | .loader => Loader Payload

/-- Compose the exact account-validation order. Account and InterfaceAccount
first check initialization; Loader does not. Only InterfaceAccount uses the
CheckOwner callback, and only the two decoded wrappers invoke the codec.
InterfaceAccount records the current owner after decoding, as its constructor
reads `*info.owner` only after the decoder has returned successfully. -/
def construct (kind : Constructor) (index : ConstructorIndex) :
    Callback.Run (World index.Aux) AccountInfo.Args
      (Except Error (kind.Result index.Payload))
      (ConstructorUnwind index.Unwind) (ConstructorTerminal index.Terminal) :=
  match kind with
  | .account => fun before args outcome =>
    resultBind (fun state input result => initialized index.ownerAt state input = some result)
      (fun _ after result =>
        resultBind (ownerCheck index)
          (fun _ checked result =>
            Callback.map (Except.map fun value => Account.mk value args.info)
              (decodeAccount index) checked args result)
          after args result)
      before args outcome
  | .interfaceAccount => fun before args outcome =>
    resultBind (fun state input result => initialized index.ownerAt state input = some result)
      (fun _ after result =>
        resultBind (widenCallback index.checkOwner)
          (fun _ checked result =>
            Callback.bind (decodeAccount index)
              (fun decoded afterDecode outcome => outcome = .returned
                (decoded.map fun value => InterfaceAccount.mk ⟨value, args.info⟩
                  (index.ownerAt afterDecode.2 args.info.ownerRef)) afterDecode)
              checked args result)
          after args.info.ownerRef result)
      before args outcome
  | .loader => fun before args outcome =>
    resultBind (ownerCheck index)
      (fun _ checked result =>
        Callback.map (Except.map fun _ => Loader.mk args.info)
          (checkLoaderData index) checked args result)
      before args outcome

/-- Admission first excludes a malformed initialization read on the actual
system-owner branch. It then checks each reached data scope after the actual
initialization and owner callbacks, covering every codec exit there,
including an exit that would otherwise make the following release undefined.
No callback termination or law at an unreachable input is assumed. -/
def ConstructorReady (kind : Constructor) (index : ConstructorIndex)
    (before : World index.Aux) (args : AccountInfo.Args) : Prop :=
  match kind with
  | .account => InitReady index.ownerAt before args ∧
      ∀ after, initialized (Unwind := index.Unwind) (Terminal := index.Terminal)
      index.ownerAt before args = some (.returned (.ok ()) after) →
      ∀ checked, ownerCheck index after args (.returned (.ok ()) checked) →
        DecodeReady index checked args
  | .interfaceAccount => InitReady index.ownerAt before args ∧ ∀ after,
      initialized (Unwind := index.Unwind) (Terminal := index.Terminal)
        index.ownerAt before args = some (.returned (.ok ()) after) →
      ∀ checked, widenCallback index.checkOwner after args.info.ownerRef
        (.returned (.ok ()) checked) → DecodeReady index checked args
  | .loader => ∀ checked, ownerCheck index before args (.returned (.ok ()) checked) →
      ∃ bytes policy, checked.1.lookupCell args.info.data = some ⟨.data bytes, policy⟩

/-- The post remains the raw constructor relation. Its reached-call admission
ensures that a finite codec exit is not lost solely at checked guard cleanup. -/
def constructorFamily (kind : Constructor) : Family where
  Index := ConstructorIndex
  State := fun i => World i.Aux
  Args := fun _ => AccountInfo.Args
  Value := fun i => Except Error (kind.Result i.Payload)
  Unwind := fun i => ConstructorUnwind i.Unwind
  Terminal := fun i => ConstructorTerminal i.Terminal
  contract := fun i => {
    requires := ConstructorReady kind i
    post := construct kind i }

def constructorRun (kind : Constructor) : FamilyRun (constructorFamily kind) := construct kind

theorem constructor_reference (kind : Constructor) :
    FamilyReference (constructorFamily kind) (constructorRun kind) := by
  intro _ _ _ _ _ step
  exact step

/-- Every actual codec exit at an admitted Account prefix has a complete
constructor exit. The equality records its checked release before wrapping
only the ordinary return value; errors, unwind state and termination survive. -/
theorem constructor_account_retain {index : ConstructorIndex}
    {before after checked : World index.Aux} {args : AccountInfo.Args}
    (ready : ((constructorFamily .account).contract index).requires before args)
    (started : initialized (Unwind := index.Unwind) (Terminal := index.Terminal)
      index.ownerAt before args = some (.returned (.ok ()) after))
    (owned : ownerCheck index after args (.returned (.ok ()) checked))
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData checked.1 args = (.ok guard, during))
    {view : AccountInfo.View} {bytes : _root_.Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes))
    {produced : Outcome (World index.Aux) (Decoded index.Payload) index.Unwind index.Terminal}
    (called : index.deserialize (during, checked.2) ⟨args.info, guard, bytes⟩ produced) :
    ∃ decoded, releaseOutcome guard (Outcome.map Decoded.result (widen produced)) = some decoded ∧
      construct .account index before args
        (Outcome.map (Except.map fun value => Account.mk value args.info) decoded) := by
  obtain ⟨decoded, released, ran⟩ := (ready.2 after started checked owned).retain acquired current
    called
  exact ⟨decoded, released, .returned (.ok ()) after, started,
    .returned (.ok ()) checked, owned, decoded, ran, rfl⟩

/-- InterfaceAccount also retains each actual admitted exit. Its successful
wrapper copies the owner in the released state of the decoder, as the source does. -/
theorem constructor_interface_retain {index : ConstructorIndex}
    {before after checked : World index.Aux} {args : AccountInfo.Args}
    (ready : ((constructorFamily .interfaceAccount).contract index).requires before args)
    (started : initialized (Unwind := index.Unwind) (Terminal := index.Terminal)
      index.ownerAt before args = some (.returned (.ok ()) after))
    (owned : widenCallback index.checkOwner after args.info.ownerRef (.returned (.ok ()) checked))
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData checked.1 args = (.ok guard, during))
    {view : AccountInfo.View} {bytes : _root_.Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes))
    {produced : Outcome (World index.Aux) (Decoded index.Payload) index.Unwind index.Terminal}
    (called : index.deserialize (during, checked.2) ⟨args.info, guard, bytes⟩ produced) :
    ∃ decoded, releaseOutcome guard (Outcome.map Decoded.result (widen produced)) = some decoded ∧
      construct .interfaceAccount index before args
        (Outcome.bind decoded fun value final => .returned
          (value.map fun payload => InterfaceAccount.mk ⟨payload, args.info⟩
            (index.ownerAt final.2 args.info.ownerRef)) final) := by
  obtain ⟨decoded, released, ran⟩ := (ready.2 after started checked owned).retain acquired current
    called
  refine ⟨decoded, released, .returned (.ok ()) after, started,
    .returned (.ok ()) checked, owned, decoded, ran, ?_⟩
  cases decoded <;> rfl

/-- Typed selected data makes the allocation-free loader check nonempty,
including a checked borrow failure. No unrelated account field is required. -/
theorem checkLoaderData_hasOutcome {index : ConstructorIndex} {before : World index.Aux}
    {args : AccountInfo.Args}
    (typed : ∃ bytes policy, before.1.lookupCell args.info.data = some ⟨.data bytes, policy⟩) :
    ∃ outcome, checkLoaderData index before args outcome := by
  cases acquired : AccountInfo.tryBorrowData before.1 args with
  | mk result during =>
    cases result with
    | error failure =>
      exact ⟨.returned (.error (programError failure)) (during, before.2),
        by simp only [checkLoaderData, acquired]⟩
    | ok guard =>
      obtain ⟨bytes, current⟩ := AccountInfo.GuardCallback.data_current typed acquired
      have released := AccountInfo.GuardCallback.releaseOutcome_returned
        (AccountInfo.GuardCallback.tryBorrow_live acquired)
        (Unwind := ConstructorUnwind index.Unwind) (Terminal := ConstructorTerminal index.Terminal)
        (after := (during, before.2)) (discriminatorCheck index.discriminator bytes)
      exact ⟨_, by simpa only [checkLoaderData, acquired, current] using released⟩

/-- An admitted Loader owner-check return always continues through its local
borrow/discriminator check. This consumes the selected-cell admission. -/
theorem constructor_loader_continue {index : ConstructorIndex}
    {before checked : World index.Aux} {args : AccountInfo.Args}
    (ready : ((constructorFamily .loader).contract index).requires before args)
    (owned : ownerCheck index before args (.returned (.ok ()) checked)) :
    ∃ outcome, construct .loader index before args outcome := by
  obtain ⟨checkedOutcome, ran⟩ := checkLoaderData_hasOutcome (index := index) (ready checked owned)
  exact ⟨_, .returned (.ok ()) checked, owned, checkedOutcome, ran, rfl⟩

/-- Inhabited callbacks for the closed model witnesses. They are explicitly
mathematical functions; no production Owner or codec implementation is asserted. -/
def constructorSample : ConstructorIndex where
  Aux := Unit
  Payload := Nat
  Unwind := String
  Terminal := String
  discriminator := [10]
  ownerAt := fun _ _ => .zero
  owner := Callback.ofFunction (fun state _ => .returned .zero state)
  checkOwner := Callback.ofFunction (fun state _ => .returned (.ok ()) state)
  deserialize := Callback.ofFunction (fun state _ => .returned ⟨.ok 7, []⟩ state)

def sampleAfterInit : AccountInfo.State :=
  (AccountInfo.observe .lamports AccountInfo.sampleState AccountInfo.sampleInfo).2

def sampleDataDuring : AccountInfo.State :=
  (AccountInfo.tryBorrowData sampleAfterInit AccountInfo.sampleArgs).2

def sampleAfterDecode : AccountInfo.State := (Borrow.release sampleDataDuring ⟨1, 0⟩).2

theorem sampleAfterInit_valid : sampleAfterInit.Valid := by
  change (Borrow.release (Borrow.acquire AccountInfo.sampleState AccountInfo.sampleInfo.lamports
    .shared AccountInfo.View.whole).2 ⟨0, 0⟩).2.Valid
  exact Borrow.release_valid
    (Borrow.acquire_valid AccountInfo.sample_valid.2.1 _ _ _) _

theorem sampleDataDuring_valid : sampleDataDuring.Valid := by
  change (Borrow.acquire sampleAfterInit AccountInfo.sampleInfo.data
    .shared AccountInfo.View.whole).2.Valid
  exact Borrow.acquire_valid sampleAfterInit_valid _ _ _

theorem ownerCheck_sample (state : World Unit) :
    ownerCheck constructorSample state AccountInfo.sampleArgs (.returned (.ok ()) state) := by
  exact ⟨.returned .zero state, ⟨.returned .zero state, rfl, rfl⟩, rfl⟩

/-- The closed decoder sample satisfies the universal held-guard premise. -/
theorem decode_sample_ready : DecodeReady constructorSample (sampleAfterInit, ())
  AccountInfo.sampleArgs := by
  refine ⟨⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩, ?_⟩
  intro guard during acquired view bytes current produced called
  change (Except.ok (⟨1, 0⟩ : Borrow.Guard), sampleDataDuring) = (.ok guard, during) at acquired
  cases acquired
  change Except.ok (AccountInfo.View.whole, AccountInfo.Content.data [10, 20, 30]) =
    .ok (view, .data bytes) at current
  cases current
  cases called
  exact sharedDataFrame_refl _ _ sampleDataDuring_valid

/-- This sample executes a codec while holding the shared guard and releases
that guard after success. Its frame is a separate proved admission premise. -/
theorem decode_sample : decodeAccount constructorSample (sampleAfterInit, ()) AccountInfo.sampleArgs
    (.returned (.ok (7 : Nat)) (sampleAfterDecode, ())) := by
  exact ⟨.returned ⟨.ok (7 : Nat), []⟩ (sampleDataDuring, ()), rfl, rfl⟩

/-- The sample satisfies admission at every reached data scope, independently
of the complete execution witness below. -/
theorem constructor_sample_ready (kind : Constructor) :
    ConstructorReady kind constructorSample (AccountInfo.sampleState, ()) AccountInfo.sampleArgs :=
      by
  cases kind with
  | account =>
    refine ⟨?_, ?_⟩
    · intro _ impossible
      cases impossible
    intro after started checked owned
    change (some (.returned (.ok ()) (sampleAfterInit, ())) :
      Option (Outcome (World Unit) (Except Error Unit) (ConstructorUnwind String)
        (ConstructorTerminal String))) = some (.returned (.ok ()) after) at started
    cases started
    have same : checked = (sampleAfterInit, ()) := by
      simp [ownerCheck, constructorSample, widenCallback, Callback.ofFunction, Callback.bind,
        widen] at owned
      exact (Outcome.returned.inj owned).2
    cases same
    exact decode_sample_ready
  | interfaceAccount =>
    refine ⟨?_, ?_⟩
    · intro _ impossible
      cases impossible
    intro after started checked owned
    change (some (.returned (.ok ()) (sampleAfterInit, ())) :
      Option (Outcome (World Unit) (Except Error Unit) (ConstructorUnwind String)
        (ConstructorTerminal String))) = some (.returned (.ok ()) after) at started
    cases started
    have same : checked = (sampleAfterInit, ()) := by
      simp [constructorSample, widenCallback, Callback.ofFunction, widen] at owned
      exact (Outcome.returned.inj owned).2.symm
    cases same
    exact decode_sample_ready
  | loader =>
    intro checked owned
    have same : checked = (AccountInfo.sampleState, ()) := by
      simp [ownerCheck, constructorSample, widenCallback, Callback.ofFunction, Callback.bind,
        widen] at owned
      exact (Outcome.returned.inj owned).2
    cases same
    exact ⟨[10, 20, 30], AccountInfo.sampleProfile.policy, rfl⟩

theorem constructor_execution (kind : Constructor) :
    FamilyHasExecution (constructorFamily kind) (constructorRun kind) constructorSample := by
  cases kind with
  | account =>
    refine ⟨(AccountInfo.sampleState, ()), AccountInfo.sampleArgs,
      .returned (.ok (Account.mk (7 : Nat) AccountInfo.sampleInfo)) (sampleAfterDecode, ()),
      constructor_sample_ready .account, ?_⟩
    refine ⟨.returned (.ok ()) (sampleAfterInit, ()), rfl, ?_⟩
    refine ⟨.returned (.ok ()) (sampleAfterInit, ()), ownerCheck_sample _, ?_⟩
    exact ⟨.returned (.ok (7 : Nat)) (sampleAfterDecode, ()), decode_sample, rfl⟩
  | interfaceAccount =>
    refine ⟨(AccountInfo.sampleState, ()), AccountInfo.sampleArgs,
      .returned (.ok (InterfaceAccount.mk ⟨(7 : Nat), AccountInfo.sampleInfo⟩ .zero))
        (sampleAfterDecode, ()), constructor_sample_ready .interfaceAccount, ?_⟩
    refine ⟨.returned (.ok ()) (sampleAfterInit, ()), rfl, ?_⟩
    refine ⟨.returned (.ok ()) (sampleAfterInit, ()),
      ⟨.returned (.ok ()) (sampleAfterInit, ()), rfl, rfl⟩, ?_⟩
    exact ⟨.returned (.ok (7 : Nat)) (sampleAfterDecode, ()), decode_sample, rfl⟩
  | loader =>
    let after := (Borrow.release
      (AccountInfo.tryBorrowData AccountInfo.sampleState AccountInfo.sampleArgs).2 ⟨0, 0⟩).2
    refine ⟨(AccountInfo.sampleState, ()), AccountInfo.sampleArgs,
      .returned (.ok (Loader.mk (Payload := Nat) AccountInfo.sampleInfo)) (after, ()),
      constructor_sample_ready .loader, ?_⟩
    refine ⟨.returned (.ok ()) (AccountInfo.sampleState, ()), ownerCheck_sample _, ?_⟩
    exact ⟨.returned (.ok ()) (after, ()), rfl, rfl⟩

/-- Generic AsRef callbacks can have effects or nonlocal exits. On return,
ToAccountInfo clones the returned alias, preserving those callback effects. -/
structure ToInfoIndex where
  State : Type
  Input : Type
  Unwind : Type
  Terminal : Type
  asRef : Callback.Run State Input AccountInfo.Value Unwind Terminal

def toInfoFamily : Family where
  Index := ToInfoIndex
  State := fun i => i.State
  Args := fun i => i.Input
  Value := fun _ => AccountInfo.Value
  Unwind := fun i => i.Unwind
  Terminal := fun i => i.Terminal
  contract := fun i => {
    requires := fun _ _ => True
    post := Callback.map AccountInfo.clone i.asRef }

def toInfoRun : FamilyRun toInfoFamily := fun i => Callback.map AccountInfo.clone i.asRef

theorem toInfo_reference : FamilyReference toInfoFamily toInfoRun := by
  intro _ _ _ _ _ step
  exact step

def toInfoSample : ToInfoIndex :=
  ⟨Nat, Unit, String, String,
    Callback.ofFunction (fun state _ => .returned AccountInfo.sampleInfo (state + 1))⟩

theorem toInfo_execution : FamilyHasExecution toInfoFamily toInfoRun toInfoSample := by
  exact ⟨(0 : Nat), (), .returned AccountInfo.sampleInfo (1 : Nat), trivial,
    .returned AccountInfo.sampleInfo (1 : Nat), rfl, rfl⟩

end Solanalib.Specs.Core.AnchorAccount
