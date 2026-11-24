/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorEffects
public import Solanalib.Specs.Core.AccountInfoRc
public import Solanalib.Specs.Core.AnchorErrorOwned
public import Solanalib.Specs.Core.AnchorErrorOwnedTransport
public import Solanalib.Specs.Core.AnchorGuardEffects

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorConstructOwned

open AnchorAccount (World Constructor ConstructorUnwind ConstructorTerminal)

/-- A codec owns its returned error or decoded value. Its local input cursor
may be replaced independently of the stored bytes of the account. -/
structure Decoded (Error Payload : Type) where
  result : Except Error Payload
  cursor : _root_.Solanalib.Runtime.Bytes

/-- Explicit trait callbacks and primitive owned-error dependencies for the
three source constructors. Error resources are stable identities, so equal
diagnostic values do not collapse independently owned boxes. Owner references
are read through the mutable auxiliary state at each actual source read. -/
structure Types where
  Aux : Type
  Payload : Type
  Unwind : Type
  Terminal : Type
  StringResource : Type
  BoxResource : Type
  errors : AnchorErrorOwned.Ops (World Aux) StringResource BoxResource Terminal
  discriminator : _root_.Solanalib.Runtime.Bytes
  ownerAt : AccountInfo.OwnerAt Aux
  owner : Callback.Run (World Aux) Unit _root_.Solanalib.Runtime.Pubkey Unwind Terminal
  checkOwner : Callback.Run (World Aux) AccountInfo.OwnerRef
    (Except (AnchorErrorOwned.Error BoxResource) Unit) Unwind Terminal
  deserialize : Callback.Run (World Aux) AnchorAccount.DecodeArgs
    (Decoded (AnchorErrorOwned.Error BoxResource) Payload) Unwind Terminal

abbrev Error (types : Types) := AnchorErrorOwned.Error types.BoxResource

/-- Embed a non-unwinding fixed-source allocation or drop dependency into the callback vocabulary of
the constructor, preserving all actual states and terminals. -/
def dependency (types : Types) {Args Value : Type}
    (run : Callback.Run (World types.Aux) Args Value Empty types.Terminal) :
    Callback.Run (World types.Aux) Args Value
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal) :=
  AnchorAccount.widenCallback (AccountInfoRc.lift run)

def code (types : Types) (value : AnchorAccount.Code) :
    Callback.Run (World types.Aux) Unit (Error types)
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal) :=
  fun state _ => dependency types (AnchorErrorOwned.buildCode types.errors) state
    ⟨value.payload.name, value.payload.code, value.payload.message⟩

/-- Compose the actual name, message and Box returns into the fixed-code
factory. This asserts no allocation availability or blanket factory law. -/
theorem code_from_allocations {types : Types} {value : AnchorAccount.Code}
    {before afterName afterMessage afterBox : World types.Aux}
    {name message : types.StringResource} {resource : types.BoxResource}
    (copied : types.errors.copyLiteral before value.payload.name (.returned name afterName))
    (formatted : types.errors.formatLiteral afterName value.payload.message (.returned message
      afterMessage))
    (boxed : types.errors.newBox afterMessage
      (.anchor ⟨name, value.payload.code, message, none, none⟩) (.returned resource afterBox)) :
    code types value before () (.returned ⟨resource⟩ afterBox) := by
  refine ⟨.returned ⟨resource⟩ afterBox, ⟨.returned ⟨resource⟩ afterBox, ?_, rfl⟩, rfl⟩
  exact ⟨.returned name afterName, copied, .returned message afterMessage, formatted,
    .returned resource afterBox, boxed, rfl⟩

/-- A real terminal at the first allocation is retained without reaching
message construction or Box allocation. -/
theorem code_from_name_terminal {types : Types} {value : AnchorAccount.Code}
    {before : World types.Aux} {terminal : types.Terminal}
    (called : types.errors.copyLiteral before value.payload.name (.terminated terminal)) :
    code types value before () (.terminated (.inr terminal)) := by
  exact ⟨.terminated terminal, ⟨.terminated terminal,
    ⟨.terminated terminal, called, rfl⟩, rfl⟩, rfl⟩

/-- The source-ordered primitive allocation premises imply admission of the
lifted factory. They constrain earlier exits even when the whole factory has
no later finite result. -/
theorem code_admissible {types : Types} {before : World types.Aux}
    {guard : Borrow.Guard} {value : AnchorAccount.Code}
    (admitted : AnchorGuardEffects.BuildCodeAdmissible types.errors before guard
      ⟨value.payload.name, value.payload.code, value.payload.message⟩) :
    AccountInfo.GuardCallback.Admissible guard (code types value) before () := by
  rintro _ ⟨_, ⟨original, called, rfl⟩, rfl⟩
  have frame := admitted.admissible original called
  cases original with
  | returned _ _ => exact frame
  | unwound impossible _ => nomatch impossible
  | terminated _ => trivial

def program (types : Types) (value : ProgramError.Value) :
    Callback.Run (World types.Aux) Unit (Error types)
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal) :=
  fun state _ => dependency types (AnchorErrorOwned.fromProgram types.errors) state value

def dropError (types : Types) (value : Error types) :
    Owned.DropAction (World types.Aux)
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal) :=
  fun state => dependency types
    (fun before (_ : Unit) => AnchorErrorOwned.dropError types.errors value before) state ()

/-- None of the fixed-source error destructors can supply a second unwind.
The empty policy supplies no invented terminal execution. -/
def noDoubleUnwind (types : Types) : Owned.DoubleUnwind (World types.Aux)
    (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal) :=
  fun _ _ _ _ => False

/-- Error construction occurs only after observing the zero-lamport
system-owned case of the source. Its String and Box operations run in their source order. -/
def initialized (types : Types) :
    Callback.Run (World types.Aux) AccountInfo.Args (Except (Error types) Unit)
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal) :=
  fun before args outcome =>
    if types.ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId then
      match AccountInfo.observe .lamports before.1 args.info with
      | (.malformed, _) => False
      | (.value balance, after) =>
        if balance = 0 then Callback.map Except.error (code types .notInitialized)
          (after, before.2) () outcome
        else outcome = .returned (.ok ()) (after, before.2)
      | (.borrowFailed, after) =>
        if args.profile.aborts then outcome = .terminated (.inl .borrowFailed)
        else outcome = .unwound (.inl .borrowFailed) (after, before.2)
    else outcome = .returned (.ok ()) before

/-- Zero balance reaches the real fixed-code factory. Each of its actual
finite exits is retained, without assuming allocation terminates. -/
theorem initialized_zero_retain {types : Types} {before : World types.Aux}
    {args : AccountInfo.Args} {after : AccountInfo.State}
    (system : types.ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId)
    (observed : AccountInfo.observe .lamports before.1 args.info = (.value 0, after))
    {produced : Outcome (World types.Aux) (Error types)
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal)}
    (called : code types .notInitialized (after, before.2) () produced) :
    initialized types before args (Outcome.map Except.error produced) := by
  simp only [initialized, system, observed, ↓reduceIte]
  exact ⟨produced, called, rfl⟩

/-- An admitted selected read either has its actual direct initializer exit
or reaches the exact zero-balance factory input. That latter branch retains
each supplied factory exit rather than claiming the allocator terminates. -/
theorem initialized_entry {types : Types} {before : World types.Aux}
    {args : AccountInfo.Args} (ready : AnchorAccount.InitReady types.ownerAt before args) :
    (∃ outcome, initialized types before args outcome) ∨
      ∃ after, types.ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId ∧
        AccountInfo.observe .lamports before.1 args.info = (.value 0, after) ∧
        ∀ produced, code types .notInitialized (after, before.2) () produced →
          initialized types before args (Outcome.map Except.error produced) := by
  by_cases system : types.ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId
  · have represented := ready system
    cases observed : AccountInfo.observe .lamports before.1 args.info with
    | mk result after =>
      cases result with
      | malformed => simp [observed] at represented
      | value balance =>
        by_cases zero : balance = 0
        · subst balance
          exact Or.inr ⟨after, system, rfl, fun _ => initialized_zero_retain system observed⟩
        · exact Or.inl ⟨.returned (.ok ()) (after, before.2),
            by simp only [initialized, system, observed, zero, ↓reduceIte]⟩
      | borrowFailed =>
        cases strategy : args.profile.aborts with
        | false => exact Or.inl ⟨.unwound (.inl .borrowFailed) (after, before.2),
            by simp only [initialized, system, observed, strategy, Bool.false_eq_true, ↓reduceIte]⟩
        | true => exact Or.inl ⟨.terminated (.inl .borrowFailed),
            by simp only [initialized, system, observed, strategy, ↓reduceIte]⟩
  · exact Or.inl ⟨.returned (.ok ()) before,
      by simp only [initialized, system, ↓reduceIte]⟩

/-- The first Owner call precedes comparison with the currently pointed owner.
On mismatch the allocations of the error occur before the diagnostic owner copy.
That copy is retained across the second Owner callback. If it unwinds, the
constructed error is dropped in the actual state of the callback. -/
def ownerCheck (types : Types) :
    Callback.Run (World types.Aux) AccountInfo.Args (Except (Error types) Unit)
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal) :=
  fun before args => Callback.bind (AnchorAccount.widenCallback types.owner)
    (fun expected after outcome =>
      if types.ownerAt after.2 args.info.ownerRef = expected then
        outcome = .returned (.ok ()) after
      else Callback.bind (code types .ownedByWrongProgram)
        (fun error afterBuild result =>
          let copiedOwner := types.ownerAt afterBuild.2 args.info.ownerRef
          Owned.protect (noDoubleUnwind types) [dropError types error]
            (Callback.bind (AnchorAccount.widenCallback types.owner)
              (fun diagnostic afterOwner final => Callback.map Except.error
                (dependency types (AnchorErrorOwned.withPubkeys types.errors))
                afterOwner (error, copiedOwner, diagnostic) final))
            afterBuild () result)
        after () outcome)
    before ()

/-- A successful Owner check comes only from the matching
current-owner comparison of the first callback. Diagnostic allocation and cleanup cannot create a
success that reaches the later data-borrow scope. -/
theorem ownerCheck_returned_ok {types : Types} {before checked : World types.Aux}
    {args : AccountInfo.Args}
    (called : ownerCheck types before args (.returned (.ok ()) checked)) :
    ∃ expected, AnchorAccount.widenCallback types.owner before () (.returned expected checked) ∧
      types.ownerAt checked.2 args.info.ownerRef = expected := by
  obtain ⟨produced, ownerCalled, continued⟩ := called
  cases produced with
  | unwound _ _ => cases continued
  | terminated _ => cases continued
  | returned expected after =>
    by_cases same : types.ownerAt after.2 args.info.ownerRef = expected
    · simp only [ite_eq_left same] at continued
      cases continued
      exact ⟨expected, ownerCalled, same⟩
    · simp only [ite_eq_right same] at continued
      obtain ⟨built, _, guarded⟩ := continued
      cases built with
      | unwound _ _ => cases guarded
      | terminated _ => cases guarded
      | returned error afterBuild =>
        obtain ⟨pending, body, finished⟩ := guarded
        have equal := AnchorEffects.protected_returned _ _ finished
        cases equal
        obtain ⟨diagnostic, _, compared⟩ := body
        cases diagnostic with
        | unwound _ _ => cases compared
        | terminated _ => cases compared
        | returned _ _ =>
          obtain ⟨result, _, impossible⟩ := compared
          cases result <;> cases impossible

/-- The exact payload passed to Box::new by the reached wrong-owner factory.
Its comparison field is absent before the diagnostic Owner call. -/
def ownerErrorPayload (types : Types) (name message : types.StringResource) :
    AnchorErrorOwned.Payload types.StringResource :=
  .anchor ⟨name, AnchorAccount.Code.ownedByWrongProgram.payload.code, message, none, none⟩

/-- The second Owner call retains the exact error Box of the caller on every
state-bearing exit. A return additionally admits the actual infallible payload
store; a terminal exit has no remaining read, store or destructor obligation. -/
def OwnerExitReady (types : Types) (args : AccountInfo.Args)
    (name message : types.StringResource) (resource : types.BoxResource)
    (before : World types.Aux) :
    Outcome (World types.Aux) _root_.Solanalib.Runtime.Pubkey types.Unwind types.Terminal → Prop
  | .returned diagnostic after =>
      types.errors.currentBox after resource = types.errors.currentBox before resource ∧
        ∃ final, types.errors.writeBox after resource
          ((ownerErrorPayload types name message).withPubkeys
            (types.ownerAt before.2 args.info.ownerRef) diagnostic) = some final
  | .unwound _ after =>
      types.errors.currentBox after resource = types.errors.currentBox before resource
  | .terminated _ => True

/-- Resource admission follows the actual first Owner mismatch and the
three primitive allocation returns. It checks the fresh Box before invoking
the diagnostic callback, including exits that would erase a later read/drop.
No completed ownerCheck outcome or uncalled error-factory law is assumed. -/
def OwnerCheckReady (types : Types) (before : World types.Aux) (args : AccountInfo.Args) : Prop :=
  ∀ expected after, types.owner before () (.returned expected after) →
    types.ownerAt after.2 args.info.ownerRef ≠ expected →
    ∀ name afterName, types.errors.copyLiteral after
      AnchorAccount.Code.ownedByWrongProgram.payload.name (.returned name afterName) →
    ∀ message afterMessage, types.errors.formatLiteral afterName
      AnchorAccount.Code.ownedByWrongProgram.payload.message (.returned message afterMessage) →
    ∀ resource afterBox, types.errors.newBox afterMessage (ownerErrorPayload types name message)
      (.returned resource afterBox) →
      types.errors.currentBox afterBox resource = some (ownerErrorPayload types name message) ∧
        ∀ produced, types.owner afterBox () produced →
          OwnerExitReady types args name message resource afterBox produced

/-- Each actual diagnostic Owner return has the full owner-check error exit.
The freshly allocated, retained payload has no compared strings, so its real
dropStrings [] step preserves the exact current Box before the admitted store. -/
theorem owner_mismatch_return_retain {types : Types} {before after : World types.Aux}
    {args : AccountInfo.Args} (ready : OwnerCheckReady types before args)
    {expected : _root_.Solanalib.Runtime.Pubkey}
    (first : types.owner before () (.returned expected after))
    (mismatch : types.ownerAt after.2 args.info.ownerRef ≠ expected)
    {name message : types.StringResource} {resource : types.BoxResource}
    {afterName afterMessage afterBox afterOwner : World types.Aux}
    (copied : types.errors.copyLiteral after AnchorAccount.Code.ownedByWrongProgram.payload.name
      (.returned name afterName))
    (formatted : types.errors.formatLiteral afterName
      AnchorAccount.Code.ownedByWrongProgram.payload.message
      (.returned message afterMessage))
    (boxed : types.errors.newBox afterMessage (ownerErrorPayload types name message)
      (.returned resource afterBox))
    {diagnostic : _root_.Solanalib.Runtime.Pubkey}
    (second : types.owner afterBox () (.returned diagnostic afterOwner)) :
    ∃ final, types.errors.currentBox afterOwner resource = some (ownerErrorPayload types name
      message) ∧
      types.errors.writeBox afterOwner resource ((ownerErrorPayload types name message).withPubkeys
        (types.ownerAt afterBox.2 args.info.ownerRef) diagnostic) = some final ∧
      ownerCheck types before args (.returned (.error ⟨resource⟩) final) := by
  have admitted := ready expected after first mismatch name afterName copied message afterMessage
    formatted resource afterBox boxed
  obtain ⟨frame, final, stored⟩ := admitted.2 _ second
  have held := frame.trans admitted.1
  refine ⟨final, held, stored, .returned expected after, ⟨.returned expected after, first, rfl⟩, ?_⟩
  simp only [mismatch, ↓reduceIte]
  refine ⟨.returned ⟨resource⟩ afterBox, code_from_allocations copied formatted boxed,
    .returned (.error ⟨resource⟩) final, ?_, rfl⟩
  refine ⟨.returned diagnostic afterOwner, ⟨.returned diagnostic afterOwner, second, rfl⟩,
    .returned ⟨resource⟩ final, ?_, rfl⟩
  refine ⟨.returned ⟨resource⟩ final, ⟨.returned ⟨resource⟩ final, ?_, rfl⟩, rfl⟩
  exact ⟨ownerErrorPayload types name message, held, .returned () afterOwner, rfl,
    ownerErrorPayload types name message, held, final, stored, rfl⟩

/-- On diagnostic unwind, admission supplies the current payload input of the error destructor.
Actual ordered String returns and the actual Box-free exit then continue the owner check,
preserving its unwind reason or the free terminal. -/
theorem owner_mismatch_unwind_retain {types : Types} {before after : World types.Aux}
    {args : AccountInfo.Args} (ready : OwnerCheckReady types before args)
    {expected : _root_.Solanalib.Runtime.Pubkey}
    (first : types.owner before () (.returned expected after))
    (mismatch : types.ownerAt after.2 args.info.ownerRef ≠ expected)
    {name message : types.StringResource} {resource : types.BoxResource}
    {afterName afterMessage afterBox afterOwner afterFields : World types.Aux}
    (copied : types.errors.copyLiteral after AnchorAccount.Code.ownedByWrongProgram.payload.name
      (.returned name afterName))
    (formatted : types.errors.formatLiteral afterName
      AnchorAccount.Code.ownedByWrongProgram.payload.message
      (.returned message afterMessage))
    (boxed : types.errors.newBox afterMessage (ownerErrorPayload types name message)
      (.returned resource afterBox))
    {reason : types.Unwind} (second : types.owner afterBox () (.unwound reason afterOwner))
    (fields : AnchorErrorOwned.dropStrings types.errors [name, message] afterOwner ()
      (.returned () afterFields))
    {freed : Outcome (World types.Aux) Unit Empty types.Terminal}
    (free : types.errors.freeBox afterFields resource freed) :
    ownerCheck types before args
      (Outcome.bind (AnchorAccount.widen (AccountInfoRc.liftOutcome freed))
        (fun _ final => .unwound (.inr reason) final)) := by
  have admitted := ready expected after first mismatch name afterName copied message afterMessage
    formatted resource afterBox boxed
  have held := (admitted.2 _ second).trans admitted.1
  have dropped : AnchorErrorOwned.dropError types.errors ⟨resource⟩ afterOwner freed :=
    ⟨ownerErrorPayload types name message, held, .returned () afterFields, fields, free⟩
  refine ⟨.returned expected after, ⟨.returned expected after, first, rfl⟩, ?_⟩
  simp only [mismatch, ↓reduceIte]
  refine ⟨.returned ⟨resource⟩ afterBox, code_from_allocations copied formatted boxed,
    .unwound (.inr reason) afterOwner, ?_, ?_⟩
  · exact ⟨.unwound (.inr reason) afterOwner, ⟨.unwound reason afterOwner, second, rfl⟩, rfl⟩
  · cases freed with
    | returned value final =>
      cases value
      exact ⟨.returned () final,
        ⟨.returned () final, ⟨.returned () final, dropped, rfl⟩, rfl⟩, rfl⟩
    | unwound impossible _ => nomatch impossible
    | terminated terminal =>
      exact ⟨.terminated (.inr terminal),
        ⟨.terminated terminal, ⟨.terminated terminal, dropped, rfl⟩, rfl⟩, rfl⟩

/-- A String-cleanup terminal after diagnostic unwind is also retained at its
actual source point, without demanding a later Box-free execution. -/
theorem owner_mismatch_unwind_fields_terminal {types : Types} {before after : World types.Aux}
    {args : AccountInfo.Args} (ready : OwnerCheckReady types before args)
    {expected : _root_.Solanalib.Runtime.Pubkey}
    (first : types.owner before () (.returned expected after))
    (mismatch : types.ownerAt after.2 args.info.ownerRef ≠ expected)
    {name message : types.StringResource} {resource : types.BoxResource}
    {afterName afterMessage afterBox afterOwner : World types.Aux}
    (copied : types.errors.copyLiteral after AnchorAccount.Code.ownedByWrongProgram.payload.name
      (.returned name afterName))
    (formatted : types.errors.formatLiteral afterName
      AnchorAccount.Code.ownedByWrongProgram.payload.message
      (.returned message afterMessage))
    (boxed : types.errors.newBox afterMessage (ownerErrorPayload types name message)
      (.returned resource afterBox))
    {reason : types.Unwind} (second : types.owner afterBox () (.unwound reason afterOwner))
    {terminal : types.Terminal}
    (fields : AnchorErrorOwned.dropStrings types.errors [name, message] afterOwner ()
      (.terminated terminal)) :
    ownerCheck types before args (.terminated (.inr terminal)) := by
  have admitted := ready expected after first mismatch name afterName copied message afterMessage
    formatted resource afterBox boxed
  have held := (admitted.2 _ second).trans admitted.1
  have dropped : AnchorErrorOwned.dropError types.errors ⟨resource⟩ afterOwner (.terminated
    terminal) :=
    ⟨ownerErrorPayload types name message, held, .terminated terminal, fields, rfl⟩
  refine ⟨.returned expected after, ⟨.returned expected after, first, rfl⟩, ?_⟩
  simp only [mismatch, ↓reduceIte]
  refine ⟨.returned ⟨resource⟩ afterBox, code_from_allocations copied formatted boxed,
    .unwound (.inr reason) afterOwner, ?_, ?_⟩
  · exact ⟨.unwound (.inr reason) afterOwner, ⟨.unwound reason afterOwner, second, rfl⟩, rfl⟩
  · exact ⟨.terminated (.inr terminal),
      ⟨.terminated terminal, ⟨.terminated terminal, dropped, rfl⟩, rfl⟩, rfl⟩

/-- A failed checked borrow is converted through the actual boxed ProgramError
constructor. A successful borrow remains live during the codec and is released
after its ordinary result or unwind, preserving its other state effects. -/
def decodeAccount (types : Types) :
    Callback.Run (World types.Aux) AccountInfo.Args (Except (Error types) types.Payload)
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal) :=
  fun before args outcome =>
    let (borrowed, during) := AccountInfo.tryBorrowData before.1 args
    match borrowed with
    | .error failure => Callback.map Except.error (program types failure) (during, before.2) ()
      outcome
    | .ok guard => match Borrow.current during guard with
      | .error _ | .ok (_, .lamports _) => False
      | .ok (_, .data bytes) =>
        AnchorEffects.withGuard guard
          (Callback.map Decoded.result (AnchorAccount.widenCallback types.deserialize))
          (during, before.2) ⟨args.info, guard, bytes⟩ outcome

/-- The actual reached state has a typed data cell after initialization and
Owner/CheckOwner effects. Every decoder exit at the acquired shared guard must
preserve the held lease and current bytes. -/
def DecodeReady (types : Types) (before : World types.Aux) (args : AccountInfo.Args) : Prop :=
  (∃ bytes policy, before.1.lookupCell args.info.data = some ⟨.data bytes, policy⟩) ∧
    ∀ guard during, AccountInfo.tryBorrowData before.1 args = (.ok guard, during) →
      ∀ view bytes, Borrow.current during guard = .ok (view, .data bytes) →
        AccountInfo.GuardCallback.Admissible guard types.deserialize (during, before.2)
          ⟨args.info, guard, bytes⟩

/-- Selected data-cell typing makes a successful borrow expose current data
and an admitted codec call; a malformed projection cannot silently erase it. -/
theorem DecodeReady.callback_input {types : Types} {before : World types.Aux}
    {args : AccountInfo.Args} (ready : DecodeReady types before args)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) ∧
      AccountInfo.GuardCallback.Admissible guard types.deserialize (during, before.2)
        ⟨args.info, guard, bytes⟩ := by
  obtain ⟨bytes, current⟩ := AccountInfo.GuardCallback.data_current ready.1 acquired
  exact ⟨bytes, current, ready.2 guard during acquired .whole bytes current⟩

/-- A real decoder exit has exact guard cleanup under universal call admission.
The conclusion retains its actual error, unwind, terminal, and state effects. -/
theorem DecodeReady.retain {types : Types} {before : World types.Aux}
    {args : AccountInfo.Args} (ready : DecodeReady types before args)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during))
    {view : AccountInfo.View} {bytes : _root_.Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes))
    {produced : Outcome (World types.Aux) (Decoded (Error types) types.Payload) types.Unwind
      types.Terminal}
    (called : types.deserialize (during, before.2) ⟨args.info, guard, bytes⟩ produced) :
    ∃ outcome, AnchorAccount.releaseOutcome guard
        (Outcome.map Decoded.result (AnchorAccount.widen produced)) = some outcome ∧
      decodeAccount types before args outcome := by
  have frame := (AnchorAccount.widen_frame
    (ready.2 guard during acquired view bytes current produced called)).map Decoded.result
  have live : during.resolve guard = some ⟨args.info.data, .shared, 0, .whole⟩ :=
    AccountInfo.GuardCallback.tryBorrow_live acquired
  obtain ⟨outcome, released⟩ := frame.release_exists live
  refine ⟨outcome, released, ?_⟩
  simp only [decodeAccount, acquired, current]
  exact ⟨_, ⟨_, ⟨produced, called, rfl⟩, rfl⟩, released⟩

/-- For an admitted successful data borrow, the decoder relation is nonempty
exactly when its actual callback is. Errors, unwinds, and terminal exits count. -/
theorem DecodeReady.hasOutcome_iff {types : Types} {before : World types.Aux}
    {args : AccountInfo.Args} (ready : DecodeReady types before args)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) ∧
      ((∃ outcome, decodeAccount types before args outcome) ↔
        ∃ produced, types.deserialize (during, before.2) ⟨args.info, guard, bytes⟩ produced) := by
  obtain ⟨bytes, current, _⟩ := ready.callback_input acquired
  refine ⟨bytes, current, ?_⟩
  constructor
  · rintro ⟨outcome, decoded⟩
    simp only [decodeAccount, acquired, current] at decoded
    obtain ⟨_, ⟨_, ⟨produced, called, _⟩, _⟩, _⟩ := decoded
    exact ⟨produced, called⟩
  · rintro ⟨produced, called⟩
    obtain ⟨outcome, _, retained⟩ := ready.retain acquired current called
    exact ⟨outcome, retained⟩

/-- The discriminator checks select a source error code before any formatting
or allocation; successful checks do not construct an error at all. -/
def discriminatorFailure (discriminator bytes : _root_.Solanalib.Runtime.Bytes) : Option
  AnchorAccount.Code :=
  if bytes.length < discriminator.length then some .discriminatorNotFound
  else if bytes.take discriminator.length ≠ discriminator then some .discriminatorMismatch
  else none

/-- The check of the Loader either constructs its selected owned error or returns
success without invoking an allocation dependency. -/
def loaderCheck (types : Types) (bytes : _root_.Solanalib.Runtime.Bytes) :
    Callback.Run (World types.Aux) Unit (Except (Error types) Unit)
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal) :=
  fun state _ result => match discriminatorFailure types.discriminator bytes with
    | some failure => Callback.map Except.error (code types failure) state () result
    | none => result = .returned (.ok ()) state

/-- The checked error from Loader is built while its temporary shared data guard is
held. Primitive admission is a separate precondition; the raw relation retains
every exit with actual checked cleanup. No codec or initialization runs here. -/
def checkLoaderData (types : Types) :
    Callback.Run (World types.Aux) AccountInfo.Args (Except (Error types) Unit)
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal) :=
  fun before args outcome =>
    let (borrowed, during) := AccountInfo.tryBorrowData before.1 args
    match borrowed with
    | .error failure => Callback.map Except.error (program types failure) (during, before.2) ()
      outcome
    | .ok guard => match Borrow.current during guard with
      | .error _ | .ok (_, .lamports _) => False
      | .ok (_, .data bytes) =>
        AnchorEffects.withGuard guard (loaderCheck types bytes) (during, before.2) () outcome

/-- Protocol validity supplies the unchanged guard frame on a successful
discriminator check. Guarded error factories are admitted through every
primitive allocation at its reached input, not only through completed exits. -/
def LoaderReady (types : Types) (before : World types.Aux) (args : AccountInfo.Args) : Prop :=
  before.1.Valid ∧
    ∀ guard during, AccountInfo.tryBorrowData before.1 args = (.ok guard, during) →
      ∀ view bytes, Borrow.current during guard = .ok (view, .data bytes) →
        ∀ failure, discriminatorFailure types.discriminator bytes = some failure →
          AnchorGuardEffects.BuildCodeAdmissible types.errors (during, before.2) guard
            ⟨failure.payload.name, failure.payload.code, failure.payload.message⟩

/-- The reached primitive premises supply the exact callback admission needed
before a Loader check, including its allocation-free success branch. -/
theorem LoaderReady.admissible {types : Types} {before : World types.Aux}
    {args : AccountInfo.Args} (ready : LoaderReady types before args)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during))
    {view : AccountInfo.View} {bytes : _root_.Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes)) :
    AccountInfo.GuardCallback.Admissible guard (loaderCheck types bytes) (during, before.2) () := by
  cases selected : discriminatorFailure types.discriminator bytes with
  | some failure =>
    have admitted := (code_admissible
      (ready.2 guard during acquired view bytes current failure selected)).map
      (Except.error (α := Unit))
    intro produced called
    exact admitted produced (by simpa only [loaderCheck, selected] using called)
  | none =>
    intro produced called
    simp only [loaderCheck, selected] at called
    cases called
    have valid := AccountInfo.GuardCallback.tryBorrow_valid ready.1 .shared args.info.data
    rw [show AccountInfo.tryBorrow .shared args.info.data before.1 = (.ok guard, during) from
      acquired] at valid
    exact AccountInfo.GuardCallback.StateFrame.refl _ _ valid

/-- Each actual finite Loader-check exit has exact cleanup under the reached
primitive laws. Inadmissible-only callbacks cannot prove this premise. -/
theorem LoaderReady.retain {types : Types} {before : World types.Aux}
    {args : AccountInfo.Args} (ready : LoaderReady types before args)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData before.1 args = (.ok guard, during))
    {view : AccountInfo.View} {bytes : _root_.Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes))
    {produced : Outcome (World types.Aux) (Except (Error types) Unit)
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal)}
    (called : loaderCheck types bytes (during, before.2) () produced) :
    ∃ outcome, AnchorAccount.releaseOutcome guard produced = some outcome ∧
      checkLoaderData types before args outcome := by
  have live : during.resolve guard = some ⟨args.info.data, .shared, 0, .whole⟩ :=
    AccountInfo.GuardCallback.tryBorrow_live acquired
  obtain ⟨outcome, released, retained⟩ := (ready.admissible acquired current).retain live called
  exact ⟨outcome, released, by
    simpa only [checkLoaderData, acquired, current, AnchorEffects.withGuard] using retained⟩

/-- Compose the source constructors from their checks and callbacks. Their
`new` helpers retain an AccountInfo reference; they do not clone either Rc.
InterfaceAccount copies the current owner only after its decoder returns. -/
def run (kind : Constructor) (types : Types) :
    Callback.Run (World types.Aux) AccountInfo.Args
      (Except (Error types) (kind.Result types.Payload))
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal) :=
  match kind with
  | .account => fun before args outcome =>
    AnchorEffects.resultBind (initialized types)
      (fun _ after result => AnchorEffects.resultBind (ownerCheck types)
        (fun _ checked result => Callback.map
          (Except.map fun value => AnchorAccount.Account.mk value args.info)
          (decodeAccount types) checked args result) after args result)
      before args outcome
  | .interfaceAccount => fun before args outcome =>
    AnchorEffects.resultBind (initialized types)
      (fun _ after result => AnchorEffects.resultBind (AnchorAccount.widenCallback types.checkOwner)
        (fun _ checked result => Callback.bind (decodeAccount types)
          (fun decoded afterDecode final => final = .returned
            (decoded.map fun value => AnchorAccount.InterfaceAccount.mk ⟨value, args.info⟩
              (types.ownerAt afterDecode.2 args.info.ownerRef)) afterDecode)
          checked args result) after args.info.ownerRef result)
      before args outcome
  | .loader => fun before args outcome =>
    AnchorEffects.resultBind (ownerCheck types)
      (fun _ checked result => Callback.map
        (Except.map fun _ => AnchorAccount.Loader.mk args.info)
        (checkLoaderData types) checked args result)
      before args outcome

/-- Admit only the actual initialization read and reached owner-error
resources, then each data scope reached through successful prefixes. The
primitive and callback gates apply before a complete constructor exit exists. -/
def Ready (kind : Constructor) (types : Types) (before : World types.Aux)
    (args : AccountInfo.Args) : Prop :=
  match kind with
  | .account => AnchorAccount.InitReady types.ownerAt before args ∧
      ∀ after, initialized types before args (.returned (.ok ()) after) →
        OwnerCheckReady types after args ∧
          ∀ checked, ownerCheck types after args (.returned (.ok ()) checked) →
            DecodeReady types checked args
  | .interfaceAccount => AnchorAccount.InitReady types.ownerAt before args ∧
      ∀ after, initialized types before args (.returned (.ok ()) after) →
      ∀ checked, AnchorAccount.widenCallback types.checkOwner after args.info.ownerRef
        (.returned (.ok ()) checked) → DecodeReady types checked args
  | .loader => OwnerCheckReady types before args ∧
      ∀ checked, ownerCheck types before args (.returned (.ok ()) checked) →
        (∃ bytes policy, checked.1.lookupCell args.info.data = some ⟨.data bytes, policy⟩) ∧
          LoaderReady types checked args

/-- The raw post retains every actual finite outcome. Reached-call admission
prevents guard-destroying providers from making local continuation undefined;
it does not assume a callback or allocator terminates. -/
def family (kind : Constructor) : Family where
  Index := Types
  State := fun types => World types.Aux
  Args := fun _ => AccountInfo.Args
  Value := fun types => Except (Error types) (kind.Result types.Payload)
  Unwind := fun types => ConstructorUnwind types.Unwind
  Terminal := fun types => ConstructorTerminal types.Terminal
  contract := fun types => {
    requires := Ready kind types
    post := run kind types }

def reference (kind : Constructor) : FamilyRun (family kind) := run kind

theorem reference_holds (kind : Constructor) : FamilyReference (family kind) (reference kind) := by
  intro _ _ _ _ _ step
  exact step

/-- Each actual decoder exit after an admitted Account prefix extends to the
complete constructor. Its ordinary error or unwind retains the actual callback
state followed by checked release; a terminal exit bypasses release. -/
theorem account_retain {types : Types} {before after checked : World types.Aux}
    {args : AccountInfo.Args}
    (ready : ((family .account).contract types).requires before args)
    (started : initialized types before args (.returned (.ok ()) after))
    (owned : ownerCheck types after args (.returned (.ok ()) checked))
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData checked.1 args = (.ok guard, during))
    {view : AccountInfo.View} {bytes : _root_.Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes))
    {produced : Outcome (World types.Aux) (Decoded (Error types) types.Payload)
      types.Unwind types.Terminal}
    (called : types.deserialize (during, checked.2) ⟨args.info, guard, bytes⟩ produced) :
    ∃ decoded, AnchorAccount.releaseOutcome guard
        (Outcome.map Decoded.result (AnchorAccount.widen produced)) = some decoded ∧
      run .account types before args
        (Outcome.map (Except.map fun value => AnchorAccount.Account.mk value args.info) decoded) :=
          by
  obtain ⟨decoded, released, ran⟩ := ((ready.2 after started).2 checked owned).retain acquired
    current called
  exact ⟨decoded, released, .returned (.ok ()) after, started,
    .returned (.ok ()) checked, owned, decoded, ran, rfl⟩

/-- The same continuation fact for InterfaceAccount preserves the post-codec
owner observation and every exceptional exit instead of filtering callbacks. -/
theorem interface_retain {types : Types} {before after checked : World types.Aux}
    {args : AccountInfo.Args}
    (ready : ((family .interfaceAccount).contract types).requires before args)
    (started : initialized types before args (.returned (.ok ()) after))
    (owned : AnchorAccount.widenCallback types.checkOwner after args.info.ownerRef
      (.returned (.ok ()) checked))
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData checked.1 args = (.ok guard, during))
    {view : AccountInfo.View} {bytes : _root_.Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes))
    {produced : Outcome (World types.Aux) (Decoded (Error types) types.Payload)
      types.Unwind types.Terminal}
    (called : types.deserialize (during, checked.2) ⟨args.info, guard, bytes⟩ produced) :
    ∃ decoded, AnchorAccount.releaseOutcome guard
        (Outcome.map Decoded.result (AnchorAccount.widen produced)) = some decoded ∧
      run .interfaceAccount types before args
        (Outcome.bind decoded fun value final => .returned
          (value.map fun payload => AnchorAccount.InterfaceAccount.mk ⟨payload, args.info⟩
            (types.ownerAt final.2 args.info.ownerRef)) final) := by
  obtain ⟨decoded, released, ran⟩ := (ready.2 after started checked owned).retain acquired current
    called
  refine ⟨decoded, released, .returned (.ok ()) after, started,
    .returned (.ok ()) checked, owned, decoded, ran, ?_⟩
  cases decoded <;> rfl

/-- Successful Loader acquisition exposes the actual current data and an
admitted check. This rules out a malformed selected-cell continuation. -/
theorem loader_input {types : Types} {before checked : World types.Aux}
    {args : AccountInfo.Args}
    (ready : ((family .loader).contract types).requires before args)
    (owned : ownerCheck types before args (.returned (.ok ()) checked))
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData checked.1 args = (.ok guard, during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) ∧
      AccountInfo.GuardCallback.Admissible guard (loaderCheck types bytes) (during, checked.2) ()
        := by
  obtain ⟨bytes, current⟩ := AccountInfo.GuardCallback.data_current (ready.2 checked owned).1
    acquired
  exact ⟨bytes, current, (ready.2 checked owned).2.admissible acquired current⟩

/-- Every finite guarded Loader-check exit at its reached input has a full
constructor continuation, including allocation failure and unwind effects. -/
theorem loader_retain {types : Types} {before checked : World types.Aux}
    {args : AccountInfo.Args}
    (ready : ((family .loader).contract types).requires before args)
    (owned : ownerCheck types before args (.returned (.ok ()) checked))
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowData checked.1 args = (.ok guard, during))
    {view : AccountInfo.View} {bytes : _root_.Solanalib.Runtime.Bytes}
    (current : Borrow.current during guard = .ok (view, .data bytes))
    {produced : Outcome (World types.Aux) (Except (Error types) Unit)
      (ConstructorUnwind types.Unwind) (ConstructorTerminal types.Terminal)}
    (called : loaderCheck types bytes (during, checked.2) () produced) :
    ∃ decoded, AnchorAccount.releaseOutcome guard produced = some decoded ∧
      run .loader types before args
        (Outcome.map (Except.map fun _ => AnchorAccount.Loader.mk args.info) decoded) := by
  obtain ⟨decoded, released, ran⟩ := (ready.2 checked owned).2.retain acquired current called
  exact ⟨decoded, released, .returned (.ok ()) checked, owned, decoded, ran, rfl⟩

end Solanalib.Specs.Core.AnchorConstructOwned
