/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycle

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorAccount (World)

/-- The actual primitive callbacks reached by the simple account wrappers.
`fromAccountInfo` is the selected Sysvar/SysvarSerialize method, whose ordinary
ProgramError is deliberately replaced by AccountSysvarMismatch by Anchor. -/
structure ValidationTypes extends Base where
  Payload : Type
  ownerAt : AccountInfo.OwnerAt Aux
  id : Callback.Run (World Aux) Unit Solanalib.Runtime.Pubkey Unwind Terminal
  checkId : Callback.Run (World Aux) Solanalib.Runtime.Pubkey
    (Except (AnchorErrorOperations.Error errorStorage Program StringResource BoxResource) Unit)
    Unwind Terminal
  fromAccountInfo : Callback.Run (World Aux) AccountReference (Except Program Payload)
    Unwind Terminal
  rc : AccountInfoRc.Ops (World Aux) Terminal

inductive ValidationKind where
  | signer
  | system
  | program
  | interface
  | unchecked
  | accountInfo
  | sysvar
  deriving DecidableEq, Repr

def ValidationKind.Value : ValidationKind → Type → Type
  | .signer, _ => AnchorAccount.Signer
  | .system, _ => AccountInfo.Value
  | .program, tag => AnchorAccount.Program tag
  | .interface, tag => AnchorAccount.Interface tag
  | .unchecked, _ => AccountInfo.Value
  | .accountInfo, _ => AccountInfo.Value
  | .sysvar, payload => Sysvar payload

/-- Program first compares the first Id callback, then constructs an error,
then calls Id again for diagnostics. A second Id unwind drops the owned error
before escaping. Executability is checked only after the first Id matches. -/
def idCheck (types : ValidationTypes) :
    types.toBase.Run AccountInfo.Args (Except types.toBase.Error Unit) :=
  fun before args => Callback.bind (AnchorAccount.widenCallback types.id)
    (fun expected after outcome =>
      if args.info.key = expected then outcome = .returned (.ok ()) after
      else Callback.bind (code types.toBase .invalidProgramId)
        (fun error afterBuild result =>
          Owned.protect (noDoubleUnwind types.toBase) [dropError types.toBase error]
            (Callback.bind (AnchorAccount.widenCallback types.id)
              (fun diagnostic afterId final => Callback.map Except.error
                (dependency types.toBase (AnchorErrorOperations.withPubkeys types.errorStorage
                  types.errors
                  args.info.key diagnostic)) afterId error final))
            afterBuild () result)
        after () outcome)
    before ()

def idErrorPayload (types : ValidationTypes) (name message : types.StringResource) :
    AnchorErrorOperations.Payload types.Program types.StringResource :=
  .anchor ⟨name, Code.invalidProgramId.payload.code, message, none, none⟩

/-- At the real mismatch branch, the allocated Box survives every diagnostic
callback exit; each returned diagnostic admits its actual local store. This
does not assert that any primitive or callback has a finite execution. -/
def IdReady (types : ValidationTypes) (before : World types.Aux) (args : AccountInfo.Args) : Prop :=
  types.errorStorage = .boxed →
  ∀ expected after, types.id before () (.returned expected after) → args.info.key ≠ expected →
    ∀ name afterName, types.errors.copyLiteral after Code.invalidProgramId.payload.name
      (.returned name afterName) →
    ∀ message afterMessage, types.errors.formatLiteral afterName
      Code.invalidProgramId.payload.message
      (.returned message afterMessage) →
    ∀ resource afterBox, types.errors.newBox afterMessage (idErrorPayload types name message)
      (.returned resource afterBox) →
      types.errors.currentBox afterBox resource = some (idErrorPayload types name message) ∧
        ∀ produced, types.id afterBox () produced →
          match produced with
          | .returned diagnostic afterId =>
            types.errors.currentBox afterId resource = types.errors.currentBox afterBox resource ∧
              ∃ final, types.errors.writeBox afterId resource
                ((idErrorPayload types name message).withCompared (some (.pubkeys args.info.key
                  diagnostic))) = some final
          | .unwound _ afterId =>
            types.errors.currentBox afterId resource = types.errors.currentBox afterBox resource
          | .terminated _ => True

/-- A success is possible only through the first matching Id call. Neither
diagnostic allocation nor error destruction can turn a mismatch into success. -/
theorem idCheck_ok {types : ValidationTypes} {before after : World types.Aux}
    {args : AccountInfo.Args}
    (called : idCheck types before args (.returned (.ok ()) after)) :
    ∃ expected, AnchorAccount.widenCallback types.id before () (.returned expected after) ∧
      args.info.key = expected := by
  obtain ⟨produced, identified, next⟩ := called
  cases produced with
  | unwound _ _ => cases next
  | terminated _ => cases next
  | returned expected checked =>
    by_cases same : args.info.key = expected
    · simp only [ite_eq_left same] at next
      cases next
      exact ⟨expected, identified, same⟩
    · simp only [ite_eq_right same] at next
      obtain ⟨built, _, guarded⟩ := next
      cases built with
      | unwound _ _ => cases guarded
      | terminated _ => cases guarded
      | returned error allocated =>
        obtain ⟨pending, body, cleaned⟩ := guarded
        have equal := AnchorEffects.protected_returned _ _ cleaned
        cases equal
        obtain ⟨diagnostic, _, compared⟩ := body
        cases diagnostic with
        | unwound _ _ => cases compared
        | terminated _ => cases compared
        | returned _ _ =>
          obtain ⟨result, _, impossible⟩ := compared
          cases result <;> cases impossible

/-- Simple constructors preserve each exact AccountInfo alias. `AccountInfo`
always clones; the slice constructor of UncheckedAccount clones only in 0.27.
Sysvar clones after successful deserialization in the old owned representation. -/
def validate (kind : ValidationKind) (storage : InfoStorage) (types : ValidationTypes) :
    types.toBase.Run ReferenceArgs (Except types.toBase.Error (kind.Value types.Payload)) :=
  match kind with
  | .signer => fun before args outcome =>
    if args.info.isSigner then Callback.map (fun info => Except.ok (AnchorAccount.Signer.mk info))
      (retainInfo storage types.toBase types.rc) before args.info outcome
    else fail types.toBase .notSigner before () outcome
  | .system => fun before args outcome =>
    if types.ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId then
      Callback.map Except.ok (retainInfo storage types.toBase types.rc) before args.info outcome
    else fail types.toBase .notSystemOwned before () outcome
  | .program => fun before args =>
    AnchorEffects.resultBind (fun state (args : ReferenceArgs) => idCheck types state
      args.toAccountInfoArgs)
      (fun _ checked outcome =>
        if args.info.executable then Callback.map (fun info => Except.ok (AnchorAccount.Program.mk
          info))
          (retainInfo storage types.toBase types.rc) checked args.info outcome
        else fail types.toBase .invalidProgramExecutable checked () outcome)
      before args
  | .interface => fun before args =>
    AnchorEffects.resultBind (AnchorAccount.widenCallback types.checkId)
      (fun _ checked outcome =>
        if args.info.executable then Callback.map
          (fun info => Except.ok (AnchorAccount.Interface.mk (AnchorAccount.Program.mk info)))
          (retainInfo storage types.toBase types.rc) checked args.info outcome
        else fail types.toBase .invalidProgramExecutable checked () outcome)
      before args.info.key
  | .unchecked => fun before args =>
    Callback.map Except.ok (retainInfo storage types.toBase types.rc) before args.info
  | .accountInfo => fun before args =>
    Callback.map Except.ok (cloneInfo types.toBase types.rc) before args.info
  | .sysvar => fun before args =>
    Callback.bind (AnchorAccount.widenCallback types.fromAccountInfo)
      (fun decoded after outcome => match decoded with
        | .error error => Owned.scope (noDoubleUnwind types.toBase)
            [fun state => dependency types.toBase
              (AnchorErrorOperations.dropStrings types.errors (types.errors.programStrings error))
                state ()]
            (fail types.toBase .sysvarMismatch) after () outcome
        | .ok value => Callback.map (fun info => Except.ok (AnchorAccount.Account.mk value info))
            (retainInfo storage types.toBase types.rc) after args.info outcome)
      before args.reference

def ValidationReady (kind : ValidationKind) (types : ValidationTypes)
    (before : World types.Aux) (args : ReferenceArgs) : Prop :=
  match kind with
  | .program => IdReady types before args.toAccountInfoArgs
  | _ => True

def validationFamily (kind : ValidationKind) (storage : InfoStorage) : Family where
  Index := ValidationTypes
  State := fun types => World types.Aux
  Args := fun _ => ReferenceArgs
  Value := fun types => Except types.toBase.Error (kind.Value types.Payload)
  Unwind := fun types => types.toBase.Unw
  Terminal := fun types => types.toBase.Term
  contract := fun types => {
    requires := ValidationReady kind types
    post := validate kind storage types }

def validationRun (kind : ValidationKind) (storage : InfoStorage) :
    FamilyRun (validationFamily kind storage) := validate kind storage

theorem validation_reference (kind : ValidationKind) (storage : InfoStorage) :
    FamilyReference (validationFamily kind storage) (validationRun kind storage) := by
  intro _ _ _ _ _ called
  exact called

structure ValidationAccountsTypes extends ValidationTypes where
  Bumps : Type

def validationAccountsFamily (kind : ValidationKind) (storage : InfoStorage) : Family where
  Index := ValidationAccountsTypes
  State := fun types => World types.Aux × AccountsState types.Bumps
  Args := fun _ => AccountsArgs
  Value := fun types => Except types.toValidationTypes.toBase.Error (kind.Value types.Payload)
  Unwind := fun types => types.toValidationTypes.toBase.Unw
  Terminal := fun types => types.toValidationTypes.toBase.Term
  contract := fun types => {
    requires := fun before args => match before.2.remaining with
      | [] => True
      | info :: _ => ValidationReady kind types.toValidationTypes before.1 ⟨args.profile, info⟩
    post := consume (code types.toValidationTypes.toBase .notEnoughKeys)
      (validate kind storage types.toValidationTypes) }

def validationAccountsRun (kind : ValidationKind) (storage : InfoStorage) :
    FamilyRun (validationAccountsFamily kind storage) := fun types =>
  consume (code types.toValidationTypes.toBase .notEnoughKeys)
    (validate kind storage types.toValidationTypes)

theorem validationAccounts_reference (kind : ValidationKind) (storage : InfoStorage) :
    FamilyReference (validationAccountsFamily kind storage) (validationAccountsRun kind storage) :=
      by
  intro _ _ _ _ _ called
  exact called

/-- An explicit shared finite error heap supplies nonvacuity. The two Rc
primitives here are only a successful scheduling sample, not an Rc body proof. -/
def validationSample (errors : AnchorErrorOperations.Storage) : ValidationTypes where
  toBase := { Base.ofConstructor AnchorOwnedSamples.constructor with errorStorage := errors }
  Payload := Nat
  ownerAt := fun _ _ => .zero
  id := Callback.ofFunction fun state _ => .returned .zero state
  checkId := Callback.ofFunction fun state _ => .returned (.ok ()) state
  fromAccountInfo := Callback.ofFunction fun state _ => .returned (.ok 7) state
  rc := {
    cloneRc := Callback.ofFunction fun state _ => .returned () state
    dropRc := Callback.ofFunction fun state _ => .returned () state }

def validationArgs : ReferenceArgs :=
  ⟨AccountInfo.sampleProfile, ⟨19, { AccountInfo.sampleInfo with isSigner := true, executable :=
    true }⟩⟩

def validationValue : (kind : ValidationKind) → kind.Value Nat
  | .signer => ⟨validationArgs.info⟩
  | .system => validationArgs.info
  | .program => ⟨validationArgs.info⟩
  | .interface => ⟨⟨validationArgs.info⟩⟩
  | .unchecked => validationArgs.info
  | .accountInfo => validationArgs.info
  | .sysvar => ⟨7, validationArgs.info⟩

theorem validationSample_ready (errors : AnchorErrorOperations.Storage) (kind : ValidationKind)
  (state : World (validationSample errors).Aux) :
    ValidationReady kind (validationSample errors) state validationArgs := by
  cases kind <;> try trivial
  intro _ expected after called mismatch
  cases called
  exact False.elim (mismatch rfl)

theorem validationSample_clone (errors : AnchorErrorOperations.Storage) (state : World
  (validationSample errors).Aux) (info : AccountInfo.Value) :
    cloneInfo (validationSample errors).toBase (validationSample errors).rc state info (.returned
      info state) := by
  exact ⟨.returned info state, ⟨.returned info state,
    ⟨.returned () state, rfl, .returned () state, rfl, rfl⟩, rfl⟩, rfl⟩

theorem validationSample_retain (errors : AnchorErrorOperations.Storage) (storage : InfoStorage)
  (state : World (validationSample errors).Aux)
    (info : AccountInfo.Value) :
    retainInfo storage (validationSample errors).toBase (validationSample errors).rc state info
      (.returned info state) := by
  cases storage
  · exact validationSample_clone errors _ _
  · rfl

theorem validationSample_run (errors : AnchorErrorOperations.Storage) (kind : ValidationKind)
  (storage : InfoStorage)
    (state : World (validationSample errors).Aux) :
    validate kind storage (validationSample errors) state validationArgs
      (.returned (.ok (validationValue kind)) state) := by
  have retained := validationSample_retain errors storage state validationArgs.info
  cases kind with
  | signer => exact ⟨.returned validationArgs.info state, retained, rfl⟩
  | system => exact ⟨.returned validationArgs.info state, retained, rfl⟩
  | program =>
    exact ⟨.returned (.ok ()) state,
      ⟨.returned .zero state, ⟨.returned .zero state, rfl, rfl⟩, rfl⟩,
      .returned validationArgs.info state, retained, rfl⟩
  | interface =>
    exact ⟨.returned (.ok ()) state, ⟨.returned (.ok ()) state, rfl, rfl⟩,
      .returned validationArgs.info state, retained, rfl⟩
  | unchecked => exact ⟨.returned validationArgs.info state, retained, rfl⟩
  | accountInfo => exact ⟨.returned validationArgs.info state, validationSample_clone errors _ _,
    rfl⟩
  | sysvar => exact ⟨.returned (.ok (7 : Nat)) state, ⟨.returned (.ok (7 : Nat)) state, rfl, rfl⟩,
      .returned validationArgs.info state, retained, rfl⟩

theorem validation_execution (errors : AnchorErrorOperations.Storage) (kind : ValidationKind)
  (storage : InfoStorage) :
    FamilyHasExecution (validationFamily kind storage) (validationRun kind storage)
      (validationSample errors) := by
  exact ⟨(AccountInfo.sampleState, AnchorOwnedSamples.auxiliary), validationArgs,
    .returned (.ok (validationValue kind)) (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary),
    validationSample_ready errors kind _, validationSample_run errors kind storage _⟩

def validationAccountsSample (errors : AnchorErrorOperations.Storage) : ValidationAccountsTypes :=
  ⟨(validationSample errors), Unit⟩

theorem validationAccounts_execution (errors : AnchorErrorOperations.Storage) (kind :
  ValidationKind) (storage : InfoStorage) :
    FamilyHasExecution (validationAccountsFamily kind storage) (validationAccountsRun kind storage)
      (validationAccountsSample errors) := by
  let state : World (validationSample errors).Aux := (AccountInfo.sampleState,
    AnchorOwnedSamples.auxiliary)
  exact ⟨(state, ⟨[validationArgs.reference], (), []⟩),
    ⟨validationArgs.profile, .zero, []⟩,
    .returned (.ok (validationValue kind)) (state, ⟨[], (), []⟩),
    validationSample_ready errors kind state,
    .returned (.ok (validationValue kind)) state, validationSample_run errors kind storage state,
      rfl⟩

end Solanalib.Specs.Core.AnchorLifecycle
