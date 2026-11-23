/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleRead
public import Solanalib.Specs.Core.AnchorLifecycleConstruct
public import Solanalib.Specs.Core.AnchorViewsAssignment

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorAccount (World)

def accountCode (base : Base) (failure : AnchorAccount.Code) : base.Run Unit base.Error :=
  fun before _ => dependency base (AnchorErrorOperations.fromCode base.errorStorage base.errors)
    before ⟨failure.payload.name, failure.payload.code, failure.payload.message⟩

/-- Generic decoded-account effects, sharing the owned String/Box vocabulary.
Inline 0.27 errors and boxed later errors are selected explicitly by Base.
The codec index names either the checked or unchecked trait method. -/
structure PayloadTypes extends Base where
  Payload : Type
  ownerAt : AccountInfo.OwnerAt Aux
  owner : Callback.Run (World Aux) Unit Solanalib.Runtime.Pubkey Unwind Terminal
  checkOwner : Callback.Run (World Aux) AccountInfo.OwnerRef
    (Except (AnchorErrorOperations.Error errorStorage Program StringResource BoxResource) Unit)
      Unwind Terminal
  deserialize : Callback.Run (World Aux) AnchorAccount.DecodeArgs
    (AnchorConstructOwned.Decoded
      (AnchorErrorOperations.Error errorStorage Program StringResource BoxResource) Payload) Unwind
        Terminal
  rc : AccountInfoRc.Ops (World Aux) Terminal

def initialized (types : PayloadTypes) : types.toBase.Run AccountInfo.Args (Except
  types.toBase.Error Unit) :=
  fun before args outcome =>
    if types.ownerAt before.2 args.info.ownerRef = AnchorAccount.systemProgramId then
      Callback.bind (observe .lamports)
        (fun balance after result =>
          if balance = 0 then Callback.map Except.error (accountCode types.toBase .notInitialized)
            after () result
          else result = .returned (.ok ()) after)
        before args outcome
    else outcome = .returned (.ok ()) before

/-- The current owner is read after the first Owner call. A mismatch builds
the error of the release, copies the then-current owner, calls Owner again, and
attaches those compared keys. The live error is protected on callback unwind. -/
def ownerCheck (types : PayloadTypes) : types.toBase.Run AccountInfo.Args (Except
  types.toBase.Error Unit) :=
  fun before args => Callback.bind (AnchorAccount.widenCallback types.owner)
    (fun expected after outcome =>
      if types.ownerAt after.2 args.info.ownerRef = expected then outcome = .returned (.ok ()) after
      else Callback.bind (accountCode types.toBase .ownedByWrongProgram)
        (fun error allocated result =>
          let observed := types.ownerAt allocated.2 args.info.ownerRef
          Owned.protect (noDoubleUnwind types.toBase) [dropError types.toBase error]
            (Callback.bind (AnchorAccount.widenCallback types.owner)
              (fun diagnostic checked final => Callback.map Except.error
                (dependency types.toBase (AnchorErrorOperations.withPubkeys types.errorStorage
                  types.errors observed diagnostic)) checked error final))
            allocated () result)
        after () outcome)
    before ()

/-- A clone is moved into the wrapper only on decoder success. An Err or
unwind drops the temporary clone; a terminal bypasses all local drops. -/
def decoderCleanup (types : PayloadTypes) (info : AccountInfo.Value)
    (pending final : Outcome (World types.Aux)
      (AnchorConstructOwned.Decoded types.toBase.Error types.Payload) types.toBase.Unw
        types.toBase.Term) : Prop :=
  match pending with
  | .returned decoded _ => match decoded.result with
    | .ok _ => final = pending
    | .error _ => Owned.cleanup (noDoubleUnwind types.toBase) [dropInfo types.toBase types.rc info]
      pending final
  | .unwound _ _ => Owned.cleanup (noDoubleUnwind types.toBase) [dropInfo types.toBase types.rc
    info] pending final
  | .terminated _ => final = pending

def decoder (storage : InfoStorage) (types : PayloadTypes) :
    types.toBase.Run AnchorAccount.DecodeArgs (AnchorConstructOwned.Decoded types.toBase.Error
      types.Payload) :=
  match storage with
  | .borrowed => AnchorAccount.widenCallback types.deserialize
  | .owned => fun before args => Callback.bind (cloneInfo types.toBase types.rc)
      (fun info afterClone outcome => ∃ decoded,
        AnchorAccount.widenCallback types.deserialize afterClone args decoded ∧
          decoderCleanup types info decoded outcome)
      before args.info

/-- The live data lease is retained at each actually reached primitive.
Admission of the decoder and failure drops starts in the state of the returned clone, and is still
required if a later dependency has no finite exit. -/
def DecoderReady (storage : InfoStorage) (types : PayloadTypes)
    (before : World types.Aux) (args : AnchorAccount.DecodeArgs) : Prop :=
  match storage with
  | .borrowed => AccountInfo.GuardCallback.Admissible args.guard
      (AnchorAccount.widenCallback types.deserialize) before args
  | .owned => RcReady types.rc.cloneRc before args.info args.guard ∧
      ∀ info afterClone, cloneInfo types.toBase types.rc before args.info (.returned info
        afterClone) →
        AccountInfo.GuardCallback.Admissible args.guard
          (AnchorAccount.widenCallback types.deserialize) afterClone args ∧
        ∀ produced, AnchorAccount.widenCallback types.deserialize afterClone args produced →
          match produced with
          | .returned decoded after => match decoded.result with
            | .ok _ => True
            | .error _ => RcReady types.rc.dropRc after info args.guard
          | .unwound _ after => RcReady types.rc.dropRc after info args.guard
          | .terminated _ => True

/-- Primitive admission justifies release of the enclosing guard on every
finite decoder path, including Rc failure cleanup after Err or unwind. -/
theorem DecoderReady.admissible {storage : InfoStorage} {types : PayloadTypes}
    {before : World types.Aux} {args : AnchorAccount.DecodeArgs}
    (ready : DecoderReady storage types before args) :
    AccountInfo.GuardCallback.Admissible args.guard (decoder storage types) before args := by
  cases storage with
  | borrowed => exact ready
  | owned =>
    apply AccountInfo.GuardCallback.Admissible.bind ready.1.clone
    intro info afterClone cloned
    obtain ⟨decodeReady, dropsReady⟩ := ready.2 info afterClone cloned
    rintro final ⟨produced, called, cleaned⟩
    have frame := decodeReady produced called
    have drops := dropsReady produced called
    cases produced with
    | terminated _ => cases cleaned; trivial
    | unwound _ _ => exact cleanup_one_frame frame drops.drop cleaned
    | returned decoded after =>
      cases selected : decoded.result with
      | ok _ => simp only [decoderCleanup, selected] at cleaned; cases cleaned; exact frame
      | error _ =>
        simp only [decoderCleanup, selected] at cleaned
        simp only [selected] at drops
        exact cleanup_one_frame frame drops.drop cleaned

def decodePayload (storage : InfoStorage) (types : PayloadTypes) :
    types.toBase.Run AccountInfo.Args (Except types.toBase.Error types.Payload) :=
  fun before args outcome =>
    let (borrowed, during) := AccountInfo.tryBorrowData before.1 args
    match borrowed with
    | .error failure => Callback.map Except.error (programError types.toBase failure) (during,
      before.2) () outcome
    | .ok guard => match Borrow.current during guard with
      | .error _ | .ok (_, .lamports _) => False
      | .ok (_, .data bytes) => AnchorEffects.withGuard guard
          (Callback.map AnchorConstructOwned.Decoded.result (decoder storage types))
          (during, before.2) ⟨args.info, guard, bytes⟩ outcome

def DecodePayloadReady (storage : InfoStorage) (types : PayloadTypes)
    (before : World types.Aux) (args : AccountInfo.Args) : Prop :=
  (∃ bytes policy, before.1.lookupCell args.info.data = some ⟨.data bytes, policy⟩) ∧
    ∀ guard during, AccountInfo.tryBorrowData before.1 args = (.ok guard, during) →
      ∀ view bytes, Borrow.current during guard = .ok (view, .data bytes) →
        DecoderReady storage types (during, before.2) ⟨args.info, guard, bytes⟩

def construct (kind : PayloadKind) (storage : InfoStorage) (types : PayloadTypes) :
    types.toBase.Run AccountInfo.Args (Except types.toBase.Error (kind.constructor.Result
      types.Payload)) :=
  fun before args => AnchorEffects.resultBind (initialized types)
    (fun _ after => AnchorEffects.resultBind
      (match kind with
        | .account => ownerCheck types
        | .interfaceAccount => fun state infoArgs =>
            AnchorAccount.widenCallback types.checkOwner state infoArgs.info.ownerRef)
      (fun _ checked => Callback.bind (decodePayload storage types)
        (fun decoded afterDecode outcome =>
          match kind with
          | .account => outcome = .returned (decoded.map fun value => AnchorAccount.Account.mk
            value args.info) afterDecode
          | .interfaceAccount => outcome = .returned
              (decoded.map fun value => AnchorAccount.InterfaceAccount.mk ⟨value, args.info⟩
                (types.ownerAt afterDecode.2 args.info.ownerRef)) afterDecode)
        checked args)
      after args)
    before args

/-- the receiver field of Reload is selected by a lawful focus. Its destructor
receives the actual old payload, and a completed or unwinding drop installs
the already decoded replacement through that same focus. -/
structure ReloadTypes extends PayloadTypes where
  payload : Owned.Focus (World Aux) Payload
  dropPayload : Callback.Run (World Aux) Payload Unit Unwind Terminal

def replacePayload (types : ReloadTypes) : types.toPayloadTypes.toBase.Run types.Payload Unit :=
  AnchorViewsAssignment.run types.payload (AnchorAccount.widenCallback types.dropPayload)

/-- Account reload performs the replacement while its shared data guard is
still live. Decoder error does not drop or replace the old payload. -/
def decodeReplace (types : ReloadTypes) :
    types.toPayloadTypes.toBase.Run AccountInfo.Args (Except types.toPayloadTypes.toBase.Error
      Unit) :=
  fun before args outcome =>
    let (borrowed, during) := AccountInfo.tryBorrowData before.1 args
    match borrowed with
    | .error failure => Callback.map Except.error (programError types.toPayloadTypes.toBase failure)
        (during, before.2) () outcome
    | .ok guard => match Borrow.current during guard with
      | .error _ | .ok (_, .lamports _) => False
      | .ok (_, .data bytes) => AnchorEffects.withGuard guard
          (AnchorEffects.resultBind
            (Callback.map AnchorConstructOwned.Decoded.result (AnchorAccount.widenCallback
              types.deserialize))
            (fun replacement after => Callback.map Except.ok (replacePayload types) after
              replacement))
          (during, before.2) ⟨args.info, guard, bytes⟩ outcome

/-- Legacy InterfaceAccount delegates to Account::reload. Modern InterfaceAccount
checks its owner and ends its inner data-borrow block before calling set_inner. -/
inductive ReloadMode where
  | legacy
  | account
  | interfaceAccount
  deriving DecidableEq, Repr

def reload (mode : ReloadMode) (types : ReloadTypes) :
    types.toPayloadTypes.toBase.Run AccountInfo.Args (Except types.toPayloadTypes.toBase.Error
      Unit) :=
  match mode with
  | .legacy => decodeReplace types
  | .account => fun before args => AnchorEffects.resultBind (ownerCheck types.toPayloadTypes)
      (fun _ after => decodeReplace types after args) before args
  | .interfaceAccount => fun before args =>
      AnchorEffects.resultBind (AnchorAccount.widenCallback types.checkOwner)
        (fun _ checked => AnchorEffects.resultBind (decodePayload .borrowed types.toPayloadTypes)
          (fun replacement after => Callback.map Except.ok (replacePayload types) after replacement)
          checked args)
        before args.info.ownerRef

/-- The error representation is required only at the reached boxed mismatch.
Inline errors already carry their payload; boxed errors require their actual
allocated payload and the current-state store of the diagnostic callback. -/
def OwnerReady (types : PayloadTypes) (before : World types.Aux) (args : AccountInfo.Args) : Prop :=
  types.errorStorage = .boxed →
  ∀ expected after, types.owner before () (.returned expected after) →
    types.ownerAt after.2 args.info.ownerRef ≠ expected →
    ∀ name afterName, types.errors.copyLiteral after
      AnchorAccount.Code.ownedByWrongProgram.payload.name
      (.returned name afterName) →
    ∀ message afterMessage, types.errors.formatLiteral afterName
      AnchorAccount.Code.ownedByWrongProgram.payload.message
      (.returned message afterMessage) →
    ∀ resource afterBox, types.errors.newBox afterMessage
      (.anchor ⟨name, AnchorAccount.Code.ownedByWrongProgram.payload.code, message, none, none⟩)
      (.returned resource afterBox) →
      types.errors.currentBox afterBox resource =
        some (.anchor ⟨name, AnchorAccount.Code.ownedByWrongProgram.payload.code, message, none,
          none⟩) ∧
      ∀ produced, types.owner afterBox () produced →
        match produced with
        | .returned diagnostic afterOwner =>
          types.errors.currentBox afterOwner resource = types.errors.currentBox afterBox resource ∧
            ∃ final, types.errors.writeBox afterOwner resource
              (.anchor ⟨name, AnchorAccount.Code.ownedByWrongProgram.payload.code, message, none,
                some (.pubkeys (types.ownerAt afterBox.2 args.info.ownerRef) diagnostic)⟩) = some
                  final
        | .unwound _ afterOwner =>
          types.errors.currentBox afterOwner resource = types.errors.currentBox afterBox resource
        | .terminated _ => True

def ConstructReady (kind : PayloadKind) (storage : InfoStorage) (types : PayloadTypes)
    (before : World types.Aux) (args : AccountInfo.Args) : Prop :=
  AnchorAccount.InitReady types.ownerAt before args ∧
    ∀ after, initialized types before args (.returned (.ok ()) after) →
      match kind with
      | .account => OwnerReady types after args ∧
          ∀ checked, ownerCheck types after args (.returned (.ok ()) checked) →
            DecodePayloadReady storage types checked args
      | .interfaceAccount =>
          ∀ checked, AnchorAccount.widenCallback types.checkOwner after args.info.ownerRef
            (.returned (.ok ()) checked) → DecodePayloadReady storage types checked args

def DecodeReplaceReady (types : ReloadTypes) (before : World types.Aux) (args : AccountInfo.Args) :
  Prop :=
  (∃ bytes policy, before.1.lookupCell args.info.data = some ⟨.data bytes, policy⟩) ∧
    ∀ guard during, AccountInfo.tryBorrowData before.1 args = (.ok guard, during) →
      ∀ view bytes, Borrow.current during guard = .ok (view, .data bytes) →
        AccountInfo.GuardCallback.Admissible guard
          (AnchorAccount.widenCallback types.deserialize) (during, before.2) ⟨args.info, guard,
            bytes⟩ ∧
        ∀ decoded after, AnchorAccount.widenCallback types.deserialize (during, before.2)
          ⟨args.info, guard, bytes⟩ (.returned decoded after) →
        ∀ replacement, decoded.result = .ok replacement →
          AccountInfo.GuardCallback.Admissible guard (replacePayload types) after replacement

def ReloadReady (mode : ReloadMode) (types : ReloadTypes) (before : World types.Aux)
    (args : AccountInfo.Args) : Prop :=
  match mode with
  | .legacy => DecodeReplaceReady types before args
  | .account => OwnerReady types.toPayloadTypes before args ∧
      ∀ checked, ownerCheck types.toPayloadTypes before args (.returned (.ok ()) checked) →
        DecodeReplaceReady types checked args
  | .interfaceAccount => ∀ checked,
      AnchorAccount.widenCallback types.checkOwner before args.info.ownerRef (.returned (.ok ())
        checked) →
        DecodePayloadReady .borrowed types.toPayloadTypes checked args

def payloadFamily (kind : PayloadKind) (storage : InfoStorage) : Family where
  Index := PayloadTypes
  State := fun types => World types.Aux
  Args := fun _ => AccountInfo.Args
  Value := fun types => Except types.toBase.Error (kind.constructor.Result types.Payload)
  Unwind := fun types => types.toBase.Unw
  Terminal := fun types => types.toBase.Term
  contract := fun types =>
    { requires := ConstructReady kind storage types, post := construct kind storage types }

def payloadRun (kind : PayloadKind) (storage : InfoStorage) : FamilyRun (payloadFamily kind
  storage) := construct kind storage

theorem payload_reference (kind : PayloadKind) (storage : InfoStorage) :
    FamilyReference (payloadFamily kind storage) (payloadRun kind storage) := by
  intro _ _ _ _ _ called
  exact called

structure PayloadAccountsTypes extends PayloadTypes where
  Bumps : Type

/-- The slice carries source record identities. Consuming the head preserves
the remaining records, bumps and reallocations even when validation fails. -/
def payloadAccountsFamily (kind : PayloadKind) (storage : InfoStorage) : Family where
  Index := PayloadAccountsTypes
  State := fun types => World types.Aux × AccountsState types.Bumps
  Args := fun _ => AccountsArgs
  Value := fun types => Except types.toPayloadTypes.toBase.Error (kind.constructor.Result
    types.Payload)
  Unwind := fun types => types.toPayloadTypes.toBase.Unw
  Terminal := fun types => types.toPayloadTypes.toBase.Term
  contract := fun types => {
    requires := fun before args => match before.2.remaining with
      | [] => True
      | reference :: _ => ConstructReady kind storage types.toPayloadTypes before.1
          ⟨args.profile, reference.info⟩
    post := consume (code types.toPayloadTypes.toBase .notEnoughKeys)
      (fun before args => construct kind storage types.toPayloadTypes before
        args.toAccountInfoArgs) }

def payloadAccountsRun (kind : PayloadKind) (storage : InfoStorage) :
    FamilyRun (payloadAccountsFamily kind storage) := fun types =>
  consume (code types.toPayloadTypes.toBase .notEnoughKeys)
    (fun before args => construct kind storage types.toPayloadTypes before args.toAccountInfoArgs)

theorem payloadAccounts_reference (kind : PayloadKind) (storage : InfoStorage) :
    FamilyReference (payloadAccountsFamily kind storage) (payloadAccountsRun kind storage) := by
  intro _ _ _ _ _ called
  exact called

def reloadFamily (mode : ReloadMode) : Family where
  Index := ReloadTypes
  State := fun types => World types.Aux
  Args := fun _ => AccountInfo.Args
  Value := fun types => Except types.toPayloadTypes.toBase.Error Unit
  Unwind := fun types => types.toPayloadTypes.toBase.Unw
  Terminal := fun types => types.toPayloadTypes.toBase.Term
  contract := fun types => { requires := ReloadReady mode types, post := reload mode types }

def reloadRun (mode : ReloadMode) : FamilyRun (reloadFamily mode) := reload mode

theorem reload_reference (mode : ReloadMode) : FamilyReference (reloadFamily mode) (reloadRun mode)
  := by
  intro _ _ _ _ _ called
  exact called

/-- Decoding happens before old-payload destruction. When destruction unwinds,
the replacement remains installed in the actual destructor state. -/
theorem replacement_unwind {types : ReloadTypes} {before after : World types.Aux}
    {replacement : types.Payload} {reason : types.Unwind}
    (dropped : types.dropPayload before (types.payload.get before) (.unwound reason after)) :
    replacePayload types before replacement
      (.unwound (.inr reason) (types.payload.set after replacement)) ∧
      types.payload.get (types.payload.set after replacement) = replacement := by
  exact AnchorViewsAssignment.unwound types.payload (AnchorAccount.widenCallback types.dropPayload)
    ⟨.unwound reason after, dropped, rfl⟩

end Solanalib.Specs.Core.AnchorLifecycle
