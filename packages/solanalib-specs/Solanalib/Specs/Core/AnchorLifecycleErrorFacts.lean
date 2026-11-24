/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecyclePayload
public import Solanalib.Specs.Core.AnchorLifecycleValidation

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorAccount (World)

/-- Source-shaped error value for a reached factory: inline payload or the
actual allocation identity. This introduces no allocation or resource effect. -/
def errorAt {Program StringResource BoxResource : Type} (storage : AnchorErrorOperations.Storage)
    (payload : AnchorErrorOperations.Payload Program StringResource) (resource : BoxResource) :
    AnchorErrorOperations.Error storage Program StringResource BoxResource :=
  match storage with
  | .inline => payload
  | .boxed => ⟨resource⟩

theorem code_from_allocations {State Program StringResource BoxResource Terminal : Type}
    (storage : AnchorErrorOperations.Storage)
    (ops : AnchorErrorOperations.Ops State Program StringResource BoxResource Terminal)
    (code : AnchorErrorOperations.Code) {before afterName afterMessage afterBox : State}
    {name message : StringResource} {resource : BoxResource}
    (boxedStorage : storage = .boxed)
    (copied : ops.copyLiteral before code.name (.returned name afterName))
    (formatted : ops.formatLiteral afterName code.message (.returned message afterMessage))
    (boxed : ops.newBox afterMessage (.anchor ⟨name, code.number, message, none, none⟩)
      (.returned resource afterBox)) :
    AnchorErrorOperations.fromCode storage ops before code
      (.returned (errorAt storage (.anchor ⟨name, code.number, message, none, none⟩) resource)
        afterBox) := by
  cases storage with
  | inline => cases boxedStorage
  | boxed => exact ⟨.returned name afterName, copied, .returned message afterMessage, formatted,
      .returned resource afterBox, boxed, rfl⟩

theorem code_inline_returns {State Program StringResource BoxResource Terminal : Type}
    (ops : AnchorErrorOperations.Ops State Program StringResource BoxResource Terminal)
    (code : AnchorErrorOperations.Code) {before afterName afterMessage : State}
    {name message : StringResource}
    (copied : ops.copyLiteral before code.name (.returned name afterName))
    (formatted : ops.formatLiteral afterName code.message (.returned message afterMessage)) :
    AnchorErrorOperations.fromCode .inline ops before code
      (.returned (.anchor ⟨name, code.number, message, none, none⟩) afterMessage) :=
  ⟨.returned name afterName, copied, .returned message afterMessage, formatted, rfl⟩

/-- The fresh diagnostic has no old compared strings to drop. Its exact
current Box is updated in place after the diagnostic callback returns. -/
theorem withPubkeys_fresh_box {State Program StringResource BoxResource Terminal : Type}
    (storage : AnchorErrorOperations.Storage)
    (ops : AnchorErrorOperations.Ops State Program StringResource BoxResource Terminal)
    {before after : State} {payload : AnchorErrorOperations.Payload Program StringResource}
    {resource : BoxResource} {left right : Solanalib.Runtime.Pubkey}
    (boxedStorage : storage = .boxed)
    (current : ops.currentBox before resource = some payload)
    (fresh : payload.compared = none)
    (stored : ops.writeBox before resource (payload.withCompared (some (.pubkeys left right))) =
      some after) :
    AnchorErrorOperations.withPubkeys storage ops left right before (errorAt storage payload
      resource)
      (.returned (errorAt storage payload resource) after) := by
  cases storage with
  | inline => cases boxedStorage
  | boxed =>
    refine ⟨payload, current, .returned () before, ?_, payload, after, current, stored, rfl⟩
    simp only [AnchorErrorOperations.dropStrings, fresh, AnchorErrorOwned.comparedStrings,
      List.map_nil,
      Owned.cleanup]

/-- Primitive boxed allocation and diagnostic Id returns extend to the full
source error return. The source-selected error Box is retained and updated;
no successful callback or allocator is postulated by admission. -/
theorem id_mismatch_return_retain {types : ValidationTypes} {before after : World types.Aux}
    {args : AccountInfo.Args} (ready : IdReady types before args)
    (boxedStorage : types.errorStorage = .boxed)
    {expected : Solanalib.Runtime.Pubkey} (first : types.id before () (.returned expected after))
    (mismatch : args.info.key ≠ expected)
    {name message : types.StringResource} {resource : types.BoxResource}
    {afterName afterMessage afterBox afterId : World types.Aux}
    (copied : types.errors.copyLiteral after Code.invalidProgramId.payload.name (.returned name
      afterName))
    (formatted : types.errors.formatLiteral afterName Code.invalidProgramId.payload.message
      (.returned message afterMessage))
    (boxed : types.errors.newBox afterMessage (idErrorPayload types name message) (.returned
      resource afterBox))
    {diagnostic : Solanalib.Runtime.Pubkey} (second : types.id afterBox () (.returned diagnostic
      afterId)) :
    ∃ final, types.errors.currentBox afterId resource = some (idErrorPayload types name message) ∧
      types.errors.writeBox afterId resource
        ((idErrorPayload types name message).withCompared (some (.pubkeys args.info.key
          diagnostic))) = some final ∧
      idCheck types before args (.returned
        (.error (errorAt types.errorStorage (idErrorPayload types name message) resource)) final)
          := by
  have admitted := ready boxedStorage expected after first mismatch name afterName copied message
    afterMessage
    formatted resource afterBox boxed
  obtain ⟨frame, final, stored⟩ := admitted.2 _ second
  have held := frame.trans admitted.1
  refine ⟨final, held, stored, .returned expected after, ⟨_, first, rfl⟩, ?_⟩
  simp only [mismatch, ↓reduceIte]
  let error := errorAt types.errorStorage (idErrorPayload types name message) resource
  have built : code types.toBase .invalidProgramId after () (.returned error afterBox) :=
    ⟨_, ⟨_, code_from_allocations types.errorStorage types.errors _ boxedStorage copied formatted
      boxed, rfl⟩, rfl⟩
  refine ⟨.returned error afterBox, built, .returned (.error error) final, ?_, rfl⟩
  refine ⟨.returned diagnostic afterId, ⟨_, second, rfl⟩, .returned error final, ?_, rfl⟩
  exact ⟨_, ⟨_, withPubkeys_fresh_box types.errorStorage types.errors boxedStorage held rfl stored,
    rfl⟩, rfl⟩

/-- Owner diagnostics use the owner copied after allocation and preserve the
actual boxed error through the second trait call and its in-place store. -/
theorem owner_mismatch_return_retain {types : PayloadTypes} {before after : World types.Aux}
    {args : AccountInfo.Args} (ready : OwnerReady types before args)
    (boxedStorage : types.errorStorage = .boxed)
    {expected : Solanalib.Runtime.Pubkey} (first : types.owner before () (.returned expected after))
    (mismatch : types.ownerAt after.2 args.info.ownerRef ≠ expected)
    {name message : types.StringResource} {resource : types.BoxResource}
    {afterName afterMessage afterBox afterOwner : World types.Aux}
    (copied : types.errors.copyLiteral after AnchorAccount.Code.ownedByWrongProgram.payload.name
      (.returned name afterName))
    (formatted : types.errors.formatLiteral afterName
      AnchorAccount.Code.ownedByWrongProgram.payload.message (.returned message afterMessage))
    (boxed : types.errors.newBox afterMessage
      (.anchor ⟨name, AnchorAccount.Code.ownedByWrongProgram.payload.code, message, none, none⟩)
      (.returned resource afterBox))
    {diagnostic : Solanalib.Runtime.Pubkey} (second : types.owner afterBox () (.returned diagnostic
      afterOwner)) :
    ∃ error final, ownerCheck types before args (.returned (.error error) final) ∧
      types.errors.writeBox afterOwner resource
        (.anchor ⟨name, AnchorAccount.Code.ownedByWrongProgram.payload.code, message, none,
          some (.pubkeys (types.ownerAt afterBox.2 args.info.ownerRef) diagnostic)⟩) = some final
            := by
  have admitted := ready boxedStorage expected after first mismatch name afterName copied message
    afterMessage
    formatted resource afterBox boxed
  obtain ⟨frame, final, stored⟩ := admitted.2 _ second
  have held := frame.trans admitted.1
  let payload : AnchorErrorOperations.Payload types.Program types.StringResource :=
    .anchor ⟨name, AnchorAccount.Code.ownedByWrongProgram.payload.code, message, none, none⟩
  let error := errorAt types.errorStorage payload resource
  refine ⟨error, final, ?_, stored⟩
  refine ⟨.returned expected after, ⟨_, first, rfl⟩, ?_⟩
  simp only [mismatch, ↓reduceIte]
  have built : accountCode types.toBase .ownedByWrongProgram after () (.returned error afterBox) :=
    ⟨_, ⟨_, code_from_allocations types.errorStorage types.errors _ boxedStorage copied formatted
      boxed, rfl⟩, rfl⟩
  refine ⟨.returned error afterBox, built, .returned (.error error) final, ?_, rfl⟩
  refine ⟨.returned diagnostic afterOwner, ⟨_, second, rfl⟩, .returned error final, ?_, rfl⟩
  exact ⟨_, ⟨_, withPubkeys_fresh_box types.errorStorage types.errors boxedStorage held rfl stored,
    rfl⟩, rfl⟩

/-- Actual fresh error fields are destroyed before freeing the same Box.
Neither step is replaced by a successful destructor assumption. -/
theorem drop_fresh_box {State Program StringResource BoxResource Terminal : Type}
    (storage : AnchorErrorOperations.Storage)
    (ops : AnchorErrorOperations.Ops State Program StringResource BoxResource Terminal)
    {before afterFields : State} {name message : StringResource} {number : UInt32}
    {resource : BoxResource} (boxedStorage : storage = .boxed)
    (current : ops.currentBox before resource = some (.anchor ⟨name, number, message, none, none⟩))
    (fields : AnchorErrorOperations.dropStrings ops [name, message] before () (.returned ()
      afterFields))
    {freed : Outcome State Unit Empty Terminal} (free : ops.freeBox afterFields resource freed) :
    AnchorErrorOperations.drop storage ops before
      (errorAt storage (.anchor ⟨name, number, message, none, none⟩) resource) freed := by
  cases storage with
  | inline => cases boxedStorage
  | boxed => exact ⟨.anchor ⟨name, number, message, none, none⟩, current,
      .returned () afterFields, fields, free⟩

/-- A second id callback unwind uses the admitted current error payload.
The actual String cleanup and Box release determine the final state or terminal
exit; the wrapper retains the original unwind after successful destruction. -/
theorem id_mismatch_unwind_retain {types : ValidationTypes} {before after : World types.Aux}
    {args : AccountInfo.Args} (ready : IdReady types before args)
    (boxedStorage : types.errorStorage = .boxed)
    {expected : Solanalib.Runtime.Pubkey} (first : types.id before () (.returned expected after))
    (mismatch : args.info.key ≠ expected)
    {name message : types.StringResource} {resource : types.BoxResource}
    {afterName afterMessage afterBox afterDiagnostic afterFields : World types.Aux}
    (copied : types.errors.copyLiteral after Code.invalidProgramId.payload.name (.returned name
      afterName))
    (formatted : types.errors.formatLiteral afterName Code.invalidProgramId.payload.message
      (.returned message afterMessage))
    (boxed : types.errors.newBox afterMessage
      (.anchor ⟨name, Code.invalidProgramId.payload.code, message, none, none⟩) (.returned resource
        afterBox))
    {reason : types.Unwind} (second : types.id afterBox () (.unwound reason afterDiagnostic))
    (fields : AnchorErrorOperations.dropStrings types.errors [name, message] afterDiagnostic ()
      (.returned () afterFields))
    {freed : Outcome (World types.Aux) Unit Empty types.Terminal}
    (free : types.errors.freeBox afterFields resource freed) :
    idCheck types before args
      (Outcome.bind (AnchorAccount.widen (AccountInfoRc.liftOutcome freed))
        (fun _ final => .unwound (.inr reason) final)) := by
  have admitted := ready boxedStorage expected after first mismatch name afterName copied message
    afterMessage
    formatted resource afterBox boxed
  have held := (admitted.2 _ second).trans admitted.1
  let payload : AnchorErrorOperations.Payload types.Program types.StringResource :=
    .anchor ⟨name, Code.invalidProgramId.payload.code, message, none, none⟩
  let error := errorAt types.errorStorage payload resource
  have dropped : AnchorErrorOperations.drop types.errorStorage types.errors afterDiagnostic error
    freed :=
    drop_fresh_box types.errorStorage types.errors boxedStorage held fields free
  have built : code types.toBase .invalidProgramId after () (.returned error afterBox) :=
    ⟨_, ⟨_, code_from_allocations types.errorStorage types.errors _ boxedStorage copied formatted
      boxed, rfl⟩, rfl⟩
  refine ⟨.returned expected after, ⟨_, first, rfl⟩, ?_⟩
  simp only [mismatch, ↓reduceIte]
  refine ⟨.returned error afterBox, built, .unwound (.inr reason) afterDiagnostic, ?_, ?_⟩
  · exact ⟨.unwound (.inr reason) afterDiagnostic, ⟨_, second, rfl⟩, rfl⟩
  · cases freed with
    | returned value final =>
      cases value
      exact ⟨.returned () final,
        ⟨.returned () final, ⟨.returned () final, dropped, rfl⟩, rfl⟩, rfl⟩
    | unwound impossible _ => nomatch impossible
    | terminated terminal =>
      exact ⟨.terminated (.inr terminal),
        ⟨.terminated terminal, ⟨.terminated terminal, dropped, rfl⟩, rfl⟩, rfl⟩

/-- A second owner callback unwind uses the admitted current error payload.
The actual String cleanup and Box release determine the final state or terminal
exit; the wrapper retains the original unwind after successful destruction. -/
theorem owner_mismatch_unwind_retain {types : PayloadTypes} {before after : World types.Aux}
    {args : AccountInfo.Args} (ready : OwnerReady types before args)
    (boxedStorage : types.errorStorage = .boxed)
    {expected : Solanalib.Runtime.Pubkey} (first : types.owner before () (.returned expected after))
    (mismatch : types.ownerAt after.2 args.info.ownerRef ≠ expected)
    {name message : types.StringResource} {resource : types.BoxResource}
    {afterName afterMessage afterBox afterDiagnostic afterFields : World types.Aux}
    (copied : types.errors.copyLiteral after AnchorAccount.Code.ownedByWrongProgram.payload.name
      (.returned name afterName))
    (formatted : types.errors.formatLiteral afterName
      AnchorAccount.Code.ownedByWrongProgram.payload.message (.returned message afterMessage))
    (boxed : types.errors.newBox afterMessage
      (.anchor ⟨name, AnchorAccount.Code.ownedByWrongProgram.payload.code, message, none, none⟩)
        (.returned resource afterBox))
    {reason : types.Unwind} (second : types.owner afterBox () (.unwound reason afterDiagnostic))
    (fields : AnchorErrorOperations.dropStrings types.errors [name, message] afterDiagnostic ()
      (.returned () afterFields))
    {freed : Outcome (World types.Aux) Unit Empty types.Terminal}
    (free : types.errors.freeBox afterFields resource freed) :
    ownerCheck types before args
      (Outcome.bind (AnchorAccount.widen (AccountInfoRc.liftOutcome freed))
        (fun _ final => .unwound (.inr reason) final)) := by
  have admitted := ready boxedStorage expected after first mismatch name afterName copied message
    afterMessage
    formatted resource afterBox boxed
  have held := (admitted.2 _ second).trans admitted.1
  let payload : AnchorErrorOperations.Payload types.Program types.StringResource :=
    .anchor ⟨name, AnchorAccount.Code.ownedByWrongProgram.payload.code, message, none, none⟩
  let error := errorAt types.errorStorage payload resource
  have dropped : AnchorErrorOperations.drop types.errorStorage types.errors afterDiagnostic error
    freed :=
    drop_fresh_box types.errorStorage types.errors boxedStorage held fields free
  have built : accountCode types.toBase .ownedByWrongProgram after () (.returned error afterBox) :=
    ⟨_, ⟨_, code_from_allocations types.errorStorage types.errors _ boxedStorage copied formatted
      boxed, rfl⟩, rfl⟩
  refine ⟨.returned expected after, ⟨_, first, rfl⟩, ?_⟩
  simp only [mismatch, ↓reduceIte]
  refine ⟨.returned error afterBox, built, .unwound (.inr reason) afterDiagnostic, ?_, ?_⟩
  · exact ⟨.unwound (.inr reason) afterDiagnostic, ⟨_, second, rfl⟩, rfl⟩
  · cases freed with
    | returned value final =>
      cases value
      exact ⟨.returned () final,
        ⟨.returned () final, ⟨.returned () final, dropped, rfl⟩, rfl⟩, rfl⟩
    | unwound impossible _ => nomatch impossible
    | terminated terminal =>
      exact ⟨.terminated (.inr terminal),
        ⟨.terminated terminal, ⟨.terminated terminal, dropped, rfl⟩, rfl⟩, rfl⟩

end Solanalib.Specs.Core.AnchorLifecycle
