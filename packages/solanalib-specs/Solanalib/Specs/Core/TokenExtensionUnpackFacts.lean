/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionUnpack

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- Dropping an owned base after a layout error cannot create a successful
unpack result, regardless of the state changes or exit kind of the destructor. -/
theorem finishExtensionBaseDrop_ne_success
    {State Base Reference Unwind Terminal : Type} (error : Error)
    (dropped : Outcome State Unit Unwind Terminal)
    (value : ExtensionUnpacked Base Reference) (after : State) :
    finishExtensionBaseDrop error dropped ≠ .returned (.ok value) after := by
  cases dropped with
  | returned value state => cases value; simp [finishExtensionBaseDrop]
  | unwound reason state => simp [finishExtensionBaseDrop]
  | terminated reason => simp [finishExtensionBaseDrop]

/-- Success retains exactly the base and state returned by the actual parser;
it also requires the layout check to return that same tail reference. -/
theorem finishExtensionUnpack_success_origin (unpacker : ExtensionUnpacker)
    (input : unpacker.Reference)
    (parsed : Outcome unpacker.State (Except Error unpacker.Base)
      unpacker.Unwind unpacker.Terminal)
    (value : ExtensionUnpacked unpacker.Base unpacker.Reference)
    (after : unpacker.State)
    (finished : finishExtensionUnpack unpacker input parsed (.returned (.ok value) after)) :
    parsed = .returned (.ok value.base) after ∧
      unpackExtensionTailReference unpacker after input = .ok value.tlv := by
  cases parsed with
  | unwound reason state => simp [finishExtensionUnpack] at finished
  | terminated reason => simp [finishExtensionUnpack] at finished
  | returned result state =>
    cases result with
    | error error => simp [finishExtensionUnpack] at finished
    | ok base =>
      cases layout : unpackExtensionTailReference unpacker state input with
      | error error =>
        simp only [finishExtensionUnpack, layout] at finished
        obtain ⟨dropped, _, equal⟩ := finished
        exact False.elim (finishExtensionBaseDrop_ne_success error dropped value after equal.symm)
      | ok tlv =>
        simp only [finishExtensionUnpack, layout, Outcome.returned.injEq, Except.ok.injEq]
          at finished
        obtain ⟨valueEqual, stateEqual⟩ := finished
        subst after
        subst value
        exact ⟨rfl, layout⟩

/-- Characterize all successful operational executions. No parser success,
state frame or destructor behavior is assumed by the converse direction. -/
theorem unpackExtensionOperational_success_iff (unpacker : ExtensionUnpacker)
    (before after : unpacker.State) (input : unpacker.Reference)
    (value : ExtensionUnpacked unpacker.Base unpacker.Reference) :
    unpackExtensionOperational unpacker before input (.returned (.ok value) after) ↔
      ¬ (unpacker.length input = multisigLength ∨ unpacker.length input < unpacker.baseLength) ∧
      unpacker.parse before ⟨input, 0, unpacker.baseLength⟩
        (.returned (.ok value.base) after) ∧
      unpackExtensionTailReference unpacker after input = .ok value.tlv := by
  constructor
  · intro run
    by_cases rejected : unpacker.length input = multisigLength ∨
        unpacker.length input < unpacker.baseLength
    · simp [unpackExtensionOperational, rejected] at run
    · simp only [unpackExtensionOperational, rejected, ↓reduceIte] at run
      obtain ⟨parsed, called, finished⟩ := run
      obtain ⟨parsedEqual, layout⟩ :=
        finishExtensionUnpack_success_origin unpacker input parsed value after finished
      exact ⟨rejected, parsedEqual ▸ called, layout⟩
  · rintro ⟨admitted, parsed, layout⟩
    exact unpackExtensionOperational_success unpacker before after input value.base value.tlv
      admitted parsed layout

/-- A successful nonempty rest contains the complete padding and marker, and
its returned bytes are precisely the suffix following that prefix. -/
theorem unpackExtensionTail_nonempty_success (baseLength : Nat)
    (accountType : ExtensionAccountType) (rest tlv : Bytes)
    (nonempty : rest.isEmpty = false)
    (layout : unpackExtensionTail baseLength accountType rest = .ok tlv) :
    accountLength - baseLength + 1 ≤ rest.length ∧
      tlv = rest.drop (accountLength - baseLength + 1) := by
  unfold unpackExtensionTail at layout
  simp only [nonempty, Bool.false_eq_true, ↓reduceIte] at layout
  split at layout
  · cases layout
  · rename_i enough
    split at layout
    · cases layout
    · split at layout
      · cases layout
        exact ⟨Nat.le_of_not_gt enough, rfl⟩
      · cases layout

/-- A borrowed tail retains the original input identity and exact source
offset. Its range is bounded and extends to the end of that same input. -/
theorem unpackExtensionTailReference_borrowed_geometry (unpacker : ExtensionUnpacker)
    (state : unpacker.State) (input : unpacker.Reference)
    (region : ExtensionRegion unpacker.Reference)
    (returned : unpackExtensionTailReference unpacker state input = .ok (.borrowed region)) :
    region.origin = input ∧
      region.offset = unpacker.baseLength + (accountLength - unpacker.baseLength) + 1 ∧
      region.offset ≤ unpacker.length input ∧
      region.length = unpacker.length input - region.offset ∧
      region.offset + region.length = unpacker.length input := by
  let rest := (unpacker.inputBytes state input).drop unpacker.baseLength
  unfold unpackExtensionTailReference at returned
  change (unpackExtensionTail unpacker.baseLength unpacker.accountType rest).map
      (fun tlv => if rest.isEmpty then ExtensionTailReference.empty else
        ExtensionTailReference.borrowed
        ⟨input, unpacker.baseLength + (accountLength - unpacker.baseLength) + 1, tlv.length⟩) =
      .ok (ExtensionTailReference.borrowed region) at returned
  cases layout : unpackExtensionTail unpacker.baseLength unpacker.accountType rest with
  | error error => simp [layout, Except.map] at returned
  | ok tlv =>
    simp only [layout, Except.map] at returned
    cases empty : rest.isEmpty with
    | true => simp [empty] at returned
    | false =>
      simp only [empty, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
        ExtensionTailReference.borrowed.injEq] at returned
      subst region
      obtain ⟨enough, tailEqual⟩ := unpackExtensionTail_nonempty_success
        unpacker.baseLength unpacker.accountType rest tlv empty layout
      have restLength : rest.length = unpacker.length input - unpacker.baseLength := by
        simp only [rest, List.length_drop, ExtensionUnpacker.inputBytes_length]
      have tailLength : tlv.length = rest.length - (accountLength - unpacker.baseLength + 1) := by
        rw [tailEqual, List.length_drop]
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> dsimp only <;> omega

/-- Observe a returned tail in the specified actual state. A borrowed range
reads through its retained origin; the static empty slice of the source stays empty. -/
def observeExtensionTailReference (unpacker : ExtensionUnpacker) (state : unpacker.State) :
    ExtensionTailReference unpacker.Reference → Bytes
  | .empty => []
  | .borrowed region =>
    ((unpacker.inputBytes state region.origin).drop region.offset).take region.length

/-- Forget reference identity only for a byte-level observation, while keeping
the exact owned parsed value. -/
def observeExtensionUnpacked (unpacker : ExtensionUnpacker) (state : unpacker.State)
    (value : ExtensionUnpacked unpacker.Base unpacker.Reference) : StateWithExtensions
      unpacker.Base :=
  ⟨value.base, observeExtensionTailReference unpacker state value.tlv⟩

/-- At the state of its layout check, the retained tail reference observes
exactly the successful suffix of the byte-level layout operation. -/
theorem unpackExtensionTailReference_observes (unpacker : ExtensionUnpacker)
    (state : unpacker.State) (input : unpacker.Reference) :
    (unpackExtensionTailReference unpacker state input).map
      (observeExtensionTailReference unpacker state) =
      unpackExtensionTail unpacker.baseLength unpacker.accountType
        ((unpacker.inputBytes state input).drop unpacker.baseLength) := by
  let rest := (unpacker.inputBytes state input).drop unpacker.baseLength
  unfold unpackExtensionTailReference
  change ((unpackExtensionTail unpacker.baseLength unpacker.accountType rest).map
      (fun tlv => if rest.isEmpty then ExtensionTailReference.empty
        else ExtensionTailReference.borrowed
          ⟨input, unpacker.baseLength + (accountLength - unpacker.baseLength) + 1, tlv.length⟩)).map
      (observeExtensionTailReference unpacker state) =
      unpackExtensionTail unpacker.baseLength unpacker.accountType rest
  cases layout : unpackExtensionTail unpacker.baseLength unpacker.accountType rest with
  | error error => rfl
  | ok tlv =>
    cases empty : rest.isEmpty with
    | true =>
      have restNil : rest = [] := List.isEmpty_iff.mp empty
      have tailNil : tlv = [] := by
        simpa only [restNil, unpackExtensionTail, List.isEmpty_nil, ↓reduceIte,
          Except.ok.injEq] using layout.symm
      simp only [↓reduceIte, Except.map, observeExtensionTailReference, tailNil]
    | false =>
      obtain ⟨_, tailEqual⟩ := unpackExtensionTail_nonempty_success
        unpacker.baseLength unpacker.accountType rest tlv empty layout
      have suffixEqual : (unpacker.inputBytes state input).drop
          (unpacker.baseLength + (accountLength - unpacker.baseLength) + 1) = tlv := by
        simpa only [rest, List.drop_drop, Nat.add_assoc] using tailEqual.symm
      simp only [Bool.false_eq_true, ↓reduceIte, Except.map,
        observeExtensionTailReference, suffixEqual, List.take_length]

/-- The pure byte-slice interpretation observes exactly its input bytes. -/
theorem pureDroplessExtensionUnpacker_inputBytes {Base : Type} (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Error Base) (bytes : Bytes) :
    (pureDroplessExtensionUnpacker baseLength accountType decode).inputBytes () bytes = bytes := by
  simp only [ExtensionUnpacker.inputBytes, currentExtensionBytes, pureDroplessExtensionUnpacker]
  exact List.ofFn_getElem

/-- The explicit pure-codec, trivial-destructor specialization recovers the
earlier byte-level unpack result when its retained tail is observed. This is a
specialization theorem, without a frame claim for arbitrary effectful parsers. -/
theorem unpackDroplessExtension_observes {Base : Type} (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Error Base) (bytes : Bytes) :
    (unpackDroplessExtension baseLength accountType decode bytes).map
      (observeExtensionUnpacked (pureDroplessExtensionUnpacker baseLength accountType decode) ()) =
      unpackStateWithExtensions baseLength accountType decode bytes := by
  by_cases rejected : extensionInputRejected baseLength bytes
  · simp only [unpackDroplessExtension, unpackStateWithExtensions, rejected, ↓reduceIte, Except.map]
  · simp only [unpackDroplessExtension, unpackStateWithExtensions, rejected, ↓reduceIte]
    cases decoded : decode (bytes.take baseLength) with
    | error error => rfl
    | ok base =>
      have observes := unpackExtensionTailReference_observes
        (pureDroplessExtensionUnpacker baseLength accountType decode) () bytes
      rw [pureDroplessExtensionUnpacker_inputBytes] at observes
      cases reference : unpackExtensionTailReference
          (pureDroplessExtensionUnpacker baseLength accountType decode) () bytes with
      | error error =>
        simp only [reference, Except.map] at observes
        simp only [Except.bind, Except.map, finishExtensionBase, ← observes]
      | ok tlv =>
        simp only [reference, Except.map] at observes
        simp only [Except.bind, Except.map, finishExtensionBase, ← observes,
          observeExtensionUnpacked]

end Solanalib.Specs.Core.Token
