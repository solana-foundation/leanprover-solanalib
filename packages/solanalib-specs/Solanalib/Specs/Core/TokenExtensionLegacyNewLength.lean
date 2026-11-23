/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionLegacyList

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Legacy

open Owned

/-- Actual dependencies of the variable-length size wrapper. The source first
calls get_tlv_data on the receiver, then get_packed_len on the borrowed new
extension, and only then constructs the temporary TLV type vector. -/
structure NewLength where
  /-- Existing receiver, live TLV slice and vector dependencies. -/
  reader : CurrentExtensionTypeReader
  /-- Identity of the new borrowed V value. -/
  NewReference : Type
  /-- Actual resolved V::get_packed_len; no particular serializer is assumed. -/
  getPackedLen : reader.State → NewReference →
    Outcome reader.State (Except Error Nat) reader.Unwind reader.Terminal → Prop
  /-- Exact source V::TYPE in the older production enum. -/
  kind : Kind
  /-- Exact S::ACCOUNT_TYPE used by the free byte lookup. -/
  accountType : ExtensionAccountType

/-- Saturating type-and-length header addition at 64-bit usize. -/
def addHeader (length : Nat) : Nat :=
  saturatingSizeAdd (saturatingSizeAdd length 2) 2

/-- A lookup error, including a mismatched base association, means that the
existing extension contributes zero bytes. Successful lookup removes its
actual declared length plus header, not its official fixed Pod size. -/
def oldExtensionLength (kind : ExtensionType) (accountType : ExtensionAccountType)
    (bytes : Bytes) : Nat :=
  if kind.accountType = accountType then
    match findExtension kind 0 bytes with
    | .ok view => addHeader view.bytes.length
    | .error _ => 0
  else 0

/-- Start from the used TLV prefix (excluding trailing uninitialized capacity),
subtract the old selected entry with saturation, add the new declared size
with saturation, then avoid the multisig length. -/
def newLengthValue (kind : ExtensionType) (accountType : ExtensionAccountType)
    (used length : Nat) (bytes : Bytes) : Nat :=
  let current := saturatingSizeAdd used (accountLength + 1)
  let old := oldExtensionLength kind accountType bytes
  adjustMultisigLength (saturatingSizeAdd (current - old) (addHeader length))

/-- Continue after both source accessors returned. The list of the scanner stays
owned while lookup and arithmetic run, then is dropped before the return. -/
def sizeFromTlv (model : NewLength) (before : model.reader.State)
    (reference : model.reader.Reference) (newLength : Nat)
    (final : Outcome model.reader.State (Except Error Nat) model.reader.Unwind
      model.reader.Terminal) :
    Prop :=
  ∃ scanned, getInfo model.reader before reference scanned ∧
    match scanned with
    | .returned (.error error) after => final = .returned (.error error) after
    | .returned (.ok (resource, used)) after =>
      let bytes := currentExtensionBytes (model.reader.length reference)
        (fun state => model.reader.byteAt state reference) after
      cleanup model.reader.doubleUnwind [model.reader.vectors.dropAction resource]
        (.returned (.ok (newLengthValue model.kind.val model.accountType used newLength bytes))
          after)
        final
    | .unwound reason after => final = .unwound reason after
    | .terminated reason => final = .terminated reason

/-- Complete generic variable-length wrapper. Resolved accessor failures and
their states are preserved, including errors before any TLV vector exists. -/
def getNewLength (model : NewLength) (before : model.reader.State) (extension : model.NewReference)
    (final : Outcome model.reader.State (Except Error Nat) model.reader.Unwind
      model.reader.Terminal) :
    Prop :=
  ∃ accessed, model.reader.getTlvData before accessed ∧
    match accessed with
    | .returned reference after =>
      ∃ measured, model.getPackedLen after extension measured ∧
        match measured with
        | .returned (.ok length) afterMeasure => sizeFromTlv model afterMeasure reference length
          final
        | .returned (.error error) afterMeasure => final = .returned (.error error) afterMeasure
        | .unwound reason afterMeasure => final = .unwound reason afterMeasure
        | .terminated reason => final = .terminated reason
    | .unwound reason after => final = .unwound reason after
    | .terminated reason => final = .terminated reason

/-- A packed-length error occurs after the actual effects of the accessor and
before any TLV scan or local type-vector allocation. -/
theorem getNewLength_measure_error (model : NewLength) (before after middle : model.reader.State)
    (extension : model.NewReference) (reference : model.reader.Reference) (error : Error)
    (accessed : model.reader.getTlvData before (.returned reference after))
    (measured : model.getPackedLen after extension (.returned (.error error) middle)) :
    getNewLength model before extension (.returned (.error error) middle) :=
  ⟨.returned reference after, accessed, .returned (.error error) middle, measured, rfl⟩

/-- Failure to return from the first accessor cannot be replaced by an
unrelated packed-length computation or a fabricated account length. -/
theorem getNewLength_no_accessor_exit (model : NewLength) (before : model.reader.State)
    (extension : model.NewReference)
    (noExit : ∀ outcome, ¬ model.reader.getTlvData before outcome) :
    ∀ final, ¬ getNewLength model before extension final := by
  rintro final ⟨accessed, called, _⟩
  exact noExit accessed called

/-- The upper usize boundary saturates; no u16 length restriction is added by
this helper before a later extension writer checks representability. -/
theorem new_length_saturates :
    newLengthValue .tokenMetadata .mint 0 (2^64 - 1) [] = 2^64 - 1 := by
  simp [newLengthValue, oldExtensionLength, findExtension, addHeader,
    saturatingSizeAdd, adjustMultisigLength, accountLength, multisigLength,
    Solanalib.Runtime.U64_MAX]

end Solanalib.Specs.Core.Token.Legacy
