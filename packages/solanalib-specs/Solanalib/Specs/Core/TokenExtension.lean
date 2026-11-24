/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Token

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- A 64-bit Rust slice has at most isize::MAX bytes. This strict upper bound
excludes impossible near-usize::MAX slices when relating the natural-number
TLV traversal to source saturating pointer-index arithmetic. -/
def extensionSliceLimit : Nat := 2^63

/-- The extensible account marker, distinct from the token account state byte. -/
inductive ExtensionAccountType where
  /-- Zero marks an uninitialized extended base. -/
  | uninitialized
  /-- A mint base. -/
  | mint
  /-- A token-holding account base. -/
  | account
  deriving DecidableEq, Repr

/-- The three wire discriminants at the account-type byte. -/
def ExtensionAccountType.tag : ExtensionAccountType → UInt8
  | .uninitialized => 0
  | .mint => 1
  | .account => 2

/-- The production extension discriminants in token-2022 interface 3.1.1.
The cfg(test)-only variants of the Rust crate are deliberately absent. -/
inductive ExtensionType where
  /-- The zero TLV sentinel. -/
  | uninitialized
  /-- Transfer-fee configuration on a mint. -/
  | transferFeeConfig
  /-- Withheld transfer fees on an account. -/
  | transferFeeAmount
  /-- Optional mint-close authority. -/
  | mintCloseAuthority
  /-- Confidential-transfer mint configuration. -/
  | confidentialTransferMint
  /-- Confidential-transfer account state. -/
  | confidentialTransferAccount
  /-- Default state for newly initialized accounts. -/
  | defaultAccountState
  /-- Immutable token-account owner. -/
  | immutableOwner
  /-- Incoming-transfer memo requirement. -/
  | memoTransfer
  /-- Nontransferable mint marker. -/
  | nonTransferable
  /-- Mint interest configuration. -/
  | interestBearingConfig
  /-- Account CPI restriction flag. -/
  | cpiGuard
  /-- Optional permanent mint delegate. -/
  | permanentDelegate
  /-- Account marker for a nontransferable mint. -/
  | nonTransferableAccount
  /-- Mint transfer-hook configuration. -/
  | transferHook
  /-- Transfer-hook account execution flag. -/
  | transferHookAccount
  /-- Confidential transfer-fee mint configuration. -/
  | confidentialTransferFeeConfig
  /-- Confidential withheld fees on an account. -/
  | confidentialTransferFeeAmount
  /-- Mint metadata pointer. -/
  | metadataPointer
  /-- Variable-length token metadata. -/
  | tokenMetadata
  /-- Mint token-group pointer. -/
  | groupPointer
  /-- Token-group data on a mint. -/
  | tokenGroup
  /-- Mint token-group member pointer. -/
  | groupMemberPointer
  /-- Token-group member data on a mint. -/
  | tokenGroupMember
  /-- Confidential minting and burning state. -/
  | confidentialMintBurn
  /-- Mint UI-amount scaling configuration. -/
  | scaledUiAmount
  /-- Mint pause authority and state. -/
  | pausable
  /-- Account marker for a pausable mint. -/
  | pausableAccount
  /-- Mint permissioned-burn authority. -/
  | permissionedBurn
  deriving DecidableEq, Repr

/-- The stable two-byte tag for each supported production extension. -/
def ExtensionType.tag : ExtensionType → Nat
  | .uninitialized => 0
  | .transferFeeConfig => 1
  | .transferFeeAmount => 2
  | .mintCloseAuthority => 3
  | .confidentialTransferMint => 4
  | .confidentialTransferAccount => 5
  | .defaultAccountState => 6
  | .immutableOwner => 7
  | .memoTransfer => 8
  | .nonTransferable => 9
  | .interestBearingConfig => 10
  | .cpiGuard => 11
  | .permanentDelegate => 12
  | .nonTransferableAccount => 13
  | .transferHook => 14
  | .transferHookAccount => 15
  | .confidentialTransferFeeConfig => 16
  | .confidentialTransferFeeAmount => 17
  | .metadataPointer => 18
  | .tokenMetadata => 19
  | .groupPointer => 20
  | .tokenGroup => 21
  | .groupMemberPointer => 22
  | .tokenGroupMember => 23
  | .confidentialMintBurn => 24
  | .scaledUiAmount => 25
  | .pausable => 26
  | .pausableAccount => 27
  | .permissionedBurn => 28

/-- Checked production enum conversion. This differs from the raw-tag
comparison of the lookup, which may skip an unknown tag. -/
def ExtensionType.decode : Nat → Option ExtensionType
  | 0 => some .uninitialized
  | 1 => some .transferFeeConfig
  | 2 => some .transferFeeAmount
  | 3 => some .mintCloseAuthority
  | 4 => some .confidentialTransferMint
  | 5 => some .confidentialTransferAccount
  | 6 => some .defaultAccountState
  | 7 => some .immutableOwner
  | 8 => some .memoTransfer
  | 9 => some .nonTransferable
  | 10 => some .interestBearingConfig
  | 11 => some .cpiGuard
  | 12 => some .permanentDelegate
  | 13 => some .nonTransferableAccount
  | 14 => some .transferHook
  | 15 => some .transferHookAccount
  | 16 => some .confidentialTransferFeeConfig
  | 17 => some .confidentialTransferFeeAmount
  | 18 => some .metadataPointer
  | 19 => some .tokenMetadata
  | 20 => some .groupPointer
  | 21 => some .tokenGroup
  | 22 => some .groupMemberPointer
  | 23 => some .tokenGroupMember
  | 24 => some .confidentialMintBurn
  | 25 => some .scaledUiAmount
  | 26 => some .pausable
  | 27 => some .pausableAccount
  | 28 => some .permissionedBurn
  | _ => none

/-- Enum encoding and decoding agree for every production variant. -/
theorem ExtensionType.decode_tag (kind : ExtensionType) :
    decode kind.tag = some kind := by cases kind <;> rfl

/-- The base-account association checked before looking up an extension. -/
def ExtensionType.accountType : ExtensionType → ExtensionAccountType
  | .uninitialized => .uninitialized
  | .transferFeeAmount | .confidentialTransferAccount | .immutableOwner
    | .memoTransfer | .cpiGuard | .nonTransferableAccount | .transferHookAccount
    | .confidentialTransferFeeAmount | .pausableAccount => .account
  | _ => .mint

/-- Packed fixed lengths, including all production account extensions.
All listed fields have alignment one; token metadata is variable length.
These are byte-layout facts, not validation of extension contents. -/
def ExtensionType.fixedLength : ExtensionType → Except Error Nat
  | .uninitialized => .ok 0
  | .transferFeeConfig => .ok 108
  | .transferFeeAmount => .ok 8
  | .mintCloseAuthority => .ok 32
  | .confidentialTransferMint => .ok 65
  | .confidentialTransferAccount => .ok 295
  | .defaultAccountState => .ok 1
  | .immutableOwner => .ok 0
  | .memoTransfer => .ok 1
  | .nonTransferable => .ok 0
  | .interestBearingConfig => .ok 52
  | .cpiGuard => .ok 1
  | .permanentDelegate => .ok 32
  | .nonTransferableAccount => .ok 0
  | .transferHook => .ok 64
  | .transferHookAccount => .ok 1
  | .confidentialTransferFeeConfig => .ok 129
  | .confidentialTransferFeeAmount => .ok 64
  | .metadataPointer => .ok 64
  | .tokenMetadata => .error .InvalidArgument
  | .groupPointer => .ok 64
  | .tokenGroup => .ok 80
  | .groupMemberPointer => .ok 64
  | .tokenGroupMember => .ok 72
  | .confidentialMintBurn => .ok 196
  | .scaledUiAmount => .ok 56
  | .pausable => .ok 33
  | .pausableAccount => .ok 0
  | .permissionedBurn => .ok 32

/-- Required token-account extensions, in the order of the source. Merely seeing an
account extension inside a mint TLV contributes no additional requirement. -/
def ExtensionType.requiredAccountExtensions : ExtensionType → List ExtensionType
  | .transferFeeConfig => [.transferFeeAmount]
  | .nonTransferable => [.nonTransferableAccount, .immutableOwner]
  | .transferHook => [.transferHookAccount]
  | .pausable => [.pausableAccount]
  | _ => []

/-- A selected byte range within the supplied TLV slice. The offset is retained
so a source binding can account for the returned reference and alignment. -/
structure ExtensionView where
  /-- Byte offset from the start of the supplied TLV slice. -/
  offset : Nat
  /-- The exact selected value bytes, without its four-byte header. -/
  bytes : Bytes
  deriving DecidableEq, Repr

/-- Decode the two bytes of a TLV tag or length without padding a short header. -/
def tlvU16 (low high : UInt8) : Nat := low.toNat + 256 * high.toNat

/-- A two-byte TLV length is bounded by the full unsigned 16-bit range. -/
theorem tlvU16_le (low high : UInt8) : tlvU16 low high ≤ 65535 := by
  have lowBound := low.toNat_lt
  have highBound := high.toNat_lt
  unfold tlvU16
  omega

/-- On any representable Rust slice, adding a complete TLV header and its
largest possible declared length cannot saturate the 64-bit source index. -/
theorem extensionTlvIndexFits (offset : Nat) (low high : UInt8)
    (bounded : offset < extensionSliceLimit) :
    offset + 4 + tlvU16 low high < Solanalib.Runtime.U64_LIMIT := by
  have lengthBound := tlvU16_le low high
  have gap : extensionSliceLimit + 4 + 65535 < Solanalib.Runtime.U64_LIMIT := by decide
  omega

/-- The raw-tag lookup walk. It requires a complete four-byte header before
examining a tag, returns the first match, skips unknown tags, and stops at zero.
A skipped length past the end causes the next iteration to fail. -/
def findExtension (wanted : Nat) (offset : Nat) (bytes : Bytes) :
    Except Error ExtensionView :=
  match bytes with
  | low :: high :: lenLow :: lenHigh :: rest =>
    let tag := tlvU16 low high
    let length := tlvU16 lenLow lenHigh
    if tag = wanted then
      if length ≤ rest.length then .ok ⟨offset + 4, rest.take length⟩
      else .error .InvalidAccountData
    else if tag = 0 then .error (.Custom 48)
    else findExtension wanted (offset + 4 + length) (rest.drop length)
  | _ => .error .InvalidAccountData
termination_by bytes.length
decreasing_by simp_wf; omega

/-- Iterate over initialized extension types. It accepts a single realloc byte,
stops at a two-byte zero sentinel, rejects unknown types and out-of-bounds values,
and invokes the supplied step before examining the next header. -/
def foldExtensionTypes {State : Type} (step : State → ExtensionType → Except Error State)
    (state : State) (offset : Nat) (bytes : Bytes) : Except Error (State × Nat) :=
  match bytes with
  | [] | [_] => .ok (state, offset)
  | low :: high :: rest =>
    match ExtensionType.decode (tlvU16 low high) with
    | none => .error .InvalidAccountData
    | some .uninitialized => .ok (state, offset)
    | some kind =>
      match rest with
      | lenLow :: lenHigh :: value =>
        let length := tlvU16 lenLow lenHigh
        if length ≤ value.length then do
          let next ← step state kind
          foldExtensionTypes step next (offset + 4 + length) (value.drop length)
        else .error .InvalidAccountData
      | _ => .error .InvalidAccountData
termination_by bytes.length
decreasing_by simp_wf; omega

/-- The ordered list of TLV types, preserving duplicates. No validation of the official fixed size
or base-account association of the
payload is added. -/
def getExtensionTypes (bytes : Bytes) : Except Error (List ExtensionType) :=
  (foldExtensionTypes (fun types kind => .ok (types ++ [kind])) [] 0 bytes).map Prod.fst

/-- A source `V: Extension + Pod` supplies its exact tag, size and alignment.
The descriptor is not proof that a Rust type has those properties. -/
structure ExtensionPod where
  /-- The source V::TYPE discriminant. -/
  kind : ExtensionType
  /-- The source size_of::<V>(). -/
  byteLength : Nat
  /-- The source align_of::<V>(). -/
  alignment : Nat
  deriving DecidableEq, Repr

/-- Lookup followed by the size and alignment checks of bytemuck. The runtime owner
is not checked by this source method and is not silently added as a condition. -/
def getExtension (baseType : ExtensionAccountType) (pod : ExtensionPod)
    (tlvAddress : Nat) (bytes : Bytes) : Except Error ExtensionView :=
  if pod.kind.accountType ≠ baseType then .error .InvalidAccountData
  else
    match findExtension pod.kind.tag 0 bytes with
    | .error error => .error error
    | .ok view =>
      if view.bytes.length = pod.byteLength ∧ (tlvAddress + view.offset) % pod.alignment = 0 then
        .ok view
      else .error .InvalidArgument

/-- A wrong base association is rejected before any TLV lookup. -/
theorem getExtension_wrong_base (baseType : ExtensionAccountType) (pod : ExtensionPod)
    (tlvAddress : Nat) (bytes : Bytes) (wrong : pod.kind.accountType ≠ baseType) :
    getExtension baseType pod tlvAddress bytes = .error .InvalidAccountData := by
  simp [getExtension, wrong]

/-- Successful Pod observations preserve the first selected bytes of the lookup,
their exact size, and the alignment of the resulting reference. -/
theorem getExtension_ok_iff (baseType : ExtensionAccountType) (pod : ExtensionPod)
    (tlvAddress : Nat) (bytes : Bytes) (view : ExtensionView) :
    getExtension baseType pod tlvAddress bytes = .ok view ↔
      pod.kind.accountType = baseType ∧
      findExtension pod.kind.tag 0 bytes = .ok view ∧
      view.bytes.length = pod.byteLength ∧ (tlvAddress + view.offset) % pod.alignment = 0 := by
  by_cases matching : pod.kind.accountType = baseType
  · simp only [getExtension, matching, ne_eq, not_true_eq_false, ↓reduceIte, true_and]
    cases found : findExtension pod.kind.tag 0 bytes with
    | error error => simp
    | ok selected =>
      dsimp only
      by_cases layout : selected.bytes.length = pod.byteLength ∧
          (tlvAddress + selected.offset) % pod.alignment = 0
      · rw [ite_eq_left layout]
        simp only [Except.ok.injEq]
        constructor
        · intro equality
          subst view
          exact ⟨rfl, layout⟩
        · exact fun correct => correct.1
      · rw [ite_eq_right layout]
        constructor
        · intro impossible
          cases impossible
        · intro ⟨equality, length, align⟩
          cases equality
          exact False.elim (layout ⟨length, align⟩)
  · simp [getExtension, matching]

/-- A zero sentinel stops the type walk before its callback or trailing bytes. -/
theorem foldExtensionTypes_sentinel {State : Type}
    (step : State → ExtensionType → Except Error State) (state : State)
    (offset : Nat) (tail : Bytes) :
    foldExtensionTypes step state offset (0 :: 0 :: tail) = .ok (state, offset) := by
  rw [foldExtensionTypes]
  rfl

/-- Type listing accepts an empty slice. -/
theorem getExtensionTypes_empty : getExtensionTypes [] = .ok [] := by
  rw [getExtensionTypes, foldExtensionTypes]
  rfl

/-- A logical observation of a source Pod type. `observe` interprets bytes; it
is not an additional Rust callback. The source binding must connect it to the representation of V,
in addition to identifying the exact tag, size and alignment of V. -/
structure ExtensionRepresentation where
  /-- Logical values used to observe the selected source V. -/
  Value : Type
  /-- the exact Pod layout and extension tag of V. -/
  pod : ExtensionPod
  /-- The bound interpretation of its bytes, applied after layout checks. -/
  observe : Bytes → Value

/-- A typed observation retains the selected raw bytes and their original
offset, rather than erasing which region the returned reference denotes. -/
structure ExtensionReference (Value : Type) where
  /-- The selected raw region and source-relative offset. -/
  view : ExtensionView
  /-- The logical observation of precisely that region. -/
  value : Value
  deriving DecidableEq, Repr

/-- Interpret only the bytes that passed lookup and Pod layout checks. -/
def getRepresentedExtension (representation : ExtensionRepresentation)
    (baseType : ExtensionAccountType) (tlvAddress : Nat) (bytes : Bytes) :
    Except Error (ExtensionReference representation.Value) :=
  (getExtension baseType representation.pod tlvAddress bytes).map fun view =>
    ⟨view, representation.observe view.bytes⟩

/-- The typed result retains the exact selected byte range of the underlying
lookup; choosing a logical observation cannot bypass its validation. -/
theorem getRepresentedExtension_raw (representation : ExtensionRepresentation)
    (baseType : ExtensionAccountType) (tlvAddress : Nat) (bytes : Bytes) :
    (getRepresentedExtension representation baseType tlvAddress bytes).map
      ExtensionReference.view = getExtension baseType representation.pod tlvAddress bytes := by
  cases selected : getExtension baseType representation.pod tlvAddress bytes <;>
    simp [getRepresentedExtension, selected, Except.map]

end Solanalib.Specs.Core.Token
