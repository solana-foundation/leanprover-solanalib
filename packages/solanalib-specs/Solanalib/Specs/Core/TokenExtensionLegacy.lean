/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionGetter
public import Solanalib.Specs.Core.TokenExtensionSize

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Legacy

/-- The production enum in token-2022 8.0.1 and interface 2.1.0 ends at
PausableAccount. PermissionedBurn and cfg(test)-only tags are not admitted. -/
def decodeType (tag : Nat) : Option ExtensionType :=
  if tag < 28 then ExtensionType.decode tag else none

/-- A source enum value at the older production type. The subtype expresses
representation, rather than adding a semantic precondition to a result. -/
abbrev Kind := {kind : ExtensionType // kind.tag < 28}

/-- Older default lookup validates every encountered tag and base association
before skipping its payload. A complete header is required even at a zero
sentinel. The ExtensionTypeMismatch error of the source is Custom(20). -/
def findExtension (wanted : ExtensionType) (offset : Nat) (bytes : Bytes) :
    Except Error ExtensionView :=
  match bytes with
  | low :: high :: lenLow :: lenHigh :: rest =>
    match decodeType (tlvU16 low high) with
    | none => .error .InvalidAccountData
    | some kind =>
      if kind = wanted then
        let length := tlvU16 lenLow lenHigh
        if length ≤ rest.length then .ok ⟨offset + 4, rest.take length⟩
        else .error .InvalidAccountData
      else if kind = .uninitialized then .error (.Custom 48)
      else if kind.accountType ≠ wanted.accountType then .error (.Custom 20)
      else findExtension wanted (offset + 4 + tlvU16 lenLow lenHigh)
        (rest.drop (tlvU16 lenLow lenHigh))
  | _ => .error .InvalidAccountData
termination_by bytes.length
decreasing_by simp_wf; omega

/-- The older free byte getter checks the requested base association first;
Pod size and pointer alignment belong to the subsequent typed cast. -/
def defaultExtensionBytes (receiver : ExtensionReceiver) (pod : ExtensionPod) :
    Except Error LocatedExtensionView :=
  if receiver.accountType = pod.kind.accountType then
    (findExtension pod.kind 0 receiver.bytes).map fun view => ⟨receiver.address, view⟩
  else .error .InvalidAccountData

/-- Observe the complete typed result using the same size-before-alignment
cast as the generic getter. The older traversal is the only changed provider. -/
def defaultByteProvider : ExtensionByteProvider where
  State := ExtensionReceiver
  Reference := LocatedExtensionView
  Unwind := Empty
  Terminal := Empty
  bytes := fun _ reference => reference.view.bytes
  address := fun reference => reference.baseAddress + reference.view.offset
  getBytes := fun pod before outcome =>
    outcome = .returned (defaultExtensionBytes before pod) before

/-- Total typed result at the concrete older default-method interpretation. -/
def getDefaultExtension (representation : ExtensionRepresentation) (before : ExtensionReceiver) :
    Except Error (TypedExtensionReference LocatedExtensionView representation.Value) :=
  (defaultExtensionBytes before representation.pod).bind
    (castExtensionReference defaultByteProvider representation before)

/-- The concrete default lookup and cast have exactly their computed result;
this is a reusable graph lemma for conformance, not a Rust-body proof. -/
theorem getDefaultExtension_iff (representation : ExtensionRepresentation) (before :
  ExtensionReceiver)
    (outcome : Outcome ExtensionReceiver
      (Except Error (TypedExtensionReference LocatedExtensionView representation.Value)) Empty
        Empty) :
    getExtensionOperational defaultByteProvider representation before outcome ↔
      outcome = .returned (getDefaultExtension representation before) before := by
  unfold getExtensionOperational
  constructor
  · rintro ⟨called, method, finished⟩
    change called = .returned (defaultExtensionBytes before representation.pod) before at method
    subst called
    cases found : defaultExtensionBytes before representation.pod <;>
      simpa [finishExtensionGetter, getDefaultExtension, defaultByteProvider, found, Except.bind]
        using finished
  · intro finished
    refine ⟨.returned (defaultExtensionBytes before representation.pod) before, rfl, ?_⟩
    cases found : defaultExtensionBytes before representation.pod <;>
      simpa [finishExtensionGetter, getDefaultExtension, defaultByteProvider, found, Except.bind]
        using finished

/-- Listing has a separate two-stage walk. Header validation happens before
push; payload-length validation happens after push in its returned state. -/
inductive Header where
  /-- Empty input, one realloc byte, or a two-byte zero sentinel. -/
  | done
  /-- Unknown tag or truncated nonzero header. -/
  | invalid
  /-- A known nonzero tag in a complete four-byte header. -/
  | entry (kind : ExtensionType)
  deriving DecidableEq, Repr

/-- Inspect only what the old source reads before its allocating Vec::push. -/
def header (bytes : Bytes) : Header :=
  match bytes with
  | [] | [_] => .done
  | low :: high :: rest =>
    match decodeType (tlvU16 low high) with
    | none => .invalid
    | some .uninitialized => .done
    | some kind => if 2 ≤ rest.length then .entry kind else .invalid

/-- The source reads these two length bytes after push. Successful header
inspection guarantees they exist in the fixed metadata length of the slice. -/
def payloadEnd (bytes : Bytes) (offset : Nat) : Nat :=
  offset + 4 + tlvU16 (bytes[offset + 2]?.getD 0) (bytes[offset + 3]?.getD 0)

/-- Every payload step advances, even when a provider changes length bytes. -/
theorem payloadEnd_progress (bytes : Bytes) (offset : Nat) : offset < payloadEnd bytes offset := by
  unfold payloadEnd
  omega

/-- Header inspection cannot allow missing length bytes. -/
theorem header_entry_width {bytes : Bytes} {kind : ExtensionType}
    (entry : header bytes = .entry kind) : 4 ≤ bytes.length := by
  cases bytes with
  | nil => cases entry
  | cons low tail =>
    cases tail with
    | nil => cases entry
    | cons high rest =>
      dsimp only [header] at entry
      split at entry
      · contradiction
      · contradiction
      · split at entry
        · simp_all
        · contradiction

/-- A value observation of the old listing walk. Allocation and failure
timing are expressed by the separate operational family, not erased here. -/
def scanInfo (types : List ExtensionType) (offset : Nat) (bytes : Bytes) :
    Except Error (List ExtensionType × Nat) :=
  match bytes with
  | [] | [_] => .ok (types, offset)
  | low :: high :: rest =>
    match decodeType (tlvU16 low high) with
    | none => .error .InvalidAccountData
    | some .uninitialized => .ok (types, offset)
    | some kind =>
      match rest with
      | lenLow :: lenHigh :: value =>
        let next := types ++ [kind]
        let length := tlvU16 lenLow lenHigh
        if length ≤ value.length then
          scanInfo next (offset + 4 + length) (value.drop length)
        else .error .InvalidAccountData
      | _ => .error .InvalidAccountData
termination_by bytes.length
decreasing_by simp_wf; omega

/-- Final ordered type-list observation, preserving duplicate tags. -/
def getExtensionTypes (bytes : Bytes) : Except Error (List ExtensionType) :=
  (scanInfo [] 0 bytes).map Prod.fst

/-- The old default lookup rejects an unknown skipped tag; the current
raw-tag walker would continue to the matching entry after it. -/
theorem unknown_tag_rejected :
    findExtension .transferFeeAmount 0 [255, 255, 0, 0, 2, 0, 8, 0] =
      .error .InvalidAccountData := by
  rw [findExtension]
  rfl

/-- An encountered mint extension blocks an account-extension lookup before
the declared length of that encountered value is examined. -/
theorem wrong_association_precedes_length :
    findExtension .transferFeeAmount 0 [1, 0, 255, 255] = .error (.Custom 20) := by
  rw [findExtension]
  rfl

/-- A two-byte zero sentinel is valid for listing, but not for byte lookup. -/
theorem sentinel_header_boundary :
    getExtensionTypes [0, 0] = .ok [] ∧
      findExtension .transferFeeAmount 0 [0, 0] = .error .InvalidAccountData := by
  constructor
  · rw [getExtensionTypes, scanInfo]
    rfl
  · simp [findExtension]

end Solanalib.Specs.Core.Token.Legacy
