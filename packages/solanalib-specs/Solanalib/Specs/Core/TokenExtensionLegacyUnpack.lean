/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionUnpack
public import Solanalib.Specs.Core.OwnedVector

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Legacy

open Owned

/-- Older unpacking compares padding against a temporary zero-filled Vec.
The base parser and destructor retain their original generic interpretations. -/
structure Unpacker where
  /-- Exact base type, source slice and parse/drop dependencies. -/
  base : ExtensionUnpacker
  /-- Identity of the temporary owned byte vector. -/
  Resource : Type
  /-- Actual zero-vector construction, contents and destruction. -/
  bytes : VectorOps base.State UInt8 Resource base.Unwind base.Terminal
  /-- A second destructor unwind has only its supplied terminal behavior. -/
  doubleUnwind : DoubleUnwind base.State base.Unwind base.Terminal

/-- Version 8.0.1 requires at least one TLV byte after the marker. Interface
2.1.0 and 3.0.1 allow a marker followed by an empty TLV slice. -/
def tailTooShort (requiresTlvByte : Bool) (padding restLength : Nat) : Prop :=
  if requiresTlvByte then restLength ≤ padding + 1 else restLength < padding + 1

instance (requiresTlvByte : Bool) (padding restLength : Nat) :
    Decidable (tailTooShort requiresTlvByte padding restLength) := by
  unfold tailTooShort
  infer_instance

/-- Allocate the exact zero sequence of the source, compare in the actual returned
state, and destroy that temporary before the caller checks the account marker.
The current vector observation is used; a provider law identifies it as zeros. -/
def paddingMatches (unpacker : Unpacker) (before : unpacker.base.State)
    (input : unpacker.base.Reference)
    (final : Outcome unpacker.base.State Bool unpacker.base.Unwind unpacker.base.Terminal) : Prop :=
  let padding := accountLength - unpacker.base.baseLength
  Callback.bind unpacker.bytes.fromList (fun resource after outcome =>
    ∃ zeros, unpacker.bytes.current after resource = some zeros ∧
      cleanup unpacker.doubleUnwind [unpacker.bytes.dropAction resource]
        (.returned (((unpacker.base.inputBytes after input).drop unpacker.base.baseLength).take
          padding == zeros) after) outcome)
    before (List.replicate padding 0) final

/-- The exact construction-content law of a source binding eliminates the current
observation gate at each actual returned allocation. It neither supplies an
allocation outcome nor frames the input across allocation or destruction. -/
theorem paddingMatches_of_current_law (unpacker : Unpacker)
    (before : unpacker.base.State) (input : unpacker.base.Reference)
    (contents : ∀ resource after,
      unpacker.bytes.fromList before
        (List.replicate (accountLength - unpacker.base.baseLength) 0)
          (.returned resource after) →
      unpacker.bytes.current after resource =
        some (List.replicate (accountLength - unpacker.base.baseLength) 0))
    (final : Outcome unpacker.base.State Bool unpacker.base.Unwind unpacker.base.Terminal) :
    paddingMatches unpacker before input final ↔
      ∃ allocated, unpacker.bytes.fromList before
          (List.replicate (accountLength - unpacker.base.baseLength) 0) allocated ∧
        match allocated with
        | .returned resource after =>
          cleanup unpacker.doubleUnwind [unpacker.bytes.dropAction resource]
            (.returned (((unpacker.base.inputBytes after input).drop unpacker.base.baseLength).take
              (accountLength - unpacker.base.baseLength) ==
                List.replicate (accountLength - unpacker.base.baseLength) 0) after) final
        | .unwound reason after => final = .unwound reason after
        | .terminated reason => final = .terminated reason := by
  constructor
  · rintro ⟨allocated, called, continued⟩
    refine ⟨allocated, called, ?_⟩
    cases allocated with
    | returned resource after =>
      obtain ⟨zeros, current, cleaned⟩ := continued
      have same := Option.some.inj (current.symm.trans (contents resource after called))
      subst zeros
      exact cleaned
    | unwound reason after => exact continued
    | terminated reason => exact continued
  · rintro ⟨allocated, called, continued⟩
    refine ⟨allocated, called, ?_⟩
    cases allocated with
    | returned resource after =>
      exact ⟨_, contents resource after called, continued⟩
    | unwound reason after => exact continued
    | terminated reason => exact continued

/-- The marker check occurs after the temporary comparison vector is dropped.
Its successful reference preserves the same input identity and exact tail. -/
def markedTail (unpacker : Unpacker) (after : unpacker.base.State)
    (input : unpacker.base.Reference) (paddingMatches : Bool) :
    Except Error (ExtensionTailReference unpacker.base.Reference) :=
  let padding := accountLength - unpacker.base.baseLength
  let markerOffset := unpacker.base.baseLength + padding
  if paddingMatches ∧ (unpacker.base.inputBytes after input)[markerOffset]? =
      some unpacker.base.accountType.tag then
    .ok (.borrowed ⟨input, markerOffset + 1, unpacker.base.length input - (markerOffset + 1)⟩)
  else .error .InvalidAccountData

/-- Complete old tail processing. A bare base returns the static empty slice;
the early length rejection precedes construction of the padding vector. -/
def unpackTail (requiresTlvByte : Bool) (unpacker : Unpacker)
    (before : unpacker.base.State) (input : unpacker.base.Reference)
    (final : Outcome unpacker.base.State (Except Error (ExtensionTailReference
      unpacker.base.Reference))
      unpacker.base.Unwind unpacker.base.Terminal) : Prop :=
  let restLength := unpacker.base.length input - unpacker.base.baseLength
  if restLength = 0 then final = .returned (.ok .empty) before
  else if tailTooShort requiresTlvByte (accountLength - unpacker.base.baseLength) restLength then
    final = .returned (.error .InvalidAccountData) before
  else Callback.map (fun pair : Bool × unpacker.base.State =>
      markedTail unpacker pair.2 input pair.1)
      (fun state (_ : Unit) result =>
        ∃ compared, paddingMatches unpacker state input compared ∧
          result = match compared with
            | .returned same after => .returned (same, after) after
            | .unwound reason after => .unwound reason after
            | .terminated reason => .terminated reason)
      before () final

/-- A parsed base is moved only after a successful tail. Every ordinary tail
error and unwind drops the same base, after any temporary-vector cleanup. -/
def finishUnpack (requiresTlvByte : Bool) (unpacker : Unpacker)
    (input : unpacker.base.Reference)
    (parsed : Outcome unpacker.base.State (Except Error unpacker.base.Base)
      unpacker.base.Unwind unpacker.base.Terminal)
    (final : Outcome unpacker.base.State
      (Except Error (ExtensionUnpacked unpacker.base.Base unpacker.base.Reference))
      unpacker.base.Unwind unpacker.base.Terminal) : Prop :=
  match parsed with
  | .returned (.error error) after => final = .returned (.error error) after
  | .returned (.ok base) after =>
    ∃ tailed, unpackTail requiresTlvByte unpacker after input tailed ∧
      let pending := Outcome.map (Except.map (fun tlv => (⟨base, tlv⟩ :
        ExtensionUnpacked unpacker.base.Base unpacker.base.Reference))) tailed
      match tailed with
      | .returned (.ok _) _ => final = pending
      | .returned (.error _) _ | .unwound _ _ | .terminated _ =>
        cleanup unpacker.doubleUnwind [fun state => unpacker.base.dropBase state base] pending final
  | .unwound reason after => final = .unwound reason after
  | .terminated reason => final = .terminated reason

/-- The full version-sensitive unpack relation, including allocation,
temporary/base cleanup and exact source-reference identity. -/
def unpack (requiresTlvByte : Bool) (unpacker : Unpacker) (before : unpacker.base.State)
    (input : unpacker.base.Reference)
    (final : Outcome unpacker.base.State
      (Except Error (ExtensionUnpacked unpacker.base.Base unpacker.base.Reference))
      unpacker.base.Unwind unpacker.base.Terminal) : Prop :=
  if unpacker.base.length input = multisigLength ∨
      unpacker.base.length input < unpacker.base.baseLength then
    final = .returned (.error .InvalidAccountData) before
  else ∃ parsed, unpacker.base.parse before ⟨input, 0, unpacker.base.baseLength⟩ parsed ∧
    finishUnpack requiresTlvByte unpacker input parsed final

/-- A returning temporary construction/observation/drop supplies the exact
padding result. Its state is the state after the temporary was destroyed. -/
theorem paddingMatches_returned (unpacker : Unpacker)
    (before allocated after : unpacker.base.State) (input : unpacker.base.Reference)
    (resource : unpacker.Resource) (zeros : Bytes)
    (created : unpacker.bytes.fromList before
      (List.replicate (accountLength - unpacker.base.baseLength) 0) (.returned resource allocated))
    (current : unpacker.bytes.current allocated resource = some zeros)
    (dropped : unpacker.bytes.drop allocated resource (.returned () after)) :
    paddingMatches unpacker before input
      (.returned (((unpacker.base.inputBytes allocated input).drop unpacker.base.baseLength).take
        (accountLength - unpacker.base.baseLength) == zeros) after) := by
  refine ⟨.returned resource allocated, created, zeros, current, .returned () after, dropped, ?_⟩
  rfl

/-- A returned padding comparison is followed by the marker read in its
actual post-drop state. -/
theorem unpackTail_compared (requiresTlvByte : Bool) (unpacker : Unpacker)
    (before after : unpacker.base.State) (input : unpacker.base.Reference) (same : Bool)
    (extended : unpacker.base.length input - unpacker.base.baseLength ≠ 0)
    (enough : ¬ tailTooShort requiresTlvByte (accountLength - unpacker.base.baseLength)
      (unpacker.base.length input - unpacker.base.baseLength))
    (compared : paddingMatches unpacker before input (.returned same after)) :
    unpackTail requiresTlvByte unpacker before input
      (.returned (markedTail unpacker after input same) after) := by
  simp only [unpackTail, extended, enough, ↓reduceIte]
  exact ⟨.returned (same, after) after, ⟨.returned same after, compared, rfl⟩, rfl⟩

/-- A successful actual parse and actual tail execution move the base and
tail reference together without invoking the base destructor. -/
theorem unpack_success (requiresTlvByte : Bool) (unpacker : Unpacker)
    (before parsedState after : unpacker.base.State) (input : unpacker.base.Reference)
    (base : unpacker.base.Base) (tail : ExtensionTailReference unpacker.base.Reference)
    (admitted : ¬ (unpacker.base.length input = multisigLength ∨
      unpacker.base.length input < unpacker.base.baseLength))
    (parsed : unpacker.base.parse before ⟨input, 0, unpacker.base.baseLength⟩
      (.returned (.ok base) parsedState))
    (tailed : unpackTail requiresTlvByte unpacker parsedState input (.returned (.ok tail) after)) :
    unpack requiresTlvByte unpacker before input (.returned (.ok ⟨base, tail⟩) after) := by
  simp only [unpack, admitted, ↓reduceIte]
  exact ⟨.returned (.ok base) parsedState, parsed, .returned (.ok tail) after, tailed, rfl⟩

/-- The exact allocation-independent observation for normal constant-byte
providers, used by native conformance in addition to the operational tests. -/
def tailValue (requiresTlvByte : Bool) (baseLength : Nat)
    (accountType : ExtensionAccountType) (rest : Bytes) : Except Error Bytes :=
  if rest.isEmpty then .ok []
  else if tailTooShort requiresTlvByte (accountLength - baseLength) rest.length then
    .error .InvalidAccountData
  else if rest.take (accountLength - baseLength) != List.replicate (accountLength - baseLength) 0
    then
    .error .InvalidAccountData
  else if rest[accountLength - baseLength]? = some accountType.tag then
    .ok (rest.drop (accountLength - baseLength + 1))
  else .error .InvalidAccountData

/-- Pure normal-value observation with the actual base codec and check order. -/
def unpackValue {Base : Type} (requiresTlvByte : Bool) (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Error Base) (bytes : Bytes) :
    Except Error (StateWithExtensions Base) :=
  if extensionInputRejected baseLength bytes then .error .InvalidAccountData
  else (decode (bytes.take baseLength)).bind fun base =>
    (tailValue requiresTlvByte baseLength accountType (bytes.drop baseLength)).map fun tlv =>
      ⟨base, tlv⟩

/-- The exact boundary difference is retained without assuming a successful
allocation or conflating it with the modern no-allocation implementation. -/
theorem empty_tlv_boundary :
    tailValue true accountLength .account [2] = .error .InvalidAccountData ∧
      tailValue false accountLength .account [2] = .ok [] := by
  exact ⟨rfl, rfl⟩

/-- An early rejected source length calls no parser and allocates no padding. -/
theorem unpack_bad_length (requiresTlvByte : Bool) (unpacker : Unpacker)
    (before : unpacker.base.State) (input : unpacker.base.Reference)
    (rejected : unpacker.base.length input = multisigLength ∨
      unpacker.base.length input < unpacker.base.baseLength) :
    unpack requiresTlvByte unpacker before input (.returned (.error .InvalidAccountData) before) :=
      by
  simp [unpack, rejected]

/-- Absence of a parser execution cannot be hidden by a tail result. -/
theorem unpack_no_parser_exit (requiresTlvByte : Bool) (unpacker : Unpacker)
    (before : unpacker.base.State) (input : unpacker.base.Reference)
    (admitted : ¬ (unpacker.base.length input = multisigLength ∨
      unpacker.base.length input < unpacker.base.baseLength))
    (noExit : ∀ outcome, ¬ unpacker.base.parse before ⟨input, 0, unpacker.base.baseLength⟩ outcome)
      :
    ∀ final, ¬ unpack requiresTlvByte unpacker before input final := by
  intro final run
  simp only [unpack, admitted, ↓reduceIte] at run
  obtain ⟨outcome, called, _⟩ := run
  exact noExit outcome called

end Solanalib.Specs.Core.Token.Legacy
