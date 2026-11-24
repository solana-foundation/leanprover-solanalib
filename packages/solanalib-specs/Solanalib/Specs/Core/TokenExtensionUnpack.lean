/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionState
public import Solanalib.Specs.Core.TokenExtensionListCurrent

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- A subrange of the same logical source slice. The reference is preserved
across parser effects; a Rust binding supplies the corresponding permissions. -/
structure ExtensionRegion (Reference : Type) where
  /-- Identity of the complete source input slice. -/
  origin : Reference
  /-- Offset relative to the start of that input. -/
  offset : Nat
  /-- Length of this subrange. -/
  length : Nat
  deriving DecidableEq, Repr

/-- The source returns either its static empty slice or a subrange of the
original input. The empty literal is distinguished from an empty input subrange. -/
inductive ExtensionTailReference (Reference : Type) where
  /-- The `&[]` literal returned for an unextended base. -/
  | empty
  /-- The range of the original input after padding and the account marker. -/
  | borrowed (region : ExtensionRegion Reference)
  deriving DecidableEq, Repr

/-- The returned owned base and the retained source TLV reference. -/
structure ExtensionUnpacked (Base Reference : Type) where
  /-- The same owned value returned by the base parser. -/
  base : Base
  /-- The unparsed tail reference of the source. -/
  tlv : ExtensionTailReference Reference
  deriving DecidableEq, Repr

/-- Dependencies for fully generic StateWithExtensions::unpack. Neither
BaseState nor Pack excludes a destructor. A successful base therefore remains
owned until it is moved to the result or dropped on a later layout error.
Source bytes are read through their original identity in actual current states. -/
structure ExtensionUnpacker where
  /-- Actual interpretation state. -/
  State : Type
  /-- Identity of an input source slice, including fixed length metadata. -/
  Reference : Type
  /-- Interpretation of the owned parsed S value, including any resource tokens. -/
  Base : Type
  /-- Dependency unwind reasons. -/
  Unwind : Type
  /-- Dependency terminal reasons. -/
  Terminal : Type
  /-- Fixed length metadata for each input reference. -/
  length : Reference → Nat
  /-- Read one byte through the original input identity in the actual state. -/
  byteAt : (state : State) → (reference : Reference) → Fin (length reference) → UInt8
  /-- Exact source S::SIZE_OF constant. -/
  baseLength : Nat
  /-- Exact source S::ACCOUNT_TYPE constant. -/
  accountType : ExtensionAccountType
  /-- Actual resolved S::unpack call on the checked source prefix. -/
  parse : State → ExtensionRegion Reference →
    Outcome State (Except Error Base) Unwind Terminal → Prop
  /-- Actual destructor for the owned value returned by that parser. -/
  dropBase : State → Base → Outcome State Unit Unwind Terminal → Prop

/-- Observe the same input slice in an actual current state. -/
def ExtensionUnpacker.inputBytes (unpacker : ExtensionUnpacker) (state : unpacker.State)
    (input : unpacker.Reference) : Bytes :=
  currentExtensionBytes (unpacker.length input) (fun state => unpacker.byteAt state input) state

/-- The live input view keeps its original metadata length. -/
theorem ExtensionUnpacker.inputBytes_length (unpacker : ExtensionUnpacker)
    (state : unpacker.State) (input : unpacker.Reference) :
    (unpacker.inputBytes state input).length = unpacker.length input :=
  currentExtensionBytes_length _ _ _

/-- Check the current layout and retain the exact input range. A bare base
returns the empty literal in the source; extended input retains origin and offset. -/
def unpackExtensionTailReference (unpacker : ExtensionUnpacker) (state : unpacker.State)
    (input : unpacker.Reference) : Except Error (ExtensionTailReference unpacker.Reference) :=
  let rest := (unpacker.inputBytes state input).drop unpacker.baseLength
  (unpackExtensionTail unpacker.baseLength unpacker.accountType rest).map fun tlv =>
    if rest.isEmpty then .empty
    else .borrowed ⟨input, unpacker.baseLength + (accountLength - unpacker.baseLength) + 1,
      tlv.length⟩

/-- Propagate the actual finite outcome of a destructor while retaining the pending
ordinary layout error only on a normal return. There is exactly one owned base
to drop, so a first destructor unwind has no second local destructor to run. -/
def finishExtensionBaseDrop (error : Error)
    {State Base Reference Unwind Terminal : Type} :
    Outcome State Unit Unwind Terminal →
      Outcome State (Except Error (ExtensionUnpacked Base Reference)) Unwind Terminal
  | .returned () after => .returned (.error error) after
  | .unwound reason after => .unwound reason after
  | .terminated reason => .terminated reason

/-- Continue from the actual base-parser outcome. Errors and abnormal exits
before creation of S need no local drop. A parsed S is moved on layout success
or passed unchanged to its actual destructor on layout failure. -/
def finishExtensionUnpack (unpacker : ExtensionUnpacker) (input : unpacker.Reference)
    (parsed : Outcome unpacker.State (Except Error unpacker.Base) unpacker.Unwind unpacker.Terminal)
    (final : Outcome unpacker.State
      (Except Error (ExtensionUnpacked unpacker.Base unpacker.Reference))
      unpacker.Unwind unpacker.Terminal) : Prop :=
  match parsed with
  | .returned (.error error) after => final = .returned (.error error) after
  | .returned (.ok base) after =>
    match unpackExtensionTailReference unpacker after input with
    | .ok tlv => final = .returned (.ok ⟨base, tlv⟩) after
    | .error error => ∃ dropped, unpacker.dropBase after base dropped ∧
        final = finishExtensionBaseDrop error dropped
  | .unwound reason after => final = .unwound reason after
  | .terminated reason => final = .terminated reason

/-- The complete operational unpack control flow above the parser and
destructor dependencies. Length rejection precedes parsing. Tail checks read
the actual parser-return state; reference origin and base ownership are kept. -/
def unpackExtensionOperational (unpacker : ExtensionUnpacker) (before : unpacker.State)
    (input : unpacker.Reference)
    (final : Outcome unpacker.State
      (Except Error (ExtensionUnpacked unpacker.Base unpacker.Reference))
      unpacker.Unwind unpacker.Terminal) : Prop :=
  if unpacker.length input = multisigLength ∨ unpacker.length input < unpacker.baseLength then
    final = .returned (.error .InvalidAccountData) before
  else ∃ parsed, unpacker.parse before ⟨input, 0, unpacker.baseLength⟩ parsed ∧
    finishExtensionUnpack unpacker input parsed final

/-- A successful base and tail transfer the same owned base and same source
region, without calling a destructor. -/
theorem unpackExtensionOperational_success (unpacker : ExtensionUnpacker)
    (before after : unpacker.State) (input : unpacker.Reference) (base : unpacker.Base)
    (tlv : ExtensionTailReference unpacker.Reference)
    (admitted : ¬ (unpacker.length input = multisigLength ∨
      unpacker.length input < unpacker.baseLength))
    (parsed : unpacker.parse before ⟨input, 0, unpacker.baseLength⟩ (.returned (.ok base) after))
    (layout : unpackExtensionTailReference unpacker after input = .ok tlv) :
    unpackExtensionOperational unpacker before input (.returned (.ok ⟨base, tlv⟩) after) := by
  simp only [unpackExtensionOperational, admitted, ↓reduceIte]
  exact ⟨.returned (.ok base) after, parsed, by simp [finishExtensionUnpack, layout]⟩

/-- Every permitted destructor exit is sequenced after the actual successful
parse and actual failed layout check, using the value and state of that parser. -/
theorem unpackExtensionOperational_layout_failure (unpacker : ExtensionUnpacker)
    (before after : unpacker.State) (input : unpacker.Reference) (base : unpacker.Base)
    (error : Error) (dropped : Outcome unpacker.State Unit unpacker.Unwind unpacker.Terminal)
    (admitted : ¬ (unpacker.length input = multisigLength ∨
      unpacker.length input < unpacker.baseLength))
    (parsed : unpacker.parse before ⟨input, 0, unpacker.baseLength⟩ (.returned (.ok base) after))
    (layout : unpackExtensionTailReference unpacker after input = .error error)
    (destroyed : unpacker.dropBase after base dropped) :
    unpackExtensionOperational unpacker before input (finishExtensionBaseDrop error dropped) := by
  simp only [unpackExtensionOperational, admitted, ↓reduceIte]
  refine ⟨.returned (.ok base) after, parsed, ?_⟩
  simp only [finishExtensionUnpack, layout]
  exact ⟨dropped, destroyed, rfl⟩

/-- A nonreturning destructor on a failed layout prevents every enclosing
finite exit; an ordinary error is not silently returned before cleanup. -/
theorem finishExtensionUnpack_no_drop_exit (unpacker : ExtensionUnpacker)
    (after : unpacker.State) (input : unpacker.Reference) (base : unpacker.Base)
    (error : Error)
    (layout : unpackExtensionTailReference unpacker after input = .error error)
    (noExit : ∀ dropped, ¬ unpacker.dropBase after base dropped) :
    ∀ final, ¬ finishExtensionUnpack unpacker input (.returned (.ok base) after) final := by
  intro final run
  simp only [finishExtensionUnpack, layout] at run
  obtain ⟨dropped, called, _⟩ := run
  exact noExit dropped called

/-- A pure-codec, trivial-destructor interpretation. It is a specialization,
not an assertion that arbitrary BaseState/Pack implementations are dropless. -/
abbrev pureDroplessExtensionUnpacker {Base : Type} (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Error Base) :
    ExtensionUnpacker where
  State := Unit
  Reference := Bytes
  Base := Base
  Unwind := Empty
  Terminal := Empty
  length := List.length
  byteAt := fun _ bytes index => bytes[index.val]
  baseLength := baseLength
  accountType := accountType
  parse := fun before region => returnsOf (fun _ _ =>
    (decode ((region.origin.drop region.offset).take region.length), before)) before ()
  dropBase := fun before _ => returnsOf (fun _ _ => ((), before)) before ()

/-- The concrete packed Mint has the shared codec and a trivial destructor. -/
def mintExtensionUnpacker : ExtensionUnpacker :=
  pureDroplessExtensionUnpacker mintLength .mint unpackMint

/-- The concrete packed Account has the shared codec and a trivial destructor. -/
def accountExtensionUnpacker : ExtensionUnpacker :=
  pureDroplessExtensionUnpacker accountLength .account unpackAccount

/-- Exact total result of the explicit pure-codec, trivial-destructor
specialization, retaining input-region identity in its returned tail. -/
def unpackDroplessExtension {Base : Type} (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Error Base)
    (bytes : Bytes) : Except Error (ExtensionUnpacked Base Bytes) :=
  if extensionInputRejected baseLength bytes then .error .InvalidAccountData
  else (decode (bytes.take baseLength)).bind fun base =>
    (unpackExtensionTailReference
      (pureDroplessExtensionUnpacker baseLength accountType decode) () bytes).map fun tlv =>
        ⟨base, tlv⟩

/-- Every concrete pure-codec execution also executes the operational model,
including the actual trivial drop on a failed tail check. -/
theorem unpackDroplessExtension_executes {Base : Type} (baseLength : Nat)
    (accountType : ExtensionAccountType) (decode : Bytes → Except Error Base) (bytes : Bytes) :
    unpackExtensionOperational (pureDroplessExtensionUnpacker baseLength accountType decode)
      () bytes (.returned (unpackDroplessExtension baseLength accountType decode bytes) ()) := by
  by_cases rejected : extensionInputRejected baseLength bytes
  · have rejected' : bytes.length = multisigLength ∨ bytes.length < baseLength := rejected
    unfold unpackExtensionOperational
    simp only [rejected', ↓reduceIte, unpackDroplessExtension, rejected]
  · have admitted : ¬ (bytes.length = multisigLength ∨ bytes.length < baseLength) := rejected
    unfold unpackExtensionOperational
    simp only [admitted, ↓reduceIte]
    refine ⟨.returned (decode (bytes.take baseLength)) (), ?_, ?_⟩
    · rfl
    · cases decoded : decode (bytes.take baseLength) with
      | error error =>
        simp [finishExtensionUnpack, unpackDroplessExtension, rejected, decoded, Except.bind]
      | ok base =>
        cases layout : unpackExtensionTailReference
            (pureDroplessExtensionUnpacker baseLength accountType decode) () bytes with
        | ok tlv =>
          simp [finishExtensionUnpack, unpackDroplessExtension, rejected, decoded, layout,
            Except.bind, Except.map]
        | error error =>
          simp only [finishExtensionUnpack, layout]
          exact ⟨.returned () (), rfl, by
            simp [finishExtensionBaseDrop, unpackDroplessExtension, rejected, decoded, layout,
              Except.bind, Except.map]⟩

end Solanalib.Specs.Core.Token
