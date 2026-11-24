/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenMetadataInitialize

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.MetadataInitialize.Sample

open InstructionAllocated.Witness (State sampleTypes)

/-- Sample Vec append, preserving both logical tokens and clearing the source.
Its current contents are read at the actual append state. -/
def append (before : State) (resources : Nat × Nat)
    (outcome : Outcome State Unit Nat Nat) : Prop :=
  ∃ target source,
    before.1.current resources.1 = some target ∧
    before.1.current resources.2 = some source ∧
    outcome = .returned ()
      ((before.1.set resources.1 (some (target ++ source))).set resources.2 (some []), before.2)

/-- Read the actual live string bytes. Invalid UTF-8 has no String image. -/
def stringCurrent (state : State) (resource : Nat) : Option String := do
  let bytes ← state.1.current resource
  String.fromUTF8? ⟨bytes.toArray⟩

/-- Current three-string observation, before invoking Borsh. -/
def readText (state : State) (owners : Owners Nat) : Option Text := do
  let name ← stringCurrent state owners.name
  let symbol ← stringCurrent state owners.symbol
  let uri ← stringCurrent state owners.uri
  return ⟨name, symbol, uri⟩

/-- Concrete serialization dependency. It reads the actual String owners,
allocates the correct encoded temporary on success, and preserves errors. -/
def toVec (before : State) (owners : Owners Nat) :
    Outcome State (Except Unit Nat) Nat Nat :=
  match readText before owners with
  | none => .unwound 98 before
  | some text => if text.fits then
      .returned (.ok before.1.length) (before.1 ++ [some text.encoded], before.2)
    else .returned (.error ()) before

/-- Concrete full index; the three moved strings occupy byte-ledger slots
before the output buffer and Borsh temporary are constructed. -/
def index : Types where
  vectors := sampleTypes
  StringResource := Nat
  stringCurrent := stringCurrent
  toVec := Callback.ofFunction toVec
  append := append
  dropString := sampleTypes.bytes.drop
  unwrap := fun _ _ outcome => outcome = .terminated (99 : Nat)

/-- The actual current String observation of the serializer determines its bytes. -/
theorem serialization : Serialization index := by
  intro before owners result after called
  change toVec before owners = .returned result after at called
  unfold toVec at called
  split at called
  · cases called
  · rename_i text observed
    split at called
    · rename_i fits
      cases called
      exact ⟨text, observed, fits, Owned.VectorState.allocate_current before.1 text.encoded⟩
    · rename_i tooLong
      cases called
      exact ⟨text, observed, tooLong⟩

/-- Non-ASCII fields ensure the witness measures UTF-8 byte lengths. -/
def text : Text := ⟨"N", "Σ", "uri"⟩

/-- The strings enter as three distinct owned resources. -/
def initial : State :=
  ([some text.name.toUTF8.data.toList, some text.symbol.toUTF8.data.toList,
    some text.uri.toUTF8.data.toList], [])

/-- Arbitrary program ID and an alias between metadata and update authority
are both admitted by the constructor. -/
def args : Args Nat := ⟨.zero, .ofNat 1, .ofNat 1, .ofNat 2, .ofNat 3, ⟨0, 1, 2⟩⟩

/-- The metadata owner of the output is slot0, while its byte buffer is slot3. -/
def returnedValue : InstructionAllocated.Value index.vectors :=
  ⟨.zero, (0 : Nat), (3 : Nat)⟩

/-- Input strings and the emptied Borsh temporary have been retired; the
complete metadata and discriminator-prefixed byte buffer remain owned. -/
def final : State :=
  ([none, none, none, some (discriminator ++ text.encoded), none], [some (metas args)])

private theorem returns_iff {S A V U T : Type} (f : S → A → V × S)
    (s : S) (a : A) (out : Outcome S V U T) :
    returnsOf f s a out ↔ out = .returned (f s a).1 (f s a).2 := by
  cases out <;> simp [returnsOf, Prod.ext_iff, eq_comm]

/-- Closed successful SDK construction, including temporary and string drops. -/
theorem executes : run index initial args (.returned returnedValue final) := by
  have nameDecoded : String.fromUTF8? ⟨"N".toByteArray.data⟩ = some "N" := by decide +kernel
  have symbolDecoded : String.fromUTF8? ⟨"Σ".toByteArray.data⟩ = some "Σ" := by decide +kernel
  have uriDecoded : String.fromUTF8? ⟨"uri".toByteArray.data⟩ = some "uri" := by decide +kernel
  have nameLength : "N".utf8ByteSize = 1 := rfl
  have symbolLength : "Σ".utf8ByteSize = 2 := rfl
  have uriLength : "uri".utf8ByteSize = 3 := rfl
  simp [run, construct, pack, index, initial, args, returnedValue, final,
    textDrops, text, metas, discriminator, toVec, readText, stringCurrent, Text.fits, Text.bytes,
      Text.encoded,
    append, Callback.ofFunction, Callback.bind, Callback.map,
    Owned.protect, Owned.scope, Owned.onUnwind, Owned.cleanup,
    InstructionAllocated.Witness.sampleTypes, InstructionAllocated.drops,
    Owned.VectorOps.focus, Owned.Focus.fst, Owned.Focus.snd,
    Owned.Focus.lift, Owned.Focus.liftOutcome, Owned.vectorReference, Owned.VectorState.allocate,
    Owned.VectorState.modify, Owned.VectorState.retire, Owned.VectorState.current,
    returns_iff, Owned.VectorOps.dropAction, Outcome.map, Solanalib.Runtime.u32le,
    nameDecoded, symbolDecoded, uriDecoded, nameLength, symbolLength, uriLength]

end Solanalib.Specs.Core.Token.MetadataInitialize.Sample
