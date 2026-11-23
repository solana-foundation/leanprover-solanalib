/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionLegacy
public import Solanalib.Specs.Core.TokenExtensionListReference

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Legacy

open Owned

/-- Older TLV scanning retains the owned vector and the used byte count. A
known complete header is pushed before the payload length is read or checked.
The latter read uses the actual state returned by the push dependency. -/
def collectInfo {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource : Resource)
    (length : Nat) (byteAt : State → Fin length → UInt8) (offset : Nat) (before : State)
    (final : Outcome State (Except Error (Resource × Nat)) Unwind Terminal) : Prop :=
  match header ((currentExtensionBytes length byteAt before).drop offset) with
  | .done => final = .returned (.ok (resource, offset)) before
  | .invalid => cleanup double [ops.dropAction resource]
      (.returned (.error .InvalidAccountData) before) final
  | .entry kind =>
    ∃ pushed, ops.push before (resource, kind) pushed ∧
      match pushed with
      | .returned () after =>
        let next := payloadEnd (currentExtensionBytes length byteAt after) offset
        if next ≤ length then
          collectInfo ops double resource length byteAt next after final
        else cleanup double [ops.dropAction resource]
          (.returned (.error .InvalidAccountData) after) final
      | .unwound reason after => cleanup double [ops.dropAction resource]
          (.unwound reason after) final
      | .terminated reason => final = .terminated reason
termination_by length - offset
decreasing_by
  have progress := payloadEnd_progress (currentExtensionBytes length byteAt after) offset
  omega

/-- The complete free scanner creates a logical empty vector, then keeps it
live until it is returned or dropped on an error or first unwind. -/
def getInfo (reader : CurrentExtensionTypeReader) (before : reader.State)
    (reference : reader.Reference)
    (final : Outcome reader.State (Except Error (reader.Resource × Nat))
      reader.Unwind reader.Terminal) : Prop :=
  let created := reader.vectors.empty before
  collectInfo reader.vectors reader.doubleUnwind created.1 (reader.length reference)
    (fun state => reader.byteAt state reference) 0 created.2 final

/-- Project the list owner without dropping it. The remaining used-length
field is Copy and has no destructor. -/
def retainTypes {State Resource Unwind Terminal : Type} :
    Outcome State (Except Error (Resource × Nat)) Unwind Terminal →
      Outcome State (Except Error Resource) Unwind Terminal
  | .returned value after => .returned (value.map Prod.fst) after
  | .unwound reason after => .unwound reason after
  | .terminated reason => .terminated reason

/-- Generic listing calls the resolved accessor before constructing its local
vector. The old free scanner then preserves allocation/error order. -/
def getTypes (reader : CurrentExtensionTypeReader) (before : reader.State)
    (final : Outcome reader.State (Except Error reader.Resource) reader.Unwind reader.Terminal) :
    Prop :=
  ∃ accessed, reader.getTlvData before accessed ∧
    match accessed with
    | .returned reference after =>
      ∃ scanned, getInfo reader after reference scanned ∧ final = retainTypes scanned
    | .unwound reason after => final = .unwound reason after
    | .terminated reason => final = .terminated reason

/-- A fully scanned buffer moves the same live vector and current offset. -/
theorem collectInfo_done {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource : Resource)
    (length : Nat) (byteAt : State → Fin length → UInt8) (offset : Nat) (before : State)
    (ended : header ((currentExtensionBytes length byteAt before).drop offset) = .done) :
    collectInfo ops double resource length byteAt offset before
      (.returned (.ok (resource, offset)) before) := by
  rw [collectInfo, ended]

/-- Actual normal pushes precede the bounds check and next read. -/
theorem collectInfo_push {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource : Resource)
    (length : Nat) (byteAt : State → Fin length → UInt8) (offset : Nat)
    (before after : State) (kind : ExtensionType)
    (final : Outcome State (Except Error (Resource × Nat)) Unwind Terminal)
    (found : header ((currentExtensionBytes length byteAt before).drop offset) = .entry kind)
    (pushed : ops.push before (resource, kind) (.returned () after))
    (within : payloadEnd (currentExtensionBytes length byteAt after) offset ≤ length)
    (continued : collectInfo ops double resource length byteAt
      (payloadEnd (currentExtensionBytes length byteAt after) offset) after final) :
    collectInfo ops double resource length byteAt offset before final := by
  rw [collectInfo, found]
  exact ⟨.returned () after, pushed, by simpa only [within, ↓reduceIte] using continued⟩

/-- A malformed declared length is checked only after push returns, so an
allocation abort at that push takes precedence over InvalidAccountData. -/
theorem collectInfo_push_terminal {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource : Resource)
    (length : Nat) (byteAt : State → Fin length → UInt8) (offset : Nat) (before : State)
    (kind : ExtensionType) (reason : Terminal)
    (found : header ((currentExtensionBytes length byteAt before).drop offset) = .entry kind)
    (pushed : ops.push before (resource, kind) (.terminated reason)) :
    collectInfo ops double resource length byteAt offset before (.terminated reason) := by
  rw [collectInfo, found]
  exact ⟨.terminated reason, pushed, rfl⟩

/-- A missing resolved accessor execution cannot become an invented list. -/
theorem getTypes_no_invented_exit (reader : CurrentExtensionTypeReader)
    (before : reader.State) (noExit : ∀ outcome, ¬ reader.getTlvData before outcome) :
    ∀ final, ¬ getTypes reader before final := by
  rintro final ⟨accessed, called, _⟩
  exact noExit accessed called

/-- The old algorithm executes a complete nonempty two-entry reference scan,
retaining the same vector identity and used offset through both pushes. -/
theorem sample_executes :
    getTypes (extensionTypeReaderReference (Unwind := Empty) (Terminal := Empty)
      extensionListSample) [] (.returned (.ok (0 : Nat)) [some extensionListSampleValues]) := by
  refine ⟨.returned () [], rfl, .returned (.ok ((0 : Nat), 9)) [some extensionListSampleValues],
    ?_, rfl⟩
  change collectInfo
    (vectorReference : VectorOps (VectorState ExtensionType) ExtensionType Nat Empty Empty)
    (fun _ _ _ _ => False) 0 extensionListSample.length
    (fun _ index => extensionListSample[index.val]) 0 [some []]
    (.returned (.ok (0, 9)) [some extensionListSampleValues])
  apply collectInfo_push (kind := .immutableOwner) (after := [some [.immutableOwner]])
  · decide +kernel
  · exact ⟨[], rfl, rfl⟩
  · decide +kernel
  · apply collectInfo_push (kind := .memoTransfer) (after := [some extensionListSampleValues])
    · decide +kernel
    · exact ⟨[.immutableOwner], rfl, rfl⟩
    · decide +kernel
    · apply collectInfo_done
      decide +kernel

end Solanalib.Specs.Core.Token.Legacy
