/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionScan
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

open Owned

/-- Read the current contents of a source slice whose metadata length is fixed.
Every byte is indexed by that same length; allocation effects may change the
observation and are not silently replaced by a saved snapshot. -/
def currentExtensionBytes {State : Type} (length : Nat)
    (byteAt : State → Fin length → UInt8) (state : State) : Bytes :=
  List.ofFn (byteAt state)

/-- Current-state byte observations retain the fixed metadata of the source slice. -/
theorem currentExtensionBytes_length {State : Type} (length : Nat)
    (byteAt : State → Fin length → UInt8) (state : State) :
    (currentExtensionBytes length byteAt state).length = length := by
  simp [currentExtensionBytes]

/-- Allocation-aware scanning through a live shared-slice interpretation.
The next iteration reads the state actually returned by push. The identity and length of the slice
remain fixed, while its observed bytes need a separate
immutability law before they can be treated as a pure input value. -/
def collectCurrentExtensionTypes {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource : Resource)
    (length : Nat) (byteAt : State → Fin length → UInt8) (offset : Nat) (before : State)
    (final : Outcome State (Except Error Resource) Unwind Terminal) : Prop :=
  match _scanEquation : nextExtension ((currentExtensionBytes length byteAt before).drop offset)
    with
  | .done => final = .returned (.ok resource) before
  | .invalid => cleanup double [ops.dropAction resource]
      (.returned (.error .InvalidAccountData) before) final
  | .next kind consumed _tail =>
    ∃ pushed, ops.push before (resource, kind) pushed ∧
      match pushed with
      | .returned () after =>
          collectCurrentExtensionTypes ops double resource length byteAt (offset + consumed) after
            final
      | .unwound reason after => cleanup double [ops.dropAction resource]
          (.unwound reason after) final
      | .terminated reason => final = .terminated reason
termination_by length - offset
decreasing_by
  have geometry := nextExtension_next_geometry _ _ _ _ (by assumption)
  simp only [List.length_drop, currentExtensionBytes_length] at geometry
  omega

/-- A completed scan moves the same owner, without invoking its destructor. -/
theorem collectCurrentExtensionTypes_done {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource : Resource)
    (length : Nat) (byteAt : State → Fin length → UInt8) (offset : Nat) (before : State)
    (scanned : nextExtension ((currentExtensionBytes length byteAt before).drop offset) = .done) :
    collectCurrentExtensionTypes ops double resource length byteAt offset before
      (.returned (.ok resource) before) := by
  rw [collectCurrentExtensionTypes]
  split <;> simp_all

/-- One validated entry exposes exactly one push, then reads the returned
state at the advanced offset or performs its required cleanup. -/
theorem collectCurrentExtensionTypes_next_iff {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource : Resource)
    (length : Nat) (byteAt : State → Fin length → UInt8) (offset : Nat) (before : State)
    (kind : ExtensionType) (consumed : Nat) (tail : Bytes)
    (final : Outcome State (Except Error Resource) Unwind Terminal)
    (scanned : nextExtension ((currentExtensionBytes length byteAt before).drop offset) =
      .next kind consumed tail) :
    collectCurrentExtensionTypes ops double resource length byteAt offset before final ↔
      ∃ pushed, ops.push before (resource, kind) pushed ∧
        match pushed with
        | .returned () after => collectCurrentExtensionTypes ops double resource length byteAt
            (offset + consumed) after final
        | .unwound reason after => cleanup double [ops.dropAction resource]
            (.unwound reason after) final
        | .terminated reason => final = .terminated reason := by
  rw [collectCurrentExtensionTypes]
  split
  · simp_all
  · simp_all
  · rename_i foundKind foundConsumed foundTail scanEquation
    have same := ExtensionScanStep.next.inj (scanned.symm.trans scanEquation)
    obtain ⟨rfl, rfl, rfl⟩ := same
    rfl

/-- Actual returning pushes resume at the next source offset in their new state. -/
theorem collectCurrentExtensionTypes_push {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource : Resource)
    (length : Nat) (byteAt : State → Fin length → UInt8) (offset : Nat)
    (before middle : State) (kind : ExtensionType) (consumed : Nat) (tail : Bytes)
    (final : Outcome State (Except Error Resource) Unwind Terminal)
    (scanned : nextExtension ((currentExtensionBytes length byteAt before).drop offset) =
      .next kind consumed tail)
    (pushed : ops.push before (resource, kind) (.returned () middle))
    (continued : collectCurrentExtensionTypes ops double resource length byteAt
      (offset + consumed) middle final) :
    collectCurrentExtensionTypes ops double resource length byteAt offset before final := by
  apply (collectCurrentExtensionTypes_next_iff ops double resource length byteAt offset before
    kind consumed tail final scanned).mpr
  exact ⟨.returned () middle, pushed, continued⟩

/-- A malformed entry triggers scope cleanup of the actual current vector. -/
theorem collectCurrentExtensionTypes_error {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource : Resource)
    (length : Nat) (byteAt : State → Fin length → UInt8) (offset : Nat) (before : State)
    (final : Outcome State (Except Error Resource) Unwind Terminal)
    (scanned : nextExtension ((currentExtensionBytes length byteAt before).drop offset) = .invalid)
    (cleaned : cleanup double [ops.dropAction resource]
      (.returned (.error .InvalidAccountData) before) final) :
    collectCurrentExtensionTypes ops double resource length byteAt offset before final := by
  rw [collectCurrentExtensionTypes]
  split <;> simp_all

/-- A push unwind carries partial effects into the vector destructor. -/
theorem collectCurrentExtensionTypes_push_unwind {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource : Resource)
    (length : Nat) (byteAt : State → Fin length → UInt8) (offset : Nat)
    (before middle : State) (kind : ExtensionType) (consumed : Nat) (tail : Bytes)
    (reason : Unwind) (final : Outcome State (Except Error Resource) Unwind Terminal)
    (scanned : nextExtension ((currentExtensionBytes length byteAt before).drop offset) =
      .next kind consumed tail)
    (pushed : ops.push before (resource, kind) (.unwound reason middle))
    (cleaned : cleanup double [ops.dropAction resource] (.unwound reason middle) final) :
    collectCurrentExtensionTypes ops double resource length byteAt offset before final := by
  apply (collectCurrentExtensionTypes_next_iff ops double resource length byteAt offset before
    kind consumed tail final scanned).mpr
  exact ⟨.unwound reason middle, pushed, cleaned⟩

/-- A terminal push bypasses all remaining reads and cleanup calls. -/
theorem collectCurrentExtensionTypes_push_terminal {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (double : DoubleUnwind State Unwind Terminal) (resource : Resource)
    (length : Nat) (byteAt : State → Fin length → UInt8) (offset : Nat)
    (before : State) (kind : ExtensionType) (consumed : Nat) (tail : Bytes) (reason : Terminal)
    (scanned : nextExtension ((currentExtensionBytes length byteAt before).drop offset) =
      .next kind consumed tail)
    (pushed : ops.push before (resource, kind) (.terminated reason)) :
    collectCurrentExtensionTypes ops double resource length byteAt offset before
      (.terminated reason) := by
  apply (collectCurrentExtensionTypes_next_iff ops double resource length byteAt offset before
    kind consumed tail (.terminated reason) scanned).mpr
  exact ⟨.terminated reason, pushed, rfl⟩

/-- Resolved accessor and vector dependencies for fully generic type listing.
The returned slice identity fixes its metadata length. Its contents are read
from actual provider states, with no assumed allocation frame law. -/
structure CurrentExtensionTypeReader where
  /-- Actual interpretation state. -/
  State : Type
  /-- Identity of the source shared-slice reference. -/
  Reference : Type
  /-- Stable logical vector identity. -/
  Resource : Type
  /-- Dependency unwind reasons. -/
  Unwind : Type
  /-- Dependency terminal reasons. -/
  Terminal : Type
  /-- Immutable length metadata carried by each source slice reference. -/
  length : Reference → Nat
  /-- Read a byte through the same reference in the actual current state. -/
  byteAt : (state : State) → (reference : Reference) → Fin (length reference) → UInt8
  /-- All actual finite exits of the resolved get_tlv_data accessor. -/
  getTlvData : State → Outcome State Reference Unwind Terminal → Prop
  /-- Actual allocation, push and drop dependencies. -/
  vectors : VectorOps State ExtensionType Resource Unwind Terminal
  /-- Explicit terminal behavior for a second unwind during cleanup. -/
  doubleUnwind : DoubleUnwind State Unwind Terminal

/-- Generic listing first calls the resolved accessor, then creates the empty
vector, then reads the live slice while pushing. The changed state and finite exit of every
dependency remain visible in the enclosing call. -/
def getExtensionTypesCurrent (reader : CurrentExtensionTypeReader) (before : reader.State)
    (final : Outcome reader.State (Except Error reader.Resource) reader.Unwind reader.Terminal) :
    Prop :=
  ∃ accessed, reader.getTlvData before accessed ∧
    match accessed with
    | .returned reference after =>
      let created := reader.vectors.empty after
      collectCurrentExtensionTypes reader.vectors reader.doubleUnwind created.1
        (reader.length reference) (fun state => reader.byteAt state reference) 0 created.2 final
    | .unwound reason after => final = .unwound reason after
    | .terminated reason => final = .terminated reason

/-- Accessor unwinds occur before a vector is created. -/
theorem getExtensionTypesCurrent_accessor_unwind (reader : CurrentExtensionTypeReader)
    (before after : reader.State) (reason : reader.Unwind)
    (called : reader.getTlvData before (.unwound reason after)) :
    getExtensionTypesCurrent reader before (.unwound reason after) :=
  ⟨.unwound reason after, called, rfl⟩

/-- Terminal accessor exits bypass all vector operations. -/
theorem getExtensionTypesCurrent_accessor_terminal (reader : CurrentExtensionTypeReader)
    (before : reader.State) (reason : reader.Terminal)
    (called : reader.getTlvData before (.terminated reason)) :
    getExtensionTypesCurrent reader before (.terminated reason) :=
  ⟨.terminated reason, called, rfl⟩

/-- A nonreturning accessor cannot be converted into any finite listing exit. -/
theorem getExtensionTypesCurrent_no_invented_exit (reader : CurrentExtensionTypeReader)
    (before : reader.State) (noExit : ∀ called, ¬ reader.getTlvData before called) :
    ∀ final, ¬ getExtensionTypesCurrent reader before final := by
  intro final run
  obtain ⟨called, method, _⟩ := run
  exact noExit called method

end Solanalib.Specs.Core.Token
