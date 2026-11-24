/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionLegacyFamilies

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false
set_option maxRecDepth 10000

namespace SolanalibTest.Specs.Core.TokenExtensionLegacy

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
  Solanalib.Specs.Core.Owned

/-- This source-like vector interpretation aborts at its first push. The
other operations retain the real logical owner and retirement behavior. -/
def abortingVectors : VectorOps (VectorState ExtensionType) ExtensionType Nat Empty Nat :=
  { vectorReference with push := fun _ _ final => final = .terminated (99 : Nat) }

/-- The malformed payload has a valid type and length header. -/
def malformed : Bytes := [7, 0, 1, 0]

def abortingReader : CurrentExtensionTypeReader :=
  { extensionTypeReaderReference (Unwind := Empty) (Terminal := Nat) malformed with
      vectors := abortingVectors }

/-- Old listing reaches push before discovering the missing payload. -/
theorem push_abort_precedes_payload_error :
    Legacy.getTypes abortingReader [] (.terminated (99 : Nat)) := by
  refine ⟨.returned () [], rfl, .terminated (99 : Nat), ?_, rfl⟩
  change Legacy.collectInfo abortingVectors (fun _ _ _ _ => False) 0 malformed.length
    (fun _ index => malformed[index.val]) 0 [some []] (.terminated (99 : Nat))
  apply Legacy.collectInfo_push_terminal (kind := .immutableOwner)
  · decide +kernel
  · rfl

/-- The exact old deduplication interpretation shares that aborting push. -/
def abortingArray : Legacy.TypeArray where
  State := VectorState ExtensionType
  Reference := List Legacy.Kind
  Resource := Nat
  Unwind := Empty
  Terminal := Nat
  length := List.length
  kindAt := fun _ input index => input[index.val]
  vectors := abortingVectors
  doubleUnwind := fun _ _ _ _ => False

/-- A variable-size kind is encountered before an ordinary fixed-size one. -/
def variableFirst : List Legacy.Kind :=
  [⟨.tokenMetadata, by decide⟩, ⟨.immutableOwner, by decide⟩]

/-- Even the variable kind is first pushed while building the dedup vector. -/
theorem allocation_precedes_variable_size_error :
    Legacy.calculateAccountLength ⟨abortingArray, 82⟩ [] variableFirst (.terminated (99 : Nat)) :=
      by
  change if variableFirst.length = 0 then _ else _
  rw [ite_eq_right (by decide)]
  refine ⟨.terminated (99 : Nat), ?_, rfl⟩
  change Legacy.buildVector .deduplicate abortingArray variableFirst (0 : Nat) 0 [some []]
    (.terminated (99 : Nat))
  apply Legacy.buildVector_push_terminal (values := []) (bound := by decide)
  · rfl
  · exact ⟨.terminated (99 : Nat), rfl, rfl⟩

/-- A complete Mint that ends immediately after the marker. -/
def atMarker : Bytes := Legacy.mintSampleBytes.take 166

/-- The later old interfaces allocate/drop the padding Vec and preserve an
empty borrowed range of the same input at the exact boundary. -/
theorem marker_only_accepted :
    Legacy.unpack false Legacy.mintUnpacker [] atMarker
      (.returned (.ok ⟨Legacy.mintSampleBase, .borrowed ⟨atMarker, 166, 0⟩⟩) [none]) := by
  apply Legacy.unpack_success false Legacy.mintUnpacker [] [] [none] atMarker
    Legacy.mintSampleBase (.borrowed ⟨atMarker, 166, 0⟩)
  · decide +kernel
  · rfl
  · have comparison : Legacy.paddingMatches Legacy.mintUnpacker [] atMarker
        (.returned true [none]) := by
      apply Legacy.paddingMatches_returned Legacy.mintUnpacker []
        [some (List.replicate 83 0)] [none] atMarker (0 : Nat) (List.replicate 83 0)
      · rfl
      · rfl
      · exact ⟨List.replicate 83 0, rfl, rfl⟩
    exact Legacy.unpackTail_compared false Legacy.mintUnpacker [] [none] atMarker true
      (by decide +kernel) (by decide +kernel) comparison

/-- Token 8.0.1 rejects the same boundary before constructing that Vec. The
successful copied base is destroyed, with no fabricated allocation event. -/
theorem marker_only_rejected :
    Legacy.unpack true Legacy.mintUnpacker [] atMarker
      (.returned (.error .InvalidAccountData) []) := by
  unfold Legacy.unpack
  rw [ite_eq_right (by decide +kernel)]
  refine ⟨.returned (.ok Legacy.mintSampleBase) [], rfl,
    .returned (.error .InvalidAccountData) [], ?_, ?_⟩
  · rfl
  · exact ⟨.returned () [], rfl, rfl⟩

/-- A terminal accessor is propagated before creating any output vector. -/
def stoppingReader : CurrentExtensionTypeReader :=
  { abortingReader with getTlvData := fun _ final => final = .terminated (17 : Nat) }

theorem accessor_terminal_precedes_vector :
    Legacy.getTypes stoppingReader [] (.terminated (17 : Nat)) :=
  ⟨.terminated (17 : Nat), rfl, rfl⟩

/-- A resolved getter creates an owned error in state 1. Its separately
interpreted destructor supplies the specified finite exit. -/
def owningErrorKey (exit : Outcome Nat Unit Nat Nat) : ExtensionKeyGetter where
  State := Nat
  Reference := Unit
  Unwind := Nat
  Terminal := Nat
  getExtension := fun _ outcome => outcome = .returned (.error .BorshIoError) 1
  dropError := fun before error outcome =>
    before = 1 ∧ error = .BorshIoError ∧ outcome = exit
  key := fun _ _ => .zero

/-- A normal error destructor changes the state before the None return. -/
theorem key_error_drop_changes_state :
    getExtensionKey (owningErrorKey (.returned () 2)) (0 : Nat) (.returned none (2 : Nat)) := by
  exact getExtensionKey_error (owningErrorKey (.returned () 2))
    (0 : Nat) (1 : Nat) (2 : Nat) .BorshIoError rfl ⟨rfl, rfl, rfl⟩

/-- Result::ok does not absorb an unwind from destruction of the error. -/
theorem key_error_drop_unwind :
    getExtensionKey (owningErrorKey (.unwound 7 2)) (0 : Nat) (.unwound (7 : Nat) (2 : Nat)) := by
  exact getExtensionKey_error_exit (owningErrorKey (.unwound 7 2))
    (0 : Nat) (1 : Nat) .BorshIoError rfl
    (.unwound (7 : Nat) (2 : Nat)) ⟨rfl, rfl, rfl⟩

/-- A terminal error drop prevents an invented ordinary None result. -/
theorem key_error_drop_terminal :
    getExtensionKey (owningErrorKey (.terminated 9)) (0 : Nat) (.terminated (9 : Nat)) := by
  exact getExtensionKey_error_exit (owningErrorKey (.terminated 9))
    (0 : Nat) (1 : Nat) .BorshIoError rfl
    (.terminated (9 : Nat)) ⟨rfl, rfl, rfl⟩

theorem key_error_drop_cannot_be_skipped :
    ¬ getExtensionKey (owningErrorKey (.returned () 2)) (0 : Nat) (.returned none (1 : Nat)) := by
  rintro ⟨_, rfl, _, ⟨_, _, rfl⟩, impossible⟩
  cases impossible

theorem key_error_terminal_cannot_return :
    ¬ getExtensionKey (owningErrorKey (.terminated 9)) (0 : Nat) (.returned none (1 : Nat)) := by
  rintro ⟨_, rfl, _, ⟨_, _, rfl⟩, impossible⟩
  cases impossible

end SolanalibTest.Specs.Core.TokenExtensionLegacy
