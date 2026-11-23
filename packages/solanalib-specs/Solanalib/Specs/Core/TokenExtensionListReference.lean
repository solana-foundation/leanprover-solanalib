/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionListCurrent
public import Solanalib.Specs.Core.OwnedVector

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

open Owned

/-- Constant source bytes and the concrete vector ledger instantiate the fully
generic reader. Only this mathematical reference provider has normal-only
operations; no success assumption is made for other allocation providers. -/
def extensionTypeReaderReference {Unwind Terminal : Type} (bytes : Bytes) :
    CurrentExtensionTypeReader where
  State := VectorState ExtensionType
  Reference := Unit
  Resource := Nat
  Unwind := Unwind
  Terminal := Terminal
  length := fun _ => bytes.length
  byteAt := fun _ _ index => bytes[index.val]
  getTlvData := fun before outcome => outcome = .returned () before
  vectors := vectorReference
  doubleUnwind := fun _ _ _ _ => False

/-- The complete two-entry sample allocates and grows an owned result vector. -/
def extensionListSample : Bytes := [7, 0, 0, 0, 8, 0, 1, 0, 1]

/-- The ordered extension values of the sample. -/
def extensionListSampleValues : List ExtensionType := [.immutableOwner, .memoTransfer]

/-- An actual nonempty reference execution creates the vector, pushes both
validated tags, and transfers that same live resource to the result. -/
theorem extensionListSample_executes :
    getExtensionTypesCurrent
      (extensionTypeReaderReference (Unwind := Empty) (Terminal := Empty)
        extensionListSample) []
      (.returned (.ok (0 : Nat)) [some extensionListSampleValues]) := by
  refine ⟨.returned () [], rfl, ?_⟩
  change collectCurrentExtensionTypes
    (vectorReference : VectorOps (VectorState ExtensionType) ExtensionType Nat Empty Empty)
    (fun _ _ _ _ => False) 0 extensionListSample.length
    (fun _ index => extensionListSample[index.val]) 0 [some []]
    (.returned (.ok 0) [some extensionListSampleValues])
  apply collectCurrentExtensionTypes_push (kind := .immutableOwner) (consumed := 4)
    (tail := [8, 0, 1, 0, 1]) (middle := [some [.immutableOwner]])
  · decide +kernel
  · exact ⟨[], rfl, rfl⟩
  · apply collectCurrentExtensionTypes_push (kind := .memoTransfer) (consumed := 5)
      (tail := []) (middle := [some extensionListSampleValues])
    · decide +kernel
    · exact ⟨[.immutableOwner], rfl, rfl⟩
    · apply collectCurrentExtensionTypes_done
      decide +kernel

/-- The nonempty result retains its source order and live resource identity. -/
theorem extensionListSample_current :
    (vectorReference : VectorOps (VectorState ExtensionType) ExtensionType Nat Empty Empty).current
      [some extensionListSampleValues] 0 = some [.immutableOwner, .memoTransfer] := rfl

end Solanalib.Specs.Core.Token
