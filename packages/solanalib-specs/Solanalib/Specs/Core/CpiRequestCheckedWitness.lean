/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.CpiRequestCheckedFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.CpiRequest.Checked

/-- The sample initializes precisely the two metadata positions, ignoring the
third supplied account. V2 copies the explicitly selected raw header of the sample. -/
def sampleDescriptors : List Descriptor :=
  [captureV2 samplePool (normalizedHeader samplePool) ⟨1⟩, captureV2 samplePool (normalizedHeader
    samplePool) ⟨2⟩]

/-- Closed calculation of the identity-instance v2 local checks. -/
theorem sample_prepareV2 :
    prepareDirectV2 samplePool (normalizedHeader samplePool) sampleInstruction.metas
      sampleArray.accounts.values =
      .ok sampleDescriptors := rfl

/-- Actual nonempty checked v2 execution, including the initialized prefix and
the observable state effect of the opaque invocation. -/
theorem sample_array_execution :
    arrayRun sampleArrayTypes (0 : Nat) sampleArray (.returned (.ok ()) (2 : Nat)) := by
  change directV2 (fun _ : Nat => samplePool) (fun _ => normalizedHeader samplePool) sampleProvider
    0
    ⟨sampleInstruction, [⟨1⟩, ⟨2⟩, ⟨7⟩], [[], [[], [8, 9]]]⟩ _
  apply (directV2_iff _ _ _ _ _ _).mpr
  change invokePrepared sampleProvider sampleInstruction [[], [[], [8, 9]]]
    sampleDescriptors 0 (.returned (.ok ()) 2)
  exact invokePrepared_returned _ _ _ _ _ _ rfl

/-- Closed execution witness for the exact checked array family and reference. -/
theorem arrayHasExecution : FamilyHasExecution arrayFamily arrayRun sampleArrayTypes :=
  ⟨(0 : Nat), sampleArray, .returned (.ok ()) (2 : Nat), trivial, sample_array_execution⟩


end Solanalib.Specs.Core.CpiRequest.Checked
