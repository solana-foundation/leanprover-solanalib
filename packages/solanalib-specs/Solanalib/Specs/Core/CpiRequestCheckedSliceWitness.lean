/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.CpiRequestCheckedFacts
public import Solanalib.Specs.Core.CpiRequestCheckedSliceFamily

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.CpiRequest.Checked

/-- The normalized flags of the v1 sample do not claim a value for struct padding. -/
def sampleSliceDescriptors : List Descriptor :=
  [capture samplePool ⟨1⟩, capture samplePool ⟨2⟩]

/-- Closed calculation of the v1 source-ordered local checks. -/
theorem sample_prepareV1 :
    prepareV1 samplePool sampleInstruction.metas sampleSigned.request.accounts =
      .ok sampleSliceDescriptors := rfl

/-- The v1 body reaches the same opaque call after allocation has changed the
state. This witness neither assumes nor erases that allocation effect. -/
theorem sample_inner_execution :
    innerV1 (fun _ : Nat => samplePool) sampleProvider 10 sampleSigned.request
      (.returned (.ok ()) (12 : Nat)) := by
  change invokePrepared sampleProvider sampleInstruction [[], [[], [8, 9]]]
    sampleSliceDescriptors 10 (.returned (.ok ()) 12)
  exact invokePrepared_returned _ _ _ _ _ _ rfl

/-- the actual temporary box of V1 is dropped after the successful invocation, using
the resulting state of the invocation rather than the allocation-entry state. -/
theorem sample_signed_execution :
    signedRun sampleSliceTypes (0 : Nat) sampleSigned
      (.returned (.ok ()) (112 : Nat)) := by
  change sliceV1 (fun _ : Nat => samplePool) sampleStorage sampleProvider 0
    sampleSigned.request _
  unfold sliceV1
  simp only [sampleSigned, sampleInstruction, Instruction.make, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte]
  refine ⟨.returned 2 10, rfl, ?_⟩
  refine ⟨.returned (.ok ()) 12, sample_inner_execution, ?_⟩
  exact ⟨.returned () 112, rfl, rfl⟩

/-- Unsigned execution uses empty signers while preserving the same allocation,
invocation and drop sequence. -/
theorem sample_unsigned_execution :
    unsignedRun sampleSliceTypes (0 : Nat) sampleUnsigned
      (.returned (.ok ()) (112 : Nat)) := by
  change sliceV1 (fun _ : Nat => samplePool) sampleStorage sampleProvider 0
    ⟨sampleInstruction, sampleUnsigned.accounts, []⟩ _
  unfold sliceV1
  simp only [sampleUnsigned, sampleInstruction, Instruction.make, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte]
  refine ⟨.returned 2 10, rfl, ?_⟩
  refine ⟨.returned (.ok ()) 12, ?_, .returned () 112, rfl, rfl⟩
  change invokePrepared sampleProvider sampleInstruction []
    sampleSliceDescriptors 10 (.returned (.ok ()) 12)
  exact invokePrepared_returned _ _ _ _ _ _ rfl

/-- Closed execution witness for the exact checked signed-slice family. -/
theorem signedHasExecution : FamilyHasExecution signedFamily signedRun sampleSliceTypes :=
  ⟨(0 : Nat), sampleSigned, .returned (.ok ()) (112 : Nat), trivial, sample_signed_execution⟩

/-- Closed execution witness for the exact checked unsigned-slice family. -/
theorem unsignedHasExecution : FamilyHasExecution unsignedFamily unsignedRun sampleSliceTypes :=
  ⟨(0 : Nat), sampleUnsigned, .returned (.ok ()) (112 : Nat), trivial, sample_unsigned_execution⟩

end Solanalib.Specs.Core.CpiRequest.Checked
