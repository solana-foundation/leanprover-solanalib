/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.CpiRequestCheckedFamily
public import Solanalib.Specs.Core.CpiRequestCheckedSlice

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.CpiRequest.Checked

/-- the owned temporary boxed-array dependency of V1, including its cleanup token. -/
structure SliceTypes extends Types where
  /-- Stable identity of the temporary box during this call. -/
  Resource : Type
  /-- Allocation, actual-state drop and double-unwind interpretation. -/
  storage : Storage State Resource Unwind Terminal

/-- Arguments of the checked v1 signed slice entry. -/
structure SignedCall (types : SliceTypes) where
  /-- Exact instruction, borrowed handles and signer tree. -/
  request : Request AccountView.Handle
  /-- Opaque unchecked invocation of the initialized prefix. -/
  invoke : Syscall types.State types.Unwind types.Terminal

/-- Arguments of the checked v1 unsigned slice entry. -/
structure UnsignedCall (types : SliceTypes) where
  /-- Immutable source instruction observation. -/
  instruction : Solanalib.Runtime.CpiInstruction
  /-- Ordered supplied borrowed AccountViews. -/
  accounts : List AccountView.Handle
  /-- Opaque unchecked invocation of the initialized prefix. -/
  invoke : Syscall types.State types.Unwind types.Terminal

/-- Checked v1 signed-slice family, retaining allocation and cleanup effects. -/
def signedFamily : Family where
  Index := SliceTypes
  State := fun types => types.State
  Args := SignedCall
  Value := fun _ => Except Error Unit
  Unwind := fun types => types.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args => sliceV1 types.pool types.storage args.invoke before args.request }

/-- The actual mathematical signed-slice reference. -/
def signedRun : FamilyRun signedFamily := fun types before args =>
  sliceV1 types.pool types.storage args.invoke before args.request

/-- Exact signed-slice reference correctness, preserving every dependency exit. -/
theorem signedReference : FamilyReference signedFamily signedRun := by
  intro _ _ _ _ _ execution
  exact execution

/-- The unsigned entry delegates to the same checked signed slice with no seeds. -/
def unsignedFamily : Family where
  Index := SliceTypes
  State := fun types => types.State
  Args := UnsignedCall
  Value := fun _ => Except Error Unit
  Unwind := fun types => types.Unwind
  Terminal := fun types => types.Terminal
  contract := fun types => {
    requires := fun _ _ => True
    post := fun before args => sliceV1 types.pool types.storage args.invoke before
      ⟨args.instruction, args.accounts, []⟩ }

/-- The actual mathematical unsigned-slice reference. -/
def unsignedRun : FamilyRun unsignedFamily := fun types before args =>
  sliceV1 types.pool types.storage args.invoke before ⟨args.instruction, args.accounts, []⟩

/-- Exact unsigned-slice reference correctness. -/
theorem unsignedReference : FamilyReference unsignedFamily unsignedRun := by
  intro _ _ _ _ _ execution
  exact execution

/-- An explicit box dependency: allocation and drop have distinguishable effects. -/
def sampleStorage : Storage Nat Nat Nat Nat where
  allocate := fun before count outcome => outcome = .returned count (before + 10)
  drop := fun before _ outcome => outcome = .returned () (before + 100)
  doubleUnwind := fun _ first second terminal => terminal = first + second

/-- The closed v1 dependency interpretation. -/
def sampleSliceTypes : SliceTypes where
  toTypes := sampleTypes
  Resource := Nat
  storage := sampleStorage

/-- The corresponding signed v1 slice and its exact nested seed tree. -/
def sampleSigned : SignedCall sampleSliceTypes where
  request := ⟨sampleInstruction, [⟨1⟩, ⟨2⟩, ⟨7⟩], [[], [[], [8, 9]]]⟩
  invoke := sampleProvider

/-- The corresponding unsigned v1 slice. -/
def sampleUnsigned : UnsignedCall sampleSliceTypes where
  instruction := sampleInstruction
  accounts := [⟨1⟩, ⟨2⟩, ⟨7⟩]
  invoke := sampleProvider

/-- The checked signed-slice family has a concrete admissible input. -/
theorem signedSatisfiable : FamilySatisfiable signedFamily sampleSliceTypes :=
  ⟨(0 : Nat), sampleSigned, trivial⟩

/-- The checked unsigned-slice family has a concrete admissible input. -/
theorem unsignedSatisfiable : FamilySatisfiable unsignedFamily sampleSliceTypes :=
  ⟨(0 : Nat), sampleUnsigned, trivial⟩

end Solanalib.Specs.Core.CpiRequest.Checked
