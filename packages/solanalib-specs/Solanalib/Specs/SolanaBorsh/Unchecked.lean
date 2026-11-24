/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.BorshUnchecked
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaBorsh.v1

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Type and callback parameters of `T::deserialize`. These are mathematical
callback interpretations, not claims about a Borsh implementation. -/
structure UncheckedIndex where
  State : Type
  Error : Type
  Value : Type
  Unwind : Type
  Terminal : Type
  deserialize : Borsh.Deserializer State Error Value Unwind Terminal

def try_from_slice_unchecked_contract : Family where
  Index := UncheckedIndex
  State := UncheckedIndex.State
  Args := fun _ => Solanalib.Runtime.Bytes
  Value := fun index => Except index.Error index.Value
  Unwind := UncheckedIndex.Unwind
  Terminal := UncheckedIndex.Terminal
  contract := fun index => {
    requires := fun _ _ => True
    post := fun before bytes outcome => match outcome with
      | .returned result after =>
          ∃ remaining, index.deserialize before bytes (.returned (result, remaining) after)
      | .unwound reason after => index.deserialize before bytes (.unwound reason after)
      | .terminated reason => index.deserialize before bytes (.terminated reason)
  }

def try_from_slice_unchecked_run : FamilyRun try_from_slice_unchecked_contract :=
  fun index => Borsh.tryFromSliceUnchecked index.deserialize

theorem try_from_slice_unchecked_reference :
    FamilyReference try_from_slice_unchecked_contract try_from_slice_unchecked_run := by
  intro index before bytes outcome _ step
  cases outcome with
  | returned result after => exact (Borsh.unchecked_returned_iff ..).mp step
  | unwound reason after => exact (Borsh.unchecked_unwound_iff ..).mp step
  | terminated reason => exact (Borsh.unchecked_terminated_iff ..).mp step

def try_from_slice_unchecked_sample : UncheckedIndex where
  State := Nat
  Error := Borsh.SampleError
  Value := UInt8
  Unwind := Empty
  Terminal := Empty
  deserialize := Callback.ofFunction Borsh.byteDeserializer

theorem try_from_slice_unchecked_hasExecution :
    FamilyHasExecution try_from_slice_unchecked_contract
      try_from_slice_unchecked_run try_from_slice_unchecked_sample := by
  refine ⟨(0 : Nat), [7, 9], .returned (.ok (7 : UInt8)) (1 : Nat), True.intro, ?_⟩
  exact ⟨.returned (.ok (7 : UInt8), [9]) (1 : Nat), rfl, rfl⟩

theorem try_from_slice_unchecked_satisfiable :
    FamilySatisfiable try_from_slice_unchecked_contract
      try_from_slice_unchecked_sample :=
  try_from_slice_unchecked_hasExecution.satisfiable

end Solanalib.Specs.SolanaBorsh.v1
