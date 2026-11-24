/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.HashInitialized

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Hash.Single

/-- `hash` borrows a one-element slice of slices. All hashv preconditions and
finite exits remain exactly those at that singleton, including an empty input. -/
def family (vectorFamily : Family)
    (input : ∀ index, Solanalib.Runtime.Bytes → vectorFamily.Args index) : Family where
  Index := vectorFamily.Index
  State := vectorFamily.State
  Args := fun _ => Solanalib.Runtime.Bytes
  Value := vectorFamily.Value
  Unwind := vectorFamily.Unwind
  Terminal := vectorFamily.Terminal
  contract := fun index => {
    requires := fun before bytes => (vectorFamily.contract index).requires before (input index
      bytes)
    post := fun before bytes => (vectorFamily.contract index).post before (input index bytes)
  }

def uninitialized : Family := family Syscall.family (fun _ bytes => [bytes])
def initialized : Family := family Initialized.family (fun _ bytes => [bytes])

def uninitializedRun : FamilyRun uninitialized :=
  fun index before bytes => Syscall.reference index before [bytes]
def initializedRun : FamilyRun initialized :=
  fun index before bytes => Initialized.reference index before [bytes]

theorem uninitialized_reference : FamilyReference uninitialized uninitializedRun := by
  intro index before bytes outcome ready called
  exact Syscall.reference_correct index before [bytes] outcome ready called

theorem initialized_reference : FamilyReference initialized initializedRun := by
  intro index before bytes outcome ready called
  exact Initialized.reference_correct index before [bytes] outcome ready called

theorem uninitialized_hasExecution :
    FamilyHasExecution uninitialized uninitializedRun Syscall.sample := by
  refine ⟨(), [1, 2, 3], .returned Hash.zero (), ?_, ?_⟩
  · intro reply after called
    cases called
    exact ⟨Hash.zero, rfl⟩
  · exact ⟨.returned ⟨0, some Hash.zero⟩ (), rfl, Hash.zero, rfl, rfl⟩

theorem initialized_hasExecution :
    FamilyHasExecution initialized initializedRun Initialized.sample :=
  ⟨(), [1, 2, 3], .returned Hash.zero (), True.intro,
    .returned ⟨7, Hash.zero⟩ (), rfl, rfl⟩

end Solanalib.Specs.Core.Hash.Single
