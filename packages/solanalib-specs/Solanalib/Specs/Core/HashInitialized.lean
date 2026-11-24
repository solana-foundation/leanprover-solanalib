/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.HashSyscall

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Hash.Initialized

/-- Earlier wrappers start with a fully initialized zero array. The reply
observes the whole final buffer, retaining zeros at bytes the provider leaves
untouched. This is distinct from the admission premise of the MaybeUninit wrapper. -/
structure Reply where
  status : UInt64
  output : Hash.Value

def request (slices : List Solanalib.Runtime.Bytes) : Syscall.Request :=
  ⟨slices, UInt64.ofNat slices.length, some Hash.zero⟩

structure Index where
  State : Type
  Unwind : Type
  Terminal : Type
  provider : Callback.Run State Syscall.Request Reply Unwind Terminal

def run (index : Index) :
    Callback.Run index.State (List Solanalib.Runtime.Bytes) Hash.Value index.Unwind index.Terminal
      :=
  fun before slices => Callback.map Reply.output index.provider before (request slices)

/-- Status is ignored; every complete final buffer and every abnormal provider
exit is retained. No initialized-output or digest-correctness premise is added. -/
def post (index : Index) (before : index.State) (slices : List Solanalib.Runtime.Bytes) :
    Outcome index.State Hash.Value index.Unwind index.Terminal → Prop
  | .returned hash after =>
      ∃ status, index.provider before (request slices) (.returned ⟨status, hash⟩ after)
  | .unwound reason after => index.provider before (request slices) (.unwound reason after)
  | .terminated reason => index.provider before (request slices) (.terminated reason)

theorem run_iff_post (index : Index) (before : index.State) (slices : List Solanalib.Runtime.Bytes)
    (outcome : Outcome index.State Hash.Value index.Unwind index.Terminal) :
    run index before slices outcome ↔ post index before slices outcome := by
  constructor
  · rintro ⟨actual, called, rfl⟩
    cases actual with
    | returned reply after => exact ⟨reply.status, called⟩
    | unwound reason after => exact called
    | terminated reason => exact called
  · intro called
    cases outcome with
    | returned hash after =>
      obtain ⟨status, called⟩ := called
      exact ⟨.returned ⟨status, hash⟩ after, called, rfl⟩
    | unwound reason after => exact ⟨.unwound reason after, called, rfl⟩
    | terminated reason => exact ⟨.terminated reason, called, rfl⟩

def family : Family where
  Index := Index
  State := Index.State
  Args := fun _ => List Solanalib.Runtime.Bytes
  Value := fun _ => Hash.Value
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => { requires := fun _ _ => True, post := post index }

def reference : FamilyRun family := run

theorem reference_correct : FamilyReference family reference := by
  intro index before slices outcome _ called
  exact (run_iff_post index before slices outcome).mp called

def sample : Index where
  State := Unit
  Unwind := Empty
  Terminal := Empty
  provider := Callback.ofFunction fun before _ => .returned ⟨7, Hash.zero⟩ before

theorem sample_hasExecution : FamilyHasExecution family reference sample :=
  ⟨(), [[1], [], [2]], .returned Hash.zero (), True.intro,
    .returned ⟨7, Hash.zero⟩ (), rfl, rfl⟩

end Solanalib.Specs.Core.Hash.Initialized
