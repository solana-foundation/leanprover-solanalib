/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfo
public import Solanalib.Specs.Core.Callback
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountInfoRc

/-- The two Rc dependencies have different payload types despite sharing the
same abstract handle vocabulary. Their source field order is retained. -/
inductive Field where
  | lamports
  | data
  deriving DecidableEq, Repr

/-- Primitive dependencies for the `Rc<_, Global>` fields of AccountInfo. The
provider state carries the actual ownership multiplicity and count changes;
these operations do not model the Rc implementation. The selected clone can
abort on count overflow, but Global cloning supplies no unwind callback. The
payloads contain borrowed references, without a user-defined destructor. For
valid Global allocator behavior their field drops likewise do not unwind.
No normal return, count bound, resource release or allocator success is assumed.
Those claims require the corresponding dependency interpretation. -/
structure Ops (State Terminal : Type) where
  cloneRc : Callback.Run State (Field × Borrow.Handle) Unit Empty Terminal
  dropRc : Callback.Run State (Field × Borrow.Handle) Unit Empty Terminal

/-- The derived Clone of the SDK runs its lamports Rc clone before its data Rc
clone. Each call uses the actual prior state. A terminal exit stops immediately,
without inventing cleanup or a returned AccountInfo. -/
def cloneCall {State Terminal : Type} (ops : Ops State Terminal) :
    Callback.Run State AccountInfo.Value AccountInfo.Value Empty Terminal :=
  fun before info => Callback.bind
    (fun state (_ : Unit) => ops.cloneRc state (.lamports, info.lamports))
    (fun _ after => Callback.map (fun _ => AccountInfo.clone info)
      (fun state (_ : Unit) => ops.cloneRc state (.data, info.data)) after ())
    before ()

/-- A moved the Rc fields of AccountInfo drop in declaration order. The caller
chooses which owners are moved or retained; a handle is not itself an ownership
permission and this adapter cannot manufacture one. -/
def dropCall {State Terminal : Type} (ops : Ops State Terminal) :
    Callback.Run State AccountInfo.Value Unit Empty Terminal :=
  fun before info => Callback.bind
    (fun state (_ : Unit) => ops.dropRc state (.lamports, info.lamports))
    (fun _ after => ops.dropRc after (.data, info.data)) before ()

/-- Embed a dependency with no unwind exit into a surrounding callback type. -/
def liftOutcome {State Value Unwind Terminal : Type} :
    Outcome State Value Empty Terminal → Outcome State Value Unwind Terminal
  | .returned value after => .returned value after
  | .unwound impossible _ => nomatch impossible
  | .terminated reason => .terminated reason

/-- Lift only the outcome vocabulary; callback state and terminal outcomes
are unchanged, and no new dependency execution is supplied. -/
def lift {State Args Value Unwind Terminal : Type}
    (run : Callback.Run State Args Value Empty Terminal) :
    Callback.Run State Args Value Unwind Terminal :=
  fun before args outcome => ∃ produced, run before args produced ∧ liftOutcome produced = outcome

/-- A normal derived clone always returns the same cell and owner-reference
identities. This theorem says nothing about Rc implementation correctness. -/
theorem clone_identity {State Terminal : Type} (ops : Ops State Terminal)
    {before after : State} {info result : AccountInfo.Value}
    (run : cloneCall ops before info (.returned result after)) : result = info := by
  obtain ⟨first, _, rest⟩ := run
  cases first with
  | unwound impossible _ => nomatch impossible
  | terminated reason => cases rest
  | returned completed middle =>
    obtain ⟨second, _, returned⟩ := rest
    cases second with
    | unwound impossible _ => nomatch impossible
    | terminated reason => cases returned
    | returned completed final => cases returned; rfl

structure Types where
  State : Type
  Terminal : Type
  ops : Ops State Terminal

def cloneFamily : Family where
  Index := Types
  State := Types.State
  Args := fun _ => AccountInfo.Value
  Value := fun _ => AccountInfo.Value
  Unwind := fun _ => Empty
  Terminal := Types.Terminal
  contract := fun types => { requires := fun _ _ => True, post := cloneCall types.ops }

def cloneRun : FamilyRun cloneFamily := fun types => cloneCall types.ops

theorem clone_reference : FamilyReference cloneFamily cloneRun := by
  intro _ _ _ _ _ run
  exact run

/-- A trace witness for dependency scheduling. It is not an Rc counter model
and does not assert successful production allocation or reference counting. -/
inductive Event where
  | clone (field : Field) (cell : Borrow.Handle)
  | drop (field : Field) (cell : Borrow.Handle)
  deriving DecidableEq, Repr

def traceOps : Ops (List Event) String where
  cloneRc := Callback.ofFunction fun state (field, cell) =>
    .returned () (state ++ [.clone field cell])
  dropRc := Callback.ofFunction fun state (field, cell) =>
    .returned () (state ++ [.drop field cell])

def cloneSample : Types := ⟨List Event, String, traceOps⟩

theorem clone_execution : FamilyHasExecution cloneFamily cloneRun cloneSample := by
  exact ⟨[], AccountInfo.sampleInfo,
    .returned AccountInfo.sampleInfo [.clone .lamports ⟨0⟩, .clone .data ⟨1⟩], trivial,
    .returned () [.clone .lamports ⟨0⟩], rfl,
    .returned () [.clone .lamports ⟨0⟩, .clone .data ⟨1⟩], rfl, rfl⟩

end Solanalib.Specs.Core.AccountInfoRc
