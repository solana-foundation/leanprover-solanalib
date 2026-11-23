/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoRc

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorToInfo

/-- AsRef is a generic trait callback; the two following Rc clones are
separate dependency operations of the concrete Clone implementation of AccountInfo. -/
structure Types where
  State : Type
  Input : Type
  Unwind : Type
  Terminal : Type
  asRef : Callback.Run State Input AccountInfo.Value Unwind Terminal
  rc : AccountInfoRc.Ops State Terminal

/-- Evaluate AsRef first, then clone the returned AccountInfo in its actual
post-state. An AsRef unwind skips both clones; an Rc terminal skips later work. -/
def run (types : Types) :
    Callback.Run types.State types.Input AccountInfo.Value types.Unwind types.Terminal :=
  Callback.bind types.asRef fun info after =>
    AccountInfoRc.lift (AccountInfoRc.cloneCall types.rc) after info

def family : Family where
  Index := Types
  State := Types.State
  Args := Types.Input
  Value := fun _ => AccountInfo.Value
  Unwind := Types.Unwind
  Terminal := Types.Terminal
  contract := fun types => { requires := fun _ _ => True, post := run types }

def reference : FamilyRun family := run

theorem reference_holds : FamilyReference family reference := by
  intro _ _ _ _ _ step
  exact step

inductive Event where
  | asRef
  | rc (event : AccountInfoRc.Event)
  deriving DecidableEq, Repr

def sample : Types where
  State := List Event
  Input := Unit
  Unwind := String
  Terminal := String
  asRef := Callback.ofFunction fun before _ => .returned AccountInfo.sampleInfo (before ++ [.asRef])
  rc := {
    cloneRc := Callback.ofFunction fun state (field, handle) =>
      .returned () (state ++ [.rc (.clone field handle)])
    dropRc := Callback.ofFunction fun state (field, handle) =>
      .returned () (state ++ [.rc (.drop field handle)]) }

def sampleTrace : List Event :=
  [.asRef, .rc (.clone .lamports ⟨0⟩), .rc (.clone .data ⟨1⟩)]

theorem sample_run : run sample [] () (.returned AccountInfo.sampleInfo sampleTrace) := by
  refine ⟨.returned AccountInfo.sampleInfo [.asRef], rfl, ?_⟩
  refine ⟨.returned AccountInfo.sampleInfo sampleTrace, ?_, rfl⟩
  exact ⟨.returned () [.asRef, .rc (.clone .lamports ⟨0⟩)], rfl,
    .returned () sampleTrace, rfl, rfl⟩

theorem reference_execution : FamilyHasExecution family reference sample :=
  ⟨[], (), .returned AccountInfo.sampleInfo sampleTrace, trivial, sample_run⟩

end Solanalib.Specs.Core.AnchorToInfo
