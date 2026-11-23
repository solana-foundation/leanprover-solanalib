/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Log
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLog

/-- Anchor 1.0.2 uses a Solana syscall or a host `black_box`, unlike the separate host stub of the
solana-program logging wrapper. -/
inductive Target where
  | solana
  | host
  deriving DecidableEq, Repr

/-- The chosen cfg and actual logging backend of the wrapper are explicit. Nested
field boundaries, callback effects and all callback exits are retained. -/
structure Index where
  State : Type
  Unwind : Type
  Terminal : Type
  target : Target
  sink : Callback.Run State Log.Event Unit Unwind Terminal

/-- The host branch calls no logging backend. Solana forwards each binary
field boundary to the explicit sink and retains the actual outcome of that sink. -/
def call (index : Index) :
    Callback.Run index.State (List _root_.Solanalib.Runtime.Bytes) Unit index.Unwind index.Terminal
      :=
  fun state fields outcome => match index.target with
    | .solana => Log.dataCall .solana index.sink state fields outcome
    | .host => outcome = .returned () state

def family : Family where
  Index := Index
  State := fun i => i.State
  Args := fun _ => List _root_.Solanalib.Runtime.Bytes
  Value := fun _ => Unit
  Unwind := fun i => i.Unwind
  Terminal := fun i => i.Terminal
  contract := fun i => {
    requires := fun _ _ => True
    post := call i }

def run : FamilyRun family := call

theorem reference : FamilyReference family run := by
  intro _ _ _ _ _ step
  exact step

def sample : Index :=
  ⟨List Log.Event, String, String, .solana, Callback.ofFunction Log.appendEvent⟩

theorem execution : FamilyHasExecution family run sample := by
  exact ⟨([] : List Log.Event), [[], [1, 2]],
    .returned () ([.data [[], [1, 2]]] : List Log.Event), trivial, rfl⟩

end Solanalib.Specs.Core.AnchorLog
