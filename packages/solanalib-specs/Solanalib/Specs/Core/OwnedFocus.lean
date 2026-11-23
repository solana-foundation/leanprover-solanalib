/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Owned

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Owned

universe u v w x y z

/-- A lawful projection of mathematical state. It describes neither source
memory layout nor pointer access. Updating the focus preserves the surrounding
state exactly as specified by `set`. -/
structure Focus (Outer : Type u) (Inner : Type v) where
  /-- Observe the selected component. -/
  get : Outer → Inner
  /-- Replace just the selected component. -/
  set : Outer → Inner → Outer
  /-- The replacement is the component subsequently observed. -/
  get_set : ∀ outer inner, get (set outer inner) = inner
  /-- Replacing the component by itself changes no state. -/
  set_get : ∀ outer, set outer (get outer) = outer
  /-- A later replacement supersedes the earlier one. -/
  set_set : ∀ outer first second, set (set outer first) second = set outer second

/-- Focus the first component of a pair of independent mathematical states. -/
def Focus.fst {Left : Type u} {Right : Type v} : Focus (Left × Right) Left where
  get := Prod.fst
  set := fun outer inner => (inner, outer.2)
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Focus the second component of a pair of independent mathematical states. -/
def Focus.snd {Left : Type u} {Right : Type v} : Focus (Left × Right) Right where
  get := Prod.snd
  set := fun outer inner => (outer.1, inner)
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Compose two lawful mathematical projections. -/
def Focus.comp {Outer : Type u} {Middle : Type v} {Inner : Type w}
    (outer : Focus Outer Middle) (inner : Focus Middle Inner) : Focus Outer Inner where
  get := fun state => inner.get (outer.get state)
  set := fun state value => outer.set state (inner.set (outer.get state) value)
  get_set := by intro state value; rw [outer.get_set, inner.get_set]
  set_get := by intro state; rw [inner.set_get, outer.set_get]
  set_set := by intro state first second; rw [outer.get_set, inner.set_set, outer.set_set]

/-- Preserve the exact value, exit kind and actual state of an inner callback while
putting its finite post-state back into the surrounding mathematical state. -/
def Focus.liftOutcome {Outer : Type u} {Inner : Type v} {Value : Type w}
    {Unwind : Type x} {Terminal : Type y} (focus : Focus Outer Inner) (before : Outer) :
    Outcome Inner Value Unwind Terminal → Outcome Outer Value Unwind Terminal
  | .returned value after => .returned value (focus.set before after)
  | .unwound reason after => .unwound reason (focus.set before after)
  | .terminated reason => .terminated reason

/-- Lift only outcomes of the supplied inner dependency. The surrounding
state is never freely chosen, on ordinary returns or on unwinds. -/
def Focus.lift {Outer : Type u} {Inner : Type v} {Args : Type w} {Value : Type z}
    {Unwind : Type x} {Terminal : Type y} (focus : Focus Outer Inner)
    (run : Callback.Run Inner Args Value Unwind Terminal) :
    Callback.Run Outer Args Value Unwind Terminal :=
  fun before args outcome => ∃ inner, run (focus.get before) args inner ∧
    focus.liftOutcome before inner = outcome

/-- Focus vector operations into a surrounding mathematical state. Current
observations use the actual focused state, and unwind effects are reinserted
just as normal effects are. -/
def VectorOps.focus {Outer : Type u} {Inner : Type v} {Element : Type w}
    {Resource : Type z} {Unwind : Type x} {Terminal : Type y}
    (ops : VectorOps Inner Element Resource Unwind Terminal) (part : Focus Outer Inner) :
    VectorOps Outer Element Resource Unwind Terminal where
  current := fun state resource => ops.current (part.get state) resource
  empty := fun before =>
    let (resource, after) := ops.empty (part.get before)
    (resource, part.set before after)
  withCapacity := part.lift ops.withCapacity
  fromList := part.lift ops.fromList
  push := part.lift ops.push
  extend := part.lift ops.extend
  drop := part.lift ops.drop

/-- A real inner return supplies the corresponding focused return. -/
theorem Focus.lift_returned {Outer : Type u} {Inner : Type v} {Args : Type w} {Value : Type z}
    {Unwind : Type x} {Terminal : Type y} (focus : Focus Outer Inner)
    (run : Callback.Run Inner Args Value Unwind Terminal) (before : Outer)
    (args : Args) (value : Value) (after : Inner)
    (called : run (focus.get before) args (.returned value after)) :
    focus.lift run before args (.returned value (focus.set before after)) :=
  ⟨.returned value after, called, rfl⟩

/-- A real inner unwind retains its reason and actual focused post-state. -/
theorem Focus.lift_unwound {Outer : Type u} {Inner : Type v} {Args : Type w} {Value : Type z}
    {Unwind : Type x} {Terminal : Type y} (focus : Focus Outer Inner)
    (run : Callback.Run Inner Args Value Unwind Terminal) (before : Outer)
    (args : Args) (reason : Unwind) (after : Inner)
    (called : run (focus.get before) args (.unwound reason after)) :
    focus.lift run before args (.unwound reason (focus.set before after)) :=
  ⟨.unwound reason after, called, rfl⟩

/-- A real inner terminal exit remains terminal without a fabricated state. -/
theorem Focus.lift_terminated {Outer : Type u} {Inner : Type v} {Args : Type w} {Value : Type z}
    {Unwind : Type x} {Terminal : Type y} (focus : Focus Outer Inner)
    (run : Callback.Run Inner Args Value Unwind Terminal) (before : Outer)
    (args : Args) (reason : Terminal)
    (called : run (focus.get before) args (.terminated reason)) :
    focus.lift run before args (.terminated reason) :=
  ⟨.terminated reason, called, rfl⟩

end Solanalib.Specs.Core.Owned
