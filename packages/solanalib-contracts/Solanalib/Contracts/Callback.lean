/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Contracts.Outcome

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Contracts.Model

universe u v w x y z

namespace Outcome

/-- Change only an ordinary return value. Callback state, unwind state, and
terminal reasons are retained exactly. -/
def map {State : Type u} {Value : Type v} {Next : Type w}
    {Unwind : Type x} {Terminal : Type y} (f : Value → Next) :
    Outcome State Value Unwind Terminal → Outcome State Next Unwind Terminal
  | .returned value state => .returned (f value) state
  | .unwound reason state => .unwound reason state
  | .terminated reason => .terminated reason

/-- Run the continuation only after an ordinary return, in the actual state
returned by the first callback. A `Result::Err` is still an ordinary value;
its early-return policy belongs to the caller. -/
def bind {State : Type u} {Value : Type v} {Next : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (outcome : Outcome State Value Unwind Terminal)
    (next : Value → State → Outcome State Next Unwind Terminal) :
    Outcome State Next Unwind Terminal :=
  match outcome with
  | .returned value state => next value state
  | .unwound reason state => .unwound reason state
  | .terminated reason => .terminated reason

@[simp] theorem map_returned {State : Type u} {Value : Type v} {Next : Type w}
    {Unwind : Type x} {Terminal : Type y} (f : Value → Next)
    (value : Value) (state : State) :
    map f (.returned value state : Outcome State Value Unwind Terminal) =
      .returned (f value) state := rfl

@[simp] theorem map_unwound {State : Type u} {Value : Type v} {Next : Type w}
    {Unwind : Type x} {Terminal : Type y} (f : Value → Next)
    (reason : Unwind) (state : State) :
    map f (.unwound reason state : Outcome State Value Unwind Terminal) =
      .unwound reason state := rfl

@[simp] theorem map_terminated {State : Type u} {Value : Type v} {Next : Type w}
    {Unwind : Type x} {Terminal : Type y} (f : Value → Next) (reason : Terminal) :
    map f (.terminated reason : Outcome State Value Unwind Terminal) =
      .terminated reason := rfl

@[simp] theorem map_id {State : Type u} {Value : Type v}
    {Unwind : Type x} {Terminal : Type y}
    (outcome : Outcome State Value Unwind Terminal) : map id outcome = outcome := by
  cases outcome <;> rfl

theorem map_map {State : Type u} {Value : Type v} {Next : Type w} {Last : Type z}
    {Unwind : Type x} {Terminal : Type y} (f : Value → Next) (g : Next → Last)
    (outcome : Outcome State Value Unwind Terminal) :
    map g (map f outcome) = map (g ∘ f) outcome := by
  cases outcome <;> rfl

@[simp] theorem bind_returned {State : Type u} {Value : Type v} {Next : Type w}
    {Unwind : Type x} {Terminal : Type y} (value : Value) (state : State)
    (next : Value → State → Outcome State Next Unwind Terminal) :
    bind (.returned value state) next = next value state := rfl

@[simp] theorem bind_unwound {State : Type u} {Value : Type v} {Next : Type w}
    {Unwind : Type x} {Terminal : Type y} (reason : Unwind) (state : State)
    (next : Value → State → Outcome State Next Unwind Terminal) :
    bind (.unwound reason state) next = .unwound reason state := rfl

@[simp] theorem bind_terminated {State : Type u} {Value : Type v} {Next : Type w}
    {Unwind : Type x} {Terminal : Type y} (reason : Terminal)
    (next : Value → State → Outcome State Next Unwind Terminal) :
    bind (.terminated reason) next = .terminated reason := rfl

@[simp] theorem bind_return {State : Type u} {Value : Type v}
    {Unwind : Type x} {Terminal : Type y}
    (outcome : Outcome State Value Unwind Terminal) :
    bind outcome (fun value state => .returned value state) = outcome := by
  cases outcome <;> rfl

theorem bind_assoc {State : Type u} {Value : Type v} {Next : Type w} {Last : Type z}
    {Unwind : Type x} {Terminal : Type y}
    (outcome : Outcome State Value Unwind Terminal)
    (next : Value → State → Outcome State Next Unwind Terminal)
    (last : Next → State → Outcome State Last Unwind Terminal) :
    bind (bind outcome next) last =
      bind outcome (fun value state => bind (next value state) last) := by
  cases outcome <;> rfl

end Outcome

namespace Callback

/-- An explicit finite-exit callback relation. It can describe partial writes,
ordinary errors, unwinding effects and terminal exits without inventing state. -/
abbrev Run (State : Type u) (Args : Type v) (Value : Type w)
    (Unwind : Type x) (Terminal : Type y) :=
  State → Args → Outcome State Value Unwind Terminal → Prop

/-- The graph of a concrete mathematical callback interpretation. -/
def ofFunction {State : Type u} {Args : Type v} {Value : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (run : State → Args → Outcome State Value Unwind Terminal) :
    Run State Args Value Unwind Terminal :=
  fun before args outcome => run before args = outcome

/-- Forward every callback exit while transforming only its return value. -/
def map {State : Type u} {Args : Type v} {Value : Type w} {Next : Type z}
    {Unwind : Type x} {Terminal : Type y} (f : Value → Next)
    (run : Run State Args Value Unwind Terminal) : Run State Args Next Unwind Terminal :=
  fun before args outcome =>
    ∃ intermediate, run before args intermediate ∧ Outcome.map f intermediate = outcome

/-- Relational callback sequencing. The continuation receives the actual
return value and state; it is not called after an unwind or terminal exit. -/
def bind {State : Type u} {Args : Type v} {Value : Type w} {Next : Type z}
    {Unwind : Type x} {Terminal : Type y}
    (run : Run State Args Value Unwind Terminal)
    (next : Value → State → Outcome State Next Unwind Terminal → Prop) :
    Run State Args Next Unwind Terminal :=
  fun before args outcome => ∃ intermediate, run before args intermediate ∧
    match intermediate with
    | .returned value state => next value state outcome
    | .unwound reason state => outcome = .unwound reason state
    | .terminated reason => outcome = .terminated reason

theorem map_ofFunction {State : Type u} {Args : Type v} {Value : Type w} {Next : Type z}
    {Unwind : Type x} {Terminal : Type y} (f : Value → Next)
    (run : State → Args → Outcome State Value Unwind Terminal)
    (before : State) (args : Args) (outcome : Outcome State Next Unwind Terminal) :
    map f (ofFunction run) before args outcome ↔
      Outcome.map f (run before args) = outcome := by
  constructor
  · rintro ⟨intermediate, rfl, result⟩
    exact result
  · intro result
    exact ⟨run before args, rfl, result⟩

theorem bind_ofFunction {State : Type u} {Args : Type v} {Value : Type w} {Next : Type z}
    {Unwind : Type x} {Terminal : Type y}
    (run : State → Args → Outcome State Value Unwind Terminal)
    (next : Value → State → Outcome State Next Unwind Terminal)
    (before : State) (args : Args) (outcome : Outcome State Next Unwind Terminal) :
    bind (ofFunction run) (fun value state result => next value state = result)
        before args outcome ↔
      Outcome.bind (run before args) next = outcome := by
  constructor
  · rintro ⟨intermediate, rfl, result⟩
    cases h : run before args <;> simpa only [h, Outcome.bind, eq_comm] using result
  · intro result
    refine ⟨run before args, rfl, ?_⟩
    cases h : run before args <;> simpa only [h, Outcome.bind, eq_comm] using result

end Callback

end Solanalib.Contracts.Model
