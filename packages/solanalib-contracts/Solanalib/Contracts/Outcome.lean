/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Contracts.Model

universe u v w x y

/-- Observable exits of a call. An ordinary `Result::Err` belongs in `Value`.
Unwinding carries the state actually supplied by the callback/binding; a
terminal exit supplies no invented post-state. Divergence is no finite exit. -/
inductive Outcome (State : Type u) (Value : Type v)
    (Unwind : Type w) (Terminal : Type x) where
  /-- An ordinary return with its actual state, including a Result error. -/
  | returned (value : Value) (state : State)
  /-- An unwinding exit with the state reached before propagation or cleanup. -/
  | unwound (reason : Unwind) (state : State)
  /-- A terminal exit that supplies no invented post-state. -/
  | terminated (reason : Terminal)

/-- The finite exits of a total mathematical reference interpretation.
Using this relation does not prove termination of a Rust implementation. -/
def returnsOf {State : Type u} {Args : Type v} {Value : Type w}
    {Unwind : Type x} {Terminal : Type y} (run : State → Args → Value × State)
    (before : State) (args : Args) : Outcome State Value Unwind Terminal → Prop
  | .returned value after => run before args = (value, after)
  | .unwound _ _ | .terminated _ => False

end Solanalib.Contracts.Model
