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

universe u v w x y

/-- Execute retained resource drops in the exact supplied source order. Normal
drop returns thread the current state. A first unwind replaces an ordinary
pending return; a second unwind invokes the explicit terminal-only policy.
Every terminal exit stops immediately, without inventing later cleanup. -/
def cleanup {State : Type u} {Value : Type v} {Unwind : Type x} {Terminal : Type y}
    (double : DoubleUnwind State Unwind Terminal) :
    List (DropAction State Unwind Terminal) →
      Outcome State Value Unwind Terminal → Outcome State Value Unwind Terminal → Prop
  | [], pending, final => final = pending
  | action :: rest, .returned value state, final =>
    ∃ dropped, action state dropped ∧
      match dropped with
      | .returned () after => cleanup double rest (.returned value after) final
      | .unwound reason after => cleanup double rest (.unwound reason after) final
      | .terminated reason => final = .terminated reason
  | action :: rest, .unwound original state, final =>
    ∃ dropped, action state dropped ∧
      match dropped with
      | .returned () after => cleanup double rest (.unwound original after) final
      | .unwound reason after =>
        ∃ terminal, double after original reason terminal ∧ final = .terminated terminal
      | .terminated reason => final = .terminated reason
  | _ :: _, .terminated reason, final => final = .terminated reason

/-- Protect retained resources during construction: a returned value transfers
ownership to its continuation, an unwind cleans the resources, and a terminal
exit performs no cleanup. -/
def onUnwind {State : Type u} {Value : Type v} {Unwind : Type x} {Terminal : Type y}
    (double : DoubleUnwind State Unwind Terminal)
    (drops : List (DropAction State Unwind Terminal))
    (pending final : Outcome State Value Unwind Terminal) : Prop :=
  match pending with
  | .returned value state => final = .returned value state
  | .unwound _ _ | .terminated _ => cleanup double drops pending final

/-- Run a body followed by source-ordered scope cleanup on every nonterminal
finite exit, including an ordinary `Result::Err`. -/
def scope {State : Type u} {Args : Type w} {Value : Type v}
    {Unwind : Type x} {Terminal : Type y}
    (double : DoubleUnwind State Unwind Terminal)
    (drops : List (DropAction State Unwind Terminal))
    (body : Callback.Run State Args Value Unwind Terminal) :
    Callback.Run State Args Value Unwind Terminal :=
  fun before args final => ∃ pending, body before args pending ∧ cleanup double drops pending final

/-- Run a constructor body under unwind protection while allowing normal
return to move the retained resources, with their exact identities and state. -/
def protect {State : Type u} {Args : Type w} {Value : Type v}
    {Unwind : Type x} {Terminal : Type y}
    (double : DoubleUnwind State Unwind Terminal)
    (drops : List (DropAction State Unwind Terminal))
    (body : Callback.Run State Args Value Unwind Terminal) :
    Callback.Run State Args Value Unwind Terminal :=
  fun before args final => ∃ pending, body before args pending ∧ onUnwind double drops pending final

/-- An empty cleanup list preserves the exact pending outcome. -/
theorem cleanup_nil {State : Type u} {Value : Type v} {Unwind : Type x} {Terminal : Type y}
    (double : DoubleUnwind State Unwind Terminal)
    (pending final : Outcome State Value Unwind Terminal) :
    cleanup double [] pending final ↔ final = pending := Iff.rfl

/-- A terminal body exit does not call even the first retained destructor. -/
theorem cleanup_terminated {State : Type u} {Value : Type v}
    {Unwind : Type x} {Terminal : Type y}
    (double : DoubleUnwind State Unwind Terminal)
    (drops : List (DropAction State Unwind Terminal)) (reason : Terminal)
    (final : Outcome State Value Unwind Terminal) :
    cleanup double drops (.terminated reason) final ↔ final = .terminated reason := by
  cases drops <;> rfl

/-- A normally returned constructor value moves out without being dropped. -/
theorem onUnwind_returned {State : Type u} {Value : Type v}
    {Unwind : Type x} {Terminal : Type y}
    (double : DoubleUnwind State Unwind Terminal)
    (drops : List (DropAction State Unwind Terminal)) (value : Value) (state : State)
    (final : Outcome State Value Unwind Terminal) :
    onUnwind double drops (.returned value state) final ↔
      final = .returned value state := Iff.rfl

/-- A terminal constructor exit has no unwind-cleanup side channel. -/
theorem onUnwind_terminated {State : Type u} {Value : Type v}
    {Unwind : Type x} {Terminal : Type y}
    (double : DoubleUnwind State Unwind Terminal)
    (drops : List (DropAction State Unwind Terminal)) (reason : Terminal)
    (final : Outcome State Value Unwind Terminal) :
    onUnwind double drops (.terminated reason) final ↔ final = .terminated reason :=
  cleanup_terminated double drops reason final

/-- An actual sequence of normally returning drops, retaining each intermediate
state and the source-supplied ordering. -/
inductive DropReturns {State : Type u} {Unwind : Type x} {Terminal : Type y} :
    List (DropAction State Unwind Terminal) → State → State → Prop
  /-- No remaining destructor changes the state. -/
  | nil (state : State) : DropReturns [] state state
  /-- The head destructor runs before the remaining ones, in the actual state
  returned by that destructor. -/
  | cons (action : DropAction State Unwind Terminal)
      (rest : List (DropAction State Unwind Terminal)) (before middle after : State)
      (head : action before (.returned () middle))
      (tail : DropReturns rest middle after) : DropReturns (action :: rest) before after

/-- Actual normal destructor executions suffice to retain the pending return
value, while the final state is the state after all those executions. -/
theorem DropReturns.cleanup_returned {State : Type u} {Value : Type v}
    {Unwind : Type x} {Terminal : Type y}
    {drops : List (DropAction State Unwind Terminal)} {before after : State}
    (trace : DropReturns drops before after) (double : DoubleUnwind State Unwind Terminal)
    (value : Value) : cleanup double drops (.returned value before) (.returned value after) := by
  induction trace with
  | nil => rfl
  | cons action rest before middle after head tail induction =>
    exact ⟨.returned () middle, head, induction⟩

/-- Normal cleanup during an unwind preserves its original reason and records
the actual final cleanup state. -/
theorem DropReturns.cleanup_unwound {State : Type u} {Value : Type v}
    {Unwind : Type x} {Terminal : Type y}
    {drops : List (DropAction State Unwind Terminal)} {before after : State}
    (trace : DropReturns drops before after) (double : DoubleUnwind State Unwind Terminal)
    (reason : Unwind) : cleanup double drops
      (.unwound reason before : Outcome State Value Unwind Terminal) (.unwound reason after) := by
  induction trace with
  | nil => rfl
  | cons action rest before middle after head tail induction =>
    exact ⟨.returned () middle, head, induction⟩

/-- A second unwind can only use an explicitly supplied terminal result, and
does not proceed to the remaining destructors. -/
theorem cleanup_double_unwind {State : Type u} {Value : Type v}
    {Unwind : Type x} {Terminal : Type y}
    (double : DoubleUnwind State Unwind Terminal)
    (action : DropAction State Unwind Terminal) (rest : List (DropAction State Unwind Terminal))
    (before after : State) (original later : Unwind) (terminal : Terminal)
    (dropped : action before (.unwound later after))
    (abort : double after original later terminal) :
    cleanup double (action :: rest) (.unwound original before : Outcome State Value Unwind Terminal)
      (.terminated terminal) :=
  ⟨.unwound later after, dropped, terminal, abort, rfl⟩

end Solanalib.Specs.Core.Owned
