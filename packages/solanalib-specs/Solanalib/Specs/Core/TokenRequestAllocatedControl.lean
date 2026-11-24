/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestOnchain
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedControl

universe u v w x y

/-- A stateful SDK computation with explicit Result, unwind and terminal exits. -/
abbrev Run (State : Type u) (Value : Type v) (Unwind : Type w) (Terminal : Type x) :=
  State → Outcome State (Except Error Value) Unwind Terminal → Prop

/-- A pure successful local step. -/
def pure {State : Type u} {Value : Type v} {Unwind : Type w} {Terminal : Type x}
    (value : Value) : Run State Value Unwind Terminal :=
  fun state outcome => outcome = .returned (.ok value) state

/-- A source ProgramError exits normally, in the actual current state. -/
def fail {State : Type u} {Value : Type v} {Unwind : Type w} {Terminal : Type x}
    (error : Error) : Run State Value Unwind Terminal :=
  fun state outcome => outcome = .returned (.error error) state

/-- Return a computed source Result without assuming success. -/
def result {State : Type u} {Value : Type v} {Unwind : Type w} {Terminal : Type x}
    (value : Except Error Value) : Run State Value Unwind Terminal :=
  fun state outcome => outcome = .returned value state

/-- Read a represented local value from the actual state. Absence is a failed
representation, rather than an invented ProgramError or panic. -/
def inspect {State : Type u} {Value : Type v} {Unwind : Type w} {Terminal : Type x}
    (observe : State → Option Value) : Run State Value Unwind Terminal :=
  fun state outcome => ∃ value, observe state = some value ∧
    outcome = .returned (.ok value) state

/-- SDK question-mark sequencing: only Ok reaches the continuation; every
other exit preserves its exact error/reason and actual state. -/
def bind {State : Type u} {Value : Type v} {Next : Type y}
    {Unwind : Type w} {Terminal : Type x}
    (first : Run State Value Unwind Terminal)
    (next : Value → Run State Next Unwind Terminal) : Run State Next Unwind Terminal :=
  fun before outcome => ∃ intermediate, first before intermediate ∧
    match intermediate with
    | .returned (.ok value) state => next value state outcome
    | .returned (.error error) state => outcome = .returned (.error error) state
    | .unwound reason state => outcome = .unwound reason state
    | .terminated reason => outcome = .terminated reason

/-- Lift a concrete dependency call that cannot return ProgramError. -/
def perform {State : Type u} {Value : Type v} {Unwind : Type w} {Terminal : Type x}
    (call : State → Outcome State Value Unwind Terminal → Prop) :
    Run State Value Unwind Terminal :=
  fun before outcome => ∃ intermediate, call before intermediate ∧
    Outcome.map Except.ok intermediate = outcome

/-- A panic dependency has no normal value. It can only unwind or terminate,
and its state effects precede the cleanup of the caller. -/
def panic {State : Type u} {Value : Type v} {Unwind : Type w} {Terminal : Type x}
    (call : State → Outcome State Empty Unwind Terminal → Prop) :
    Run State Value Unwind Terminal :=
  fun before outcome => ∃ intermediate, call before intermediate ∧
    Outcome.map (fun impossible => nomatch impossible) intermediate = outcome

/-- Scope cleanup also runs after Result::Err. -/
def scope {State : Type u} {Value : Type v} {Unwind : Type w} {Terminal : Type x}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (body : Run State Value Unwind Terminal) : Run State Value Unwind Terminal :=
  fun before outcome => ∃ pending, body before pending ∧ Owned.cleanup double drops pending outcome

/-- A helper that returns an owned value moves it out only on Ok. Its retained
resources are cleaned on Err or unwind; a terminal exit bypasses cleanup. -/
def moveOnOk {State : Type u} {Value : Type v} {Unwind : Type w} {Terminal : Type x}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (drops : List (Owned.DropAction State Unwind Terminal))
    (body : Run State Value Unwind Terminal) : Run State Value Unwind Terminal :=
  fun before outcome => ∃ pending, body before pending ∧
    match pending with
    | .returned (.ok value) state => outcome = .returned (.ok value) state
    | .returned (.error _) _ | .unwound _ _ | .terminated _ =>
      Owned.cleanup double drops pending outcome

/-- Convert a preexisting pure state step while retaining the ambient state.
Local panic behavior is supplied through an Empty-valued dependency. -/
def fromStep {Extra : Type} {Value : Type} {Unwind Terminal : Type}
    (raise : Callback.Run (AccountInfo.State × Extra) Onchain.Panic Empty Unwind Terminal)
    (step : AccountInfo.State → Onchain.Step Value × AccountInfo.State) :
    Run (AccountInfo.State × Extra) Value Unwind Terminal :=
  fun before outcome =>
    let (value, after) := step before.1
    match value with
    | .success returned => outcome = .returned (.ok returned) (after, before.2)
    | .error error => outcome = .returned (.error error) (after, before.2)
    | .panic reason => panic (fun state => raise state reason) (after, before.2) outcome
    | .malformed => False

/-- A live shared Ref into an AccountInfo data cell, retaining the slice length
copied by the source borrow. Later byte reads follow the current guard. -/
structure DataRef where
  /-- The retained shared borrow identity. -/
  guard : Borrow.Guard
  /-- The source slice length copied when the Ref was acquired. -/
  length : Nat
  deriving DecidableEq, Repr

/-- Re-read the same retained data slice after a callback. A consumed guard,
wrong cell type or changed slice length is a representation failure. -/
def DataRef.read {Extra : Type} (reference : DataRef)
    (state : AccountInfo.State × Extra) : Option Bytes :=
  match Borrow.current state.1 reference.guard with
  | .ok (_, .data bytes) => if bytes.length = reference.length then some bytes else none
  | _ => none

/-- Actual shared-guard retirement; malformed mathematical guards do not
fabricate a successful destructor or a source ProgramError. -/
def DataRef.drop {Extra : Type} {Unwind Terminal : Type} (reference : DataRef) :
    Owned.DropAction (AccountInfo.State × Extra) Unwind Terminal :=
  fun before outcome =>
    match Borrow.release before.1 reference.guard with
    | (.ok (), after) => outcome = .returned () (after, before.2)
    | (.error _, _) => False

/-- Acquire the source data guard and retain its reference identity. Checked
conflicts return AccountBorrowFailed; unchecked conflicts call the panic
dependency. Both paths preserve the actual borrow state. -/
def borrow {Extra : Type} {Unwind Terminal : Type}
    (raise : Callback.Run (AccountInfo.State × Extra) Onchain.Panic Empty Unwind Terminal)
    (checked : Bool) (info : AccountInfo.Value) :
    Run (AccountInfo.State × Extra) DataRef Unwind Terminal :=
  fromStep raise fun state =>
    let (value, after) := Onchain.borrowData checked state info
    (match value with
      | .success borrowed => .success ⟨borrowed.guard, borrowed.bytes.length⟩
      | .error error => .error error
      | .panic reason => .panic reason
      | .malformed => .malformed, after)

/-- A DataRef scope releases its actual guard on ordinary return, Err or unwind. -/
def withData {Extra : Type} {Value : Type} {Unwind Terminal : Type}
    (raise : Callback.Run (AccountInfo.State × Extra) Onchain.Panic Empty Unwind Terminal)
    (double : Owned.DoubleUnwind (AccountInfo.State × Extra) Unwind Terminal)
    (checked : Bool) (info : AccountInfo.Value)
    (body : DataRef → Run (AccountInfo.State × Extra) Value Unwind Terminal) :
    Run (AccountInfo.State × Extra) Value Unwind Terminal :=
  bind (borrow raise checked info) fun reference =>
    scope double [reference.drop] (body reference)

/-- A normally returned dependency can be used without inventing preservation. -/
theorem perform_returned {State : Type u} {Value : Type v}
    {Unwind : Type w} {Terminal : Type x}
    (call : State → Outcome State Value Unwind Terminal → Prop)
    (before after : State) (value : Value)
    (called : call before (.returned value after)) :
    perform call before (.returned (.ok value) after) :=
  ⟨.returned value after, called, rfl⟩

/-- Result errors short-circuit a continuation with no assumption about it. -/
theorem bind_error {State : Type u} {Value : Type v} {Next : Type y}
    {Unwind : Type w} {Terminal : Type x}
    (first : Run State Value Unwind Terminal)
    (next : Value → Run State Next Unwind Terminal)
    (before after : State) (error : Error)
    (failed : first before (.returned (.error error) after)) :
    bind first next before (.returned (.error error) after) :=
  ⟨.returned (.error error) after, failed, rfl⟩

end Solanalib.Specs.Core.Token.AllocatedControl
