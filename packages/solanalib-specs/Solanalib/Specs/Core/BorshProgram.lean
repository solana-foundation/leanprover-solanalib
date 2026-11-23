/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Callback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borsh

universe u v w x y

/-- A finite request program. A borsh member is written once as a program over
its dependency requests (element trait calls, `write_all`, allocation calls);
references, executable functions and pure evaluation interpret the same term. -/
inductive Program (Req : Type) (Resp : Req → Type) (α : Type) : Type where
  | pure (value : α)
  | call (request : Req) (next : Resp request → Program Req Resp α)

namespace Program

variable {Req : Type} {Resp : Req → Type}

def bind {α β : Type} : Program Req Resp α → (α → Program Req Resp β) → Program Req Resp β
  | .pure value, next => next value
  | .call request rest, next => .call request (fun response => bind (rest response) next)

instance : Monad (Program Req Resp) where
  pure := .pure
  bind := bind

/-- Issue one request and return its response. -/
def request (r : Req) : Program Req Resp (Resp r) := .call r .pure

/-- Relational interpretation. Each request runs the supplied callback relation
in the actual current state; the continuation sees the actual response and
state. Unwind and terminal exits stop the program unchanged. -/
def Runs {State : Type u} {Unwind : Type w} {Terminal : Type x} {α : Type}
    (handler : (r : Req) → State → Outcome State (Resp r) Unwind Terminal → Prop) :
    Program Req Resp α → State → Outcome State α Unwind Terminal → Prop
  | .pure value, before, outcome => outcome = .returned value before
  | .call r next, before, outcome => ∃ intermediate, handler r before intermediate ∧
      match intermediate with
      | .returned response state => Runs handler (next response) state outcome
      | .unwound reason state => outcome = .unwound reason state
      | .terminated reason => outcome = .terminated reason

/-- Executable interpretation with function callbacks. -/
def run {State : Type u} {Unwind : Type w} {Terminal : Type x} {α : Type}
    (handler : (r : Req) → State → Outcome State (Resp r) Unwind Terminal) :
    Program Req Resp α → State → Outcome State α Unwind Terminal
  | .pure value, before => .returned value before
  | .call r next, before => Outcome.bind (handler r before)
      (fun response state => run handler (next response) state)

/-- State-free evaluation with total responses. -/
def eval {α : Type} (respond : (r : Req) → Resp r) : Program Req Resp α → α
  | .pure value => value
  | .call r next => eval respond (next (respond r))

theorem runs_pure {State : Type u} {Unwind : Type w} {Terminal : Type x} {α : Type}
    (handler : (r : Req) → State → Outcome State (Resp r) Unwind Terminal → Prop)
    (value : α) (before : State) (outcome : Outcome State α Unwind Terminal) :
    Runs handler (.pure value) before outcome ↔ outcome = .returned value before := by
  rw [Runs]

theorem runs_call {State : Type u} {Unwind : Type w} {Terminal : Type x} {α : Type}
    (handler : (r : Req) → State → Outcome State (Resp r) Unwind Terminal → Prop)
    (r : Req) (next : Resp r → Program Req Resp α) (before : State)
    (outcome : Outcome State α Unwind Terminal) :
    Runs handler (.call r next) before outcome ↔ ∃ intermediate, handler r before intermediate ∧
      match intermediate with
      | .returned response state => Runs handler (next response) state outcome
      | .unwound reason state => outcome = .unwound reason state
      | .terminated reason => outcome = .terminated reason := by
  rw [Runs]

/-- The relational interpretation at function-graph callbacks is the graph of
the executable interpretation. -/
theorem runs_ofFunction_iff {State : Type u} {Unwind : Type w} {Terminal : Type x} {α : Type}
    (handler : (r : Req) → State → Outcome State (Resp r) Unwind Terminal)
    (program : Program Req Resp α) (before : State)
    (outcome : Outcome State α Unwind Terminal) :
    Runs (fun r before outcome => handler r before = outcome) program before outcome ↔
      run handler program before = outcome := by
  induction program generalizing before with
  | pure value => exact eq_comm
  | call r next ih =>
    simp only [Runs, run]
    constructor
    · rintro ⟨intermediate, rfl, rest⟩
      cases h : handler r before with
      | returned response state =>
        rw [h] at rest
        exact (ih response state).1 rest
      | unwound reason state => rw [h] at rest; exact rest.symm
      | terminated reason => rw [h] at rest; exact rest.symm
    · intro result
      refine ⟨handler r before, rfl, ?_⟩
      cases h : handler r before with
      | returned response state =>
        rw [h] at result
        exact (ih response state).2 result
      | unwound reason state => rw [h] at result; exact result.symm
      | terminated reason => rw [h] at result; exact result.symm

/-- Total responses that never change state agree with pure evaluation. -/
theorem run_pure_handler {State : Type u} {Unwind : Type w} {Terminal : Type x} {α : Type}
    (respond : (r : Req) → Resp r) (program : Program Req Resp α) (before : State) :
    run (Unwind := Unwind) (Terminal := Terminal)
        (fun r state => .returned (respond r) state) program before =
      .returned (eval respond program) before := by
  induction program with
  | pure value => rfl
  | call r next ih => exact ih (respond r)

end Program

end Solanalib.Specs.Core.Borsh
