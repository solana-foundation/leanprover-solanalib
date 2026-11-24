/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Contracts.Outcome

@[expose] public section

set_option autoImplicit false

universe u v w

/-- One pure model relation for every finite exit. This is supporting mathematical
data, not the canonical implementation specification of a Rust function. -/
structure Solanalib.Contracts.Model (State : Type u) (Args : Type v) (Value : Type w)
    (Unwind : Type := Empty) (Terminal : Type := Empty) where
  /-- The admissible initial states and function arguments. -/
  requires : State → Args → Prop
  /-- The permitted finite outcomes from those initial observations. -/
  post : State → Args → Solanalib.Contracts.Model.Outcome State Value Unwind Terminal → Prop

/-- Some state and arguments meet the precondition. This rules out a vacuous
precondition; it does not assert that an interpretation returns. -/
def Solanalib.Contracts.Model.Satisfiable {State : Type u} {Args : Type v} {Value : Type w}
    {Unwind Terminal : Type}
    (contract : Solanalib.Contracts.Model State Args Value Unwind Terminal) : Prop :=
  ∃ before args, contract.requires before args

/-- All exits produced by an interpretation satisfy the model contract.
Neither determinism nor progress follows from this partial-correctness relation. -/
def Solanalib.Contracts.Model.Holds {State : Type u} {Args : Type v} {Value : Type w}
    {Unwind Terminal : Type}
    (contract : Solanalib.Contracts.Model State Args Value Unwind Terminal)
    (run : State → Args → Solanalib.Contracts.Model.Outcome State Value Unwind Terminal → Prop) :
      Prop :=
  ∀ before args outcome, contract.requires before args → run before args outcome →
    contract.post before args outcome

/-- A reference relation has an actual finite execution at a permitted input.
Unlike `Holds`, this excludes an everywhere-empty reference relation. It does
not assert termination, progress at every input, or a Rust implementation. -/
def Solanalib.Contracts.Model.HasExecution {State : Type u} {Args : Type v} {Value : Type w}
    {Unwind Terminal : Type}
    (contract : Solanalib.Contracts.Model State Args Value Unwind Terminal)
    (run : State → Args → Solanalib.Contracts.Model.Outcome State Value Unwind Terminal → Prop) :
      Prop :=
  ∃ before args outcome, contract.requires before args ∧ run before args outcome

/-- A permitted reference execution also witnesses a satisfiable precondition. -/
theorem Solanalib.Contracts.Model.HasExecution.satisfiable
    {State : Type u} {Args : Type v} {Value : Type w} {Unwind Terminal : Type}
    {contract : Solanalib.Contracts.Model State Args Value Unwind Terminal}
    {run : State → Args → Solanalib.Contracts.Model.Outcome State Value Unwind Terminal → Prop}
    (execution : contract.HasExecution run) : contract.Satisfiable := by
  obtain ⟨before, args, _, precondition, _⟩ := execution
  exact ⟨before, args, precondition⟩

/-- Total mathematical references have a permitted finite execution exactly
when the precondition is satisfiable. This concerns the reference function. -/
theorem Solanalib.Contracts.Model.hasExecution_returnsOf_iff_satisfiable
    {State : Type u} {Args : Type v} {Value : Type w} {Unwind Terminal : Type}
    (contract : Solanalib.Contracts.Model State Args Value Unwind Terminal)
    (run : State → Args → Value × State) :
    contract.HasExecution (Solanalib.Contracts.Model.returnsOf run) ↔ contract.Satisfiable := by
  constructor
  · exact HasExecution.satisfiable
  · rintro ⟨before, args, precondition⟩
    exact ⟨before, args, .returned (run before args).1 (run before args).2,
      precondition, rfl⟩

/-- The return case of the same outcome relation, for ordinary mathematical clients. -/
abbrev Solanalib.Contracts.Model.ensures {State : Type u} {Args : Type v} {Value : Type w}
    {Unwind Terminal : Type}
    (contract : Solanalib.Contracts.Model State Args Value Unwind Terminal)
    (before : State) (args : Args) (value : Value) (after : State) : Prop :=
  contract.post before args (.returned value after)

/-- Construct a return-only contract. Empty unwind and terminal types exclude
those exits from a satisfying interpretation. A Rust binding must justify this
outcome restriction separately. -/
abbrev Solanalib.Contracts.Model.returning {State : Type u} {Args : Type v} {Value : Type w}
    (precondition : State → Args → Prop) (postcondition : State → Args → Value → State → Prop) :
    Solanalib.Contracts.Model State Args Value where
  requires := precondition
  post := fun before args outcome => match outcome with
    | .returned value after => postcondition before args value after
    | .unwound reason _ | .terminated reason => nomatch reason

/-- Computing the postcondition of a return-only reference contract. -/
@[simp] theorem Solanalib.Contracts.Model.returning_ensures {State : Type u} {Args : Type v}
    {Value : Type w} (precondition : State → Args → Prop)
    (postcondition : State → Args → Value → State → Prop)
    (before : State) (args : Args) (value : Value) (after : State) :
    (returning precondition postcondition).ensures before args value after ↔
      postcondition before args value after := Iff.rfl

/-- The specialized proof interface for a total mathematical reference function. -/
def Solanalib.Contracts.Model.RealizedBy {State : Type u} {Args : Type v} {Value : Type w}
    (contract : Solanalib.Contracts.Model State Args Value) (run : State → Args → Value × State) :
      Prop :=
  ∀ before args, contract.requires before args →
    contract.ensures before args (run before args).1 (run before args).2

/-- The specialized reference proof is exactly the general outcome-relation proof. -/
theorem Solanalib.Contracts.Model.realized_iff_holds {State : Type u} {Args : Type v} {Value : Type
  w}
    (contract : Solanalib.Contracts.Model State Args Value) (run : State → Args → Value × State) :
    contract.RealizedBy run ↔ contract.Holds (Solanalib.Contracts.Model.returnsOf run) := by
  constructor
  · intro h before args outcome pre step
    cases outcome with
    | returned value after =>
      have post := h before args pre
      change run before args = (value, after) at step
      simpa only [Solanalib.Contracts.Model.ensures, step] using post
    | unwound reason _ => cases reason
    | terminated reason => cases reason
  · intro h before args pre
    exact h before args (.returned (run before args).1 (run before args).2) pre rfl
