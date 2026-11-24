/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.ProgramOptionOperations
public import Solanalib.Runtime.Ids

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.ProgramOption

/-- Byte-key equality is total and has no interior state or cleanup effects.
Source bindings must select a reviewed key implementation for this index. -/
def keyEqIndex : EqIndex where
  State := Unit
  T := Solanalib.Runtime.Pubkey
  Unwind := Empty
  Terminal := Empty
  equal := Callback.ofFunction fun before args => .returned (decide (args.1 = args.2)) before

/-- A borrowed key query uses the same complete equality, with the query first. -/
def keyContainsIndex : ContainsIndex where
  State := Unit
  T := Solanalib.Runtime.Pubkey
  Query := Solanalib.Runtime.Pubkey
  Unwind := Empty
  Terminal := Empty
  equal := Callback.ofFunction fun before args => .returned (decide (args.1 = args.2)) before

/-- The reviewed key Default constructs the all-zero byte array. -/
def keyDefaultIndex : DefaultIndex where
  State := Unit
  T := Solanalib.Runtime.Pubkey
  Unwind := Empty
  Terminal := Empty
  defaultValue := Callback.ofFunction fun before _ => .returned Solanalib.Runtime.Ids.systemProgram
    before

/-- The production panic-abort profile preserves the terminal diagnostic of None.
The general unwrap family also represents unwinding panic providers. -/
def keyUnwrapAbortIndex : UnwrapIndex where
  State := Unit
  T := Solanalib.Runtime.Pubkey
  Unwind := Empty
  Terminal := String
  panic := Callback.ofFunction fun _ message => .terminated message

/-- A Boolean has trivial drop. The selected return-place policy remains
explicit even though this destructor cannot unwind. -/
def boolUnwrapOrIndex : UnwrapOrIndex where
  State := Unit
  T := Bool
  Unwind := Empty
  Terminal := Empty
  dropValue := Callback.ofFunction fun before _ => .returned () before
  returnPlace := .retain
  doubleUnwind := fun _ first _ _ => Empty.elim first

def keyEq : Value Solanalib.Runtime.Pubkey → Value Solanalib.Runtime.Pubkey → Bool
  | .none, .none => true
  | .some left, .some right => decide (left = right)
  | _, _ => false

def keyContains : Value Solanalib.Runtime.Pubkey → Solanalib.Runtime.Pubkey → Bool
  | .none, _ => false
  | .some value, query => decide (query = value)

def keyDefault : Value Solanalib.Runtime.Pubkey → Solanalib.Runtime.Pubkey
  | .none => Solanalib.Runtime.Ids.systemProgram
  | .some key => key

def boolUnwrapOr : Value Bool → Bool → Bool
  | .none, fallback => fallback
  | .some value, _ => value

/-- This specialization is derived from the generic comparison graph. -/
theorem keyEq_graph (before : Unit) (left right : Value Solanalib.Runtime.Pubkey)
    (outcome : Outcome Unit Bool Empty Empty) :
    eqRun keyEqIndex before (left, right) outcome ↔
      outcome = .returned (keyEq left right) before := by
  cases left <;> cases right
  all_goals first | exact Iff.rfl | exact eq_comm

theorem keyContains_graph (before : Unit) (value : Value Solanalib.Runtime.Pubkey) (query :
  Solanalib.Runtime.Pubkey)
    (outcome : Outcome Unit Bool Empty Empty) :
    containsRun keyContainsIndex before (value, query) outcome ↔
      outcome = .returned (keyContains value query) before := by
  cases value
  all_goals first | exact Iff.rfl | exact eq_comm

theorem keyDefault_graph (before : Unit) (value : Value Solanalib.Runtime.Pubkey)
    (outcome : Outcome Unit Solanalib.Runtime.Pubkey Empty Empty) :
    unwrapOrDefaultRun keyDefaultIndex before value outcome ↔
      outcome = .returned (keyDefault value) before := by
  cases value
  all_goals first | exact Iff.rfl | exact eq_comm

/-- Trivial drop removes no outcome of the general fallback cleanup model. -/
theorem boolUnwrapOr_graph (before : Unit) (value : Value Bool) (fallback : Bool)
    (outcome : Outcome Unit Bool Empty Empty) :
    unwrapOrRun boolUnwrapOrIndex before (value, fallback) outcome ↔
      outcome = .returned (boolUnwrapOr value fallback) before := by
  cases value <;> simp [unwrapOrRun, boolUnwrapOrIndex, boolUnwrapOr,
    Callback.map, Callback.ofFunction, Outcome.map, eq_comm]

theorem keyUnwrap_none_terminal (before : Unit)
    (outcome : Outcome Unit Solanalib.Runtime.Pubkey Empty String) :
    unwrapRun keyUnwrapAbortIndex before .none outcome ↔
      outcome = .terminated unwrapMessage := by
  simp [unwrapRun, keyUnwrapAbortIndex, Callback.map, Callback.ofFunction, Outcome.map, eq_comm]

end Solanalib.Specs.Core.ProgramOption
