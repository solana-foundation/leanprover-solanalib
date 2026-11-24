/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.Core.ProgramOptionOperations
import Solanalib.Runtime.Ids

set_option autoImplicit false

open Solanalib.Contracts.Model Solanalib.Specs.Core.ProgramOption

namespace SolanalibTest.Conformance.Library.Families.SdkValues.KeyEquality

/-- Byte-key equality is total and has no interior state or cleanup effects.
Source bindings must select a reviewed key implementation for this index. -/
def keyEqIndex : EqIndex where
  State := Unit
  T := Solanalib.Runtime.Pubkey
  Unwind := Empty
  Terminal := Empty
  equal := Callback.ofFunction fun before args => .returned (decide (args.1 = args.2)) before

def keyEq : Value Solanalib.Runtime.Pubkey → Value Solanalib.Runtime.Pubkey → Bool
  | .none, .none => true
  | .some left, .some right => decide (left = right)
  | _, _ => false

/-- This specialization is derived from the generic comparison graph. -/
theorem keyEq_graph (before : Unit) (left right : Value Solanalib.Runtime.Pubkey)
    (outcome : Outcome Unit Bool Empty Empty) :
    eqRun keyEqIndex before (left, right) outcome ↔
      outcome = .returned (keyEq left right) before := by
  cases left <;> cases right
  all_goals first | exact Iff.rfl | exact eq_comm

end SolanalibTest.Conformance.Library.Families.SdkValues.KeyEquality
