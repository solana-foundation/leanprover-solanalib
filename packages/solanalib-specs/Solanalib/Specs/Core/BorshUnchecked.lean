/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Borsh

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Borsh

universe u v w x y

/-- A deserializer can update its local remaining slice on ordinary success
or error. The unchecked wrapper discards that slice, without requiring it to
be empty. Even a suffix property would be a separate callback obligation. -/
abbrev Deserializer (State : Type u) (Error : Type v) (Value : Type w)
    (Unwind : Type x) (Terminal : Type y) :=
  Callback.Run State Solanalib.Runtime.Bytes (Except Error Value × Solanalib.Runtime.Bytes) Unwind
    Terminal

def tryFromSliceUnchecked {State : Type u} {Error : Type v} {Value : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (deserialize : Deserializer State Error Value Unwind Terminal) :
    Callback.Run State Solanalib.Runtime.Bytes (Except Error Value) Unwind Terminal :=
  Callback.map Prod.fst deserialize

theorem unchecked_returned_iff {State : Type u} {Error : Type v} {Value : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (deserialize : Deserializer State Error Value Unwind Terminal)
    (before after : State) (bytes : Solanalib.Runtime.Bytes) (result : Except Error Value) :
    tryFromSliceUnchecked deserialize before bytes (.returned result after) ↔
      ∃ remaining, deserialize before bytes (.returned (result, remaining) after) := by
  constructor
  · rintro ⟨outcome, step, projected⟩
    cases outcome with
    | returned value state =>
      cases value with
      | mk value remaining =>
        cases projected
        exact ⟨remaining, step⟩
    | unwound reason state => cases projected
    | terminated reason => cases projected
  · rintro ⟨remaining, step⟩
    exact ⟨.returned (result, remaining) after, step, rfl⟩

theorem unchecked_unwound_iff {State : Type u} {Error : Type v} {Value : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (deserialize : Deserializer State Error Value Unwind Terminal)
    (before after : State) (bytes : Solanalib.Runtime.Bytes) (reason : Unwind) :
    tryFromSliceUnchecked deserialize before bytes (.unwound reason after) ↔
      deserialize before bytes (.unwound reason after) := by
  constructor
  · rintro ⟨outcome, step, projected⟩
    cases outcome <;> cases projected
    exact step
  · intro step
    exact ⟨.unwound reason after, step, rfl⟩

theorem unchecked_terminated_iff {State : Type u} {Error : Type v} {Value : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (deserialize : Deserializer State Error Value Unwind Terminal)
    (before : State) (bytes : Solanalib.Runtime.Bytes) (reason : Terminal) :
    tryFromSliceUnchecked deserialize before bytes (.terminated reason) ↔
      deserialize before bytes (.terminated reason) := by
  constructor
  · rintro ⟨outcome, step, projected⟩
    cases outcome <;> cases projected
    exact step
  · intro step
    exact ⟨.terminated reason, step, rfl⟩

/-- Closed sample error and callback for model nonvacuity. The counter records
one callback invocation, including a failed invocation on an empty slice. -/
inductive SampleError where
  | unexpectedEof
  deriving DecidableEq, Repr

def byteDeserializer (calls : Nat) (bytes : Solanalib.Runtime.Bytes) :
    Outcome Nat (Except SampleError UInt8 × Solanalib.Runtime.Bytes) Empty Empty :=
  match bytes with
  | [] => .returned (.error .unexpectedEof, []) (calls + 1)
  | byte :: remaining => .returned (.ok byte, remaining) (calls + 1)

end Solanalib.Specs.Core.Borsh
