/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OwnedFocus

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Owned

universe u v w x y z

/-- A focused return can come only from a real inner return with that value
and the actual inner state subsequently inserted into the outer state. -/
theorem Focus.lift_returned_iff {Outer : Type u} {Inner : Type v}
    {Args : Type w} {Value : Type z} {Unwind : Type x} {Terminal : Type y}
    (focus : Focus Outer Inner) (run : Callback.Run Inner Args Value Unwind Terminal)
    (before : Outer) (args : Args) (value : Value) (after : Outer) :
    focus.lift run before args (.returned value after) ↔
      ∃ innerAfter, run (focus.get before) args (.returned value innerAfter) ∧
        after = focus.set before innerAfter := by
  constructor
  · rintro ⟨inner, called, equal⟩
    cases inner with
    | returned actual innerAfter =>
      change .returned actual (focus.set before innerAfter) =
        (.returned value after : Outcome Outer Value Unwind Terminal) at equal
      cases equal
      exact ⟨innerAfter, called, rfl⟩
    | unwound reason innerAfter => cases equal
    | terminated reason => cases equal
  · rintro ⟨innerAfter, called, rfl⟩
    exact focus.lift_returned run before args value innerAfter called

/-- Focused unwinding preserves the reason and the actual inner unwind state. -/
theorem Focus.lift_unwound_iff {Outer : Type u} {Inner : Type v}
    {Args : Type w} {Value : Type z} {Unwind : Type x} {Terminal : Type y}
    (focus : Focus Outer Inner) (run : Callback.Run Inner Args Value Unwind Terminal)
    (before : Outer) (args : Args) (reason : Unwind) (after : Outer) :
    focus.lift run before args (.unwound reason after) ↔
      ∃ innerAfter, run (focus.get before) args (.unwound reason innerAfter) ∧
        after = focus.set before innerAfter := by
  constructor
  · rintro ⟨inner, called, equal⟩
    cases inner with
    | returned actual innerAfter => cases equal
    | unwound actual innerAfter =>
      change .unwound actual (focus.set before innerAfter) =
        (.unwound reason after : Outcome Outer Value Unwind Terminal) at equal
      cases equal
      exact ⟨innerAfter, called, rfl⟩
    | terminated actual => cases equal
  · rintro ⟨innerAfter, called, rfl⟩
    exact focus.lift_unwound run before args reason innerAfter called

/-- Focusing cannot invent a terminal exit or attach a state to one. -/
theorem Focus.lift_terminated_iff {Outer : Type u} {Inner : Type v}
    {Args : Type w} {Value : Type z} {Unwind : Type x} {Terminal : Type y}
    (focus : Focus Outer Inner) (run : Callback.Run Inner Args Value Unwind Terminal)
    (before : Outer) (args : Args) (reason : Terminal) :
    focus.lift run before args (.terminated reason) ↔
      run (focus.get before) args (.terminated reason) := by
  constructor
  · rintro ⟨inner, called, equal⟩
    cases inner with
    | returned actual innerAfter => cases equal
    | unwound actual innerAfter => cases equal
    | terminated actual => cases equal; exact called
  · intro called
    exact focus.lift_terminated run before args reason called

/-- Every primitive dependency law is preserved by a lawful focus. This proves
the two independent reference heaps used by instruction-builder witnesses can
share one surrounding state without losing the exact current-content laws. -/
theorem VectorOps.focus_laws {Outer : Type u} {Inner : Type v} {Element : Type w}
    {Resource : Type z} {Unwind : Type x} {Terminal : Type y}
    {ops : VectorOps Inner Element Resource Unwind Terminal} (laws : ops.Laws)
    (part : Focus Outer Inner) : (ops.focus part).Laws := by
  constructor
  · intro before
    change ops.current (part.get (part.set before (ops.empty (part.get before)).2))
      (ops.empty (part.get before)).1 = some []
    rw [part.get_set]
    exact laws.empty_current (part.get before)
  · intro before
    exact laws.empty_fresh (part.get before)
  · intro before capacity resource after run
    obtain ⟨innerAfter, called, rfl⟩ :=
      (part.lift_returned_iff ops.withCapacity before capacity resource after).mp run
    change ops.current (part.get (part.set before innerAfter)) resource = some []
    rw [part.get_set]
    exact laws.capacity_current (part.get before) capacity resource innerAfter called
  · intro before capacity resource after run
    obtain ⟨innerAfter, called, rfl⟩ :=
      (part.lift_returned_iff ops.withCapacity before capacity resource after).mp run
    exact laws.capacity_fresh (part.get before) capacity resource innerAfter called
  · intro before values resource after run
    obtain ⟨innerAfter, called, rfl⟩ :=
      (part.lift_returned_iff ops.fromList before values resource after).mp run
    change ops.current (part.get (part.set before innerAfter)) resource = some values
    rw [part.get_set]
    exact laws.list_current (part.get before) values resource innerAfter called
  · intro before values resource after run
    obtain ⟨innerAfter, called, rfl⟩ :=
      (part.lift_returned_iff ops.fromList before values resource after).mp run
    exact laws.list_fresh (part.get before) values resource innerAfter called
  · intro before resource value values after current run
    obtain ⟨innerAfter, called, rfl⟩ :=
      (part.lift_returned_iff ops.push before (resource, value) () after).mp run
    change ops.current (part.get (part.set before innerAfter)) resource = some (values ++ [value])
    rw [part.get_set]
    exact laws.push_current (part.get before) resource value values innerAfter current called
  · intro before resource value reason after live run
    obtain ⟨innerAfter, called, rfl⟩ :=
      (part.lift_unwound_iff ops.push before (resource, value) reason after).mp run
    change ∃ values, ops.current (part.get (part.set before innerAfter)) resource = some values
    rw [part.get_set]
    exact laws.push_unwind_live (part.get before) resource value reason innerAfter live called
  · intro before resource extra values after current run
    obtain ⟨innerAfter, called, rfl⟩ :=
      (part.lift_returned_iff ops.extend before (resource, extra) () after).mp run
    change ops.current (part.get (part.set before innerAfter)) resource = some (values ++ extra)
    rw [part.get_set]
    exact laws.extend_current (part.get before) resource extra values innerAfter current called
  · intro before resource extra reason after live run
    obtain ⟨innerAfter, called, rfl⟩ :=
      (part.lift_unwound_iff ops.extend before (resource, extra) reason after).mp run
    change ∃ values, ops.current (part.get (part.set before innerAfter)) resource = some values
    rw [part.get_set]
    exact laws.extend_unwind_live (part.get before) resource extra reason innerAfter live called
  · intro before resource after live run
    obtain ⟨innerAfter, called, rfl⟩ :=
      (part.lift_returned_iff ops.drop before resource () after).mp run
    change ops.current (part.get (part.set before innerAfter)) resource = none
    rw [part.get_set]
    exact laws.drop_current (part.get before) resource innerAfter live called
  · intro before resource reason after live run
    obtain ⟨innerAfter, called, rfl⟩ :=
      (part.lift_unwound_iff ops.drop before resource reason after).mp run
    change ops.current (part.get (part.set before innerAfter)) resource = none
    rw [part.get_set]
    exact laws.drop_unwind_consumed (part.get before) resource reason innerAfter live called

end Solanalib.Specs.Core.Owned
