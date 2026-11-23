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

namespace Solanalib.Specs.Core.Owned

universe u v w x y

/-- Explicit dependency operations for a typed vector resource. `Resource`
identifies the same logical vector across reallocations; it is neither its
machine address nor a claim of source ownership by itself. `current` observes
the actual supplied state, so cleanup never substitutes a saved content value.
The separate `Laws` state primitive dependency guarantees. Binding these
operations, observations and lifetimes to Rust remains an independent task. -/
structure VectorOps (State : Type u) (Element : Type v) (Resource : Type w)
    (Unwind : Type x) (Terminal : Type y) where
  /-- Current contents of a live logical vector; absent after retirement. -/
  current : State → Resource → Option (List Element)
  /-- Empty vector construction is infallible. Any state change here is part
  of the supplied interpretation, including logical identity bookkeeping. -/
  empty : State → Resource × State
  /-- The actual with-capacity dependency, including its finite panic exits. -/
  withCapacity : Callback.Run State Nat Resource Unwind Terminal
  /-- The dependency constructing a vector from the supplied ordered array.
  Elements have already been evaluated by the surrounding SDK model. -/
  fromList : Callback.Run State (List Element) Resource Unwind Terminal
  /-- One actual push call. A normal return retains the same vector identity. -/
  push : Callback.Run State (Resource × Element) Unit Unwind Terminal
  /-- One actual extend call, preserving the allocation granularity of the source call. -/
  extend : Callback.Run State (Resource × List Element) Unit Unwind Terminal
  /-- Drop this vector using its current state. The provider handles element
  cleanup and allocation retirement inside that dependency. -/
  drop : Callback.Run State Resource Unit Unwind Terminal

/-- A live resource has a current typed sequence observation. This predicate
does not assert permissions, provenance, separation or a Rust representation. -/
def VectorOps.Live {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (ops : VectorOps State Element Resource Unwind Terminal)
    (state : State) (resource : Resource) : Prop :=
  ∃ values, ops.current state resource = some values

/-- Primitive vector dependency guarantees, separate from the postcondition of any SDK function.
They permit partial contents changes on unwind: the live token
then selects the actual current sequence of the provider. These laws do not assert
framing of other resources, allocator success, determinism or termination. -/
structure VectorOps.Laws {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (ops : VectorOps State Element Resource Unwind Terminal) : Prop where
  /-- Empty construction creates a represented empty logical vector. -/
  empty_current : ∀ before,
    ops.current (ops.empty before).2 (ops.empty before).1 = some []
  /-- A newly constructed vector does not reuse a currently live identity. -/
  empty_fresh : ∀ before, ops.current before (ops.empty before).1 = none
  /-- Capacity construction returns the exact empty sequence. -/
  capacity_current : ∀ before capacity resource after,
    ops.withCapacity before capacity (.returned resource after) →
      ops.current after resource = some []
  /-- Capacity construction creates a fresh logical identity. -/
  capacity_fresh : ∀ before capacity resource after,
    ops.withCapacity before capacity (.returned resource after) →
      ops.current before resource = none
  /-- Array construction retains all values, order and duplicates. -/
  list_current : ∀ before values resource after,
    ops.fromList before values (.returned resource after) →
      ops.current after resource = some values
  /-- Array construction creates a fresh logical identity. -/
  list_fresh : ∀ before values resource after,
    ops.fromList before values (.returned resource after) →
      ops.current before resource = none
  /-- Successful push appends to the actual pre-call sequence. -/
  push_current : ∀ before resource value values after,
    ops.current before resource = some values →
    ops.push before (resource, value) (.returned () after) →
      ops.current after resource = some (values ++ [value])
  /-- A push unwind leaves the same vector token available for caller cleanup;
  its contents must be read from the actual unwind state. -/
  push_unwind_live : ∀ before resource value reason after,
    ops.Live before resource →
    ops.push before (resource, value) (.unwound reason after) →
      ops.Live after resource
  /-- Successful extend appends exactly the supplied ordered slice. -/
  extend_current : ∀ before resource extra values after,
    ops.current before resource = some values →
    ops.extend before (resource, extra) (.returned () after) →
      ops.current after resource = some (values ++ extra)
  /-- Partial extension during unwind preserves a live cleanup token without
  claiming that the old sequence is still current. -/
  extend_unwind_live : ∀ before resource extra reason after,
    ops.Live before resource →
    ops.extend before (resource, extra) (.unwound reason after) →
      ops.Live after resource
  /-- A completed drop consumes the resource rather than returning a second owner. -/
  drop_current : ∀ before resource after,
    ops.Live before resource → ops.drop before resource (.returned () after) →
      ops.current after resource = none
  /-- The unwinding drop has also consumed this owner. Cleanup must continue
  with the remaining distinct resources, without redropping this token. -/
  drop_unwind_consumed : ∀ before resource reason after,
    ops.Live before resource → ops.drop before resource (.unwound reason after) →
      ops.current after resource = none

/-- One source cleanup dependency, already bound to its retained resource.
It receives the actual state at the point its drop begins. -/
abbrev DropAction (State : Type u) (Unwind : Type x) (Terminal : Type y) :=
  State → Outcome State Unit Unwind Terminal → Prop

/-- Bind the stable identity of a vector for cleanup. Its provider consults the
state supplied when this action runs, not a pre-operation contents snapshot. -/
def VectorOps.dropAction {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (ops : VectorOps State Element Resource Unwind Terminal) (resource : Resource) :
    DropAction State Unwind Terminal := fun state outcome => ops.drop state resource outcome

/-- The terminal-only dependency used when a destructor unwinds while another
unwind is already in progress. It receives the actual second unwind state and
both reasons. An empty relation models no finite exit; no terminal is invented. -/
abbrev DoubleUnwind (State : Type u) (Unwind : Type x) (Terminal : Type y) :=
  State → Unwind → Unwind → Terminal → Prop

/-- An empty construction has a live current vector under its primitive law. -/
theorem VectorOps.empty_live {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    {ops : VectorOps State Element Resource Unwind Terminal}
    (empty_current : ∀ before,
      ops.current (ops.empty before).2 (ops.empty before).1 = some [])
    (before : State) : ops.Live (ops.empty before).2 (ops.empty before).1 :=
  ⟨[], empty_current before⟩

/-- The returned vector identity denotes exactly the ordered supplied array. -/
theorem VectorOps.fromList_live {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    {ops : VectorOps State Element Resource Unwind Terminal}
    (list_current : ∀ before values resource after,
      ops.fromList before values (.returned resource after) →
        ops.current after resource = some values)
    {before after : State} {values : List Element} {resource : Resource}
    (run : ops.fromList before values (.returned resource after)) : ops.Live after resource :=
  ⟨values, list_current before values resource after run⟩

end Solanalib.Specs.Core.Owned
