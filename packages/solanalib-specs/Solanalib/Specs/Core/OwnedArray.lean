/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Owned.Array

universe u v w x y

/-- A construction dependency may do another finite chunk of work, request
the next expression, or request completion. This is deliberately not a fixed
reserve/push expansion of a Rust array or vector macro. -/
inductive Command where
  /-- Another dependency chunk may run before the next expression. -/
  | again
  /-- Evaluate exactly the next, as yet unevaluated, expression. -/
  | evaluate
  /-- All expressions are ready for the separate completion dependency. -/
  | finish
  deriving DecidableEq, Repr

/-- The point at which construction began unwinding. In particular, an
evaluator may have consumed one of its own inputs before it unwinds. -/
inductive FailureSite where
  /-- Internal construction work failed between expression evaluations. -/
  | work
  /-- The next expression failed; its partial-input cleanup is its own job. -/
  | evaluate
  /-- The completion dependency failed after every expression returned. -/
  | finish
  deriving DecidableEq, Repr

/-- Exact progress made before an unwind. `completed` counts only expressions
that returned an owned value. It alone does not describe the partially consumed captures of a
failing evaluator; `site` and the actual state retain that boundary. -/
structure Failure where
  /-- Length of the ordered prefix of successfully evaluated expressions. -/
  completed : Nat
  /-- The dependency or expression that initiated this unwind. -/
  site : FailureSite
  deriving DecidableEq, Repr

/-- Primitive interpretation of owned array construction. Every expression is
supplied separately to `run`; construction work can change state before and
between evaluations. Successfully evaluated outputs belong to this constructor
until completion transfers them to a vector, or unwind cleanup destroys them.

`finish` must leave those outputs available on unwind. `retire` only retires
temporary storage, and must not destroy the elements a second time. These are
separate source dependency binding obligations. The local laws in
`OwnedArrayLaws` support the stated current-content, ownership-predicate and
retained-token theorems; they do not establish preservation of arbitrary element
lifecycle observations. This structure supplies no Rust or allocator proof. -/
structure Provider (State : Type u) (Element : Type v) (Resource : Type w)
    (Unwind : Type x) (Terminal : Type y) where
  /-- Actual work before or between evaluations. Arguments are the total
expression count and the exact prefix of values returned so far. -/
  work : Callback.Run State (Nat × List Element) Command Unwind Terminal
  /-- Actual completion, retaining its returned resource and after-state. -/
  finish : Callback.Run State (List Element) Resource Unwind Terminal
  /-- Cleanup order selected from the actual unwind state. Positions, rather
than element equality, distinguish repeated equal values and pending elements. -/
  cleanupOrder : (state : State) → (values : List Element) → List (Fin values.length)
  /-- Destroy one successfully evaluated element in the current state. The
callback owns its own internal cleanup when it unwinds. -/
  drop : Callback.Run State Element Unit Unwind Terminal
  /-- Retire only temporary construction storage, using the actual state after
element cleanup. An implementation without such storage can return unchanged. -/
  retire : Callback.Run State (List Element) Unit Unwind Terminal
  /-- Exact terminal policy for a destructor unwinding during an unwind. -/
  double : DoubleUnwind State Unwind Terminal

/-- Local control-flow obligations for the supplied construction dependencies.
They neither specify a complete SDK postcondition nor guarantee a finite exit.
The cleanup permutation covers every evaluated occurrence exactly once.
The trace checks these conditions at each admitted step itself; this stronger
provider-wide certificate is separate from finite-trace partial correctness. -/
structure Provider.Conforms {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (provider : Provider State Element Resource Unwind Terminal) : Prop where
  /-- A dependency requests another expression only while one remains. -/
  evaluate_bound : ∀ before count values after,
    values.length ≤ count →
    provider.work before (count, values) (.returned .evaluate after) →
      values.length < count
  /-- A dependency requests completion only at the exact requested count. -/
  finish_count : ∀ before count values after,
    values.length ≤ count →
    provider.work before (count, values) (.returned .finish after) →
      values.length = count
  /-- Cleanup does not omit or duplicate any evaluated position. -/
  cleanup_permutation : ∀ state values,
    (provider.cleanupOrder state values).Perm (List.finRange values.length)

/-- Attach construction progress to an unwind without changing its reason,
state, any returned resource, or a terminal exit. -/
def annotate {State : Type u} {Resource : Type w} {Unwind : Type x} {Terminal : Type y}
    (failure : Failure) : Outcome State Resource Unwind Terminal →
      Outcome State Resource (Failure × Unwind) Terminal
  | .returned resource state => .returned resource state
  | .unwound reason state => .unwound (failure, reason) state
  | .terminated reason => .terminated reason

/-- Forget only construction progress; actual exit reasons and states remain. -/
def erase {State : Type u} {Resource : Type w} {Unwind : Type x} {Terminal : Type y} :
    Outcome State Resource (Failure × Unwind) Terminal → Outcome State Resource Unwind Terminal
  | .returned resource state => .returned resource state
  | .unwound failure state => .unwound failure.2 state
  | .terminated reason => .terminated reason

/-- Position-indexed element drops followed by storage-only retirement.
Every action receives its own actual invocation state. The retained prefix
contains returned element identities, not snapshots of their mutable referents. -/
def Provider.cleanupActions {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (provider : Provider State Element Resource Unwind Terminal)
    (values : List Element) (order : List (Fin values.length)) :
    List (DropAction State Unwind Terminal) :=
  order.map (fun index state outcome => provider.drop state values[index] outcome) ++
    [fun state outcome => provider.retire state values outcome]

/-- Clean the evaluated prefix after a construction unwind. The actual unwind
state selects a permutation of evaluated positions, including any last value
still pending insertion. Terminal outcomes stop cleanup immediately. -/
def Provider.close {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (provider : Provider State Element Resource Unwind Terminal)
    (values : List Element) (site : FailureSite) (before : State) (reason : Unwind)
    (final : Outcome State Resource (Failure × Unwind) Terminal) : Prop :=
  let order := provider.cleanupOrder before values
  order.Perm (List.finRange values.length) ∧
    ∃ pending, cleanup provider.double (provider.cleanupActions values order)
      (.unwound reason before) pending ∧
      annotate ⟨values.length, site⟩ pending = final

/-- Exact finite construction traces. A dependency can run arbitrarily many
finite work chunks at any prefix. Each successful expression is evaluated once
at the length of that prefix and its actual returned value is appended in order.
No later evaluation or destructor runs after a terminal exit. -/
inductive Trace {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (provider : Provider State Element Resource Unwind Terminal) (count : Nat)
    (evaluate : Callback.Run State Nat Element Unwind Terminal) :
    List Element → State → Outcome State Resource (Failure × Unwind) Terminal → Prop
  /-- One more internal chunk, preserving the exact evaluated prefix. -/
  | again (values : List Element) (before middle : State)
      (final : Outcome State Resource (Failure × Unwind) Terminal)
      (work : provider.work before (count, values) (.returned .again middle))
      (rest : Trace provider count evaluate values middle final) :
      Trace provider count evaluate values before final
  /-- The next expression returns one value; construction resumes in the actual after-state of that
expression with the extended ordered prefix. -/
  | next (values : List Element) (before ready after : State) (value : Element)
      (final : Outcome State Resource (Failure × Unwind) Terminal)
      (bound : values.length < count)
      (work : provider.work before (count, values) (.returned .evaluate ready))
      (expression : evaluate ready values.length (.returned value after))
      (rest : Trace provider count evaluate (values ++ [value]) after final) :
      Trace provider count evaluate values before final
  /-- A work unwind cleans exactly the prefix completed before that work. -/
  | workUnwind (values : List Element) (before after : State) (reason : Unwind)
      (final : Outcome State Resource (Failure × Unwind) Terminal)
      (work : provider.work before (count, values) (.unwound reason after))
      (closed : provider.close values .work after reason final) :
      Trace provider count evaluate values before final
  /-- A work terminal exit has no subsequent expression or cleanup. -/
  | workTerminal (values : List Element) (before : State) (reason : Terminal)
      (work : provider.work before (count, values) (.terminated reason)) :
      Trace provider count evaluate values before (.terminated reason)
  /-- An expression unwind cleans earlier returned values; the failing
expression remains responsible for cleanup of its own partial evaluation. -/
  | evaluateUnwind (values : List Element) (before ready after : State) (reason : Unwind)
      (final : Outcome State Resource (Failure × Unwind) Terminal)
      (bound : values.length < count)
      (work : provider.work before (count, values) (.returned .evaluate ready))
      (expression : evaluate ready values.length (.unwound reason after))
      (closed : provider.close values .evaluate after reason final) :
      Trace provider count evaluate values before final
  /-- An expression terminal exit stops before all constructor cleanup. -/
  | evaluateTerminal (values : List Element) (before ready : State) (reason : Terminal)
      (bound : values.length < count)
      (work : provider.work before (count, values) (.returned .evaluate ready))
      (expression : evaluate ready values.length (.terminated reason)) :
      Trace provider count evaluate values before (.terminated reason)
  /-- Completion transfers the exact returned logical vector resource. -/
  | finishReturn (values : List Element) (before ready after : State) (resource : Resource)
      (complete : values.length = count)
      (work : provider.work before (count, values) (.returned .finish ready))
      (finished : provider.finish ready values (.returned resource after)) :
      Trace provider count evaluate values before (.returned resource after)
  /-- Completion failure leaves all evaluated outputs for constructor cleanup. -/
  | finishUnwind (values : List Element) (before ready after : State) (reason : Unwind)
      (final : Outcome State Resource (Failure × Unwind) Terminal)
      (complete : values.length = count)
      (work : provider.work before (count, values) (.returned .finish ready))
      (finished : provider.finish ready values (.unwound reason after))
      (closed : provider.close values .finish after reason final) :
      Trace provider count evaluate values before final
  /-- Completion may terminate without running element or storage cleanup. -/
  | finishTerminal (values : List Element) (before ready : State) (reason : Terminal)
      (complete : values.length = count)
      (work : provider.work before (count, values) (.returned .finish ready))
      (finished : provider.finish ready values (.terminated reason)) :
      Trace provider count evaluate values before (.terminated reason)

/-- Higher-order construction with exact progress exposed on a surviving
unwind. An outer source scope can then clean only its unevaluated owned inputs. -/
def Provider.runDetailed {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (provider : Provider State Element Resource Unwind Terminal) (count : Nat)
    (evaluate : Callback.Run State Nat Element Unwind Terminal) :
    State → Outcome State Resource (Failure × Unwind) Terminal → Prop :=
  Trace provider count evaluate []

/-- Higher-order construction when the caller does not need unwind progress.
This projects the detailed relation and preserves every actual finite exit. -/
def Provider.run {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (provider : Provider State Element Resource Unwind Terminal) (count : Nat)
    (evaluate : Callback.Run State Nat Element Unwind Terminal)
    (before : State) (final : Outcome State Resource Unwind Terminal) : Prop :=
  ∃ detailed, provider.runDetailed count evaluate before detailed ∧ erase detailed = final

end Solanalib.Specs.Core.Owned.Array
