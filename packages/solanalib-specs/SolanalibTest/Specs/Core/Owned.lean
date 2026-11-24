/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OwnedCleanup
public import Solanalib.Specs.Core.OwnedVector
public import Solanalib.Specs.Core.OwnedFocusFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.Owned

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Owned

/-- A closed reference ledger with observable nontrivial element values. -/
def reference : VectorOps (VectorState Nat) Nat Nat Nat Nat := vectorReference

/-- The complete vector dependency laws have a closed reference instance. -/
theorem reference_laws : reference.Laws := vectorReference_laws

/-- A new vector preserves earlier live slots and tombstones, and retains
the supplied order and duplicate elements in a fresh slot. -/
theorem construction_preserves_slots : reference.fromList [some [7], none] [4, 4, 9]
    (.returned 2 [some [7], none, some [4, 4, 9]]) := rfl

/-- A push updates the same identity and leaves a different live vector alone. -/
theorem push_preserves_other_vector : reference.push [some [7], some [4, 4, 9]] (1, 6)
    (.returned () [some [7], some [4, 4, 9, 6]]) :=
  ⟨[4, 4, 9], rfl, rfl⟩

/-- A drop retires its own slot and preserves an independently live slot. -/
theorem drop_preserves_other_vector : reference.drop [some [7], some [4, 4, 9, 6]] 1
    (.returned () [some [7], none]) := ⟨[4, 4, 9, 6], rfl, rfl⟩

/-- A retired slot cannot be dropped again in the reference model. -/
theorem stale_drop_rejected : ∀ outcome, ¬ reference.drop [some [7], none] 1 outcome := by
  intro outcome run
  obtain ⟨values, current, _⟩ := run
  cases current

/-- New construction after retirement never reuses the stale identity. -/
theorem construction_after_retirement : reference.fromList [some [7], none] [11]
    (.returned 2 [some [7], none, some [11]]) := rfl

/-- A dependency that appends one element and then actually unwinds. The
prefix mutation is deliberately visible in the finite state of the callback. -/
def partialExtend : Callback.Run (VectorState Nat) (Nat × List Nat) Unit Nat Nat :=
  fun before (resource, extra) outcome => ∃ values,
    before.current resource = some values ∧ outcome = .unwound 42
      (before.set resource (some (values ++ extra.take 1)))

/-- A lawful failure-injection instance, sharing all other reference operations. -/
def partialReference : VectorOps (VectorState Nat) Nat Nat Nat Nat :=
  { reference with extend := partialExtend }

/-- The generic laws admit an actual contents-changing unwind, rather than
only a provider whose unwind cases are impossible. -/
theorem partial_reference_laws : partialReference.Laws := by
  refine { reference_laws with extend_current := ?_, extend_unwind_live := ?_ }
  · intro before resource extra values after current run
    obtain ⟨actual, observed, impossible⟩ := run
    cases impossible
  · intro before resource extra reason after live run
    obtain ⟨actual, observed, equal⟩ := run
    cases equal
    exact ⟨actual ++ extra.take 1,
      before.current_set resource (some (actual ++ extra.take 1))
        (VectorState.current_bound observed)⟩

/-- This real unwind changed the live sequence, retaining the same token. -/
theorem partial_extension_changes_contents : partialReference.extend [some [37]] (0, [41, 99])
    (.unwound 42 [some [37, 41]]) := ⟨[37], rfl, rfl⟩

/-- A destructor control that checks the actual current contents before
retiring the vector. This is not an element-destructor implementation claim. -/
def observingDrop (expected : List Nat) (resource : Nat) :
    DropAction (VectorState Nat) Nat Nat := fun before outcome =>
  before.current resource = some expected ∧ reference.drop before resource outcome

/-- A terminal policy whose reason encodes both unwinds and their actual state. -/
def double : DoubleUnwind Nat Nat Nat := fun state original later terminal =>
  terminal = state + original + later

/-- The vector control needs no admitted double-unwind terminal because its
destructor returns normally. An empty policy does not invent a terminal exit. -/
def noVectorDouble : DoubleUnwind (VectorState Nat) Nat Nat := fun _ _ _ _ => False

/-- Scope cleanup reads the contents produced by the actual partial unwind,
then retires that exact live resource while preserving the original reason. -/
theorem cleanup_after_partial_mutation : scope noVectorDouble [observingDrop [37, 41] 0]
    partialReference.extend [some [37]] (0, [41, 99]) (.unwound 42 [none]) := by
  refine ⟨.unwound 42 [some [37, 41]], partial_extension_changes_contents, ?_⟩
  exact ⟨.returned () [none], ⟨rfl, ⟨[37, 41], rfl, rfl⟩⟩, rfl⟩

/-- The same observation would reject an obsolete pre-unwind snapshot. -/
theorem old_snapshot_rejected : ∀ outcome, ¬ observingDrop [37, 41] 0 [some [37]] outcome := by
  intro outcome run
  have impossible := run.1
  change some [37] = some [37, 41] at impossible
  cases impossible

/-- A normal destructor used to make cleanup order observable. -/
def doubleDrop : DropAction Nat Nat Nat := fun before outcome =>
  outcome = .returned () (before * 2)

/-- A second destructor whose effect does not commute with doubling. -/
def addDrop : DropAction Nat Nat Nat := fun before outcome =>
  outcome = .returned () (before + 3)

/-- A cleanup action that has no finite execution at all. -/
def blockedDrop : DropAction Nat Nat Nat := fun _ _ => False

/-- A pair of real destructor calls establishes the exact order-sensitive
state; reversing these calls would produce eight instead of five. -/
theorem ordered_drop_trace : DropReturns [doubleDrop, addDrop] 1 5 :=
  .cons doubleDrop [addDrop] 1 2 5 rfl
    (.cons addDrop [] 2 5 5 rfl (.nil 5))

/-- Successful cleanup keeps the pending value and the actual ordered state. -/
theorem ordered_cleanup_return : cleanup double [doubleDrop, addDrop]
    (.returned 9 1) (.returned 9 5) := ordered_drop_trace.cleanup_returned double 9

/-- A first destructor unwind replaces an ordinary pending return and the
remaining destructor runs in that unwound state. -/
theorem first_unwind_runs_remaining : cleanup double
    [(fun state outcome => outcome = .unwound 17 (state + 10)), addDrop]
    (.returned 9 1) (.unwound 17 14) := by
  exact ⟨.unwound 17 11, rfl, .returned () 14, rfl, rfl⟩

/-- A second unwind invokes the supplied terminal policy with the actual
post-state and both reasons, and does not run a later blocked destructor. -/
theorem second_unwind_terminates : cleanup double
    [(fun state outcome => outcome = .unwound 23 (state + 4)), blockedDrop]
    (.unwound 17 11 : Outcome Nat Nat Nat Nat) (.terminated 55) := by
  exact ⟨.unwound 23 15, rfl, 55, rfl, rfl⟩

/-- A terminal destructor stops before a subsequent action with no execution. -/
theorem terminal_drop_stops : cleanup double
    [(fun _ outcome => outcome = .terminated 71), blockedDrop]
    (.returned 9 1) (.terminated 71) := ⟨.terminated 71, rfl, rfl⟩

/-- A terminal body outcome performs no cleanup, even if no drop can execute. -/
theorem terminal_body_stops : cleanup double [blockedDrop]
    (.terminated 71 : Outcome Nat Nat Nat Nat) (.terminated 71) := rfl

/-- Ordinary Result errors are cleaned by a scope just like other returns. -/
theorem scope_cleans_ordinary_error : scope double [addDrop]
    (Callback.ofFunction (fun state (_ : Unit) =>
      (.returned (Except.error 8 : Except Nat Nat) state : Outcome Nat (Except Nat Nat) Nat Nat)))
    1 () (.returned (.error 8) 4) :=
  ⟨.returned (.error 8) 1, rfl, .returned () 4, rfl, rfl⟩

/-- Unwind-only protection deliberately transfers every ordinary value. A
constructor with an error requiring cleanup must instead model that branch. -/
theorem protection_transfers_ordinary_error : protect double [blockedDrop]
    (Callback.ofFunction (fun state (_ : Unit) =>
      (.returned (Except.error 8 : Except Nat Nat) state : Outcome Nat (Except Nat Nat) Nat Nat)))
    1 () (.returned (.error 8) 1) := ⟨.returned (.error 8) 1, rfl, rfl⟩

/-- Two independent reference heaps share a surrounding state through a focus. -/
def focused : VectorOps (VectorState Nat × VectorState Nat) Nat Nat Nat Nat :=
  reference.focus Focus.fst

/-- The focused reference also satisfies every primitive law as a closed instance. -/
theorem focused_laws : focused.Laws := VectorOps.focus_laws reference_laws Focus.fst

/-- Focusing normal construction preserves the unrelated heap verbatim. -/
theorem focused_construction : focused.fromList ([some [7]], [some [99]]) [4, 4, 9]
    (.returned 1 ([some [7], some [4, 4, 9]], [some [99]])) :=
  ⟨.returned 1 [some [7], some [4, 4, 9]], rfl, rfl⟩

/-- Focusing a genuine partial unwind retains both the changed inner contents
and the exact untouched outer component. -/
theorem focused_partial_unwind : (partialReference.focus
    (Focus.fst : Focus (VectorState Nat × VectorState Nat) (VectorState Nat))).extend
    ([some [37]], [some [99]]) (0, [41, 99])
    (.unwound 42 ([some [37, 41]], [some [99]])) :=
  ⟨.unwound 42 [some [37, 41]], partial_extension_changes_contents, rfl⟩

end SolanalibTest.Specs.Core.Owned
