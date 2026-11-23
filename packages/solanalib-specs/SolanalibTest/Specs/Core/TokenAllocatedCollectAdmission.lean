/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedCollectAdmission
public import SolanalibTest.Specs.Core.TokenAllocatedCollect

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.TokenAllocatedCollectAdmission

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.AllocatedCollect
open TokenAllocatedCollect

/-- The first element comes from a real source checked borrow at index zero,
independently of the later internal schedule of the collection provider. -/
theorem first_prefix (protocol : Protocol ReferenceExtra Nat Nat Nat) :
    ForwardPrefix protocol iterator (borrowElement noPanic) (accounts, [])
      1 [(first.key, firstRef)] (afterFirst, []) [0] :=
  .next .start (by decide) rfl first_callback

/-- The prefix includes both actual callbacks and their returned references. -/
theorem both_prefix (protocol : Protocol ReferenceExtra Nat Nat Nat) :
    ForwardPrefix protocol iterator (borrowElement noPanic) (accounts, [])
      2 elements (afterBoth, []) [0, 1] :=
  .next (first_prefix protocol) (by decide) rfl second_callback

/-- A real internal unwind reaches the malformed empty order after a nonempty
acquisition prefix. This premise contains no completed collection result. -/
theorem leaking_order_reached : CleanupSite leakingOrderProtocol iterator
    (borrowElement noPanic) (accounts, []) [(first.key, firstRef)] (afterFirst, [none])
    (.unwound 77 (afterFirst, [none])) [0] :=
  .internalUnwind (first_prefix leakingOrderProtocol) (by decide) rfl

/-- The new admission rejects that actual prefix even when cleanup has no
protocol outcome and any condition on complete outcomes would be vacuous. -/
theorem leaking_order_rejected :
    ¬ CleanupReady leakingOrderProtocol iterator (borrowElement noPanic) (accounts, []) := by
  intro ready
  have impossible := (ready leaking_order_reached).length_eq
  change 0 = 1 at impossible
  cases impossible

/-- Without the permutation gate the same downstream storage retirement has
an actual unwind exit, leaving the omitted acquired reference live. -/
theorem leaking_downstream_exit : Owned.cleanup leakingOrderProtocol.double
    (leakingOrderProtocol.partialDrops (afterFirst, [none]) [(first.key, firstRef)])
    (.unwound 77 (afterFirst, [none]) : Outcome ReferenceWorld (Except Error Nat) Nat Nat)
    (.unwound 77 (afterFirst, [none])) :=
  ⟨.returned () (afterFirst, [none]), rfl, rfl⟩

/-- The local check discards the above real destructor exit; this is precisely
why admission is tested before complete protocol outcomes. -/
theorem leaking_protocol_exit_missing : ∀ final,
    ¬ leakingOrderProtocol.cleanup [(first.key, firstRef)]
      (.unwound 77 (afterFirst, [none]) : Outcome ReferenceWorld (Except Error Nat) Nat Nat) final
        := by
  intro final cleaned
  have impossible := cleaned.1.length_eq
  change 0 = 1 at impossible
  cases impossible

/-- Ordinary stateful internal effects satisfy source admission using just its
three reachable failure classes; no callback-unwind or panic law is supplied. -/
theorem stateful_order_admitted :
    CleanupReady unwindingProtocol iterator (borrowElement noPanic) (accounts, []) := by
  apply CleanupReady.of_borrowElement <;> intros <;> exact List.Perm.refl _

/-- Cleanup starts in the actual state after the internal bookkeeping change. -/
theorem stateful_site : CleanupSite unwindingProtocol iterator (borrowElement noPanic)
    (accounts, []) [(first.key, firstRef)] (afterFirst, [none])
    (.unwound 77 (afterFirst, [none])) [0] :=
  .internalUnwind (first_prefix unwindingProtocol) (by decide) rfl

/-- The real element destructor and storage retirement preserve the original
unwind reason and the changed auxiliary state of the internal callback. -/
theorem stateful_downstream : Owned.cleanup unwindingProtocol.double
    (unwindingProtocol.partialDrops (afterFirst, [none]) [(first.key, firstRef)])
    (.unwound 77 (afterFirst, [none]) : Outcome ReferenceWorld (Except Error Nat) Nat Nat)
    (.unwound 77 ({ accounts with slots := [none] }, [none])) := by
  refine ⟨.returned () ({ accounts with slots := [none] }, [none]), rfl, ?_⟩
  exact ⟨.returned () ({ accounts with slots := [none] }, [none]), rfl, rfl⟩

/-- The generic extension lemma retains that same real exit in the original
protocol provider, including the source callback index and current state. -/
theorem stateful_exit_retained :
    (protocolProvider unwindingProtocol).run iterator (borrowElement noPanic) (accounts, [])
      (.unwound 77 ({ accounts with slots := [none] }, [none])) :=
  stateful_site.provider stateful_order_admitted stateful_downstream

/-- Finite internal chunks may return with bookkeeping effects or unwind;
admission does not choose a preferred exit or bound their number. -/
def returningProtocol : Protocol ReferenceExtra Nat Nat Nat :=
  { unwindingProtocol with
    internal := fun _ _ before outcome =>
      outcome = .returned () (before.1, before.2 ++ [some []]) ∨
      outcome = .unwound 77 (before.1, before.2 ++ [none]) }

/-- An actual internal return is retained in the prefix before the next
internal unwind, with both effects in their original order. -/
theorem returned_chunk_reached : CleanupSite returningProtocol iterator (borrowElement noPanic)
    (accounts, []) [(first.key, firstRef)] (afterFirst, [some [], none])
    (.unwound 77 (afterFirst, [some [], none])) [0] :=
  .internalUnwind
    (.internalReturn (first_prefix returningProtocol) (by decide) (.inl rfl))
    (by decide) (.inr rfl)

/-- Forward-prefix composition preserves the state of the returned chunk through
the later real failure and its element/storage cleanup. -/
theorem returned_chunk_retained : Trace returningProtocol iterator (borrowElement noPanic)
    0 [] (accounts, []) [0]
    (.unwound 77 ({ accounts with slots := [none] }, [some [], none])) := by
  apply returned_chunk_reached.extend (CleanupReady.of_order fun _ _ => List.Perm.refl _)
  refine ⟨.returned () ({ accounts with slots := [none] }, [some [], none]), rfl, ?_⟩
  exact ⟨.returned () ({ accounts with slots := [none] }, [some [], none]), rfl, rfl⟩

/-- A pending last insertion may be destroyed before its stored predecessor.
Admission allows this exact reverse permutation, not just the default order. -/
theorem reverse_order_admitted :
    CleanupReady pendingLastProtocol iterator (borrowElement noPanic) (accounts, []) :=
  CleanupReady.of_order fun _ acquired => List.reverse_perm acquired

/-- Both returned elements, including the pending one, are recorded before
this internal unwind starts cleanup. -/
theorem reverse_site : CleanupSite pendingLastProtocol iterator (borrowElement noPanic)
    (accounts, []) elements (afterBoth, [none]) (.unwound 77 (afterBoth, [none])) [0, 1] :=
  .internalUnwind (both_prefix pendingLastProtocol) (by decide) rfl

/-- Actual last-first release retires both distinct guard identities. -/
theorem reverse_downstream : Owned.cleanup pendingLastProtocol.double
    (pendingLastProtocol.partialDrops (afterBoth, [none]) elements)
    (.unwound 77 (afterBoth, [none]) : Outcome ReferenceWorld (Except Error Nat) Nat Nat)
    (.unwound 77 ({ accounts with slots := [none, none] }, [none])) := by
  refine ⟨.returned ()
    ({ accounts with slots := [some ⟨⟨1⟩, .shared, 0, .whole⟩, none] }, [none]), rfl, ?_⟩
  refine ⟨.returned () ({ accounts with slots := [none, none] }, [none]), rfl, ?_⟩
  exact ⟨.returned () ({ accounts with slots := [none, none] }, [none]), rfl, rfl⟩

/-- The retained trace has both original callback indices and exact cleanup state. -/
theorem reverse_exit_retained : Trace pendingLastProtocol iterator (borrowElement noPanic)
    0 [] (accounts, []) [0, 1]
    (.unwound 77 ({ accounts with slots := [none, none] }, [none])) :=
  reverse_site.extend reverse_order_admitted reverse_downstream

/-- Finish can fail after all callbacks, with an actual state change. -/
def failingFinish : Protocol ReferenceExtra Nat Nat Nat :=
  { referenceProtocol with
    finish := fun before _ outcome =>
      outcome = .unwound 41 (before.1, before.2 ++ [none]) }

/-- Default cleanup order is valid at every actual finish failure. -/
theorem finish_order_admitted :
    CleanupReady failingFinish iterator (borrowElement noPanic) (accounts, []) :=
  CleanupReady.of_order fun _ _ => List.Perm.refl _

/-- The failed transfer follows both actual source callbacks. -/
theorem finish_site : CleanupSite failingFinish iterator (borrowElement noPanic)
    (accounts, []) elements (afterBoth, [none]) (.unwound 41 (afterBoth, [none])) [0, 1] :=
  .finishUnwind (both_prefix failingFinish) rfl rfl

/-- Each actual destructor exit after failed transfer extends the root trace. -/
theorem finish_exit_retained : Trace failingFinish iterator (borrowElement noPanic)
    0 [] (accounts, []) [0, 1]
    (.unwound 41 ({ accounts with slots := [none, none] }, [none])) := by
  apply finish_site.extend finish_order_admitted
  refine ⟨.returned ()
    ({ accounts with slots := [none, some ⟨⟨2⟩, .shared, 0, .whole⟩] }, [none]), rfl, ?_⟩
  refine ⟨.returned () ({ accounts with slots := [none, none] }, [none]), rfl, ?_⟩
  exact ⟨.returned () ({ accounts with slots := [none, none] }, [none]), rfl, rfl⟩

/-- A real second checked-borrow error follows the fresh first acquisition. -/
theorem borrow_error_site : CleanupSite referenceProtocol longerIterator (borrowElement noPanic)
    (locked, []) [(first.key, failureRef)] (duringFailure, [])
    (.returned (.error .AccountBorrowFailed) (duringFailure, [])) [0, 1] :=
  .error (.next .start (by decide) rfl
      (borrowElement_ok noPanic (locked, []) (duringFailure, []) first failureRef rfl))
    (by decide) rfl
    (borrowElement_error noPanic (duringFailure, []) (duringFailure, []) second
      .AccountBorrowFailed rfl)

/-- Ordinary callback errors retain the prior unrelated exclusive guard and
return their original error after releasing only the acquired shared guard. -/
theorem borrow_error_retained : Trace referenceProtocol longerIterator (borrowElement noPanic)
    0 [] (locked, []) [0, 1]
    (.returned (.error .AccountBorrowFailed)
      ({ accounts with slots := [some ⟨⟨2⟩, .exclusive, 0, .whole⟩, none] }, [])) := by
  apply borrow_error_site.extend (CleanupReady.of_order fun _ _ => List.Perm.refl _)
  refine ⟨.returned ()
    ({ accounts with slots := [some ⟨⟨2⟩, .exclusive, 0, .whole⟩, none] }, []), rfl, ?_⟩
  exact ⟨.returned ()
    ({ accounts with slots := [some ⟨⟨2⟩, .exclusive, 0, .whole⟩, none] }, []), rfl, rfl⟩

/-- A generic caller may supply an effectful callback with actual unwind
exits; this is separate from the source checked-borrow closure. -/
def callbackWithUnwind : Callback.Run ReferenceWorld AccountInfo.Value
    (Except Error Element) Nat Nat := fun before info outcome =>
  borrowElement noPanic before info outcome ∨
    outcome = .unwound 9 (before.1, before.2 ++ [none])

/-- The generic unwind branch retains its actual callback state and cleans the
already acquired reference, with no assumption on uncalled source callbacks. -/
theorem generic_callback_unwind_retained : Trace referenceProtocol iterator callbackWithUnwind
    0 [] (accounts, []) [0, 1]
    (.unwound 9 ({ accounts with slots := [none] }, [none])) := by
  have reached : ForwardPrefix referenceProtocol iterator callbackWithUnwind (accounts, [])
      1 [(first.key, firstRef)] (afterFirst, []) [0] :=
    .next .start (by decide) rfl (.inl first_callback)
  have site : CleanupSite referenceProtocol iterator callbackWithUnwind (accounts, [])
      [(first.key, firstRef)] (afterFirst, [none]) (.unwound 9 (afterFirst, [none])) [0, 1] :=
    .callbackUnwind reached (by decide) (show iterator.elementAt (afterFirst, []) 1 = some second
      from rfl)
      (.inr rfl)
  apply site.extend (CleanupReady.of_order fun _ _ => List.Perm.refl _)
  refine ⟨.returned () ({ accounts with slots := [none] }, [none]), rfl, ?_⟩
  exact ⟨.returned () ({ accounts with slots := [none] }, [none]), rfl, rfl⟩

/-- Termination ignores even a malformed partial order. -/
def terminalBadOrder : Protocol ReferenceExtra Nat Nat Nat :=
  { leakingOrderProtocol with internal := fun _ _ _ outcome => outcome = .terminated 88 }

/-- An actual terminal exit survives after a nonempty prefix without any
order, destructor, or retirement assumption. -/
theorem terminal_bypasses_order : Trace terminalBadOrder iterator (borrowElement noPanic)
    0 [] (accounts, []) [0] (.terminated 88) :=
  (first_prefix terminalBadOrder).internal_terminal (by decide) rfl

/-- Order validity imposes no termination requirement on storage retirement. -/
def absentRetirement : Protocol ReferenceExtra Nat Nat Nat :=
  { unwindingProtocol with retire := fun _ _ _ _ => False }

/-- This provider has a valid actual cleanup order despite unavailable retirement. -/
theorem absent_retirement_order_admitted :
    CleanupReady absentRetirement iterator (borrowElement noPanic) (accounts, []) :=
  CleanupReady.of_order fun _ _ => List.Perm.refl _

/-- The first internal unwind is an actual cleanup site before any acquisition. -/
theorem absent_retirement_site : CleanupSite absentRetirement iterator (borrowElement noPanic)
    (accounts, []) [] (accounts, [none]) (.unwound 77 (accounts, [none])) [] :=
  .internalUnwind .start (by decide) rfl

/-- No retirement exit is invented by admission or by the extension theorem. -/
theorem absent_retirement_stays_partial : ∀ final,
    ¬ absentRetirement.cleanup []
      (.unwound 77 (accounts, [none]) : Outcome ReferenceWorld (Except Error Nat) Nat Nat) final :=
        by
  intro final cleaned
  have actual := (absent_retirement_site.cleanup_iff absent_retirement_order_admitted).1 cleaned
  obtain ⟨_, impossible, _⟩ := actual
  exact impossible

/-- Actual second-unwind policy outcomes remain explicit and are retained. -/
theorem double_unwind_retained : Trace doubleUnwindProtocol iterator (borrowElement noPanic)
    0 [] (accounts, []) [0] (.terminated 100) := by
  have site : CleanupSite doubleUnwindProtocol iterator (borrowElement noPanic)
      (accounts, []) [(first.key, firstRef)] (afterFirst, [none])
      (.unwound 77 (afterFirst, [none])) [0] :=
    .internalUnwind (first_prefix doubleUnwindProtocol) (by decide) rfl
  apply site.extend (CleanupReady.of_order fun _ _ => List.Perm.refl _)
  refine ⟨.returned () ({ accounts with slots := [none] }, [none]), rfl, ?_⟩
  exact ⟨.unwound 23 ({ accounts with slots := [none] }, [none, none]), rfl, 100, rfl, rfl⟩

/-- A successful vector transfer also needs no partial-cleanup order check. -/
theorem success_bypasses_order : Trace referenceProtocol iterator (borrowElement noPanic)
    0 [] (accounts, []) [0, 1] (.returned (.ok 0) (afterBoth, [some elements])) :=
  (both_prefix referenceProtocol).finish_returned rfl ⟨.returned 0 [some elements], rfl, rfl⟩

end SolanalibTest.Specs.Core.TokenAllocatedCollectAdmission
