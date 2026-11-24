/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedCollectFrame
import Solanalib.Specs.Core.TokenRequestAllocatedCollectFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.TokenAllocatedCollect

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.AllocatedCollect

/-- Two distinct data cells containing nontrivial current bytes. -/
def accounts : AccountInfo.State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data [37], AccountInfo.sampleProfile.policy⟩,
    ⟨.data [19, 23], AccountInfo.sampleProfile.policy⟩], []⟩

/-- First source account, retaining the existing typed lamports cell. -/
def first : AccountInfo.Value := { AccountInfo.sampleInfo with key := .ofNat 11 }

/-- Second source account has a distinct key and data cell. -/
def second : AccountInfo.Value :=
  { AccountInfo.sampleInfo with key := .ofNat 22, data := ⟨2⟩ }

/-- The source iterator has two elements in a definite order. -/
def iterator : Iterator ReferenceExtra := ⟨2, fun _ index => [first, second][index]?⟩

/-- A checked borrow does not need a panic exit in these reference controls. -/
def noPanic : Callback.Run ReferenceWorld Onchain.Panic Empty Nat Nat := fun _ _ _ => False

/-- Actual shared guard produced by the first acquisition. -/
def firstRef : AllocatedControl.DataRef := ⟨⟨0, 0⟩, 1⟩

/-- Actual shared guard produced by the second acquisition. -/
def secondRef : AllocatedControl.DataRef := ⟨⟨1, 0⟩, 2⟩

/-- State after only the first actual checked borrow. -/
def afterFirst : AccountInfo.State :=
  { accounts with slots := [some ⟨⟨1⟩, .shared, 0, .whole⟩] }

/-- State after both actual checked borrows. -/
def afterBoth : AccountInfo.State :=
  { accounts with slots := [some ⟨⟨1⟩, .shared, 0, .whole⟩,
    some ⟨⟨2⟩, .shared, 0, .whole⟩] }

/-- The completed vector keeps copied keys and guard identities in source order. -/
def elements : List Element := [(first.key, firstRef), (second.key, secondRef)]

/-- A real first callback follows the common checked-borrow implementation. -/
theorem first_callback : borrowElement noPanic (accounts, []) first
    (.returned (.ok (first.key, firstRef)) (afterFirst, [])) :=
  borrowElement_ok noPanic _ _ _ _ rfl

/-- A real second callback sees the state left by the first acquisition. -/
theorem second_callback : borrowElement noPanic (afterFirst, []) second
    (.returned (.ok (second.key, secondRef)) (afterBoth, [])) :=
  borrowElement_ok noPanic _ _ _ _ rfl

/-- A complete successful trace runs both callbacks and transfers a nonempty
owned vector; it does not choose bytes or guard identities independently. -/
theorem successful_trace : Trace referenceProtocol iterator (borrowElement noPanic)
    0 [] (accounts, []) [0, 1] (.returned (.ok 0) (afterBoth, [some elements])) := by
  refine .next (by decide) rfl first_callback ?_
  refine .next (by decide) rfl second_callback ?_
  exact .done rfl ⟨.returned 0 [some elements], rfl, rfl⟩ rfl

/-- The closed reference provider has a nonempty successful execution. -/
theorem successful_execution : referenceProvider.run iterator (borrowElement noPanic)
    (accounts, []) (.returned (.ok 0) (afterBoth, [some elements])) :=
  ⟨[0, 1], successful_trace⟩

/-- The current observation of the result retains both ordered live elements. -/
theorem successful_current : referenceVectors.current (afterBoth, [some elements]) 0 =
    some elements := rfl

/-- The generic protocol and resource laws derive the exact result length at
this real successful acquisition trace. -/
theorem successful_length_from_laws : ∃ values,
    referenceVectors.current (afterBoth, [some elements]) 0 = some values ∧ values.length = 2 :=
  Provider.success_length reference_conforms reference_resource_laws iterator
    (borrowElement noPanic) (accounts, []) (afterBoth, [some elements]) 0 successful_execution

/-- Both retained references read the actual account cells, not saved byte arrays. -/
theorem successful_references_read_current :
    firstRef.read (afterBoth, [some elements]) = some [37] ∧
    secondRef.read (afterBoth, [some elements]) = some [19, 23] := ⟨rfl, rfl⟩

/-- Dropping the returned vector releases both actual guards, then its own
storage, preserving the account contents and leaving permanent tombstones. -/
theorem successful_vector_drop : referenceVectors.drop (afterBoth, [some elements]) 0
    (.returned () ({ accounts with slots := [none, none] }, [none])) := by
  refine ⟨elements, rfl, ?_⟩
  refine ⟨.returned ()
    ({ accounts with slots := [none, some ⟨⟨2⟩, .shared, 0, .whole⟩] }, [some elements]), rfl, ?_⟩
  refine ⟨.returned () ({ accounts with slots := [none, none] }, [some elements]), rfl, ?_⟩
  exact ⟨.returned () ({ accounts with slots := [none, none] }, [none]),
    ⟨.returned () [none], ⟨elements, rfl, rfl⟩, rfl⟩, rfl⟩

/-- The first returned reference is unusable after its owning vector is dropped. -/
theorem dropped_reference_rejected :
    firstRef.read (({ accounts with slots := [none, none] }, [none]) : ReferenceWorld) = none := rfl

/-- A conflicting owner of the second cell predates this collection call. -/
def locked : AccountInfo.State :=
  { accounts with slots := [some ⟨⟨2⟩, .exclusive, 0, .whole⟩] }

/-- First acquisition during the failure case follows the preexisting guard. -/
def duringFailure : AccountInfo.State :=
  { accounts with slots := [some ⟨⟨2⟩, .exclusive, 0, .whole⟩,
    some ⟨⟨1⟩, .shared, 0, .whole⟩] }

/-- The partial result has a fresh identity after the unrelated exclusive guard. -/
def failureRef : AllocatedControl.DataRef := ⟨⟨1, 0⟩, 1⟩

/-- The third valid source account is deliberately present to check early stopping. -/
def longerIterator : Iterator ReferenceExtra :=
  ⟨3, fun _ index => [first, second, first][index]?⟩

/-- An actual second borrow failure cleans the first acquisition, preserves
the preexisting exclusive guard, and never invokes the third valid callback. -/
theorem partial_acquisition_failure : Trace referenceProtocol longerIterator (borrowElement noPanic)
    0 [] (locked, []) [0, 1]
    (.returned (.error .AccountBorrowFailed)
      ({ accounts with slots := [some ⟨⟨2⟩, .exclusive, 0, .whole⟩, none] }, [])) := by
  refine .next (by decide) rfl (borrowElement_ok noPanic _ _ _ failureRef rfl) ?_
  refine .error (by decide) rfl (borrowElement_error noPanic _ _ _ .AccountBorrowFailed rfl) ?_
  refine ⟨.refl _, ?_⟩
  refine ⟨.returned ()
    ({ accounts with slots := [some ⟨⟨2⟩, .exclusive, 0, .whole⟩, none] }, []), rfl, ?_⟩
  exact ⟨.returned ()
    ({ accounts with slots := [some ⟨⟨2⟩, .exclusive, 0, .whole⟩, none] }, []), rfl, rfl⟩

/-- The dependency admits the real partial-acquisition error and its cleanup state. -/
theorem partial_failure_execution : referenceProvider.run longerIterator (borrowElement noPanic)
    (locked, []) (.returned (.error .AccountBorrowFailed)
      ({ accounts with slots := [some ⟨⟨2⟩, .exclusive, 0, .whole⟩, none] }, [])) :=
  ⟨[0, 1], partial_acquisition_failure⟩

/-- Failure cleanup leaves the unrelated exclusive guard live with its original data. -/
theorem failure_preserves_prior_guard : Borrow.current
    ({ accounts with slots := [some ⟨⟨2⟩, .exclusive, 0, AccountInfo.View.whole⟩, none] }) ⟨0, 0⟩ =
    .ok (AccountInfo.View.whole, .data [19, 23]) := rfl

/-- Failure cleanup consumes the newly acquired guard instead of leaking it. -/
theorem failure_retires_partial_guard : failureRef.read
    (({ accounts with slots := [some ⟨⟨2⟩, .exclusive, 0, .whole⟩, none] }, []) : ReferenceWorld) =
    none := rfl

/-- The protocol cannot justify skipping the middle source callback. -/
theorem skipped_callback_rejected : ∀ outcome,
    ¬ Trace referenceProtocol longerIterator (borrowElement noPanic)
      0 [] (locked, []) [0, 2] outcome := by
  intro outcome trace
  have impossible := trace.calls_prefix
  change [0, 2] = [0, 1] at impossible
  cases impossible

/-- The protocol cannot reuse the first callback in place of the second. -/
theorem repeated_callback_rejected : ∀ outcome,
    ¬ Trace referenceProtocol longerIterator (borrowElement noPanic)
      0 [] (locked, []) [0, 0] outcome := by
  intro outcome trace
  have impossible := trace.calls_prefix
  change [0, 0] = [0, 1] at impossible
  cases impossible

/-- A missing current source element cannot become an invented borrow error
or successful result in the reference provider. -/
theorem missing_element_rejected : ∀ outcome,
    ¬ referenceProvider.run ⟨1, fun _ _ => none⟩ (borrowElement noPanic) (accounts, []) outcome :=
      by
  rintro outcome ⟨calls, trace⟩
  cases trace with
  | done endOfIterator finished exit => cases endOfIterator
  | next within read called tail => cases read
  | error within read called cleaned => cases read
  | unwind within read called cleaned => cases read
  | terminal within read called => cases read
  | internalReturn within stepped tail => cases stepped
  | internalUnwind within stepped cleaned => cases stepped
  | internalTerminal within stepped => cases stepped

/-- An empty source iterator transfers a represented empty vector without
invoking an otherwise unavailable source callback. -/
theorem empty_collection : referenceProvider.run ⟨0, fun _ _ => none⟩ (fun _ _ _ => False)
    (accounts, []) (.returned (.ok 0) (accounts, [some []])) :=
  ⟨[], .done rfl ⟨.returned 0 [some []], rfl, rfl⟩ rfl⟩

/-- An internal provider can mutate its bookkeeping and then unwind. This
does not prescribe the allocation granularity of another collection provider. -/
def unwindingProtocol : Protocol ReferenceExtra Nat Nat Nat :=
  { referenceProtocol with
    internal := fun _ _ before outcome =>
      outcome = .unwound 77 (before.1, before.2 ++ [none]) }

/-- The state-changing unwind provider still satisfies the explicit account
frame: allocation bookkeeping can change while held references remain live. -/
theorem unwinding_internal_frame (index : Nat) (acquired : List Element)
    (before : ReferenceWorld) (outcome : Outcome ReferenceWorld Unit Nat Nat)
    (called : unwindingProtocol.internal index acquired before outcome) :
    PreservesAccounts before outcome := by
  cases called
  rfl

/-- Before cleanup begins, the framed actual unwind still exposes the current
bytes through the same retained reference identity. -/
theorem unwind_reference_live_before_cleanup :
    firstRef.read ((afterFirst, [none]) : ReferenceWorld) = some [37] := by
  have framed := unwind_read 1 [(first.key, firstRef)]
    (unwinding_internal_frame 1 [(first.key, firstRef)])
    (afterFirst, []) (afterFirst, [none]) firstRef 77 rfl
  exact framed.trans rfl

/-- The first acquired reference is dropped in the actual internal-unwind
state, retaining the changed auxiliary state and original reason of the provider. -/
theorem internal_unwind_cleans_current_state : Trace unwindingProtocol iterator (borrowElement
  noPanic)
    0 [] (accounts, []) [0]
    (.unwound 77 ({ accounts with slots := [none] }, [none])) := by
  refine .next (by decide) rfl first_callback ?_
  refine .internalUnwind (after := (afterFirst, [none])) (by decide) rfl ?_
  refine ⟨.refl _, ?_⟩
  refine ⟨.returned () ({ accounts with slots := [none] }, [none]), rfl, ?_⟩
  exact ⟨.returned () ({ accounts with slots := [none] }, [none]), rfl, rfl⟩

/-- A partial collector may still hold the most recently returned Ref as a
pending insertion input. This two-element control drops it before its stored
predecessor, with no unproved release-commutation assumption. -/
def pendingLastProtocol : Protocol ReferenceExtra Nat Nat Nat :=
  { unwindingProtocol with partialOrder := fun _ acquired => acquired.reverse }

/-- Both real callbacks ran, but insertion failed with the last Ref pending.
Cleanup follows the supplied last-first order and retires both actual guards. -/
theorem pending_last_drops_before_stored_prefix :
    Trace pendingLastProtocol iterator (borrowElement noPanic) 0 [] (accounts, []) [0, 1]
      (.unwound 77 ({ accounts with slots := [none, none] }, [none])) := by
  refine .next (by decide) rfl first_callback ?_
  refine .next (by decide) rfl second_callback ?_
  refine .internalUnwind (after := (afterBoth, [none])) (by decide) rfl ?_
  refine ⟨List.reverse_perm _, ?_⟩
  refine ⟨.returned ()
    ({ accounts with slots := [some ⟨⟨1⟩, .shared, 0, .whole⟩, none] }, [none]), rfl, ?_⟩
  refine ⟨.returned () ({ accounts with slots := [none, none] }, [none]), rfl, ?_⟩
  exact ⟨.returned () ({ accounts with slots := [none, none] }, [none]), rfl, rfl⟩

/-- An invalid cleanup order that silently omits every acquired reference. -/
def leakingOrderProtocol : Protocol ReferenceExtra Nat Nat Nat :=
  { unwindingProtocol with partialOrder := fun _ _ => [] }

/-- The permutation check rejects a cleanup plan that would leak a live Ref. -/
theorem omitted_guard_order_rejected : ∀ outcome, ¬ leakingOrderProtocol.cleanup
    [(first.key, firstRef)] (.unwound 77 (afterFirst, []) : Outcome ReferenceWorld Nat Nat Nat)
    outcome := by
  intro outcome run
  have impossible := run.1.length_eq
  change 0 = 1 at impossible
  cases impossible

/-- An internal terminal policy with no cleanup or continuation. -/
def terminalProtocol : Protocol ReferenceExtra Nat Nat Nat :=
  { referenceProtocol with internal := fun _ _ _ outcome => outcome = .terminated 88 }

/-- Internal termination stops after the first callback without inventing a
later callback, a successful vector, or a destructor execution. -/
theorem internal_terminal_stops : Trace terminalProtocol iterator (borrowElement noPanic)
    0 [] (accounts, []) [0] (.terminated 88) := by
  exact .next (by decide) rfl first_callback (.internalTerminal (by decide) rfl)

/-- A storage cleanup unwind is separate from the already retired element guard. -/
def doubleUnwindProtocol : Protocol ReferenceExtra Nat Nat Nat :=
  { unwindingProtocol with
    retire := fun _ _ before outcome => outcome = .unwound 23 (before.1, before.2 ++ [none]) }

/-- A second unwind can terminate only through the supplied policy; both
unwind reasons reach it after the guard release and actual storage effect. -/
theorem cleanup_double_unwind : Trace doubleUnwindProtocol iterator (borrowElement noPanic)
    0 [] (accounts, []) [0] (.terminated 100) := by
  refine .next (by decide) rfl first_callback ?_
  refine .internalUnwind (after := (afterFirst, [none])) (by decide) rfl ?_
  refine ⟨.refl _, ?_⟩
  refine ⟨.returned () ({ accounts with slots := [none] }, [none]), rfl, ?_⟩
  exact ⟨.unwound 23 ({ accounts with slots := [none] }, [none, none]), rfl, 100, rfl, rfl⟩

end SolanalibTest.Specs.Core.TokenAllocatedCollect
