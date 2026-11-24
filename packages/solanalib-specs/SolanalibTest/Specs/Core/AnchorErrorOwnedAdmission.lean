/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOwnedCallbackContracts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AnchorErrorOwnedAdmission

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorErrorOwned

/-- Minimal current error without any owned String field. -/
def payload : Payload Reference.StringId := .program ⟨.invalidArgument, none, none⟩

/-- Stable Box zero; the handle is not an immutable payload snapshot. -/
def error : Error Reference.BoxId := ⟨⟨0⟩⟩

/-- A live Box and a finite two-String allocation budget. -/
def initial : Reference.State := ⟨[], [some payload], 2, []⟩

/-- Borrowed unit operands isolate the cleanup domain of the held error. -/
def args : ValuesArgs Reference.BoxId Unit Unit := ⟨error, (), ()⟩

/-- Adversarial state after a callback erases the current Box of `self`. -/
def erased : Reference.State := { initial with boxes := [none] }

private theorem ready : Ready Reference.natOps initial error :=
  ⟨payload, rfl, List.nodup_nil, fun _ member => nomatch member⟩

private theorem laws : Reference.natOps.ComparisonLaws :=
  ⟨Reference.natOps_laws.stringDrop.other, Reference.natOps_laws.drop_boxes,
    Reference.natOps_laws.store.current, Reference.natOps_laws.store_strings⟩

/-- A real finite left unwind erases self; both operand drops return normally. -/
def erasedLeft : ValuesCallbacks Reference.State Reference.StringId Unit Unit Nat Nat where
  left := fun _ _ outcome => outcome = .unwound 7 erased
  right := fun _ _ _ => False
  dropLeft := fun before _ outcome => outcome = .returned () before
  dropRight := fun before _ outcome => outcome = .returned () before
  double := fun _ _ _ terminal => terminal = 99

private theorem erased_left_returned : erasedLeft.ReturnedAdmissible Reference.natOps args initial
  where
  left := by intro _ _ _ _ _ run; cases run
  right := by intro _ _ _ _ _ _ _ run; cases run
  dropLeft := by intro _ _ _ _ _ _ run; cases run; exact HeldFrame.refl _ _ _ _
  dropRight := by intro _ _ _ _ _ _ run; cases run; exact HeldFrame.refl _ _ _ _

private theorem erased_scope {outcome : Outcome Reference.State (Error Reference.BoxId) Nat Nat}
    (run : Owned.scope erasedLeft.double
      [fun state result => erasedLeft.dropLeft state args.left result,
       fun state result => erasedLeft.dropRight state args.right result]
      (valuesBody Reference.natOps erasedLeft args) initial () outcome) :
    outcome = .unwound 7 erased := by
  obtain ⟨bodyExit, ⟨first, called, next⟩, cleaned⟩ := run
  cases called
  change bodyExit = .unwound 7 erased at next
  cases next
  obtain ⟨firstDrop, dropped, rest⟩ := cleaned
  cases dropped
  obtain ⟨secondDrop, dropped, rest⟩ := rest
  cases dropped
  exact rest

private theorem erased_no_outcome :
    ¬ ∃ outcome, withValues Reference.natOps erasedLeft initial args outcome := by
  rintro ⟨outcome, _, _, ⟨pending, scope, cleanup⟩ | ⟨_, _, ⟨first, called, next⟩, _⟩⟩
  · have equal := erased_scope scope
    cases equal
    obtain ⟨_, ⟨actual, ⟨current, present, _⟩, _⟩, _⟩ := cleanup
    cases present
  · -- The return-place alternative needs a normal body, but the left conversion unwinds.
    cases called
    cases next

/-- A returned-only admission can accept a finite unwind that vanishes at the local Box lookup of
`self`. The reached cleanup premise rejects it. -/
theorem left_unwind_erasure_is_rejected :
    Reference.natOps.ComparisonLaws ∧ Ready Reference.natOps initial error ∧
    erasedLeft.ReturnedAdmissible Reference.natOps args initial ∧
    erasedLeft.left initial () (.unwound 7 erased) ∧
    (¬ ∃ outcome, withValues Reference.natOps erasedLeft initial args outcome) ∧
    ¬ erasedLeft.CallReady Reference.natOps args initial := by
  refine ⟨laws, ready, erased_left_returned, rfl, erased_no_outcome, ?_⟩
  intro admitted
  obtain ⟨_, present, _⟩ := admitted.left_unwind 7 erased rfl
  cases present

/-- The first conversion has returned an initialized owned String. -/
def afterFirst : Reference.State := ⟨[some "first"], [some payload], 1, []⟩

/-- A right unwind erases only that actual pending String, leaving self live. -/
def firstErased : Reference.State := { afterFirst with strings := [none] }

/-- Actual right-conversion corruption before its pending first-String drop. -/
def erasedRight : ValuesCallbacks Reference.State Reference.StringId Unit Unit Nat Nat :=
  { erasedLeft with
    left := fun _ _ outcome => outcome = .returned ⟨0⟩ afterFirst
    right := fun _ _ outcome => outcome = .unwound 11 firstErased }

/-- Universal admission checks the actual first result on a right unwind,
even though the error itself still has a valid current payload. -/
theorem right_unwind_partial_owner_erasure_is_rejected :
    erasedRight.left initial () (.returned ⟨0⟩ afterFirst) ∧
    erasedRight.right afterFirst () (.unwound 11 firstErased) ∧
    Ready Reference.natOps firstErased error ∧
    ¬ erasedRight.CallReady Reference.natOps args initial := by
  refine ⟨rfl, rfl, ⟨payload, rfl, List.nodup_nil, fun _ member => nomatch member⟩, ?_⟩
  intro admitted
  obtain ⟨_, _, _, ⟨_, present⟩, _⟩ := admitted.right_unwind ⟨0⟩ afterFirst 11 firstErased rfl rfl
  cases present

/-- A second actual conversion returns another distinct current String. -/
def afterSecond : Reference.State := ⟨[some "first", some "second"], [some payload], 0, []⟩

/-- The actual output of the source assignment before operand destruction. -/
def afterStore : Reference.State :=
  { afterSecond with boxes := [some (payload.withValues ⟨0⟩ ⟨1⟩)], events := [.write ⟨0⟩] }

/-- Operand destruction erases the newly assigned error and starts unwinding. -/
def afterBadDrop : Reference.State := { afterStore with boxes := [none] }

/-- Deterministic finite conversions isolate the later operand-unwind site. -/
def erasedOperand : ValuesCallbacks Reference.State Reference.StringId Unit Unit Nat Nat :=
  { erasedLeft with
    left := fun _ _ outcome => outcome = .returned ⟨0⟩ afterFirst
    right := fun _ _ outcome => outcome = .returned ⟨1⟩ afterSecond
    dropLeft := fun _ _ outcome => outcome = .unwound 13 afterBadDrop }

private theorem assigned_body :
    valuesBody Reference.natOps erasedOperand args initial () (.returned error afterStore) :=
  ⟨.returned ⟨0⟩ afterFirst, rfl, .returned ⟨1⟩ afterSecond,
    ⟨.returned ⟨1⟩ afterSecond, rfl, rfl⟩,
    .returned error afterStore, ⟨payload, rfl, .returned () afterSecond, rfl,
      payload, rfl, afterStore, rfl, rfl⟩, rfl⟩

private theorem assigned_ready : Ready Reference.natOps afterStore error := by
  refine ⟨payload.withValues ⟨0⟩ ⟨1⟩, rfl, by decide, ?_⟩
  intro resource member
  change resource ∈ [⟨0⟩, ⟨1⟩] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨"first", rfl⟩
  · have equal := List.mem_singleton.mp member
    subst resource
    exact ⟨"second", rfl⟩

/-- The gate sees the actual completed assignment before the first operand
unwind. It cannot be satisfied merely by framing returned destructor exits. -/
theorem operand_unwind_erasure_is_rejected :
    valuesBody Reference.natOps erasedOperand args initial () (.returned error afterStore) ∧
    erasedOperand.dropLeft afterStore () (.unwound 13 afterBadDrop) ∧
    ¬ erasedOperand.CallReady Reference.natOps args initial := by
  refine ⟨assigned_body, rfl, ?_⟩
  intro admitted
  have entry : valuesCleanupEntry Reference.natOps erasedOperand args [] initial
      (.returned error afterStore) := ⟨.returned error afterStore, assigned_body, rfl⟩
  obtain ⟨_, present, _⟩ := admitted.dropLeft (.returned error afterStore) afterStore
    (.unwound 13 afterBadDrop) entry rfl assigned_ready rfl
  cases present

/-- Ordinary local stores are missing even at live Boxes; all observations and
the String-drop primitives are otherwise the reference interpretation. -/
def missingStore : Ops Reference.State Reference.StringId Reference.BoxId Nat :=
  { Reference.natOps with writeBox := fun _ _ _ => none }

private theorem missing_store_laws : missingStore.ComparisonLaws where
  string_other := Reference.natOps_laws.stringDrop.other
  drop_boxes := Reference.natOps_laws.drop_boxes
  store_current := by intro _ _ _ _ impossible; cases impossible
  store_strings := by intro _ _ _ _ impossible; cases impossible

/-- No irrelevant allocation or retirement provider capability is added. -/
def missingStoreTypes : Types := ⟨Reference.State, Reference.StringId, Reference.BoxId, Nat,
  missingStore⟩

private theorem no_pubkeys_outcome :
    ¬ ∃ outcome, withPubkeys missingStore initial (error, sampleKey, sampleKey) outcome := by
  rintro ⟨outcome, current, present, cleanupExit, cleaned, rest⟩
  have equal : current = payload := Option.some.inj present.symm
  subst current
  change cleanupExit = .returned () initial at cleaned
  cases cleaned
  obtain ⟨_, _, _, impossible, _⟩ := rest
  cases impossible

/-- Comparison frame laws alone admitted a call with a real empty cleanup and
no local assignment result. The reached-store admission now excludes it. -/
theorem missing_pubkeys_store_is_rejected :
    missingStore.ComparisonLaws ∧ Ready missingStore initial error ∧
    dropStrings missingStore [] initial () (.returned () initial) ∧
    (¬ ∃ outcome, withPubkeys missingStore initial (error, sampleKey, sampleKey) outcome) ∧
    ¬ (withPubkeysFamily.contract missingStoreTypes).requires initial (error, sampleKey, sampleKey)
      := by
  refine ⟨missing_store_laws, ready, rfl, no_pubkeys_outcome, ?_⟩
  intro admitted
  obtain ⟨_, impossible⟩ := admitted.2.2 payload rfl initial rfl
  cases impossible

/-- Returning conversions with trivial operand drops isolate store failure. -/
def normalConversions : ValuesCallbacks Reference.State Reference.StringId Unit Unit Nat Nat :=
  { erasedOperand with dropLeft := fun before _ outcome => outcome = .returned () before }

private theorem missing_values_returned :
    normalConversions.ReturnedAdmissible missingStore args initial where
  left := by
    intro actual resource after present _ run
    cases run
    have same : actual = payload := Option.some.inj present.symm
    subst actual
    exact ⟨⟨rfl, fun _ member => nomatch member⟩, ⟨"first", rfl⟩, by simp [payload,
      Payload.strings, originStrings, comparedStrings]⟩
  right := by
    intro actual retained afterLeft resource after present _ first run
    cases first
    cases run
    have same : actual = payload := Option.some.inj present.symm
    subst actual
    refine ⟨⟨rfl, ?_⟩, ⟨"second", rfl⟩, by decide⟩
    intro held member
    change held ∈ [⟨0⟩] at member
    have same := List.mem_singleton.mp member
    subst held
    rfl
  dropLeft := by intro _ _ _ _ _ _ run; cases run; exact HeldFrame.refl _ _ _ _
  dropRight := by intro _ _ _ _ _ _ run; cases run; exact HeldFrame.refl _ _ _ _

private theorem no_values_body :
    ¬ ∃ outcome, valuesBody missingStore normalConversions args initial () outcome := by
  rintro ⟨outcome, first, called, next⟩
  cases called
  obtain ⟨second, guarded, assignment⟩ := next
  obtain ⟨rightExit, called, kept⟩ := guarded
  cases called
  cases kept
  obtain ⟨actual, assigned, _⟩ := assignment
  obtain ⟨current, present, cleanupExit, cleaned, rest⟩ := assigned
  have same : current = payload := Option.some.inj present.symm
  subst current
  change cleanupExit = .returned () afterSecond at cleaned
  cases cleaned
  obtain ⟨_, _, _, impossible, _⟩ := rest
  cases impossible

/-- The old admission accepted both real conversions but their local store
had no outcome. The new reached assignment condition excludes exactly that
missing continuation without assuming either callback terminates. -/
theorem missing_values_store_is_rejected :
    missingStore.ComparisonLaws ∧ Ready missingStore initial error ∧
    normalConversions.ReturnedAdmissible missingStore args initial ∧
    normalConversions.left initial () (.returned ⟨0⟩ afterFirst) ∧
    normalConversions.right afterFirst () (.returned ⟨1⟩ afterSecond) ∧
    (¬ ∃ outcome, valuesBody missingStore normalConversions args initial () outcome) ∧
    ¬ normalConversions.CallReady missingStore args initial := by
  refine ⟨missing_store_laws, ready, missing_values_returned, rfl, rfl, no_values_body, ?_⟩
  intro admitted
  have store := admitted.assignment ⟨0⟩ afterFirst ⟨1⟩ afterSecond rfl rfl
  obtain ⟨_, impossible⟩ := store payload rfl afterSecond rfl
  cases impossible

/-- Terminal conversion outcomes have no invented post-state. -/
def terminalCallbacks : ValuesCallbacks Reference.State Reference.StringId Unit Unit Nat Nat :=
  { erasedLeft with left := fun _ _ outcome => outcome = .terminated 41 }

private theorem terminal_admissible :
    terminalCallbacks.Admissible Reference.natOps args initial where
  left := by intro _ _ _ _ run; cases run; trivial
  right := by intro _ _ _ _ _ _ first _; cases first
  dropLeft := by intro _ _ _ _ _ _ run; cases run; exact HeldFrame.refl _ _ _ _
  dropRight := by intro _ _ _ _ _ _ run; cases run; exact HeldFrame.refl _ _ _ _

/-- Terminal exits are admitted and retained without executing either operand
or self cleanup. The new premises do not demand a terminal post-state. -/
theorem terminal_conversion_is_retained :
    terminalCallbacks.CallReady Reference.natOps args initial ∧
    withValues Reference.natOps terminalCallbacks initial args (.terminated 41) := by
  refine ⟨ValuesCallbacks.CallReady.of_admissible ready terminal_admissible
    Reference.natOps_laws.drop_boxes Reference.natOps_laws.store.available, ?_⟩
  apply withValues_scope_terminal Reference.natOps terminalCallbacks (payload := payload) rfl
  exact ⟨.terminated 41, ⟨.terminated 41, rfl, rfl⟩,
    (Owned.cleanup_terminated _ _ _ _).mpr rfl⟩

/-- A second unwind aborts before any later error lookup. Its actual state is
allowed to lack the error, since source cleanup never reaches that lookup. -/
def doubleCallbacks : ValuesCallbacks Reference.State Reference.StringId Unit Unit Nat Nat :=
  { erasedLeft with
    left := fun before _ outcome => outcome = .unwound 7 before
    dropLeft := fun _ _ outcome => outcome = .unwound 8 erased }

private theorem double_returned : doubleCallbacks.ReturnedAdmissible Reference.natOps args initial
  where
  left := by intro _ _ _ _ _ run; cases run
  right := by intro _ _ _ _ _ _ _ run; cases run
  dropLeft := by intro _ _ _ _ _ _ run; cases run
  dropRight := by intro _ _ _ _ _ _ run; cases run; exact HeldFrame.refl _ _ _ _

private theorem double_ready : doubleCallbacks.CallReady Reference.natOps args initial where
  returned := double_returned
  left_unwind := by intro _ _ run; cases run; exact ready
  right_unwind := by intro _ _ _ _ first _; cases first
  dropLeft := by
    intro pending before outcome reached located _ run
    obtain ⟨bodyExit, ⟨first, called, next⟩, trace⟩ := reached
    cases called
    change bodyExit = .unwound 7 initial at next
    cases next
    cases trace
    cases run
    trivial
  dropRight := by
    intro pending before outcome reached located _ _
    obtain ⟨bodyExit, ⟨first, called, next⟩, trace⟩ := reached
    cases called
    change bodyExit = .unwound 7 initial at next
    cases next
    obtain ⟨dropped, called, finished⟩ := trace
    cases called
    obtain ⟨terminal, _, equal⟩ := finished
    cases equal
    exact False.elim located
  assignment := by intro _ _ _ _ first _; cases first

/-- Double unwind keeps its supplied terminal outcome and does not require
resources for a later cleanup step that the source never executes. -/
theorem double_unwind_needs_no_later_resources :
    doubleCallbacks.CallReady Reference.natOps args initial ∧
    withValues Reference.natOps doubleCallbacks initial args (.terminated 99) ∧
    Reference.currentBox erased error.resource = none := by
  refine ⟨double_ready, ?_, rfl⟩
  apply withValues_scope_terminal Reference.natOps doubleCallbacks (payload := payload) rfl
  exact ⟨.unwound 7 initial, ⟨.unwound 7 initial, rfl, rfl⟩,
    .unwound 8 erased, rfl, 99, rfl, rfl⟩

/-- A left unwind with live resources; no conversion result is manufactured. -/
def safeUnwind : ValuesCallbacks Reference.State Reference.StringId Unit Unit Nat Nat :=
  { erasedLeft with left := fun before _ outcome => outcome = .unwound 7 before }

private theorem safe_admissible : safeUnwind.Admissible Reference.natOps args initial where
  left := by intro _ _ _ _ run; cases run; exact HeldFrame.refl _ _ _ _
  right := by intro _ _ _ _ _ _ first _; cases first
  dropLeft := by intro _ _ _ _ _ _ run; cases run; exact HeldFrame.refl _ _ _ _
  dropRight := by intro _ _ _ _ _ _ run; cases run; exact HeldFrame.refl _ _ _ _

/-- Exact version-family type index for the admitted unwind challenge. -/
def safeTypes : ValuesTypes where
  base := ⟨Reference.State, Reference.StringId, Reference.BoxId, Nat, Reference.natOps⟩
  Left := Unit
  Right := Unit
  Unwind := Nat
  callbacks := safeUnwind

private theorem safe_requires : (withValuesFamily.contract safeTypes).requires initial args :=
  ⟨laws, ready, ValuesCallbacks.CallReady.of_admissible ready safe_admissible
    Reference.natOps_laws.drop_boxes Reference.natOps_laws.store.available⟩

/-- Actual freeBox output after empty-field error cleanup. -/
def safelyRetired : Reference.State := { initial with boxes := [none], events := [.freeBox ⟨0⟩] }

/-- The family continuation theorem constructs the exact unwind from a real
scope exit and real field/Box destructor exits. Self is retired only after both
operand drops; the reason and final free event of the callback are retained. -/
theorem admitted_unwind_has_exact_cleanup :
    (withValuesFamily.contract safeTypes).requires initial args ∧
    withValuesRun safeTypes initial args (.unwound (7 : Nat) safelyRetired) ∧
    Reference.currentBox safelyRetired error.resource = none ∧
    safelyRetired.events = [.freeBox ⟨0⟩] := by
  have scope : Owned.scope safeUnwind.double
      [fun state result => safeUnwind.dropLeft state args.left result,
       fun state result => safeUnwind.dropRight state args.right result]
      (valuesBody Reference.natOps safeUnwind args) initial () (.unwound 7 initial) :=
    ⟨.unwound 7 initial, ⟨.unwound 7 initial, rfl, rfl⟩,
      .returned () initial, rfl, .returned () initial, rfl, rfl⟩
  obtain ⟨actual, present, _, continuation⟩ := withValues_family_unwind_continues safeTypes
    safe_requires scope
  have same : actual = payload := Option.some.inj present.symm
  subst actual
  have continuationAfter := (continuation (.returned () initial) rfl).2
  have freed : Reference.natOps.freeBox initial error.resource (.returned () safelyRetired) :=
    ⟨.returned () safelyRetired, ⟨payload, rfl, rfl⟩, rfl⟩
  exact ⟨safe_requires, continuationAfter _ freed, rfl, rfl⟩

/-- An admitted with_pubkeys call has a real store continuation after its
actual old-field cleanup; this control uses the family progress result. -/
theorem admitted_pubkeys_store_has_execution :
    ∃ after, Reference.ops.writeBox sampleBoxState sampleError.resource
      ((Payload.anchor sampleAnchor).withPubkeys sampleKey sampleKey) = some after ∧
      withPubkeysRun withPubkeys_sample sampleBoxState (sampleError, sampleKey, sampleKey)
        (.returned sampleError after) := by
  have admitted : (withPubkeysFamily.contract withPubkeys_sample).requires
      sampleBoxState (sampleError, sampleKey, sampleKey) :=
    ⟨⟨Reference.ops_laws.stringDrop.other, Reference.ops_laws.drop_boxes,
      Reference.ops_laws.store.current, Reference.ops_laws.store_strings⟩, sampleBox_ready,
      ComparisonStoreReady.of_available Reference.ops Reference.ops_laws.drop_boxes
        Reference.ops_laws.store.available _ _ _⟩
  exact withPubkeys_family_cleanup_continues withPubkeys_sample admitted
    (payload := .anchor sampleAnchor) rfl (outcome := .returned () sampleBoxState) rfl

/-- An opaque first conversion may genuinely diverge; admission constrains its
finite exits and does not create a new one. -/
def diverging : ValuesCallbacks Reference.State Reference.StringId Unit Unit Nat Nat :=
  { erasedLeft with left := fun _ _ _ => False }

private theorem diverging_admissible : diverging.Admissible Reference.natOps args initial where
  left := by intro _ _ _ _ run; exact False.elim run
  right := by intro _ _ _ _ _ _ first _; exact False.elim first
  dropLeft := by intro _ _ _ _ _ _ run; cases run; exact HeldFrame.refl _ _ _ _
  dropRight := by intro _ _ _ _ _ _ run; cases run; exact HeldFrame.refl _ _ _ _

/-- Genuine opaque divergence remains distinct from an unavailable reached
local read or store. No callback termination was added to fix the latter. -/
theorem opaque_divergence_remains_possible :
    diverging.CallReady Reference.natOps args initial ∧
    ¬ ∃ outcome, withValues Reference.natOps diverging initial args outcome := by
  refine ⟨ValuesCallbacks.CallReady.of_admissible ready diverging_admissible
    Reference.natOps_laws.drop_boxes Reference.natOps_laws.store.available, ?_⟩
  rintro ⟨_, _, _, ⟨_, ⟨_, ⟨_, impossible, _⟩, _⟩, _⟩ | ⟨_, _, ⟨_, impossible, _⟩, _⟩⟩ <;> exact
    impossible

end SolanalibTest.Specs.Core.AnchorErrorOwnedAdmission
