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

namespace SolanalibTest.Specs.Core.AnchorErrorOwnedCallbacks

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AnchorErrorOwned

private theorem reference_comparison_laws : Reference.natOps.ComparisonLaws :=
  ⟨Reference.natOps_laws.stringDrop.other, Reference.natOps_laws.drop_boxes,
    Reference.natOps_laws.store.current, Reference.natOps_laws.store_strings⟩

/-- Independent captured-state events, including observations at each operand
drop. These observations distinguish partial-RHS cleanup from receiver cleanup. -/
inductive Event where
  /-- Which borrowed operand conversion was entered. -/
  | conversion (left : Bool) (operand : Nat)
  /-- Operand retirement observes the partial String and the error Box. -/
  | drop (operand : Nat) (partialLive boxLive : Bool)
  deriving DecidableEq, Repr

/-- Finite error heap, separately owned operand IDs, and captured effects. -/
structure World where
  /-- The same shared concrete String/Box interpretation. -/
  heap : Reference.State
  /-- Live operand identities; the fixtures begin without duplicates. -/
  operands : List Nat
  /-- Actual callback and operand-cleanup effects. -/
  history : List Event
  deriving DecidableEq, Repr

/-- Error heap projection preserves independent operands and captured effects. -/
def heapFocus : Owned.Focus World Reference.State where
  get := World.heap
  set := fun before heap => { before with heap := heap }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- Fixed-source String/Box operations in the full callback world. -/
def ops : Ops World Reference.StringId Reference.BoxId Nat :=
  Reference.natOps.focus heapFocus

/-- The primitive provider in the callback world satisfies all shared storage laws. -/
theorem ops_laws : ops.Laws :=
  Reference.natOps.focus_laws Reference.natOps_laws heapFocus

/-- Three explicit finite exit choices for a callback or operand destructor. -/
inductive Exit where
  /-- Ordinary return. -/
  | returned
  /-- Unwind with an actual state. -/
  | unwound (reason : Nat)
  /-- Terminal exit, with no post-state. -/
  | terminated (reason : Nat)
  deriving DecidableEq, Repr

/-- Supply an exit choice with its actual value/state only where appropriate. -/
def exit {Value : Type} (mode : Exit) (value : Value) (after : World) :
    Outcome World Value Nat Nat :=
  match mode with
  | .returned => .returned value after
  | .unwound reason => .unwound reason after
  | .terminated reason => .terminated reason

/-- Captured-state effect at conversion entry. -/
def entered (before : World) (left : Bool) (operand : Nat) : World :=
  { before with history := before.history ++ [.conversion left operand] }

/-- A borrowed conversion owns no operand cleanup. Success performs an actual
String allocation; failure retains the explicit captured entry effect. -/
def convert (left : Bool) (mode : Exit) :
    Callback.Run World Nat Reference.StringId Nat Nat :=
  fun before operand outcome => operand ∈ before.operands ∧
    let actual := entered before left operand
    match mode with
    | .returned => lift (if left then ops.copyLiteral else ops.formatLiteral)
        actual (if left then "L" else "R") outcome
    | .unwound reason => outcome = .unwound reason actual
    | .terminated reason => outcome = .terminated reason

/-- Expected actual state after one operand is consumed. The drop records
whether partial String two and receiver Box zero are live at that moment. -/
def operandGone (before : World) (operand : Nat) : World :=
  ⟨before.heap, before.operands.erase operand, before.history ++
    [.drop operand (ops.currentString before ⟨2⟩).isSome (ops.currentBox before ⟨0⟩).isSome]⟩

/-- An individual operand destructor rejects an absent ID and consumes a
present ID on normal return or unwind. Its other effects stay explicit. -/
def dropOperand (mode : Exit) : Callback.Run World Nat Unit Nat Nat :=
  fun before operand outcome => operand ∈ before.operands ∧
    outcome = exit mode () (operandGone before operand)

/-- Explicit provider choices. Double unwind uses both reasons and observes
the actual remaining Box before producing its terminal-only reason. -/
def callbacks (left right dropLeft dropRight : Exit) :
    ValuesCallbacks World Reference.StringId Nat Nat Nat Nat where
  left := convert true left
  right := convert false right
  dropLeft := dropOperand dropLeft
  dropRight := dropOperand dropRight
  double := fun actual first second terminal =>
    terminal = first + second + (if (ops.currentBox actual ⟨0⟩).isSome then 100 else 200)

/-- A simple initialized receiver without prior compared Strings. -/
def payload : Payload Reference.StringId :=
  .anchor ⟨⟨0⟩, 7, ⟨1⟩, none, none⟩

/-- Distinct operand IDs and exactly two permitted String allocations. -/
def initial : World :=
  ⟨⟨[some "N", some "M"], [some payload], 2, []⟩, [10, 20], []⟩

/-- Receiver and operand identities stay separate throughout the control. -/
def args : ValuesArgs Reference.BoxId Nat Nat := ⟨⟨⟨0⟩⟩, 10, 20⟩

/-- Expected world after an ordinary String allocation. -/
def allocated (left : Bool) (before : World) : Reference.StringId × World :=
  let actual := Reference.stringResult (!left) before.heap (if left then "L" else "R")
  (actual.1, heapFocus.set before actual.2)

/-- Expected world after one actual current String is retired. -/
def stringGone (before : World) (index : Nat) (text : String) : World :=
  heapFocus.set before
    ⟨before.heap.strings.set index none, before.heap.boxes, before.heap.remaining,
      before.heap.events ++ [.dropString ⟨index⟩ text]⟩

/-- Expected world after the final deallocation of Box zero. -/
def boxGone (before : World) : World :=
  heapFocus.set before
    ⟨before.heap.strings, before.heap.boxes.set 0 none, before.heap.remaining,
      before.heap.events ++ [.freeBox ⟨0⟩]⟩

private theorem string_drop (before : World) (index : Nat) (text : String)
    (present : Reference.currentString before.heap ⟨index⟩ = some text) :
    ops.dropString before ⟨index⟩ (.returned () (stringGone before index text)) :=
  ⟨.returned () (stringGone before index text).heap,
    ⟨.returned () (stringGone before index text).heap, ⟨text, present, rfl⟩, rfl⟩, rfl⟩

private theorem box_drop (before : World) (value : Payload Reference.StringId)
    (present : Reference.currentBox before.heap ⟨0⟩ = some value) :
    ops.freeBox before ⟨0⟩ (.returned () (boxGone before)) :=
  ⟨.returned () (boxGone before).heap,
    ⟨.returned () (boxGone before).heap, ⟨value, present, rfl⟩, rfl⟩, rfl⟩

/-- The captured effect and actual successful String result of the first conversion. -/
def leftReturned : Reference.StringId × World := allocated true (entered initial true 10)

/-- Second conversion mutates captured history before its unwind. -/
def rightUnwound : World := entered leftReturned.2 false 20

/-- The incomplete RHS String is retired before either parameter destructor. -/
def partialGone : World := stringGone rightUnwound 2 "L"

/-- First parameter cleanup follows the partial-RHS cleanup. -/
def leftGone : World := operandGone partialGone 10

/-- Second parameter cleanup precedes receiver cleanup. -/
def bothGone : World := operandGone leftGone 20

/-- The name of the receiver then message are retired in declaration order. -/
def nameGone : World := stringGone bothGone 0 "N"

/-- State after both original receiver String fields have been retired. -/
def fieldsGone : World := stringGone nameGone 1 "M"

/-- Final actual unwind state after receiver Box deallocation. -/
def retired : World := boxGone fieldsGone

private theorem left_returns :
    convert true .returned initial 10 (.returned leftReturned.1 leftReturned.2) := by
  refine ⟨by decide, ?_⟩
  exact ⟨.returned leftReturned.1 leftReturned.2,
    ⟨.returned leftReturned.1 leftReturned.2.heap,
      ⟨.returned leftReturned.1 leftReturned.2.heap, rfl, rfl⟩, rfl⟩, rfl⟩

private theorem receiver_drops :
    dropError ops args.error bothGone (.returned () retired) :=
  ⟨payload, rfl, .returned () fieldsGone,
    ⟨.returned () nameGone, string_drop bothGone 0 "N" rfl,
      .returned () fieldsGone, string_drop nameGone 1 "M" rfl, rfl⟩,
    box_drop fieldsGone payload rfl⟩

/-- A second conversion unwind cleans the first returned String, then both
operands, then self, and preserves the captured state effects of the conversion. -/
theorem second_conversion_unwind_cleans_in_order :
    withValues ops (callbacks .returned (.unwound 7) .returned .returned) initial args
      (.unwound 7 retired) := by
  refine ⟨payload, rfl, Or.inl ⟨.unwound 7 bothGone, ?_, ?_⟩⟩
  · refine ⟨.unwound 7 partialGone, ?_, ?_⟩
    · refine ⟨.returned leftReturned.1 leftReturned.2, left_returns,
        .unwound 7 partialGone, ?_, rfl⟩
      exact ⟨.unwound 7 rightUnwound, ⟨by decide, rfl⟩,
        .returned () partialGone,
        ⟨.returned () partialGone, string_drop rightUnwound 2 "L" rfl, rfl⟩, rfl⟩
    · exact ⟨.returned () leftGone, ⟨by decide, rfl⟩,
        .returned () bothGone, ⟨by decide, rfl⟩, rfl⟩
  · exact ⟨.returned () retired, ⟨.returned () retired, receiver_drops, rfl⟩, rfl⟩

/-- Parameter destructors observe the partial String already dead and the
receiver still live; afterward every owned operand and error field is gone. -/
theorem second_unwind_observable_order :
    retired.history = [.conversion true 10, .conversion false 20,
      .drop 10 false true, .drop 20 false true] ∧
    retired.operands = [] ∧ retired.heap.strings = [none, none, none] ∧
    retired.heap.boxes = [none] ∧
    retired.heap.events = [.name ⟨2⟩ "L", .dropString ⟨2⟩ "L",
      .dropString ⟨0⟩ "N", .dropString ⟨1⟩ "M", .freeBox ⟨0⟩] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An operand cannot be consumed a second time in the finite control. -/
theorem operand_second_drop_rejected :
    ¬ dropOperand .returned retired 10 (.returned () retired) := by
  rintro ⟨present, _⟩
  cases present

/-- If a cleanup destructor unwinds during the conversion unwind, the
terminal-only policy sees the still-live receiver and stops further cleanup. -/
theorem conversion_double_unwind_is_terminal :
    withValues ops (callbacks .returned (.unwound 7) (.unwound 8) .returned) initial args
      (.terminated 115) := by
  refine ⟨payload, rfl, Or.inl ⟨.terminated 115, ?_, rfl⟩⟩
  refine ⟨.unwound 7 partialGone, ?_, ?_⟩
  · refine ⟨.returned leftReturned.1 leftReturned.2, left_returns,
      .unwound 7 partialGone, ?_, rfl⟩
    exact ⟨.unwound 7 rightUnwound, ⟨by decide, rfl⟩,
      .returned () partialGone,
      ⟨.returned () partialGone, string_drop rightUnwound 2 "L" rfl, rfl⟩, rfl⟩
  · exact ⟨.unwound 8 leftGone, ⟨by decide, rfl⟩, 115, rfl, rfl⟩

/-- Terminal exit in the first conversion bypasses both operand destructors
and receiver cleanup, even when those later providers would unwind. -/
theorem first_conversion_terminal_stops :
    withValues ops (callbacks (.terminated 40) .returned (.unwound 8) (.unwound 9)) initial args
      (.terminated 40) :=
  ⟨payload, rfl, Or.inl ⟨.terminated 40,
    ⟨.terminated 40, ⟨.terminated 40, ⟨by decide, rfl⟩, rfl⟩, rfl⟩, rfl⟩⟩

/-- A terminal second conversion does not drop the completed first String;
its terminal outcome contains no invented cleanup or post-state. -/
theorem second_conversion_terminal_stops :
    withValues ops (callbacks .returned (.terminated 41) (.unwound 8) (.unwound 9)) initial args
      (.terminated 41) := by
  refine ⟨payload, rfl, Or.inl ⟨.terminated 41, ?_, rfl⟩⟩
  refine ⟨.terminated 41, ?_, rfl⟩
  exact ⟨.returned leftReturned.1 leftReturned.2, left_returns,
    .terminated 41, ⟨.terminated 41, ⟨by decide, rfl⟩, rfl⟩, rfl⟩


/-- Actual second String allocation after its captured conversion event. -/
def rightReturned : Reference.StringId × World := allocated false (entered leftReturned.2 false 20)

/-- Actual same-Box assignment moves both returned String IDs into its payload. -/
def assigned : World :=
  heapFocus.set rightReturned.2
    ⟨rightReturned.2.heap.strings,
      rightReturned.2.heap.boxes.set 0 (some (payload.withValues leftReturned.1 rightReturned.1)),
      rightReturned.2.heap.remaining, rightReturned.2.heap.events ++ [.write ⟨0⟩]⟩

/-- First operand drop after the comparison assignment. -/
def assignedLeftGone : World := operandGone assigned 10

/-- Second operand drop after the comparison assignment. -/
def assignedBothGone : World := operandGone assignedLeftGone 20

/-- Receiver cleanup now starts from its updated comparison-bearing payload. -/
def assignedNameGone : World := stringGone assignedBothGone 0 "N"

/-- Updated receiver cleanup has retired the original message. -/
def assignedMessageGone : World := stringGone assignedNameGone 1 "M"

/-- Updated receiver cleanup also retires the new left comparison String. -/
def assignedFirstGone : World := stringGone assignedMessageGone 2 "L"

/-- Updated receiver cleanup retires the new right comparison String last. -/
def assignedSecondGone : World := stringGone assignedFirstGone 3 "R"

/-- Final unwind state after destruction of the updated error Box. -/
def assignedRetired : World := boxGone assignedSecondGone

private theorem right_returns :
    convert false .returned leftReturned.2 20 (.returned rightReturned.1 rightReturned.2) := by
  refine ⟨by decide, ?_⟩
  exact ⟨.returned rightReturned.1 rightReturned.2,
    ⟨.returned rightReturned.1 rightReturned.2.heap,
      ⟨.returned rightReturned.1 rightReturned.2.heap, rfl, rfl⟩, rfl⟩, rfl⟩

private theorem assignment_returns :
    replaceValues ops rightReturned.2 (args.error, leftReturned.1, rightReturned.1)
      (.returned args.error assigned) :=
  ⟨payload, rfl, .returned () rightReturned.2, rfl,
    payload, rfl, assigned, rfl, rfl⟩

private theorem body_returns (dropLeft dropRight : Exit) :
    valuesBody ops (callbacks .returned .returned dropLeft dropRight) args initial ()
      (.returned args.error assigned) := by
  refine ⟨.returned leftReturned.1 leftReturned.2, left_returns,
    .returned rightReturned.1 rightReturned.2, ?_,
    .returned args.error assigned, assignment_returns, rfl⟩
  exact (protect_returned_iff _ _ _ _ _ _ _).mpr right_returns

private theorem updated_receiver_drops :
    dropError ops args.error assignedBothGone (.returned () assignedRetired) :=
  ⟨payload.withValues leftReturned.1 rightReturned.1, rfl, .returned () assignedSecondGone,
    ⟨.returned () assignedNameGone, string_drop assignedBothGone 0 "N" rfl,
      .returned () assignedMessageGone, string_drop assignedNameGone 1 "M" rfl,
      .returned () assignedFirstGone, string_drop assignedMessageGone 2 "L" rfl,
      .returned () assignedSecondGone, string_drop assignedFirstGone 3 "R" rfl, rfl⟩,
    box_drop assignedSecondGone (payload.withValues leftReturned.1 rightReturned.1) rfl⟩

/-- Normal operand retirement preserves the two new Strings in the returned
Box. The operands see both the moved comparison and receiver still live. -/
theorem normal_operand_cleanup_transfers_box :
    withValues ops (callbacks .returned .returned .returned .returned) initial args
      (.returned args.error assignedBothGone) ∧
    assignedBothGone.history = [.conversion true 10, .conversion false 20,
      .drop 10 true true, .drop 20 true true] ∧
    current ops assignedBothGone args.error =
      some (.anchor ⟨"N", 7, "M", none, some (.values "L" "R")⟩) := by
  refine ⟨⟨payload, rfl, ?_⟩, rfl, rfl⟩
  apply protectReturnPlace_of_protect
  apply (protect_returned_iff _ _ _ _ _ _ _).mpr
  apply (scope_returned_iff _ _ _ _ _ _ _).mpr
  exact ⟨assigned, body_returns _ _, .cons _ _ _ _ _ ⟨by decide, rfl⟩
    (.cons _ _ _ _ _ ⟨by decide, rfl⟩ (.nil _))⟩

/-- When an operand destructor starts an unwind after assignment, remaining
parameter cleanup finishes first, then self drops the new compared Strings.
A saved pre-assignment error value would miss these two real resources. -/
theorem operand_unwind_drops_updated_error :
    withValues ops (callbacks .returned .returned (.unwound 8) .returned) initial args
      (.unwound 8 assignedRetired) ∧
    assignedRetired.heap.strings = [none, none, none, none] ∧
    assignedRetired.heap.boxes = [none] ∧
    assignedRetired.heap.events = [.name ⟨2⟩ "L", .message ⟨3⟩ "R", .write ⟨0⟩,
      .dropString ⟨0⟩ "N", .dropString ⟨1⟩ "M",
      .dropString ⟨2⟩ "L", .dropString ⟨3⟩ "R", .freeBox ⟨0⟩] := by
  refine ⟨⟨payload, rfl, Or.inl ⟨.unwound 8 assignedBothGone, ?_, ?_⟩⟩, rfl, rfl, rfl⟩
  · exact ⟨.returned args.error assigned, body_returns _ _,
      .unwound 8 assignedLeftGone, ⟨by decide, rfl⟩,
      .returned () assignedBothGone, ⟨by decide, rfl⟩, rfl⟩
  · exact ⟨.returned () assignedRetired,
      ⟨.returned () assignedRetired, updated_receiver_drops, rfl⟩, rfl⟩

/-- rust-lang/rust#47949: rustc does not drop the return place when an operand
destructor unwinds after the receiver has moved into it. The same run admits
both that outcome, where the updated Box and its four Strings stay live, and
the release above. -/
theorem operand_unwind_may_leave_returned_error_live :
    withValues ops (callbacks .returned .returned (.unwound 8) .returned) initial args
      (.unwound 8 assignedBothGone) ∧
    withValues ops (callbacks .returned .returned (.unwound 8) .returned) initial args
      (.unwound 8 assignedRetired) ∧
    current ops assignedBothGone args.error =
      some (.anchor ⟨"N", 7, "M", none, some (.values "L" "R")⟩) ∧
    assignedBothGone.heap.strings = [some "N", some "M", some "L", some "R"] := by
  refine ⟨⟨payload, rfl, protectReturnPlace_leak (body_returns _ _) ?_⟩,
    operand_unwind_drops_updated_error.1, rfl, rfl⟩
  exact ⟨.unwound 8 assignedLeftGone, ⟨by decide, rfl⟩,
    .returned () assignedBothGone, ⟨by decide, rfl⟩, rfl⟩

private theorem right_unwind_body_never_returns (value : Error Reference.BoxId) (returned : World) :
    ¬ valuesBody ops (callbacks .returned (.unwound 7) .returned .returned) args initial ()
      (.returned value returned) := by
  rintro ⟨first, _, next⟩
  cases first with
  | unwound _ _ | terminated _ => cases next
  | returned left middle =>
    obtain ⟨second, secondRun, assignment⟩ := next
    cases second with
    | unwound _ _ | terminated _ => cases assignment
    | returned right final =>
      obtain ⟨_, impossible⟩ := (protect_returned_iff _ _ _ _ _ _ _).mp secondRun
      cases impossible

/-- A conversion unwind precedes the move of the receiver into the return place: on
that path the protected scope alone decides, so the receiver is released, as
before the rust-lang/rust#47949 alternative was added. -/
theorem conversion_unwind_has_no_return_place_alternative
    (final : Outcome World (Error Reference.BoxId) Nat Nat) :
    withValues ops (callbacks .returned (.unwound 7) .returned .returned) initial args final ↔
      ∃ present, ops.currentBox initial args.error.resource = some present ∧
        Owned.protect (callbacks .returned (.unwound 7) .returned .returned).double
          [dropErrorLift ops args.error]
          (Owned.scope (callbacks .returned (.unwound 7) .returned .returned).double
            [fun state result => (callbacks .returned (.unwound 7) .returned .returned).dropLeft
              state args.left result,
             fun state result => (callbacks .returned (.unwound 7) .returned .returned).dropRight
              state args.right result]
            (valuesBody ops (callbacks .returned (.unwound 7) .returned .returned) args))
          initial () final :=
  exists_congr fun _ => and_congr_right fun _ =>
    protectReturnPlace_iff_of_no_return _ _ _ _ _ _ right_unwind_body_never_returns final

/-- A second operand panic during unwind reaches the explicit terminal policy
before receiver cleanup. Its reason observes the actual still-live Box. -/
theorem two_operand_unwinds_are_terminal :
    withValues ops (callbacks .returned .returned (.unwound 8) (.unwound 9)) initial args
      (.terminated 117) := by
  refine ⟨payload, rfl, Or.inl ⟨.terminated 117, ?_, rfl⟩⟩
  exact ⟨.returned args.error assigned, body_returns _ _,
    .unwound 8 assignedLeftGone, ⟨by decide, rfl⟩,
    .unwound 9 assignedBothGone, ⟨by decide, rfl⟩, 117, rfl, rfl⟩


private theorem conversion_frame (left : Bool) (mode : Exit)
    {before : World} {operand : Nat} {error : Error Reference.BoxId}
    {strings : List Reference.StringId} {outcome : Outcome World Reference.StringId Nat Nat}
    (live : ∀ resource ∈ strings, ∃ text, ops.currentString before resource = some text)
    (run : convert left mode before operand outcome) :
    StringFrame ops error strings before outcome := by
  obtain ⟨_, called⟩ := run
  cases mode with
  | terminated reason => cases called; trivial
  | unwound reason => cases called; exact ⟨rfl, fun _ _ => rfl⟩
  | returned =>
    cases left with
    | false =>
      exact allocation_stringFrame ops ops.formatLiteral ops_laws.format ops_laws.format_boxes
        (before := entered before false operand) live called
    | true =>
      exact allocation_stringFrame ops ops.copyLiteral ops_laws.copy ops_laws.copy_boxes
        (before := entered before true operand) live called

private theorem operand_frame (mode : Exit)
    {before : World} {operand : Nat} {error : Error Reference.BoxId}
    {strings : List Reference.StringId} {outcome : Outcome World Unit Nat Nat}
    (run : dropOperand mode before operand outcome) :
    DropFrame ops error strings before outcome := by
  obtain ⟨_, equal⟩ := run
  cases mode with
  | terminated reason => cases equal; trivial
  | returned => cases equal; exact ⟨rfl, fun _ _ => rfl⟩
  | unwound reason => cases equal; exact ⟨rfl, fun _ _ => rfl⟩

/-- Every exit choice respects the held error/partial-String footprint while
retaining the actual independent operand and captured-history effects. -/
theorem callbacks_admissible (left right dropLeft dropRight : Exit)
    (input : ValuesArgs Reference.BoxId Nat Nat) (start : World) :
    (callbacks left right dropLeft dropRight).Admissible ops input start where
  left := by
    intro current outcome _ ready run
    exact conversion_frame true left ready.2 run
  right := by
    intro current retained afterLeft outcome _ ready first run
    have frame := conversion_frame true left (error := input.error) ready.2 first
    exact conversion_frame false right (StringFrame.returned_live ops ready.2 frame) run
  dropLeft := by
    intro before current outcome _ _ _ run
    exact operand_frame dropLeft run
  dropRight := by
    intro before current outcome _ _ _ run
    exact operand_frame dropRight run

/-- The callback controls start from initialized distinct error String fields. -/
theorem initial_ready : Ready ops initial args.error := by
  refine ⟨payload, rfl, by decide, ?_⟩
  intro resource member
  have choice : resource = (⟨0⟩ : Reference.StringId) ∨ resource = ⟨1⟩ := by
    simpa [Payload.strings, payload, originStrings, comparedStrings] using member
  rcases choice with rfl | rfl
  · exact ⟨"N", rfl⟩
  · exact ⟨"M", rfl⟩

/-- The same world/providers instantiate the generic owned callback family. -/
def familyTypes (left right dropLeft dropRight : Exit) : ValuesTypes where
  base := ⟨World, Reference.StringId, Reference.BoxId, Nat, ops⟩
  Left := Nat
  Right := Nat
  Unwind := Nat
  callbacks := callbacks left right dropLeft dropRight

/-- The real second-conversion unwind is admitted by the source readiness and callback-frame
preconditions of the family, not merely by a raw relation. -/
theorem conversion_unwind_is_family_execution :
    (withValuesFamily.contract (familyTypes .returned (.unwound 7) .returned
      .returned)).HasExecution
      (withValuesRun (familyTypes .returned (.unwound 7) .returned .returned)) :=
  ⟨initial, args, (Outcome.unwound 7 retired : Outcome World (Error Reference.BoxId) Nat Nat),
    ⟨⟨ops_laws.stringDrop.other, ops_laws.drop_boxes, ops_laws.store.current,
      ops_laws.store_strings⟩,
      initial_ready, ValuesCallbacks.CallReady.of_admissible initial_ready
        (callbacks_admissible _ _ _ _ args initial) ops_laws.drop_boxes ops_laws.store.available⟩,
    second_conversion_unwind_cleans_in_order⟩

/-- The updated-payload cleanup execution also meets the exact generic family
precondition, including the held-resource frame of every callback. -/
theorem operand_unwind_is_family_execution :
    (withValuesFamily.contract (familyTypes .returned .returned (.unwound 8)
      .returned)).HasExecution
      (withValuesRun (familyTypes .returned .returned (.unwound 8) .returned)) :=
  ⟨initial, args, (Outcome.unwound 8 assignedRetired : Outcome World (Error Reference.BoxId) Nat
    Nat),
    ⟨⟨ops_laws.stringDrop.other, ops_laws.drop_boxes, ops_laws.store.current,
      ops_laws.store_strings⟩,
      initial_ready, ValuesCallbacks.CallReady.of_admissible initial_ready
        (callbacks_admissible _ _ _ _ args initial) ops_laws.drop_boxes ops_laws.store.available⟩,
    operand_unwind_drops_updated_error.1⟩

namespace CapturedString

/-- This receiver owns no Strings before the comparison is assigned. -/
def payload : Payload Reference.StringId := .program ⟨.invalidArgument, none, none⟩

/-- Stable receiver identity, separate from the captured String identity. -/
def error : Error Reference.BoxId := ⟨⟨0⟩⟩

/-- Borrowed unit operands carry no destructor resources in this instance. -/
def args : ValuesArgs Reference.BoxId Unit Unit := ⟨error, (), ()⟩

/-- String zero belongs to unrelated captured state, outside the receiver. -/
def initial : Reference.State := ⟨[some "captured"], [some payload], 2, []⟩

/-- The first conversion creates the actual retained String one. -/
def leftResult : Reference.StringId × Reference.State :=
  Reference.stringResult false initial "L"

/-- The right conversion first drops the unrelated captured String zero. -/
def capturedGone : Reference.State :=
  ⟨[none, some "L"], [some payload], 1,
    [.name ⟨1⟩ "L", .dropString ⟨0⟩ "captured"]⟩

/-- A normal right conversion then creates fresh String two. -/
def rightResult : Reference.StringId × Reference.State :=
  Reference.stringResult true capturedGone "R"

/-- First conversion in this finite legal-input instance performs the real
shared String allocation, rather than assuming an allocated result. -/
def left : Callback.Run Reference.State Unit Reference.StringId Nat Nat :=
  fun before _ outcome => before = initial ∧
    lift Reference.natOps.copyLiteral before "L" outcome

/-- The right provider uses the real String retirement operation before its
chosen finite exit. Its normal path performs a real subsequent allocation. -/
def right (mode : Exit) : Callback.Run Reference.State Unit Reference.StringId Nat Nat :=
  fun before _ => Callback.bind (lift Reference.natOps.dropString)
    (fun _ actual outcome => match mode with
      | .returned => lift Reference.natOps.formatLiteral actual "R" outcome
      | .unwound reason => outcome = .unwound reason actual
      | .terminated reason => outcome = .terminated reason)
    before ⟨0⟩

/-- Actual finite outcome after the captured effect, with no terminal state. -/
def rightOutcome (mode : Exit) : Outcome Reference.State Reference.StringId Nat Nat :=
  match mode with
  | .returned => .returned rightResult.1 rightResult.2
  | .unwound reason => .unwound reason capturedGone
  | .terminated reason => .terminated reason

/-- Concrete callbacks can drop captured String storage disjoint from the
receiver and the actual partial result. Borrowed unit drops do nothing. -/
def callbacks (mode : Exit) :
    ValuesCallbacks Reference.State Reference.StringId Unit Unit Nat Nat where
  left := left
  right := right mode
  dropLeft := fun before _ outcome => outcome = .returned () before
  dropRight := fun before _ outcome => outcome = .returned () before
  double := fun _ _ _ terminal => terminal = 100

private theorem left_iff (before : Reference.State)
    (outcome : Outcome Reference.State Reference.StringId Nat Nat) :
    left before () outcome ↔ before = initial ∧ outcome = .returned leftResult.1 leftResult.2 := by
  constructor
  · rintro ⟨rfl, middle, ⟨actual, called, mapped⟩, lifted⟩
    change .returned leftResult.1 leftResult.2 = actual at called
    cases called
    cases mapped
    cases lifted
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, .returned leftResult.1 leftResult.2,
      ⟨.returned leftResult.1 leftResult.2, rfl, rfl⟩, rfl⟩

private theorem captured_drop_iff (outcome : Outcome Reference.State Unit Nat Nat) :
    lift Reference.natOps.dropString leftResult.2 ⟨0⟩ outcome ↔
      outcome = .returned () capturedGone := by
  constructor
  · rintro ⟨middle, ⟨actual, ⟨text, present, called⟩, mapped⟩, lifted⟩
    have same : text = "captured" := Option.some.inj present.symm
    subst text
    cases called
    cases mapped
    cases lifted
    rfl
  · rintro rfl
    exact ⟨.returned () capturedGone,
      ⟨.returned () capturedGone, ⟨"captured", rfl, rfl⟩, rfl⟩, rfl⟩

private theorem right_iff (mode : Exit)
    (outcome : Outcome Reference.State Reference.StringId Nat Nat) :
    right mode leftResult.2 () outcome ↔ outcome = rightOutcome mode := by
  constructor
  · rintro ⟨middle, called, remaining⟩
    have same := (captured_drop_iff middle).mp called
    cases same
    cases mode with
    | unwound _ | terminated _ => exact remaining
    | returned =>
      obtain ⟨middle, ⟨actual, allocated, mapped⟩, lifted⟩ := remaining
      change .returned rightResult.1 rightResult.2 = actual at allocated
      cases allocated
      cases mapped
      cases lifted
      rfl
  · rintro rfl
    refine ⟨.returned () capturedGone, (captured_drop_iff _).mpr rfl, ?_⟩
    cases mode with
    | unwound _ | terminated _ => rfl
    | returned =>
      exact ⟨.returned rightResult.1 rightResult.2,
        ⟨.returned rightResult.1 rightResult.2, rfl, rfl⟩, rfl⟩

private theorem right_frame (mode : Exit) :
    StringFrame Reference.natOps error [leftResult.1] leftResult.2 (rightOutcome mode) := by
  cases mode with
  | terminated _ => trivial
  | unwound _ =>
    refine ⟨rfl, ?_⟩
    intro resource member
    have same : resource = leftResult.1 := List.mem_singleton.mp member
    subst resource
    rfl
  | returned =>
    refine ⟨⟨rfl, ?_⟩, ⟨"R", rfl⟩, by decide⟩
    intro resource member
    have same : resource = leftResult.1 := List.mem_singleton.mp member
    subst resource
    rfl

/-- Every chosen exit meets the corrected admission: only the String reached
by a successful actual left conversion is retained alongside the receiver. -/
theorem callbacks_admissible (mode : Exit) :
    (callbacks mode).Admissible Reference.natOps args initial where
  left := by
    intro actual outcome present ready run
    exact allocation_stringFrame Reference.natOps Reference.natOps.copyLiteral
      Reference.natOps_laws.copy Reference.natOps_laws.copy_boxes ready.2 run.2
  right := by
    intro actual retained afterLeft outcome present _ first run
    obtain ⟨_, returned⟩ := (left_iff initial _).mp first
    cases returned
    have same : actual = payload := Option.some.inj present.symm
    subst actual
    have same := (right_iff mode outcome).mp run
    cases same
    exact right_frame mode
  dropLeft := by
    intro before actual outcome _ _ _ run
    cases run
    exact HeldFrame.refl _ _ _ _
  dropRight := by
    intro before actual outcome _ _ _ run
    cases run
    exact HeldFrame.refl _ _ _ _

/-- The unrelated captured String is retired on the unwind path, while the
actual retained result and receiver are unchanged. A global String frame
would incorrectly reject this explicitly admitted callback. -/
theorem unrelated_string_is_not_framed :
    right (.unwound 7) leftResult.2 () (.unwound 7 capturedGone) ∧
    StringFrame Reference.natOps error [leftResult.1] leftResult.2 (.unwound 7 capturedGone) ∧
    Reference.currentString leftResult.2 ⟨0⟩ = some "captured" ∧
    Reference.currentString capturedGone ⟨0⟩ = none ∧
    ¬ StringFrame Reference.natOps error [⟨0⟩] leftResult.2 (.unwound 7 capturedGone) := by
  refine ⟨(right_iff _ _).mpr rfl, right_frame (.unwound 7), rfl, rfl, ?_⟩
  intro frame
  have impossible := frame.2 ⟨0⟩ (by simp)
  cases impossible

/-- The same Box now contains the two returned comparison resources. -/
def assigned : Reference.State :=
  ⟨rightResult.2.strings, [some (payload.withValues leftResult.1 rightResult.1)], 0,
    rightResult.2.events ++ [.write ⟨0⟩]⟩

/-- Unwinding the second conversion retires the partial result after the
unrelated captured String has already been retired by the callback. -/
def partialGone : Reference.State :=
  ⟨[none, none], [some payload], 1,
    capturedGone.events ++ [.dropString ⟨1⟩ "L"]⟩

/-- Receiver cleanup then retires the String-free ProgramError Box. -/
def retired : Reference.State :=
  ⟨partialGone.strings, [none], 1, partialGone.events ++ [.freeBox ⟨0⟩]⟩

/-- Complete model outcome, preserving every state-bearing captured effect. -/
def result (mode : Exit) : Outcome Reference.State (Error Reference.BoxId) Nat Nat :=
  match mode with
  | .returned => .returned error assigned
  | .unwound reason => .unwound reason retired
  | .terminated reason => .terminated reason

private theorem assignment_returns :
    replaceValues Reference.natOps rightResult.2 (error, leftResult.1, rightResult.1)
      (.returned error assigned) :=
  ⟨payload, rfl, .returned () rightResult.2, rfl, payload, rfl, assigned, rfl, rfl⟩

private theorem partial_drop :
    dropStringLift (Unwind := Nat) Reference.natOps leftResult.1 capturedGone
      (.returned () partialGone) :=
  ⟨.returned () partialGone,
    ⟨.returned () partialGone, ⟨"L", rfl, rfl⟩, rfl⟩, rfl⟩

private theorem receiver_drop :
    dropErrorLift (Unwind := Nat) Reference.natOps error partialGone (.returned () retired) :=
  ⟨.returned () retired,
    ⟨payload, rfl, .returned () partialGone, rfl,
      .returned () retired, ⟨payload, rfl, rfl⟩, rfl⟩, rfl⟩

private theorem run (mode : Exit) :
    withValues Reference.natOps (callbacks mode) initial args (result mode) := by
  have first := (left_iff initial (.returned leftResult.1 leftResult.2)).mpr ⟨rfl, rfl⟩
  cases mode with
  | returned =>
    refine ⟨payload, rfl, ?_⟩
    apply protectReturnPlace_of_protect
    apply (protect_returned_iff _ _ _ _ _ _ _).mpr
    apply (scope_returned_iff _ _ _ _ _ _ _).mpr
    refine ⟨assigned, ?_, .cons _ _ _ _ _ rfl (.cons _ _ _ _ _ rfl (.nil _))⟩
    refine ⟨.returned leftResult.1 leftResult.2, first,
      .returned rightResult.1 rightResult.2, ?_,
      .returned error assigned, assignment_returns, rfl⟩
    exact (protect_returned_iff _ _ _ _ _ _ _).mpr ((right_iff .returned _).mpr rfl)
  | unwound reason =>
    refine ⟨payload, rfl, Or.inl ⟨.unwound reason partialGone, ?_, ?_⟩⟩
    · refine ⟨.unwound reason partialGone, ?_, ?_⟩
      · exact ⟨.returned leftResult.1 leftResult.2, first,
          .unwound reason partialGone,
          ⟨.unwound reason capturedGone, (right_iff (.unwound reason) _).mpr rfl,
            .returned () partialGone, partial_drop, rfl⟩, rfl⟩
      · exact ⟨.returned () partialGone, rfl, .returned () partialGone, rfl, rfl⟩
    · exact ⟨.returned () retired, receiver_drop, rfl⟩
  | terminated reason =>
    refine ⟨payload, rfl, Or.inl ⟨.terminated reason, ?_, rfl⟩⟩
    refine ⟨.terminated reason, ?_, rfl⟩
    exact ⟨.returned leftResult.1 leftResult.2, first,
      .terminated reason,
      ⟨.terminated reason, (right_iff (.terminated reason) _).mpr rfl, rfl⟩, rfl⟩

private theorem initial_ready : Ready Reference.natOps initial error := by
  refine ⟨payload, rfl, by decide, ?_⟩
  intro resource member
  cases member

/-- The concrete effectful callback family uses the proved heap provider. -/
def familyTypes (mode : Exit) : ValuesTypes where
  base := ⟨Reference.State, Reference.StringId, Reference.BoxId, Nat,
    Reference.natOps⟩
  Left := Unit
  Right := Unit
  Unwind := Nat
  callbacks := callbacks mode

/-- A full normal with_values execution permits retirement of unrelated
captured storage while retaining the same Box and both actual result Strings. -/
theorem normal_is_family_execution :
    (withValuesFamily.contract (familyTypes .returned)).HasExecution
      (withValuesRun (familyTypes .returned)) :=
  ⟨initial, args, result .returned,
    ⟨reference_comparison_laws, initial_ready, ValuesCallbacks.CallReady.of_admissible initial_ready
      (callbacks_admissible .returned) Reference.natOps_laws.drop_boxes
        Reference.natOps_laws.store.available⟩, run .returned⟩

/-- A full unwinding execution preserves the unrelated captured effect and
then cleans the actual partial result and receiver. -/
theorem unwind_is_family_execution :
    (withValuesFamily.contract (familyTypes (.unwound 7))).HasExecution
      (withValuesRun (familyTypes (.unwound 7))) :=
  ⟨initial, args, result (.unwound 7),
    ⟨reference_comparison_laws, initial_ready, ValuesCallbacks.CallReady.of_admissible initial_ready
      (callbacks_admissible (.unwound 7)) Reference.natOps_laws.drop_boxes
        Reference.natOps_laws.store.available⟩, run (.unwound 7)⟩

/-- A terminal right conversion is admitted without inventing a final state
or running cleanup after its terminal outcome. -/
theorem terminal_is_family_execution :
    (withValuesFamily.contract (familyTypes (.terminated 40))).HasExecution
      (withValuesRun (familyTypes (.terminated 40))) :=
  ⟨initial, args, result (.terminated 40),
    ⟨reference_comparison_laws, initial_ready, ValuesCallbacks.CallReady.of_admissible initial_ready
      (callbacks_admissible (.terminated 40)) Reference.natOps_laws.drop_boxes
        Reference.natOps_laws.store.available⟩, run (.terminated 40)⟩

/-- The normal return keeps captured String zero retired while its current
error contains live String identities one and two. -/
theorem normal_preserves_captured_effect :
    assigned.strings = [none, some "L", some "R"] ∧
    current Reference.natOps assigned error =
      some (.program ⟨.invalidArgument, none, some (.values "L" "R")⟩) ∧
    assigned.events = [.name ⟨1⟩ "L", .dropString ⟨0⟩ "captured",
      .message ⟨2⟩ "R", .write ⟨0⟩] := ⟨rfl, rfl, rfl⟩

/-- The unwind retains the drop of the callback before the partial-result and
receiver drops; no captured resource is restored from an earlier snapshot. -/
theorem unwind_preserves_captured_effect :
    retired.strings = [none, none] ∧ retired.boxes = [none] ∧
    retired.events = [.name ⟨1⟩ "L", .dropString ⟨0⟩ "captured",
      .dropString ⟨1⟩ "L", .freeBox ⟨0⟩] := ⟨rfl, rfl, rfl⟩

/-- An adversarial right provider instead retires the actual partial result.
Its primitive step exists, but the independent all-outcome frame rejects it. -/
def corruptCallbacks :
    ValuesCallbacks Reference.State Reference.StringId Unit Unit Nat Nat :=
  { callbacks .returned with
    right := fun before _ => Callback.bind (lift Reference.natOps.dropString)
      (fun _ actual outcome => outcome = .unwound 7 actual) before leftResult.1 }

/-- Reachability narrows the frame without permitting the actual retained
String to be consumed by the second conversion. -/
theorem actual_partial_result_drop_rejected :
    ¬ corruptCallbacks.Admissible Reference.natOps args initial := by
  intro admitted
  let badAfter : Reference.State :=
    ⟨[some "captured", none], [some payload], 1,
      [.name ⟨1⟩ "L", .dropString ⟨1⟩ "L"]⟩
  have first := (left_iff initial (.returned leftResult.1 leftResult.2)).mpr ⟨rfl, rfl⟩
  have called : corruptCallbacks.right leftResult.2 () (.unwound 7 badAfter) :=
    ⟨.returned () badAfter,
      ⟨.returned () badAfter,
        ⟨.returned () badAfter, ⟨"L", rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  have frame := admitted.right payload leftResult.1 leftResult.2
    (.unwound 7 badAfter) rfl (by exact ⟨by decide, fun _ member => nomatch member⟩) first called
  have impossible := frame.2 leftResult.1 (by simp)
  cases impossible

end CapturedString

namespace TransferredStrings

/-- Two captured owners are separate from storage liveness. Taking one
clears its slot while transferring the same live String identity. -/
structure World where
  /-- Shared stable String and Box storage. -/
  heap : Reference.State
  /-- The captured owner of the first callback, if not already moved. -/
  first : Option Reference.StringId
  /-- The independent captured owner of the second callback. -/
  second : Option Reference.StringId
  deriving DecidableEq, Repr

/-- Primitive storage operations preserve both captured-owner slots. -/
def heapFocus : Owned.Focus World Reference.State where
  get := World.heap
  set := fun before heap => { before with heap := heap }
  get_set := fun _ _ => rfl
  set_get := fun _ => rfl
  set_set := fun _ _ _ => rfl

/-- The same proved heap provider in the captured-owner world. -/
def ops : Ops World Reference.StringId Reference.BoxId Nat :=
  Reference.natOps.focus heapFocus

/-- A receiver without any preexisting owned String fields. -/
def payload : Payload Reference.StringId := .program ⟨.invalidArgument, none, none⟩

/-- Stable Box zero is independent of both captured String allocations. -/
def error : Error Reference.BoxId := ⟨⟨0⟩⟩

/-- Borrowed unit operands have no owned destructor fields. -/
def args : ValuesArgs Reference.BoxId Unit Unit := ⟨error, (), ()⟩

/-- Move from the first captured owner without changing storage contents. -/
def takeFirst (before : World) : World := { before with first := none }

/-- Move from the second captured owner, likewise retaining its identity. -/
def takeSecond (before : World) : World := { before with second := none }

/-- A finite ownership-transfer interpretation of ToString. Its legal input
domain requires initialized storage and disjoint captured owner slots. It
performs no allocation and clears the owner it moves from. -/
def left : Callback.Run World Unit Reference.StringId Nat Nat :=
  fun before _ outcome => ∃ resource,
    before.first = some resource ∧ before.second ≠ some resource ∧
    ops.currentBox before error.resource = some payload ∧
    (∃ text, ops.currentString before resource = some text) ∧
    outcome = .returned resource (takeFirst before)

/-- The second borrowed conversion can also transfer a preexisting captured
String. Actual left reachability supplies disjointness from the first result. -/
def right : Callback.Run World Unit Reference.StringId Nat Nat :=
  fun before _ outcome => ∃ resource,
    before.second = some resource ∧ ops.currentBox before error.resource = some payload ∧
    (∃ text, ops.currentString before resource = some text) ∧
    outcome = .returned resource (takeSecond before)

/-- Both callbacks transfer captured ownership; borrowed unit drops are empty. -/
def callbacks : ValuesCallbacks World Reference.StringId Unit Unit Nat Nat where
  left := left
  right := right
  dropLeft := fun before _ outcome => outcome = .returned () before
  dropRight := fun before _ outcome => outcome = .returned () before
  double := fun _ _ _ terminal => terminal = 100

private theorem admissible (start : World) : callbacks.Admissible ops args start where
  left := by
    intro actual outcome present _ run
    obtain ⟨resource, _, _, observed, live, rfl⟩ := run
    have same : actual = payload := Option.some.inj (present.symm.trans observed)
    subst actual
    exact ⟨⟨rfl, fun _ _ => rfl⟩, live, by simp [Payload.strings, payload, originStrings,
      comparedStrings]⟩
  right := by
    intro actual retained afterLeft outcome present _ first run
    obtain ⟨resource, _, apart, observed, _, returned⟩ := first
    cases returned
    obtain ⟨other, captured, _, live, rfl⟩ := run
    have same : actual = payload := Option.some.inj (present.symm.trans observed)
    subst actual
    refine ⟨⟨rfl, fun _ _ => rfl⟩, live, ?_⟩
    change other ∉ [retained]
    intro member
    have same := List.mem_singleton.mp member
    apply apart
    exact captured.trans (congrArg some same)
  dropLeft := by
    intro before actual outcome _ _ _ run
    cases run
    exact HeldFrame.refl _ _ _ _
  dropRight := by
    intro before actual outcome _ _ _ run
    cases run
    exact HeldFrame.refl _ _ _ _

/-- Both Strings already exist, and no new allocations are available. -/
def initial : World :=
  ⟨⟨[some "existing L", some "existing R"], [some payload], 0, []⟩,
    some ⟨0⟩, some ⟨1⟩⟩

/-- The first source owner is empty after its String is returned. -/
def afterLeft : World := takeFirst initial

/-- Both captured source owners are empty after the two transfers. -/
def afterRight : World := takeSecond afterLeft

/-- Assignment moves the transferred IDs into the same existing error Box. -/
def assigned : World := heapFocus.set afterRight
  ⟨afterRight.heap.strings, [some (payload.withValues ⟨0⟩ ⟨1⟩)], 0, [.write ⟨0⟩]⟩

private theorem left_returns : left initial () (.returned ⟨0⟩ afterLeft) :=
  ⟨⟨0⟩, rfl, by decide, rfl, ⟨"existing L", rfl⟩, rfl⟩

private theorem right_returns : right afterLeft () (.returned ⟨1⟩ afterRight) :=
  ⟨⟨1⟩, rfl, rfl, ⟨"existing R", rfl⟩, rfl⟩

private theorem run : withValues ops callbacks initial args (.returned error assigned) := by
  refine ⟨payload, rfl, ?_⟩
  apply protectReturnPlace_of_protect
  apply (protect_returned_iff _ _ _ _ _ _ _).mpr
  apply (scope_returned_iff _ _ _ _ _ _ _).mpr
  refine ⟨assigned, ?_, .cons _ _ _ _ _ rfl (.cons _ _ _ _ _ rfl (.nil _))⟩
  refine ⟨.returned ⟨0⟩ afterLeft, left_returns, .returned ⟨1⟩ afterRight, ?_, ?_⟩
  · exact (protect_returned_iff _ _ _ _ _ _ _).mpr right_returns
  · exact ⟨.returned error assigned,
      ⟨payload, rfl, .returned () afterRight, rfl, payload, rfl, assigned, rfl, rfl⟩, rfl⟩

/-- Preexisting String identities enter the returned error without allocation.
Both captured owners are cleared, and storage identity/content is preserved. -/
theorem existing_resources_are_transferred :
    withValues ops callbacks initial args (.returned error assigned) ∧
    ops.currentString initial ⟨0⟩ = some "existing L" ∧
    ops.currentString afterLeft ⟨1⟩ = some "existing R" ∧
    assigned.first = none ∧ assigned.second = none ∧
    assigned.heap.strings = initial.heap.strings ∧ assigned.heap.events = [.write ⟨0⟩] ∧
    current ops assigned error =
      some (.program ⟨.invalidArgument, none, some (.values "existing L" "existing R")⟩) :=
  ⟨run, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Closed type index with actual heap providers and transfer callbacks. -/
def familyTypes : ValuesTypes where
  base := ⟨World, Reference.StringId, Reference.BoxId, Nat, ops⟩
  Left := Unit
  Right := Unit
  Unwind := Nat
  callbacks := callbacks

/-- Existing-ID transfer satisfies the exact generic callback family, including
its local frame/disjointness admission and live receiver precondition. -/
theorem transfer_is_family_execution :
    (withValuesFamily.contract familyTypes).HasExecution (withValuesRun familyTypes) := by
  have laws := Reference.natOps.focus_laws Reference.natOps_laws heapFocus
  have ready : Ready ops initial error :=
    ⟨payload, rfl, List.nodup_nil, fun _ member => nomatch member⟩
  exact ⟨initial, args, .returned error assigned,
    ⟨⟨laws.stringDrop.other, laws.drop_boxes, laws.store.current, laws.store_strings⟩,
      ready, ValuesCallbacks.CallReady.of_admissible ready (admissible initial)
        laws.drop_boxes laws.store.available⟩, run⟩

/-- Clearing each source owner prevents taking either resource a second time. -/
theorem captured_owners_cannot_be_taken_twice :
    (¬ ∃ outcome, left afterLeft () outcome) ∧ (¬ ∃ outcome, right afterRight () outcome) := by
  constructor
  · rintro ⟨_, _, impossible, _⟩
    cases impossible
  · rintro ⟨_, _, impossible, _⟩
    cases impossible

/-- A second conversion may transfer a different existing String, but cannot
return the already-held first result as an additional owned String. -/
theorem partial_result_alias_rejected :
    ¬ StringFrame (Unwind := Nat) ops error [⟨0⟩] afterLeft (.returned ⟨0⟩ afterLeft) := by
  intro frame
  exact frame.2.2 (by simp)

end TransferredStrings

namespace OwnedStringOperands

/-- Both consumed operands own String slots in the same heap as the error.
The conversions copy their current contents; the operand destructors really
retire the original slots. These are mathematical dependency interpretations. -/
def copyOperand : Callback.Run Reference.State Reference.StringId Reference.StringId Nat Nat :=
  fun before operand outcome => ∃ text,
    Reference.currentString before operand = some text ∧
    lift Reference.natOps.copyLiteral before text outcome

def callbacks :
    ValuesCallbacks Reference.State Reference.StringId Reference.StringId Reference.StringId Nat
      Nat where
  left := copyOperand
  right := copyOperand
  dropLeft := lift Reference.natOps.dropString
  dropRight := lift Reference.natOps.dropString
  double := fun _ _ _ terminal => terminal = 100

def payload : Payload Reference.StringId := .program ⟨.invalidArgument, none, none⟩
def error : Error Reference.BoxId := ⟨⟨0⟩⟩
def args : ValuesArgs Reference.BoxId Reference.StringId Reference.StringId :=
  ⟨error, ⟨0⟩, ⟨1⟩⟩
def initial : Reference.State :=
  ⟨[some "owned L", some "owned R"], [some payload], 2, []⟩
def leftCopy := Reference.stringResult false initial "owned L"
def rightCopy := Reference.stringResult false leftCopy.2 "owned R"
def assignedPayload := payload.withValues leftCopy.1 rightCopy.1
def assigned : Reference.State :=
  { rightCopy.2 with boxes := [some assignedPayload], events := rightCopy.2.events ++ [.write ⟨0⟩] }

def retiredString (before : Reference.State) (operand : Reference.StringId) (text : String) :
    Reference.State :=
  { before with
    strings := before.strings.set operand.index none
    events := before.events ++ [.dropString operand text] }

def leftGone := retiredString assigned args.left "owned L"
def finalState := retiredString leftGone args.right "owned R"

private theorem copy_iff (before : Reference.State) (operand : Reference.StringId) (text : String)
    (present : Reference.currentString before operand = some text) (available : before.remaining ≠
      0)
    (outcome : Outcome Reference.State Reference.StringId Nat Nat) :
    copyOperand before operand outcome ↔ outcome = .returned
      (Reference.stringResult false before text).1 (Reference.stringResult false before text).2 :=
        by
  simp [copyOperand, present, lift, Reference.natOps, Ops.mapTerminal, mapTerminal,
    Reference.ops, Callback.ofFunction, Reference.allocateString, available,
    mapTerminalOutcome, liftOutcome, eq_comm]

private theorem drop_iff (before : Reference.State) (operand : Reference.StringId) (text : String)
    (present : Reference.currentString before operand = some text)
    (outcome : Outcome Reference.State Unit Nat Nat) :
    lift Reference.natOps.dropString before operand outcome ↔
      outcome = .returned () (retiredString before operand text) := by
  simp [lift, Reference.natOps, Ops.mapTerminal, mapTerminal, Reference.ops,
    Reference.retireString, present, mapTerminalOutcome, liftOutcome, retiredString, eq_comm]

private theorem assignment_iff (outcome : Outcome Reference.State (Error Reference.BoxId) Empty
  Nat) :
    replaceValues Reference.natOps rightCopy.2 (error, leftCopy.1, rightCopy.1) outcome ↔
      outcome = .returned error assigned := by
  simp [replaceValues, rightCopy, leftCopy, Reference.stringResult, initial, Reference.natOps,
    Ops.mapTerminal, Reference.ops, Reference.currentBox, error, payload, Payload.compared,
    comparedStrings, Callback.bind, dropStrings, Owned.cleanup, Reference.writeBox,
    assigned, assignedPayload]

private theorem body_returns :
    valuesBody Reference.natOps callbacks args initial () (.returned error assigned) := by
  refine ⟨.returned leftCopy.1 leftCopy.2,
    (copy_iff initial args.left "owned L" rfl (by decide) _).mpr rfl, ?_⟩
  refine ⟨.returned rightCopy.1 rightCopy.2, ?_, ?_⟩
  · exact ⟨.returned rightCopy.1 rightCopy.2,
      (copy_iff leftCopy.2 args.right "owned R" rfl (by decide) _).mpr rfl, rfl⟩
  exact ⟨.returned error assigned, (assignment_iff _).mpr rfl, rfl⟩

private theorem body_iff (outcome : Outcome Reference.State (Error Reference.BoxId) Nat Nat) :
    valuesBody Reference.natOps callbacks args initial () outcome ↔
      outcome = .returned error assigned := by
  constructor
  · rintro ⟨first, called, next⟩
    have same := (copy_iff initial args.left "owned L" rfl (by decide) first).mp called
    cases same
    obtain ⟨second, guarded, rest⟩ := next
    obtain ⟨actual, called, kept⟩ := guarded
    have same := (copy_iff leftCopy.2 args.right "owned R" rfl (by decide) actual).mp called
    cases same
    change second = .returned rightCopy.1 rightCopy.2 at kept
    cases kept
    obtain ⟨actual, stored, kept⟩ := rest
    have same := (assignment_iff actual).mp stored
    cases same
    exact kept.symm
  · rintro rfl
    exact body_returns

private theorem left_entry {before : Reference.State}
    (entry : valuesDropEntry Reference.natOps callbacks args [] initial before) :
    before = assigned := by
  obtain ⟨pending, actual, body, cleaned, state⟩ := entry
  cases (body_iff pending).mp body
  change actual = .returned error assigned at cleaned
  cases cleaned
  exact state

private theorem right_entry {before : Reference.State}
    (entry : valuesDropEntry Reference.natOps callbacks args
      [fun state outcome => callbacks.dropLeft state args.left outcome] initial before) :
    before = leftGone := by
  obtain ⟨pending, actual, body, cleaned, state⟩ := entry
  cases (body_iff pending).mp body
  obtain ⟨dropped, run, rest⟩ := cleaned
  have same := (drop_iff assigned args.left "owned L" rfl dropped).mp run
  cases same
  change actual = .returned error leftGone at rest
  cases rest
  exact state

/-- Reachable cleanup frames hold for real owned String operands. A destructor
need not preserve its own storage in states unrelated to this admitted call. -/
theorem callbacks_admissible : callbacks.Admissible Reference.natOps args initial where
  left := by
    intro current outcome _ ready run
    obtain ⟨text, _, copied⟩ := run
    exact allocation_stringFrame Reference.natOps Reference.natOps.copyLiteral
      Reference.natOps_laws.copy Reference.natOps_laws.copy_boxes ready.2 copied
  right := by
    intro current retained afterLeft outcome _ ready first run
    obtain ⟨text, _, copied⟩ := first
    have frame := allocation_stringFrame Reference.natOps Reference.natOps.copyLiteral
      Reference.natOps_laws.copy Reference.natOps_laws.copy_boxes (error := args.error) ready.2
        copied
    obtain ⟨text, _, copied⟩ := run
    exact allocation_stringFrame Reference.natOps Reference.natOps.copyLiteral
      Reference.natOps_laws.copy Reference.natOps_laws.copy_boxes
      (StringFrame.returned_live Reference.natOps ready.2 frame) copied
  dropLeft := by
    intro before current outcome reached present _ run
    cases left_entry reached
    have same : current = assignedPayload := Option.some.inj present.symm
    subst current
    exact retirement_dropFrame Reference.natOps Reference.natOps_laws.stringDrop.other
      Reference.natOps_laws.drop_boxes (by decide) run
  dropRight := by
    intro before current outcome reached present _ run
    cases right_entry reached
    have same : current = assignedPayload := Option.some.inj present.symm
    subst current
    exact retirement_dropFrame Reference.natOps Reference.natOps_laws.stringDrop.other
      Reference.natOps_laws.drop_boxes (by decide) run

def familyTypes : ValuesTypes where
  base := ⟨Reference.State, Reference.StringId, Reference.BoxId, Nat,
    Reference.natOps⟩
  Left := Reference.StringId
  Right := Reference.StringId
  Unwind := Nat
  callbacks := callbacks

private theorem initial_ready : Ready Reference.natOps initial error :=
  ⟨payload, rfl, List.nodup_nil, fun _ member => nomatch member⟩

theorem run : withValues Reference.natOps callbacks initial args (.returned error finalState) := by
  refine ⟨payload, rfl, Or.inl ⟨.returned error finalState, ?_, rfl⟩⟩
  refine ⟨.returned error assigned, body_returns, ?_⟩
  exact ⟨.returned () leftGone, (drop_iff assigned args.left "owned L" rfl _).mpr rfl,
    .returned () finalState, (drop_iff leftGone args.right "owned R" rfl _).mpr rfl, rfl⟩

/-- The precondition and finite execution of the registered family both hold when
the source operand interpretations own resources, rather than borrowed text. -/
theorem owned_strings_have_execution :
    (withValuesFamily.contract familyTypes).HasExecution (withValuesRun familyTypes) := by
  refine ⟨initial, args, .returned error finalState,
    ⟨reference_comparison_laws, initial_ready,
      ValuesCallbacks.CallReady.of_admissible initial_ready callbacks_admissible
        Reference.natOps_laws.drop_boxes Reference.natOps_laws.store.available⟩, run⟩

/-- New comparison Strings survive; original operand storage is consumed left
then right after the Box store. No allocation resource is replaced by text. -/
theorem copies_survive_operand_drops :
    finalState.strings = [none, none, some "owned L", some "owned R"] ∧
    Reference.currentBox finalState error.resource = some assignedPayload ∧
    finalState.events = [.name ⟨2⟩ "owned L", .name ⟨3⟩ "owned R", .write ⟨0⟩,
      .dropString ⟨0⟩ "owned L", .dropString ⟨1⟩ "owned R"] := ⟨rfl, rfl, rfl⟩

def copiedLeftGone := retiredString finalState leftCopy.1 "owned L"
def copiedBothGone := retiredString copiedLeftGone rightCopy.1 "owned R"
def pubkeysAfter : Reference.State :=
  { copiedBothGone with
    boxes := [some (assignedPayload.withPubkeys sampleKey sampleKey)]
    events := copiedBothGone.events ++ [.write ⟨0⟩] }

private theorem pubkeys_run :
    withPubkeys Reference.natOps finalState (error, sampleKey, sampleKey)
      (.returned error pubkeysAfter) := by
  refine ⟨assignedPayload, rfl, .returned () copiedBothGone, ?_,
    assignedPayload, rfl, pubkeysAfter, rfl, rfl⟩
  exact ⟨.returned () copiedLeftGone,
    ⟨.returned () copiedLeftGone, ⟨"owned L", rfl, rfl⟩, rfl⟩,
    .returned () copiedBothGone,
    ⟨.returned () copiedBothGone, ⟨"owned R", rfl, rfl⟩, rfl⟩, rfl⟩

/-- The returned Ready of the first contract admits a second owned operation on
the same Box. That operation really drops both copied comparison Strings; no
independent readiness assumption is supplied for the intermediate state. -/
theorem values_then_pubkeys :
    (withPubkeysFamily.contract familyTypes.base).requires finalState (error, sampleKey, sampleKey)
      ∧
    (withPubkeysFamily.contract familyTypes.base).post finalState (error, sampleKey, sampleKey)
      (.returned error pubkeysAfter) := by
  have initialReady : Ready Reference.natOps initial error := by
    refine ⟨payload, rfl, ?_, ?_⟩ <;>
      simp [Payload.strings, payload, originStrings, comparedStrings]
  have firstPost := withValues_reference familyTypes initial args (.returned error finalState)
    ⟨reference_comparison_laws, initialReady, ValuesCallbacks.CallReady.of_admissible initialReady
      callbacks_admissible
      Reference.natOps_laws.drop_boxes Reference.natOps_laws.store.available⟩ run
  exact ⟨⟨reference_comparison_laws, firstPost.2.2,
      ComparisonStoreReady.of_available Reference.natOps Reference.natOps_laws.drop_boxes
        Reference.natOps_laws.store.available _ _ _⟩, withPubkeys_reference familyTypes.base
          finalState
    (error, sampleKey, sampleKey) (.returned error pubkeysAfter)
    ⟨reference_comparison_laws, firstPost.2.2,
      ComparisonStoreReady.of_available Reference.natOps Reference.natOps_laws.drop_boxes
        Reference.natOps_laws.store.available _ _ _⟩ pubkeys_run⟩

theorem next_update_retires_copies :
    pubkeysAfter.strings = [none, none, none, none] ∧
    Reference.currentBox pubkeysAfter error.resource =
      some (assignedPayload.withPubkeys sampleKey sampleKey) ∧
    pubkeysAfter.events = finalState.events ++
      [.dropString ⟨2⟩ "owned L", .dropString ⟨3⟩ "owned R", .write ⟨0⟩] := ⟨rfl, rfl, rfl⟩

/-- This different state aliases the comparison of the error with both operands.
It is deliberately outside the admitted initial call and its cleanup entries. -/
def aliased : Reference.State :=
  { initial with boxes := [some (payload.withValues args.left args.right)] }

/-- A global destructor frame would reject this valid call solely because an
unreachable aliasing state exists. Initial-state reachability avoids that
extra requirement while the actual destructor still retires its String. -/
theorem unreachable_alias_does_not_block_owned_operands :
    callbacks.Admissible Reference.natOps args initial ∧
    ¬ DropFrame (Unwind := Nat) Reference.natOps error [args.left, args.right] aliased
      (.returned () (retiredString aliased args.left "owned L")) := by
  refine ⟨callbacks_admissible, ?_⟩
  intro frame
  have impossible := frame.2 args.left (by simp)
  cases impossible

/-- A bad destructor retires a newly held comparison instead of its operand.
The raw relation still reports that actual effect. -/
def destructiveCallbacks :=
  { callbacks with dropLeft := fun before _ => lift Reference.natOps.dropString before leftCopy.1 }
def destructiveLeftGone := retiredString assigned leftCopy.1 "owned L"
def destructiveFinal := retiredString destructiveLeftGone args.right "owned R"

theorem destructive_operand_keeps_raw_exit :
    withValues Reference.natOps destructiveCallbacks initial args (.returned error
      destructiveFinal) := by
  refine ⟨payload, rfl, Or.inl ⟨.returned error destructiveFinal, ?_, rfl⟩⟩
  refine ⟨.returned error assigned, body_returns, ?_⟩
  exact ⟨.returned () destructiveLeftGone, (drop_iff assigned leftCopy.1 "owned L" rfl _).mpr rfl,
    .returned () destructiveFinal, (drop_iff destructiveLeftGone args.right "owned R" rfl _).mpr
      rfl, rfl⟩

private theorem assigned_ready : assignedPayload.Ready Reference.natOps assigned := by
  constructor
  · change ([⟨2⟩, ⟨3⟩] : List Reference.StringId).Nodup
    decide
  · intro held member
    have choice : held = leftCopy.1 ∨ held = rightCopy.1 := by
      simpa [assignedPayload, Payload.withValues, payload, Payload.strings, originStrings,
        comparedStrings] using member
    rcases choice with rfl | rfl
    · exact ⟨"owned L", rfl⟩
    · exact ⟨"owned R", rfl⟩

/-- The destructive callback is rejected at the cleanup state this call really
reaches, rather than erased from the operational outcomes. -/
theorem destructive_operand_not_admitted :
    ¬ destructiveCallbacks.Admissible Reference.natOps args initial := by
  intro admitted
  have reached : valuesDropEntry Reference.natOps destructiveCallbacks args [] initial assigned :=
    ⟨.returned error assigned, .returned error assigned, body_returns, rfl, rfl⟩
  have frame := admitted.dropLeft assigned assignedPayload (.returned () destructiveLeftGone)
    reached rfl assigned_ready ((drop_iff assigned leftCopy.1 "owned L" rfl _).mpr rfl)
  have impossible := frame.2 leftCopy.1 (by
    simp [assignedPayload, Payload.withValues, payload, Payload.strings, originStrings,
      comparedStrings])
  cases impossible

/-- The smaller returned-path gate of the family still rejects an operand drop
that destroys the actual comparison String of its normally returned error. -/
theorem destructive_operand_not_return_admitted :
    ¬ destructiveCallbacks.ReturnedAdmissible Reference.natOps args initial := by
  intro admitted
  have reached : valuesReturnedDropEntry Reference.natOps destructiveCallbacks args [] initial
    assigned :=
    ⟨error, assigned, body_returns, .nil _⟩
  have frame := admitted.dropLeft assigned assignedPayload destructiveLeftGone
    reached rfl assigned_ready ((drop_iff assigned leftCopy.1 "owned L" rfl _).mpr rfl)
  have impossible := frame.2 leftCopy.1 (by
    simp [assignedPayload, Payload.withValues, payload, Payload.strings, originStrings,
      comparedStrings])
  cases impossible

/-- An operand type can own a String while its ToString implementation
unwinds. The right callback preserves the actual borrowed state on that exit. -/
def unwindCallbacks :
    ValuesCallbacks Reference.State Reference.StringId Reference.StringId Reference.StringId Nat
      Nat :=
  { callbacks with right := fun before _ outcome => outcome = Outcome.unwound 7 before }
def partialGone := retiredString leftCopy.2 leftCopy.1 "owned L"
def unwindLeftGone := retiredString partialGone args.left "owned L"
def unwindBothGone := retiredString unwindLeftGone args.right "owned R"
def unwindFinal : Reference.State :=
  { unwindBothGone with boxes := [none], events := unwindBothGone.events ++ [.freeBox ⟨0⟩] }

private theorem unwind_body :
    valuesBody Reference.natOps unwindCallbacks args initial () (.unwound 7 partialGone) := by
  refine ⟨.returned leftCopy.1 leftCopy.2,
    (copy_iff initial args.left "owned L" rfl (by decide) _).mpr rfl, ?_⟩
  refine ⟨.unwound 7 partialGone, ?_, rfl⟩
  exact ⟨.unwound 7 leftCopy.2, rfl,
    .returned () partialGone, (drop_iff leftCopy.2 leftCopy.1 "owned L" rfl _).mpr rfl, rfl⟩

private theorem unwind_body_iff (outcome : Outcome Reference.State (Error Reference.BoxId) Nat Nat)
  :
    valuesBody Reference.natOps unwindCallbacks args initial () outcome ↔
      outcome = .unwound 7 partialGone := by
  constructor
  · rintro ⟨first, called, next⟩
    cases (copy_iff initial args.left "owned L" rfl (by decide) first).mp called
    obtain ⟨second, ⟨actual, called, cleaned⟩, rest⟩ := next
    change actual = .unwound 7 leftCopy.2 at called
    cases called
    obtain ⟨dropped, run, finish⟩ := cleaned
    cases (drop_iff leftCopy.2 leftCopy.1 "owned L" rfl dropped).mp run
    change second = .unwound 7 partialGone at finish
    cases finish
    exact rest
  · rintro rfl
    exact unwind_body

private theorem unwind_left_entry {before : Reference.State}
    (entry : valuesDropEntry Reference.natOps unwindCallbacks args [] initial before) :
    before = partialGone := by
  obtain ⟨pending, actual, body, cleaned, state⟩ := entry
  cases (unwind_body_iff pending).mp body
  change actual = .unwound 7 partialGone at cleaned
  cases cleaned
  exact state

private theorem unwind_right_entry {before : Reference.State}
    (entry : valuesDropEntry Reference.natOps unwindCallbacks args
      [fun state outcome => unwindCallbacks.dropLeft state args.left outcome] initial before) :
    before = unwindLeftGone := by
  obtain ⟨pending, actual, body, cleaned, state⟩ := entry
  cases (unwind_body_iff pending).mp body
  obtain ⟨dropped, run, rest⟩ := cleaned
  cases (drop_iff partialGone args.left "owned L" rfl dropped).mp run
  change actual = .unwound 7 unwindLeftGone at rest
  cases rest
  exact state

private theorem unwind_admissible : unwindCallbacks.Admissible Reference.natOps args initial where
  left := callbacks_admissible.left
  right := by
    intro _ _ _ outcome _ _ _ run
    cases run
    exact HeldFrame.refl _ _ _ _
  dropLeft := by
    intro before current outcome reached present _ run
    cases unwind_left_entry reached
    have same : current = payload := Option.some.inj present.symm
    subst current
    exact retirement_dropFrame Reference.natOps Reference.natOps_laws.stringDrop.other
      Reference.natOps_laws.drop_boxes (by simp [payload,
      Payload.strings, originStrings, comparedStrings]) run
  dropRight := by
    intro before current outcome reached present _ run
    cases unwind_right_entry reached
    have same : current = payload := Option.some.inj present.symm
    subst current
    exact retirement_dropFrame Reference.natOps Reference.natOps_laws.stringDrop.other
      Reference.natOps_laws.drop_boxes (by simp [payload,
      Payload.strings, originStrings, comparedStrings]) run

theorem unwind_run :
    withValues Reference.natOps unwindCallbacks initial args (.unwound 7 unwindFinal) := by
  refine ⟨payload, rfl, Or.inl ⟨.unwound 7 unwindBothGone, ?_, ?_⟩⟩
  · exact ⟨.unwound 7 partialGone, unwind_body,
      .returned () unwindLeftGone, (drop_iff partialGone args.left "owned L" rfl _).mpr rfl,
      .returned () unwindBothGone, (drop_iff unwindLeftGone args.right "owned R" rfl _).mpr rfl,
        rfl⟩
  · refine ⟨.returned () unwindFinal, ?_, rfl⟩
    refine ⟨.returned () unwindFinal, ?_, rfl⟩
    exact ⟨payload, rfl, .returned () unwindBothGone, rfl,
      .returned () unwindFinal, ⟨payload, rfl, rfl⟩, rfl⟩

/-- This admitted finite unwind cleans the partial result, both original
String operands, then the receiver; it keeps the actual callback reason. -/
theorem owned_strings_unwind_has_execution :
    let types : ValuesTypes := { familyTypes with callbacks := unwindCallbacks }
    (withValuesFamily.contract types).HasExecution (withValuesRun types) := by
  refine ⟨initial, args, .unwound (7 : Nat) unwindFinal,
    ⟨reference_comparison_laws, initial_ready,
      ValuesCallbacks.CallReady.of_admissible initial_ready unwind_admissible
        Reference.natOps_laws.drop_boxes Reference.natOps_laws.store.available⟩, unwind_run⟩

theorem owned_unwind_cleanup_order :
    unwindFinal.strings = [none, none, none] ∧ unwindFinal.boxes = [none] ∧
    unwindFinal.events = [.name ⟨2⟩ "owned L", .dropString ⟨2⟩ "owned L",
      .dropString ⟨0⟩ "owned L", .dropString ⟨1⟩ "owned R", .freeBox ⟨0⟩] := ⟨rfl, rfl, rfl⟩

end OwnedStringOperands

end SolanalibTest.Specs.Core.AnchorErrorOwnedCallbacks
