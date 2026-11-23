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

namespace SolanalibTest.Specs.Core.AnchorErrorOwned

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AnchorErrorOwned

/-- Fixed diagnostic used by the allocation controls. -/
def code : Code := ⟨"Example", 3007, "different owner"⟩
/-- The explicit normal three-allocation result. -/
def built := Reference.buildCodeResult (Reference.initial 3) code

/-- Three actual dependencies allocate distinct Strings before the Box. -/
theorem code_builds_in_order :
    buildCode Reference.ops (Reference.initial 3) code (.returned built.1 built.2) ∧
    built.2.events = [.name ⟨0⟩ "Example", .message ⟨1⟩ "different owner",
      .box ⟨0⟩ (.anchor ⟨⟨0⟩, 3007, ⟨1⟩, none, none⟩)] :=
  ⟨Reference.buildCode_returns _ _ (by decide), rfl⟩

/-- The normal result observes both actual allocated texts and the source code. -/
theorem code_current_value :
    current Reference.ops built.2 built.1 = some (.anchor code.value) :=
  buildCode_current
    ⟨Reference.ops_laws.copy.current, Reference.ops_laws.format,
      Reference.ops_laws.box.current, Reference.ops_laws.box_strings⟩ code_builds_in_order.1

/-- The constructed error has distinct, initialized owned fields. -/
theorem code_fields_ready : Ready Reference.ops built.2 built.1 :=
  buildCode_ready
    ⟨Reference.ops_laws.copy.current, Reference.ops_laws.format,
      Reference.ops_laws.box.current, Reference.ops_laws.box_strings⟩ code_builds_in_order.1

/-- Failure of the first allocation has a finite terminal outcome. -/
theorem name_allocation_terminal :
    buildCode Reference.ops (Reference.initial 0) code (.terminated (.allocation .name)) :=
  ⟨.terminated (.allocation .name), rfl, rfl⟩

/-- Message allocation occurs only after the first String has returned. -/
theorem message_allocation_terminal :
    buildCode Reference.ops (Reference.initial 1) code (.terminated (.allocation .message)) := by
  let copied := Reference.stringResult false (Reference.initial 1) code.name
  exact ⟨.returned copied.1 copied.2, rfl, .terminated (.allocation .message), rfl, rfl⟩

/-- Box failure follows both successful String dependencies, without a fake
Box return or a fabricated post-state for the terminal exit. -/
theorem box_allocation_terminal :
    buildCode Reference.ops (Reference.initial 2) code (.terminated (.allocation .box)) := by
  let copied := Reference.stringResult false (Reference.initial 2) code.name
  let formatted := Reference.stringResult true copied.2 code.message
  exact ⟨.returned copied.1 copied.2, rfl, .returned formatted.1 formatted.2, rfl,
    .terminated (.allocation .box), rfl, rfl⟩

/-- A zero-budget provider cannot also supply a successful error construction. -/
theorem zero_budget_rejects_return :
    ¬ buildCode Reference.ops (Reference.initial 0) code (.returned built.1 built.2) := by
  intro run
  obtain ⟨_, _, _, _, copied, _⟩ := (buildCode_returned_iff _ _ _ _ _).mp run
  cases copied

/-- ProgramError conversion allocates only a Box and preserves its exact value. -/
theorem program_error_is_boxed_once :
    let result := Reference.fromProgramResult (Reference.initial 1) .invalidArgument
    fromProgram Reference.ops (Reference.initial 1) .invalidArgument (.returned result.1 result.2) ∧
    result.2.events = [.box ⟨0⟩ (.program ⟨.invalidArgument, none, none⟩)] ∧
    current Reference.ops result.2 result.1 =
      some (.program ⟨.invalidArgument, none, none⟩) := by
  have run := Reference.fromProgram_returns (Reference.initial 1) .invalidArgument (by decide)
  exact ⟨run, rfl, fromProgram_current Reference.ops_laws.box.current run⟩

/-- From<AnchorError> moves existing String identities into its fresh Box. -/
theorem from_anchor_keeps_existing_strings :
    fromAnchor Reference.ops sampleAnchorState sampleAnchor
      (.returned sampleError sampleBoxState) ∧
    sampleBoxState.strings = sampleAnchorState.strings :=
  ⟨sampleAnchor_run, rfl⟩

/-- Fixture with all five owned String fields present. -/
def payload : Payload Reference.StringId :=
  .anchor ⟨⟨0⟩, 3007, ⟨1⟩, some (.accountName ⟨2⟩), some (.values ⟨3⟩ ⟨4⟩)⟩
/-- Five distinct String slots and one live diagnostic Box. -/
def initial : Reference.State :=
  ⟨[some "Name", some "Message", some "account", some "old-left", some "old-right"],
    [some payload], 0, []⟩
/-- Stable identity of the fixture Box. -/
def error : Error Reference.BoxId := ⟨⟨0⟩⟩
/-- Expected heap after one named String slot is retired. -/
def stringGone (before : Reference.State) (index : Nat) (text : String) : Reference.State :=
  ⟨before.strings.set index none, before.boxes, before.remaining,
    before.events ++ [.dropString ⟨index⟩ text]⟩
/-- Expected heap after the fixture Box allocation is retired. -/
def boxGone (before : Reference.State) : Reference.State :=
  ⟨before.strings, before.boxes.set 0 none, before.remaining,
    before.events ++ [.freeBox ⟨0⟩]⟩

/-- Expected state after retiring the old left comparison. -/
def oldLeftGone := stringGone initial 3 "old-left"
/-- Expected state after retiring both old comparison Strings. -/
def oldBothGone := stringGone oldLeftGone 4 "old-right"
/-- Expected same-Box payload store after comparison cleanup. -/
def replaced : Reference.State :=
  ⟨oldBothGone.strings, oldBothGone.boxes.set 0 (some (payload.withPubkeys sampleKey sampleKey)),
    oldBothGone.remaining, oldBothGone.events ++ [.write ⟨0⟩]⟩

private theorem old_strings_drop :
    dropStrings Reference.ops [⟨3⟩, ⟨4⟩] initial () (.returned () oldBothGone) :=
  ⟨.returned () oldLeftGone, ⟨"old-left", rfl, rfl⟩,
    .returned () oldBothGone, ⟨"old-right", rfl, rfl⟩, rfl⟩

/-- Pubkey replacement really retires the old compared Strings before the
same-Box assignment, in left-to-right tuple order. -/
theorem pubkeys_replaces_after_drops :
    withPubkeys Reference.ops initial (error, sampleKey, sampleKey) (.returned error replaced) ∧
    replaced.events = [.dropString ⟨3⟩ "old-left", .dropString ⟨4⟩ "old-right", .write ⟨0⟩] :=
  ⟨⟨payload, rfl, .returned () oldBothGone, old_strings_drop,
    payload, rfl, replaced, rfl, rfl⟩, rfl⟩

/-- Name, message and account-name resources remain current after replacement. -/
theorem pubkeys_keeps_other_owned_fields :
    replaced.strings = [some "Name", some "Message", some "account", none, none] ∧
    current Reference.ops replaced error = some
      (.anchor ⟨"Name", 3007, "Message", some (.accountName "account"),
        some (.pubkeys sampleKey sampleKey)⟩) :=
  ⟨rfl, rfl⟩

/-- The generic identity and payload theorem applies to an execution with real
old String destruction, not only a comparison-free sample. -/
theorem pubkeys_identity_and_payload :
    Reference.ops.currentBox replaced error.resource = some (payload.withPubkeys sampleKey
      sampleKey) :=
  (withPubkeys_payload Reference.ops_laws.drop_boxes Reference.ops_laws.store.current rfl
    pubkeys_replaces_after_drops.1).2

/-- Expected state after the name field drops. -/
def gone0 := stringGone initial 0 "Name"
/-- Expected state after the message field drops. -/
def gone1 := stringGone gone0 1 "Message"
/-- Expected state after the account-name origin drops. -/
def gone2 := stringGone gone1 2 "account"
/-- Expected state after the left comparison field drops. -/
def gone3 := stringGone gone2 3 "old-left"
/-- Expected state after the right comparison field drops. -/
def gone4 := stringGone gone3 4 "old-right"
/-- Expected fully retired error allocation and fields. -/
def retired := boxGone gone4

private theorem fields_drop :
    dropStrings Reference.ops payload.strings initial () (.returned () gone4) :=
  ⟨.returned () gone0, ⟨"Name", rfl, rfl⟩,
    .returned () gone1, ⟨"Message", rfl, rfl⟩,
    .returned () gone2, ⟨"account", rfl, rfl⟩,
    .returned () gone3, ⟨"old-left", rfl, rfl⟩,
    .returned () gone4, ⟨"old-right", rfl, rfl⟩, rfl⟩

/-- Error destruction executes every owned field in declaration order, followed
by the Box allocation, using actual intermediate heap states. -/
theorem drop_error_order :
    dropError Reference.ops error initial (.returned () retired) ∧
    retired.events = [.dropString ⟨0⟩ "Name", .dropString ⟨1⟩ "Message",
      .dropString ⟨2⟩ "account", .dropString ⟨3⟩ "old-left",
      .dropString ⟨4⟩ "old-right", .freeBox ⟨0⟩] :=
  ⟨⟨payload, rfl, .returned () gone4, fields_drop, ⟨payload, rfl, rfl⟩⟩, rfl⟩

/-- Completed error destruction invalidates both the Box and its owned fields. -/
theorem drop_retires_every_resource :
    retired.strings = [none, none, none, none, none] ∧
    Reference.ops.currentBox retired error.resource = none :=
  ⟨rfl, dropError_consumed Reference.ops_laws.boxFree.current drop_error_order.1⟩

/-- The retired handle cannot be dropped a second time. -/
theorem double_drop_rejected :
    ¬ dropError Reference.ops error retired (.returned () retired) :=
  dropError_no_double_drop Reference.ops_laws.boxFree.current drop_error_order.1 _

/-- A diagnostic store cannot revive the consumed Box. -/
theorem replacement_after_drop_rejected :
    ¬ withPubkeys Reference.ops retired (error, sampleKey, sampleKey) (.returned error retired) :=
  withPubkeys_dead _ _ _ _ _ drop_retires_every_resource.2 _

/-- Monotone finite-heap allocation does not recycle a retired identity. -/
theorem retired_identity_not_reallocated :
    (Reference.boxResult { retired with remaining := 1 } (.program ⟨.invalidArgument, none,
      none⟩)).1 =
      (⟨1⟩ : Reference.BoxId) ∧
    Reference.currentBox
      (Reference.boxResult { retired with remaining := 1 } (.program ⟨.invalidArgument, none,
        none⟩)).2
      ⟨0⟩ = none :=
  ⟨rfl, rfl⟩

/-- An explicit alternative input state for current-observation controls. -/
def changed : Reference.State := { initial with strings := initial.strings.set 0 (some "cha\
  nged") }

/-- Current error observation follows the String contents of the supplied state.
This observer test does not claim a legal Rust mutation of a held String. -/
theorem current_is_not_a_saved_snapshot :
    current Reference.ops changed error =
      some (.anchor ⟨"changed", 3007, "Message", some (.accountName "account"),
        some (.values "old-left" "old-right")⟩) := rfl

/-- The drop dependency likewise reads the actual current text at drop time. -/
theorem string_drop_reads_actual_contents :
    Reference.ops.dropString changed ⟨0⟩ (.returned () (stringGone changed 0 "changed")) :=
  ⟨"changed", rfl, rfl⟩

/-- Focusing a successful build preserves the unrelated outer state. -/
theorem focused_build_preserves_outer_state :
    buildCode (Reference.ops.focus (Owned.Focus.snd : Owned.Focus (Nat × Reference.State)
      Reference.State))
      (91, Reference.initial 3) code (.returned built.1 (91, built.2)) :=
  buildCode_focus_returned Reference.ops Owned.Focus.snd _ code _ _ code_builds_in_order.1

/-- The two callback conversions produce actual independently owned strings. -/
theorem values_normal_current :
    withValues Reference.natOps sampleValuesCallbacks sampleValuesState sampleValuesArgs
      (.returned sampleError sampleValuesAfter) ∧
    current Reference.natOps sampleValuesAfter sampleError = some
      (.anchor ⟨"AccountOwnedByWrongProgram", 3007,
        "The given account is owned by a different program", none, some (.values "12" "34")⟩) :=
  ⟨sampleValues_run, rfl⟩

/-- Allocation order and the same-identity comparison store stay observable. -/
theorem values_normal_trace :
    sampleValuesAfter.events = [.box ⟨0⟩ (.anchor sampleAnchor),
      .name ⟨2⟩ "12", .message ⟨3⟩ "34", .write ⟨0⟩] := rfl


/-- State at assignment after two new compared String resources have returned. -/
def rhsReady : Reference.State :=
  { initial with strings := initial.strings ++ [some "new-left", some "new-right"] }

/-- Old comparison cleanup retains the newly created RHS resources. -/
def rhsOldLeftGone : Reference.State := stringGone rhsReady 3 "old-left"

/-- Both old comparison fields are gone before the new descriptor is stored. -/
def rhsOldBothGone : Reference.State := stringGone rhsOldLeftGone 4 "old-right"

/-- Expected assignment state with the two new String identities in Box zero. -/
def valuesReplaced : Reference.State :=
  ⟨rhsOldBothGone.strings, rhsOldBothGone.boxes.set 0 (some (payload.withValues ⟨5⟩ ⟨6⟩)),
    rhsOldBothGone.remaining, rhsOldBothGone.events ++ [.write ⟨0⟩]⟩

/-- Owned value assignment drops old comparison Strings and retains both new
resources. This exercises the replacement component with nonempty old values. -/
theorem values_replacement_drops_old_keeps_new :
    replaceValues Reference.ops rhsReady (error, ⟨5⟩, ⟨6⟩) (.returned error valuesReplaced) ∧
    valuesReplaced.strings =
      [some "Name", some "Message", some "account", none, none, some "new-left", some "new-\
        right"] ∧
    current Reference.ops valuesReplaced error = some
      (.anchor ⟨"Name", 3007, "Message", some (.accountName "account"),
        some (.values "new-left" "new-right")⟩) := by
  refine ⟨?_, rfl, rfl⟩
  exact ⟨payload, rfl, .returned () rhsOldBothGone,
    ⟨.returned () rhsOldLeftGone, ⟨"old-left", rfl, rfl⟩,
      .returned () rhsOldBothGone, ⟨"old-right", rfl, rfl⟩, rfl⟩,
    payload, rfl, valuesReplaced, rfl, rfl⟩

/-- The generic descriptor theorem applies after actual old-comparison cleanup. -/
theorem values_replacement_payload_preserved :
    Reference.ops.currentBox valuesReplaced error.resource = some (payload.withValues ⟨5⟩ ⟨6⟩) :=
  (replaceValues_payload Reference.ops Reference.ops_laws.drop_boxes
    Reference.ops_laws.store.current rfl values_replacement_drops_old_keeps_new.1).2

end SolanalibTest.Specs.Core.AnchorErrorOwned
