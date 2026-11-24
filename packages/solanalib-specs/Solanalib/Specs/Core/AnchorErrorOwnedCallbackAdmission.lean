/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOwnedCallbacks

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOwned

variable {State StringResource BoxResource Left Right Unwind Terminal : Type}

/-- The incomplete comparison RHS owns its actual first String separately
from the current error. The error may have changed, but both owners must still
be live and disjoint when a second-conversion unwind starts their cleanup. -/
def PartialValuesReady (ops : Ops State StringResource BoxResource Terminal)
    (state : State) (error : Error BoxResource) (retained : StringResource) : Prop :=
  ∃ payload, ops.currentBox state error.resource = some payload ∧ payload.Ready ops state ∧
    (∃ text, ops.currentString state retained = some text) ∧ retained ∉ payload.strings

/-- The error resources needed by a later nonterminal local step. A terminal
exit has no state and supplies no later resource obligation. -/
def ValuesResources (ops : Ops State StringResource BoxResource Terminal)
    (error : Error BoxResource) {Value : Type} : Outcome State Value Unwind Terminal → Prop
  | .returned _ state | .unwound _ state => Ready ops state error
  | .terminated _ => True

/-- Identify the actual state of a pending nonterminal cleanup exit. -/
def ValuesStateAt {Value : Type} (pending : Outcome State Value Unwind Terminal)
    (before : State) : Prop :=
  match pending with
  | .returned _ actual | .unwound _ actual => before = actual
  | .terminated _ => False

/-- The resource obligation of a destructor depends on whether unwinding is already
in progress. A second unwind and a terminal exit do not reach another local
read or destructor, so their states need not retain the error. -/
def ValuesDropResources (ops : Ops State StringResource BoxResource Terminal)
    (error : Error BoxResource) {Value : Type}
    (pending : Outcome State Value Unwind Terminal)
    (dropped : Outcome State Unit Unwind Terminal) : Prop :=
  match pending, dropped with
  | .returned _ _, .returned _ after | .returned _ _, .unwound _ after
  | .unwound _ _, .returned _ after => Ready ops after error
  | _, _ => True

/-- The actual body exit and destructor prefix leading to a particular pending
cleanup outcome. This is reachability evidence, not a filter on any run. -/
def valuesCleanupEntry (ops : Ops State StringResource BoxResource Terminal)
    (callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal)
    (args : ValuesArgs BoxResource Left Right)
    (prior : List (Owned.DropAction State Unwind Terminal)) (initial : State)
    (pending : Outcome State (Error BoxResource) Unwind Terminal) : Prop :=
  ∃ bodyExit, valuesBody ops callbacks args initial () bodyExit ∧
    Owned.cleanup callbacks.double prior bodyExit pending

/-- Admission for actual with_values callback sites. Normal-return frames are
kept for the returned ownership result. Other continuing exits require only the
current resources needed by source cleanup; unrelated effects and changed
ready error payloads remain possible. Store availability applies only after
actual returning conversions and old-comparison cleanup. No provider is
assumed to terminate or to have a finite result. -/
structure ValuesCallbacks.CallReady
    (ops : Ops State StringResource BoxResource Terminal)
    (callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal)
    (args : ValuesArgs BoxResource Left Right) (initial : State) : Prop where
  /-- The existing normal-path ownership frames. -/
  returned : callbacks.ReturnedAdmissible ops args initial
  /-- The unwind of the first conversion must leave self ready for later cleanup. -/
  left_unwind : ∀ reason after, callbacks.left initial args.left (.unwound reason after) →
    Ready ops after args.error
  /-- A second-conversion unwind also retains the actual incomplete RHS owner. -/
  right_unwind : ∀ retained afterLeft reason after,
    callbacks.left initial args.left (.returned retained afterLeft) →
    callbacks.right afterLeft args.right (.unwound reason after) →
      PartialValuesReady ops after args.error retained
  /-- The first operand is constrained only at an actual nonterminal entry. -/
  dropLeft : ∀ pending before outcome,
    valuesCleanupEntry ops callbacks args [] initial pending → ValuesStateAt pending before →
    Ready ops before args.error → callbacks.dropLeft before args.left outcome →
      ValuesDropResources ops args.error pending outcome
  /-- The second operand follows the actual first-operand cleanup step. -/
  dropRight : ∀ pending before outcome,
    valuesCleanupEntry ops callbacks args
      [fun state result => callbacks.dropLeft state args.left result] initial pending →
    ValuesStateAt pending before → Ready ops before args.error →
    callbacks.dropRight before args.right outcome →
      ValuesDropResources ops args.error pending outcome
  /-- An ordinary assignment cannot disappear after a real returning RHS and
  old-field cleanup. This does not require those dependencies to return. -/
  assignment : ∀ retained afterLeft resource afterRight,
    callbacks.left initial args.left (.returned retained afterLeft) →
    callbacks.right afterLeft args.right (.returned resource afterRight) →
      ComparisonStoreReady ops afterRight args.error
        (fun payload => payload.withValues retained resource)

/-- Stronger equality frames imply the smaller cleanup resource requirements
at exactly the reached states. The primitive store premise is used only to
supply the reached ordinary assignments. -/
theorem ValuesCallbacks.CallReady.of_admissible
    {ops : Ops State StringResource BoxResource Terminal}
    {callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal}
    {args : ValuesArgs BoxResource Left Right} {initial : State}
    (ready : Ready ops initial args.error)
    (frames : callbacks.Admissible ops args initial)
    (drop_boxes : ∀ before resource after,
      ops.dropString before resource (.returned () after) →
        ∀ box, ops.currentBox after box = ops.currentBox before box)
    (available : ∀ before resource old value,
      ops.currentBox before resource = some old →
        ∃ after, ops.writeBox before resource value = some after) :
    callbacks.CallReady ops args initial := by
  obtain ⟨payload, present, fields⟩ := ready
  have dropResult : ∀ (pending : Outcome State (Error BoxResource) Unwind Terminal) before outcome,
      ValuesStateAt (Value := Error BoxResource) pending before →
      Ready ops before args.error →
      (∀ current, ops.currentBox before args.error.resource = some current →
        current.Ready ops before → DropFrame ops args.error current.strings before outcome) →
      ValuesDropResources ops args.error pending outcome := by
    intro pending before outcome _ ready frame
    obtain ⟨current, currentBox, currentFields⟩ := ready
    have held := frame current currentBox currentFields
    cases pending <;> cases outcome <;> try trivial
    all_goals exact ⟨current, held.1.trans currentBox,
      HeldFrame.payloadReady ops currentFields held⟩
  refine ⟨frames.returned, ?_, ?_, ?_, ?_, ?_⟩
  · intro reason after run
    have held := frames.left payload (.unwound reason after) present fields run
    exact ⟨payload, held.1.trans present, HeldFrame.payloadReady ops fields held⟩
  · intro retained afterLeft reason after first second
    have firstFrame := frames.left payload (.returned retained afterLeft) present fields first
    have secondFrame := frames.right payload retained afterLeft (.unwound reason after)
      present fields first second
    have held : HeldFrame ops args.error payload.strings afterLeft after :=
      ⟨secondFrame.1, fun resource member => secondFrame.2 resource (List.mem_cons_of_mem _ member)⟩
    obtain ⟨text, live⟩ := firstFrame.2.1
    exact ⟨payload, held.1.trans (firstFrame.1.1.trans present),
      HeldFrame.payloadReady ops (HeldFrame.payloadReady ops fields firstFrame.1) held,
      ⟨text, (secondFrame.2 retained (by simp)).trans live⟩, firstFrame.2.2⟩
  · intro pending before outcome reached located ready run
    apply dropResult pending before outcome located ready
    intro current currentBox currentFields
    obtain ⟨bodyExit, body, trace⟩ := reached
    exact frames.dropLeft before current outcome ⟨bodyExit, pending, body, trace, by cases pending
      <;> exact located⟩
      currentBox currentFields run
  · intro pending before outcome reached located ready run
    apply dropResult pending before outcome located ready
    intro current currentBox currentFields
    obtain ⟨bodyExit, body, trace⟩ := reached
    exact frames.dropRight before current outcome ⟨bodyExit, pending, body, trace, by cases pending
      <;> exact located⟩
      currentBox currentFields run
  · intro retained afterLeft resource afterRight _ _
    exact ComparisonStoreReady.of_available ops drop_boxes available _ _ _

/-- Every actual normal first-String cleanup preserves the live fields of the current error.
Distinct resource ownership, not equality with the entry error,
is what prevents this drop from retiring a field that self still owns. -/
theorem PartialValuesReady.after_drop
    {ops : Ops State StringResource BoxResource Terminal}
    (laws : ops.ComparisonLaws) {before after : State} {error : Error BoxResource}
    {retained : StringResource} (ready : PartialValuesReady ops before error retained)
    (dropped : ops.dropString before retained (.returned () after)) : Ready ops after error := by
  obtain ⟨payload, present, fields, _, apart⟩ := ready
  refine ⟨payload, (laws.drop_boxes _ _ _ dropped error.resource).trans present, fields.1, ?_⟩
  intro resource member
  obtain ⟨text, live⟩ := fields.2 resource member
  refine ⟨text, (laws.string_other _ _ _ dropped resource ?_).trans live⟩
  intro same
  exact apart (same ▸ member)

/-- Every supplied finite old-comparison cleanup after two returning
conversions has the exact local assignment continuation. -/
theorem replaceValues_cleanup_continues (ops : Ops State StringResource BoxResource Terminal)
    (drop_boxes : ∀ before resource after,
      ops.dropString before resource (.returned () after) →
        ∀ box, ops.currentBox after box = ops.currentBox before box)
    {before : State} {error : Error BoxResource} {left right : StringResource}
    (stores : ComparisonStoreReady ops before error (fun payload => payload.withValues left right))
    {payload : Payload StringResource}
    (present : ops.currentBox before error.resource = some payload)
    {outcome : Outcome State Unit Empty Terminal}
    (dropped : dropStrings ops (comparedStrings payload.compared) before () outcome) :
    match outcome with
    | .returned () afterDrops => ∃ after,
        ops.writeBox afterDrops error.resource (payload.withValues left right) = some after ∧
        replaceValues ops before (error, left, right) (.returned error after)
    | .unwound impossible _ => nomatch impossible
    | .terminated reason => replaceValues ops before (error, left, right) (.terminated reason) := by
  cases outcome with
  | unwound impossible _ => nomatch impossible
  | terminated reason => exact ⟨payload, present, .terminated reason, dropped, rfl⟩
  | returned completed afterDrops =>
    cases completed
    obtain ⟨current, after, stored⟩ := stores.after_drops ops drop_boxes present dropped
    exact ⟨after, stored, payload, present, .returned () afterDrops, dropped,
      payload, current, after, stored, rfl⟩

/-- Two actual returning conversions leave exactly the current error and the
separate new String owners needed by the comparison assignment. -/
theorem ValuesCallbacks.CallReady.rhs_resources
    {ops : Ops State StringResource BoxResource Terminal}
    {callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal}
    {args : ValuesArgs BoxResource Left Right} {initial : State}
    (admitted : callbacks.CallReady ops args initial)
    (ready : Ready ops initial args.error)
    {left right : StringResource} {afterLeft afterRight : State}
    (first : callbacks.left initial args.left (.returned left afterLeft))
    (second : callbacks.right afterLeft args.right (.returned right afterRight)) :
    ∃ payload, ops.currentBox afterRight args.error.resource = some payload ∧
      payload.Ready ops afterRight ∧
      (∃ text, ops.currentString afterRight left = some text) ∧
      (∃ text, ops.currentString afterRight right = some text) ∧
      left ∉ payload.strings ∧ right ∉ left :: payload.strings := by
  obtain ⟨payload, present, fields⟩ := ready
  have leftFrame := admitted.returned.left payload left afterLeft present fields first
  have rightFrame := admitted.returned.right payload left afterLeft right afterRight
    present fields first second
  have held : HeldFrame ops args.error payload.strings afterLeft afterRight :=
    ⟨rightFrame.1.1, fun resource member => rightFrame.1.2 resource (List.mem_cons_of_mem _ member)⟩
  obtain ⟨text, live⟩ := leftFrame.2.1
  exact ⟨payload, held.1.trans (leftFrame.1.1.trans present),
    HeldFrame.payloadReady ops (HeldFrame.payloadReady ops fields leftFrame.1) held,
    ⟨text, (rightFrame.1.2 left (by simp)).trans live⟩,
    rightFrame.2.1, leftFrame.2.2, rightFrame.2.2⟩

/-- Every actual nonterminal body exit has the resources required by operand
cleanup. The proof follows both conversion exits and the real partial-RHS
destructor; no existence of a complete body exit is used as admission. -/
theorem ValuesCallbacks.CallReady.body_resources
    {ops : Ops State StringResource BoxResource Terminal}
    (laws : ops.ComparisonLaws)
    {callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal}
    {args : ValuesArgs BoxResource Left Right} {initial : State}
    (admitted : callbacks.CallReady ops args initial)
    (ready : Ready ops initial args.error)
    {outcome : Outcome State (Error BoxResource) Unwind Terminal}
    (run : valuesBody ops callbacks args initial () outcome) :
    ValuesResources ops args.error outcome := by
  obtain ⟨first, firstCalled, next⟩ := run
  cases first with
  | terminated reason => cases next; trivial
  | unwound reason after => cases next; exact admitted.left_unwind reason after firstCalled
  | returned left afterLeft =>
    obtain ⟨second, guarded, assignment⟩ := next
    obtain ⟨rightExit, secondCalled, protectedExit⟩ := guarded
    cases rightExit with
    | terminated reason =>
      have equal := (Owned.onUnwind_terminated _ _ _ _).mp protectedExit
      cases equal
      cases assignment
      trivial
    | returned right afterRight =>
      cases protectedExit
      obtain ⟨actual, assigned, equal⟩ := assignment
      cases actual with
      | unwound impossible _ => nomatch impossible
      | terminated reason => cases equal; trivial
      | returned result after =>
        cases equal
        obtain ⟨payload, present, fields, leftLive, rightLive, leftApart, rightApart⟩ :=
          admitted.rhs_resources ready firstCalled secondCalled
        have assignedReady := replaceValues_ready ops laws present fields
          leftLive rightLive leftApart rightApart assigned
        have same := replaceValues_identity ops assigned
        simpa only [same, ValuesResources, liftOutcome] using assignedReady
    | unwound reason afterRight =>
      have partialReady := admitted.right_unwind left afterLeft reason afterRight firstCalled
        secondCalled
      obtain ⟨dropped, stringDrop, finished⟩ := protectedExit
      obtain ⟨actual, actualDrop, equal⟩ := stringDrop
      cases actual with
      | unwound impossible _ => nomatch impossible
      | terminated terminal =>
        cases equal
        cases finished
        cases assignment
        trivial
      | returned completed afterDrop =>
        cases completed
        cases equal
        cases finished
        cases assignment
        exact partialReady.after_drop laws actualDrop

/-- One real destructor step transports the required error resources whenever
source cleanup continues. Terminal and double-unwind exits stop immediately. -/
theorem values_cleanup_one_resources
    (ops : Ops State StringResource BoxResource Terminal)
    (error : Error BoxResource) {Value : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (action : Owned.DropAction State Unwind Terminal)
    {pending final : Outcome State Value Unwind Terminal}
    (ready : ValuesResources ops error pending)
    (step : ∀ before outcome, ValuesStateAt pending before → Ready ops before error →
      action before outcome → ValuesDropResources ops error pending outcome)
    (run : Owned.cleanup double [action] pending final) : ValuesResources ops error final := by
  cases pending with
  | terminated reason => cases run; trivial
  | returned value before =>
    obtain ⟨dropped, called, rest⟩ := run
    have preserved := step before dropped rfl ready called
    cases dropped with
    | returned completed after => cases completed; cases rest; exact preserved
    | unwound reason after => cases rest; exact preserved
    | terminated reason => cases rest; trivial
  | unwound reason before =>
    obtain ⟨dropped, called, rest⟩ := run
    have preserved := step before dropped rfl ready called
    cases dropped with
    | returned completed after => cases completed; cases rest; exact preserved
    | unwound later after => obtain ⟨terminal, _, equal⟩ := rest; cases equal; trivial
    | terminated terminal => cases rest; trivial

/-- Two source-ordered operand drops preserve the current error exactly when
another cleanup step is reached. The second law is applied to the actual first
step, including a first unwind after normal body completion. -/
theorem values_cleanup_two_resources
    (ops : Ops State StringResource BoxResource Terminal)
    (error : Error BoxResource) {Value : Type}
    (double : Owned.DoubleUnwind State Unwind Terminal)
    (first second : Owned.DropAction State Unwind Terminal)
    {pending final : Outcome State Value Unwind Terminal}
    (ready : ValuesResources ops error pending)
    (firstStep : ∀ before outcome, ValuesStateAt pending before → Ready ops before error →
      first before outcome → ValuesDropResources ops error pending outcome)
    (secondStep : ∀ entry before outcome,
      Owned.cleanup double [first] pending entry → ValuesStateAt entry before →
      Ready ops before error → second before outcome → ValuesDropResources ops error entry outcome)
    (run : Owned.cleanup double [first, second] pending final) : ValuesResources ops error final :=
      by
  cases pending with
  | terminated reason => cases run; trivial
  | returned value before =>
    obtain ⟨dropped, called, rest⟩ := run
    have preserved := firstStep before dropped rfl ready called
    cases dropped with
    | terminated reason => cases rest; trivial
    | returned completed after =>
      cases completed
      have reached : Owned.cleanup double [first] (.returned value before) (.returned value after)
        :=
        ⟨.returned () after, called, rfl⟩
      exact values_cleanup_one_resources ops error double second (pending := .returned value after)
        preserved
        (secondStep _ · · reached) rest
    | unwound reason after =>
      have reached : Owned.cleanup double [first] (.returned value before) (.unwound reason after)
        :=
        ⟨.unwound reason after, called, rfl⟩
      exact values_cleanup_one_resources ops error double second (pending := .unwound reason after)
        preserved
        (secondStep _ · · reached) rest
  | unwound reason before =>
    obtain ⟨dropped, called, rest⟩ := run
    have preserved := firstStep before dropped rfl ready called
    cases dropped with
    | terminated terminal => cases rest; trivial
    | unwound later after => obtain ⟨terminal, _, equal⟩ := rest; cases equal; trivial
    | returned completed after =>
      cases completed
      have reached : Owned.cleanup (Value := Value) double [first] (.unwound reason before)
        (.unwound reason after) :=
        ⟨.returned () after, called, rfl⟩
      exact values_cleanup_one_resources ops error double second (pending := .unwound reason after)
        preserved
        (secondStep _ · · reached) rest

/-- Every actual nonterminal operand-scope exit leaves the current Box of `self` and
owned fields available to its outer cleanup. In particular an admitted finite
unwind cannot disappear because the error Box was erased by a callback. -/
theorem ValuesCallbacks.CallReady.scope_resources
    {ops : Ops State StringResource BoxResource Terminal}
    (laws : ops.ComparisonLaws)
    {callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal}
    {args : ValuesArgs BoxResource Left Right} {initial : State}
    (admitted : callbacks.CallReady ops args initial)
    (ready : Ready ops initial args.error)
    {outcome : Outcome State (Error BoxResource) Unwind Terminal}
    (run : Owned.scope callbacks.double
      [fun state result => callbacks.dropLeft state args.left result,
       fun state result => callbacks.dropRight state args.right result]
      (valuesBody ops callbacks args) initial () outcome) :
    ValuesResources ops args.error outcome := by
  obtain ⟨bodyExit, body, cleaned⟩ := run
  apply values_cleanup_two_resources ops args.error callbacks.double _ _
    (admitted.body_resources laws ready body) ?_ ?_ cleaned
  · intro before outcome located current run
    exact admitted.dropLeft bodyExit before outcome ⟨bodyExit, body, rfl⟩ located current run
  · intro entry before outcome trace located current run
    exact admitted.dropRight entry before outcome ⟨bodyExit, body, trace⟩ located current run

/-- A reached second-conversion unwind has a live actual first String to
destroy. Every supplied finite String-destructor exit produces the exact body
continuation, retaining the error for operand cleanup after a normal drop. -/
theorem ValuesCallbacks.CallReady.right_unwind_continues
    {ops : Ops State StringResource BoxResource Terminal}
    (laws : ops.ComparisonLaws)
    {callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal}
    {args : ValuesArgs BoxResource Left Right} {initial afterLeft afterRight : State}
    {left : StringResource} {reason : Unwind}
    (admitted : callbacks.CallReady ops args initial)
    (first : callbacks.left initial args.left (.returned left afterLeft))
    (second : callbacks.right afterLeft args.right (.unwound reason afterRight)) :
    (∃ text, ops.currentString afterRight left = some text) ∧
      ∀ dropExit, ops.dropString afterRight left dropExit →
        match dropExit with
        | .returned () after => Ready ops after args.error ∧
            valuesBody ops callbacks args initial () (.unwound reason after)
        | .unwound impossible _ => nomatch impossible
        | .terminated terminal => valuesBody ops callbacks args initial () (.terminated terminal)
          := by
  have partialReady := admitted.right_unwind left afterLeft reason afterRight first second
  have live : ∃ text, ops.currentString afterRight left = some text := by
    obtain ⟨_, _, _, live, _⟩ := partialReady
    exact live
  refine ⟨live, ?_⟩
  intro dropExit dropped
  cases dropExit with
  | unwound impossible _ => nomatch impossible
  | returned completed after =>
    cases completed
    refine ⟨partialReady.after_drop laws dropped, ?_⟩
    exact ⟨.returned left afterLeft, first, .unwound reason after,
      ⟨.unwound reason afterRight, second, .returned () after,
        ⟨.returned () after, dropped, rfl⟩, rfl⟩, rfl⟩
  | terminated terminal =>
    exact ⟨.returned left afterLeft, first, .terminated terminal,
      ⟨.unwound reason afterRight, second, .terminated terminal,
        ⟨.terminated terminal, dropped, rfl⟩, rfl⟩, rfl⟩

/-- At each actual normal prefix of the field destruction of `self`, its Box remains
current and every not-yet-dropped String remains live. This justifies the next
local cleanup entry without assuming that the next destructor terminates. -/
theorem ready_error_cleanup_prefix
    {ops : Ops State StringResource BoxResource Terminal}
    (laws : ops.ComparisonLaws) {before after : State} {error : Error BoxResource}
    {payload : Payload StringResource} {done remaining : List StringResource}
    (present : ops.currentBox before error.resource = some payload)
    (ready : payload.Ready ops before) (split : payload.strings = done ++ remaining)
    (dropped : dropStrings ops done before () (.returned () after)) :
    ops.currentBox after error.resource = some payload ∧
      ∀ resource ∈ remaining, ∃ text, ops.currentString after resource = some text := by
  refine ⟨(dropStrings_boxes laws.drop_boxes dropped error.resource).trans present, ?_⟩
  have distinct := List.nodup_append.mp (split ▸ ready.1)
  intro resource member
  obtain ⟨text, live⟩ := ready.2 resource (split ▸ List.mem_append_right done member)
  exact ⟨text, (dropStrings_other laws.string_other dropped resource
    (fun previous => distinct.2.2 resource previous resource member rfl)).trans live⟩

/-- A terminal operand scope stops before self cleanup, preserving its exact
terminal reason without demanding any final state or live error resource. -/
theorem withValues_scope_terminal
    (ops : Ops State StringResource BoxResource Terminal)
    (callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal)
    {initial : State} {args : ValuesArgs BoxResource Left Right} {reason : Terminal}
    {payload : Payload StringResource}
    (present : ops.currentBox initial args.error.resource = some payload)
    (scope : Owned.scope callbacks.double
      [fun state result => callbacks.dropLeft state args.left result,
       fun state result => callbacks.dropRight state args.right result]
      (valuesBody ops callbacks args) initial () (.terminated reason)) :
    withValues ops callbacks initial args (.terminated reason) := by
  exact ⟨payload, present, Or.inl ⟨.terminated reason, scope,
    (Owned.onUnwind_terminated _ _ _ _).mpr rfl⟩⟩

/-- Every actual unwind from the operand scope reaches a live current error.
Each supplied finite field-cleanup and Box-free exit then gives the exact full
with_values continuation, preserving the original unwind or the actual
terminal exit. No future dependency result is invented. -/
theorem ValuesCallbacks.CallReady.unwind_continues
    {ops : Ops State StringResource BoxResource Terminal}
    (laws : ops.ComparisonLaws)
    {callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal}
    {args : ValuesArgs BoxResource Left Right} {initial afterScope : State} {reason : Unwind}
    (admitted : callbacks.CallReady ops args initial)
    (ready : Ready ops initial args.error)
    (scope : Owned.scope callbacks.double
      [fun state result => callbacks.dropLeft state args.left result,
       fun state result => callbacks.dropRight state args.right result]
      (valuesBody ops callbacks args) initial () (.unwound reason afterScope)) :
    ∃ payload, ops.currentBox afterScope args.error.resource = some payload ∧
      payload.Ready ops afterScope ∧
      ∀ fieldsExit, dropStrings ops payload.strings afterScope () fieldsExit →
        match fieldsExit with
        | .returned () afterFields =>
            ops.currentBox afterFields args.error.resource = some payload ∧
            ∀ freeExit, ops.freeBox afterFields args.error.resource freeExit →
              match freeExit with
              | .returned () after => withValues ops callbacks initial args (.unwound reason after)
              | .unwound impossible _ => nomatch impossible
              | .terminated terminal => withValues ops callbacks initial args (.terminated terminal)
        | .unwound impossible _ => nomatch impossible
        | .terminated terminal => withValues ops callbacks initial args (.terminated terminal) := by
  obtain ⟨original, initialBox, _⟩ := ready
  obtain ⟨payload, currentBox, currentFields⟩ := admitted.scope_resources laws
    ⟨original, initialBox, by assumption⟩ scope
  refine ⟨payload, currentBox, currentFields, ?_⟩
  intro fieldsExit fieldsRun
  cases fieldsExit with
  | unwound impossible _ => nomatch impossible
  | terminated terminal =>
    have dropped : dropError ops args.error afterScope (.terminated terminal) :=
      ⟨payload, currentBox, .terminated terminal, fieldsRun, rfl⟩
    exact ⟨original, initialBox, Or.inl ⟨.unwound reason afterScope, scope,
      .terminated terminal, ⟨.terminated terminal, dropped, rfl⟩, rfl⟩⟩
  | returned completed afterFields =>
    cases completed
    refine ⟨(dropStrings_boxes laws.drop_boxes fieldsRun args.error.resource).trans currentBox, ?_⟩
    intro freeExit freed
    have dropped : dropError ops args.error afterScope freeExit :=
      ⟨payload, currentBox, .returned () afterFields, fieldsRun, freed⟩
    cases freeExit with
    | unwound impossible _ => nomatch impossible
    | terminated terminal =>
      exact ⟨original, initialBox, Or.inl ⟨.unwound reason afterScope, scope,
        .terminated terminal, ⟨.terminated terminal, dropped, rfl⟩, rfl⟩⟩
    | returned completed after =>
      cases completed
      exact ⟨original, initialBox, Or.inl ⟨.unwound reason afterScope, scope,
        .returned () after, ⟨.returned () after, dropped, rfl⟩, rfl⟩⟩

/-- Each actual pair of returning conversions has live assignment inputs, and
every supplied finite old-comparison cleanup has a body continuation. This is
progress at the reached local store, not assumed conversion termination. -/
theorem ValuesCallbacks.CallReady.assignment_continues
    {ops : Ops State StringResource BoxResource Terminal}
    (laws : ops.ComparisonLaws)
    {callbacks : ValuesCallbacks State StringResource Left Right Unwind Terminal}
    {args : ValuesArgs BoxResource Left Right} {initial : State}
    (admitted : callbacks.CallReady ops args initial)
    (ready : Ready ops initial args.error)
    {left right : StringResource} {afterLeft afterRight : State}
    (first : callbacks.left initial args.left (.returned left afterLeft))
    (second : callbacks.right afterLeft args.right (.returned right afterRight)) :
    ∃ payload, ops.currentBox afterRight args.error.resource = some payload ∧
      payload.Ready ops afterRight ∧
      ∀ fieldsExit, dropStrings ops (comparedStrings payload.compared) afterRight () fieldsExit →
        match fieldsExit with
        | .returned () afterFields => ∃ after,
            ops.writeBox afterFields args.error.resource (payload.withValues left right) = some
              after ∧
            valuesBody ops callbacks args initial () (.returned args.error after)
        | .unwound impossible _ => nomatch impossible
        | .terminated reason => valuesBody ops callbacks args initial () (.terminated reason) := by
  obtain ⟨payload, present, fields, _⟩ := admitted.rhs_resources ready first second
  refine ⟨payload, present, fields, ?_⟩
  intro fieldsExit dropped
  have stores := admitted.assignment left afterLeft right afterRight first second
  have continues := replaceValues_cleanup_continues ops laws.drop_boxes stores present dropped
  cases fieldsExit with
  | unwound impossible _ => nomatch impossible
  | terminated reason =>
    exact ⟨.returned left afterLeft, first, .returned right afterRight,
      ⟨.returned right afterRight, second, rfl⟩,
      .terminated reason, continues, rfl⟩
  | returned completed afterFields =>
    cases completed
    obtain ⟨after, stored, assigned⟩ := continues
    exact ⟨after, stored, .returned left afterLeft, first,
      .returned right afterRight, ⟨.returned right afterRight, second, rfl⟩,
      .returned args.error after, assigned, rfl⟩

end Solanalib.Specs.Core.AnchorErrorOwned
