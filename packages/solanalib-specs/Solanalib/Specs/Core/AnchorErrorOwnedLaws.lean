/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOwnedFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOwned

/-- Primitive fresh-storage laws. They concern logical observations, not
Rust pointer ownership, allocator success or termination. -/
structure AllocationLaws {State Resource Value Terminal : Type}
    (read : State → Resource → Option Value)
    (allocate : Callback.Run State Value Resource Empty Terminal) : Prop where
  /-- A returned identity observes the supplied value in its actual state. -/
  current : ∀ before value resource after,
    allocate before value (.returned resource after) → read after resource = some value
  /-- This allocation does not alias a currently live resource. -/
  fresh : ∀ before value resource after,
    allocate before value (.returned resource after) → read before resource = none
  /-- Every other logical resource retains its current contents. -/
  other : ∀ before value resource after,
    allocate before value (.returned resource after) →
      ∀ other, other ≠ resource → read after other = read before other

/-- Primitive retirement laws rule out returning a second owner or fabricating
a drop for a missing logical resource. They leave terminal exits explicit. -/
structure RetirementLaws {State Resource Value Terminal : Type}
    (read : State → Resource → Option Value)
    (retire : Callback.Run State Resource Unit Empty Terminal) : Prop where
  /-- Every finite retirement begins with an existing resource. -/
  present : ∀ before resource outcome, retire before resource outcome →
    ∃ value, read before resource = some value
  /-- A completed retirement invalidates the resource. -/
  current : ∀ before resource after,
    retire before resource (.returned () after) → read after resource = none
  /-- Retirement leaves every different resource unchanged. -/
  other : ∀ before resource after,
    retire before resource (.returned () after) →
      ∀ other, other ≠ resource → read after other = read before other

/-- Primitive in-place storage guarantees for a live Box. -/
structure StoreLaws {State Resource Value : Type}
    (read : State → Resource → Option Value)
    (write : State → Resource → Value → Option State) : Prop where
  /-- A represented Box admits its infallible mathematical store. -/
  available : ∀ before resource old value, read before resource = some old →
    ∃ after, write before resource value = some after
  /-- An actual store does not revive a missing logical Box. -/
  present : ∀ before resource value after, write before resource value = some after →
    ∃ old, read before resource = some old
  /-- The stored payload becomes the current payload of the same identity. -/
  current : ∀ before resource value after, write before resource value = some after →
    read after resource = some value
  /-- Every other Box keeps its current payload. -/
  other : ∀ before resource value after, write before resource value = some after →
    ∀ other, other ≠ resource → read after other = read before other

/-- Local String/Box dependency guarantees used by the resource-preservation
theorems. Cross-store frame clauses exclude arbitrary changes to the held
error while a primitive String dependency runs. The operations remain explicit
inputs, and these laws are not postconditions assumed for an SDK function. -/
structure Ops.Laws {State StringResource BoxResource Terminal : Type}
    (ops : Ops State StringResource BoxResource Terminal) : Prop where
  /-- Literal copying is a fresh, exact String construction. -/
  copy : AllocationLaws ops.currentString ops.copyLiteral
  /-- Fixed-literal formatting is a distinct fresh String construction. -/
  format : AllocationLaws ops.currentString ops.formatLiteral
  /-- Box construction keeps the complete supplied resource-bearing payload. -/
  box : AllocationLaws ops.currentBox ops.newBox
  /-- String retirement is real and preserves other String resources. -/
  stringDrop : RetirementLaws ops.currentString ops.dropString
  /-- Box retirement is real and preserves other Box identities. -/
  boxFree : RetirementLaws ops.currentBox ops.freeBox
  /-- Stores preserve Box identity without allocation. -/
  store : StoreLaws ops.currentBox ops.writeBox
  /-- Copying a literal does not modify an existing error payload. -/
  copy_boxes : ∀ before text resource after,
    ops.copyLiteral before text (.returned resource after) →
    ∀ box, ops.currentBox after box = ops.currentBox before box
  /-- Formatting a fixed literal does not modify an existing error payload. -/
  format_boxes : ∀ before text resource after,
    ops.formatLiteral before text (.returned resource after) →
    ∀ box, ops.currentBox after box = ops.currentBox before box
  /-- Boxing fields preserves their owned String resources. -/
  box_strings : ∀ before payload resource after,
    ops.newBox before payload (.returned resource after) →
    ∀ string, ops.currentString after string = ops.currentString before string
  /-- String destruction leaves the containing Box payload descriptor intact. -/
  drop_boxes : ∀ before resource after,
    ops.dropString before resource (.returned () after) →
    ∀ box, ops.currentBox after box = ops.currentBox before box
  /-- An in-place payload store does not independently mutate String storage. -/
  store_strings : ∀ before resource payload after,
    ops.writeBox before resource payload = some after →
    ∀ string, ops.currentString after string = ops.currentString before string
  /-- Box deallocation follows field cleanup without a second String drop. -/
  free_strings : ∀ before resource after,
    ops.freeBox before resource (.returned () after) →
    ∀ string, ops.currentString after string = ops.currentString before string

/-- Only the three primitive guarantees used by the owned boxing family.
They apply to actual returned allocations and assume no finite execution. -/
structure Ops.BoxingLaws {State StringResource BoxResource Terminal : Type}
    (ops : Ops State StringResource BoxResource Terminal) : Prop where
  current : ∀ before payload resource after,
    ops.newBox before payload (.returned resource after) →
      ops.currentBox after resource = some payload
  fresh : ∀ before payload resource after,
    ops.newBox before payload (.returned resource after) →
      ops.currentBox before resource = none
  strings : ∀ before payload resource after,
    ops.newBox before payload (.returned resource after) →
      ∀ string, ops.currentString after string = ops.currentString before string

/-- Comparison replacement uses exactly the old-String cleanup frames and the
actual payload store. It assumes no allocation, store availability or Box drop. -/
structure Ops.ComparisonLaws {State StringResource BoxResource Terminal : Type}
    (ops : Ops State StringResource BoxResource Terminal) : Prop where
  string_other : ∀ before resource after,
    ops.dropString before resource (.returned () after) →
      ∀ other, other ≠ resource → ops.currentString after other = ops.currentString before other
  drop_boxes : ∀ before resource after,
    ops.dropString before resource (.returned () after) →
      ∀ box, ops.currentBox after box = ops.currentBox before box
  store_current : ∀ before resource payload after,
    ops.writeBox before resource payload = some after →
      ops.currentBox after resource = some payload
  store_strings : ∀ before resource payload after,
    ops.writeBox before resource payload = some after →
      ∀ string, ops.currentString after string = ops.currentString before string

/-- The fixed-code lifecycle results use six allocation facts: the contents of the first
String, all three second-String allocation facts, and the contents and String frame of the Box.
Uncalled retirement and store laws are excluded. -/
structure Ops.CodeLaws {State StringResource BoxResource Terminal : Type}
    (ops : Ops State StringResource BoxResource Terminal) : Prop where
  copy_current : ∀ before text resource after,
    ops.copyLiteral before text (.returned resource after) →
      ops.currentString after resource = some text
  format : AllocationLaws ops.currentString ops.formatLiteral
  box_current : ∀ before payload resource after,
    ops.newBox before payload (.returned resource after) →
      ops.currentBox after resource = some payload
  box_strings : ∀ before payload resource after,
    ops.newBox before payload (.returned resource after) →
      ∀ string, ops.currentString after string = ops.currentString before string

variable {State StringResource BoxResource Terminal : Type}

/-- The observable value of the constructed error follows from primitive allocation
laws, including the actual String contents and their preserved identities. -/
theorem buildCode_current {ops : Ops State StringResource BoxResource Terminal}
    (laws : ops.CodeLaws) {before after : State} {code : Code} {error : Error BoxResource}
    (run : buildCode ops before code (.returned error after)) :
    current ops after error = some (.anchor code.value) := by
  obtain ⟨name, afterName, message, afterMessage, copied, formatted, allocated⟩ :=
    (buildCode_returned_iff _ _ _ _ _).mp run
  have nameCurrent := laws.copy_current _ _ _ _ copied
  have messageFresh := laws.format.fresh _ _ _ _ formatted
  have different : name ≠ message := by
    intro same
    subst message
    rw [nameCurrent] at messageFresh
    cases messageFresh
  have nameAfter : ops.currentString after name = some code.name := by
    rw [laws.box_strings _ _ _ _ allocated,
      laws.format.other _ _ _ _ formatted name different]
    exact nameCurrent
  have messageAfter : ops.currentString after message = some code.message := by
    rw [laws.box_strings _ _ _ _ allocated]
    exact laws.format.current _ _ _ _ formatted
  simp only [current, laws.box_current _ _ _ _ allocated, Option.bind_some,
    Payload.observe, nameAfter, messageAfter, observeOrigin, observeCompared, Code.value]
  rfl

/-- From<ProgramError> keeps the entire source error and absent diagnostics. -/
theorem fromProgram_current {ops : Ops State StringResource BoxResource Terminal}
    (box_current : ∀ before payload resource after,
      ops.newBox before payload (.returned resource after) →
        ops.currentBox after resource = some payload)
    {before after : State} {program : ProgramError.Value}
    {error : Error BoxResource}
    (run : fromProgram ops before program (.returned error after)) :
    current ops after error = some (.program ⟨program, none, none⟩) := by
  have allocated := (fromProgram_returned_iff _ _ _ _ _).mp run
  simp only [current, box_current _ _ _ _ allocated, Option.bind_some,
    Payload.observe, observeOrigin, observeCompared]
  rfl

/-- The fixed constructor returns an initialized Box whose two owned String
identities are distinct. No Clone/Copy ownership is inferred from the strings. -/
theorem buildCode_ready {ops : Ops State StringResource BoxResource Terminal}
    (laws : ops.CodeLaws) {before after : State} {code : Code} {error : Error BoxResource}
    (run : buildCode ops before code (.returned error after)) : Ready ops after error := by
  obtain ⟨name, afterName, message, afterMessage, copied, formatted, allocated⟩ :=
    (buildCode_returned_iff _ _ _ _ _).mp run
  have nameCurrent := laws.copy_current _ _ _ _ copied
  have messageFresh := laws.format.fresh _ _ _ _ formatted
  have different : name ≠ message := by
    intro same
    subst message
    rw [nameCurrent] at messageFresh
    cases messageFresh
  refine ⟨.anchor ⟨name, code.number, message, none, none⟩,
    laws.box_current _ _ _ _ allocated, ?_, ?_⟩
  · simpa [Payload.strings, originStrings, comparedStrings] using different
  · intro resource member
    have either : resource = name ∨ resource = message := by
      simpa [Payload.strings, originStrings, comparedStrings] using member
    rcases either with same | same
    · subst resource
      refine ⟨code.name, ?_⟩
      rw [laws.box_strings _ _ _ _ allocated,
        laws.format.other _ _ _ _ formatted name different]
      exact nameCurrent
    · subst resource
      exact ⟨code.message, (laws.box_strings _ _ _ _ allocated message).trans
        (laws.format.current _ _ _ _ formatted)⟩

/-- A normal String cleanup consists of real ordered normal destructor calls. -/
theorem dropStrings_returns {ops : Ops State StringResource BoxResource Terminal}
    {resources : List StringResource} {before after : State}
    (run : dropStrings ops resources before () (.returned () after)) :
    Owned.DropReturns
      (resources.map (fun resource state result => ops.dropString state resource result))
      before after := by
  induction resources generalizing before with
  | nil =>
      change Outcome.returned () after = Outcome.returned () before at run
      cases run
      exact .nil _
  | cons head rest induction =>
      obtain ⟨intermediate, dropped, remaining⟩ := run
      cases intermediate with
      | unwound impossible _ => nomatch impossible
      | terminated _ => cases remaining
      | returned acknowledgement middle =>
          cases acknowledgement
          exact .cons _ _ before middle after dropped (induction remaining)

/-- String cleanup preserves every Box descriptor while threading state. -/
theorem dropStrings_boxes {ops : Ops State StringResource BoxResource Terminal}
    (drop_boxes : ∀ before resource after,
      ops.dropString before resource (.returned () after) →
        ∀ box, ops.currentBox after box = ops.currentBox before box)
    {resources : List StringResource} {before after : State}
    (run : dropStrings ops resources before () (.returned () after)) (box : BoxResource) :
    ops.currentBox after box = ops.currentBox before box := by
  induction resources generalizing before with
  | nil =>
      change Outcome.returned () after = Outcome.returned () before at run
      cases run
      rfl
  | cons head rest induction =>
      obtain ⟨intermediate, dropped, remaining⟩ := run
      cases intermediate with
      | unwound impossible _ => nomatch impossible
      | terminated _ => cases remaining
      | returned acknowledgement middle =>
          cases acknowledgement
          exact (induction remaining).trans (drop_boxes _ _ _ dropped box)

/-- Ordered String cleanup preserves every retained String outside the actual
drop list, using the primitive destructor frame at each intermediate state. -/
theorem dropStrings_other {ops : Ops State StringResource BoxResource Terminal}
    (string_other : ∀ before resource after,
      ops.dropString before resource (.returned () after) →
        ∀ other, other ≠ resource → ops.currentString after other = ops.currentString before other)
    {resources : List StringResource} {before after : State}
    (run : dropStrings ops resources before () (.returned () after))
    (held : StringResource) (apart : held ∉ resources) :
    ops.currentString after held = ops.currentString before held := by
  induction resources generalizing before with
  | nil =>
      change Outcome.returned () after = Outcome.returned () before at run
      cases run
      rfl
  | cons head rest induction =>
      obtain ⟨intermediate, dropped, remaining⟩ := run
      cases intermediate with
      | unwound impossible _ => nomatch impossible
      | terminated _ => cases remaining
      | returned acknowledgement middle =>
          cases acknowledgement
          have different : held ≠ head := fun same => apart (by simp [same])
          have outside : held ∉ rest := fun member => apart (List.mem_cons_of_mem _ member)
          exact (induction remaining outside).trans
            (string_other _ _ _ dropped held different)

/-- A normally completed error drop retires its Box identity. -/
theorem dropError_consumed {ops : Ops State StringResource BoxResource Terminal}
    (box_retired : ∀ before resource after,
      ops.freeBox before resource (.returned () after) → ops.currentBox after resource = none)
    {before after : State} {error : Error BoxResource}
    (run : dropError ops error before (.returned () after)) :
    ops.currentBox after error.resource = none := by
  obtain ⟨_, _, intermediate, _, remaining⟩ := run
  cases intermediate with
  | unwound impossible _ => nomatch impossible
  | terminated _ => cases remaining
  | returned acknowledgement middle =>
      cases acknowledgement
      exact box_retired _ _ _ remaining

/-- Completed retirement rejects every attempted second finite error drop. -/
theorem dropError_no_double_drop {ops : Ops State StringResource BoxResource Terminal}
    (box_retired : ∀ before resource after,
      ops.freeBox before resource (.returned () after) → ops.currentBox after resource = none)
    {before after : State} {error : Error BoxResource}
    (run : dropError ops error before (.returned () after))
    (outcome : Outcome State Unit Empty Terminal) : ¬ dropError ops error after outcome :=
  dropError_dead ops after error (dropError_consumed box_retired run) outcome

/-- A normal comparison replacement writes the same variant and all remaining
resource descriptors back into the same Box. -/
theorem withPubkeys_payload {ops : Ops State StringResource BoxResource Terminal}
    (drop_boxes : ∀ before resource after,
      ops.dropString before resource (.returned () after) →
        ∀ box, ops.currentBox after box = ops.currentBox before box)
    (store_current : ∀ before resource payload after,
      ops.writeBox before resource payload = some after →
        ops.currentBox after resource = some payload)
    {before after : State} {error result : Error BoxResource}
    {left right : Solanalib.Runtime.Pubkey} {payload : Payload StringResource}
    (present : ops.currentBox before error.resource = some payload)
    (run : withPubkeys ops before (error, left, right) (.returned result after)) :
    result = error ∧ ops.currentBox after error.resource = some (payload.withPubkeys left right) :=
      by
  obtain ⟨actual, observed, intermediate, dropped, remaining⟩ := run
  have same : actual = payload := Option.some.inj (observed.symm.trans present)
  subst actual
  cases intermediate with
  | unwound impossible _ => nomatch impossible
  | terminated _ => cases remaining
  | returned acknowledgement middle =>
      cases acknowledgement
      obtain ⟨next, readable, final, stored, returned⟩ := remaining
      have boxes := dropStrings_boxes drop_boxes dropped error.resource
      have same : next = payload := Option.some.inj (readable.symm.trans (boxes.trans present))
      subst next
      cases returned
      exact ⟨rfl, store_current _ _ _ _ stored⟩

/-- Owned String descriptors outside the replaceable comparison field. -/
def Payload.retainedStrings : Payload StringResource → List StringResource
  | .anchor value => [value.name, value.message] ++ originStrings value.origin
  | .program value => originStrings value.origin

/-- The original field order separates retained resources from the comparison
resources that assignment must destroy. -/
theorem Payload.strings_eq_append (payload : Payload StringResource) :
    payload.strings = payload.retainedStrings ++ comparedStrings payload.compared := by
  cases payload <;> rfl

/-- Pubkey comparisons introduce no new owned String fields. -/
theorem Payload.withPubkeys_strings (payload : Payload StringResource)
    (left right : Solanalib.Runtime.Pubkey) :
    (payload.withPubkeys left right).strings = payload.retainedStrings := by
  cases payload <;>
    simp [Payload.withPubkeys, Payload.strings, Payload.retainedStrings, comparedStrings]

/-- Replacing the comparison removes precisely its old owned Strings; all
other resource descriptors remain in their declaration order. -/
theorem Payload.withPubkeys_strings_append (payload : Payload StringResource)
    (left right : Solanalib.Runtime.Pubkey) :
    (payload.withPubkeys left right).strings ++ comparedStrings payload.compared =
      payload.strings := by
  rw [Payload.withPubkeys_strings, ← Payload.strings_eq_append]

/-- A ready receiver returns ready after comparison replacement. Distinctness
of its owned fields prevents cleanup of the old comparison from retiring a
retained name, message or origin; primitive stores then preserve those fields. -/
theorem withPubkeys_ready {ops : Ops State StringResource BoxResource Terminal}
    (laws : ops.ComparisonLaws) {before after : State} {error result : Error BoxResource}
    {left right : Solanalib.Runtime.Pubkey} (ready : Ready ops before error)
    (run : withPubkeys ops before (error, left, right) (.returned result after)) :
    Ready ops after result := by
  obtain ⟨payload, present, distinct, live⟩ := ready
  obtain ⟨actual, observed, intermediate, dropped, remaining⟩ := run
  have same : actual = payload := Option.some.inj (observed.symm.trans present)
  subst actual
  cases intermediate with
  | unwound impossible _ => nomatch impossible
  | terminated _ => cases remaining
  | returned acknowledgement middle =>
      cases acknowledgement
      obtain ⟨next, readable, final, stored, returned⟩ := remaining
      have boxes := dropStrings_boxes laws.drop_boxes dropped error.resource
      have same : next = payload := Option.some.inj (readable.symm.trans (boxes.trans present))
      subst next
      cases returned
      have split : ((payload.withPubkeys left right).strings ++
          comparedStrings payload.compared).Nodup := by
        rw [Payload.withPubkeys_strings_append]
        exact distinct
      have separated := List.nodup_append.mp split
      refine ⟨payload.withPubkeys left right, laws.store_current _ _ _ _ stored,
        separated.1, ?_⟩
      intro held member
      have original : held ∈ payload.strings := by
        rw [← Payload.withPubkeys_strings_append payload left right]
        exact List.mem_append_left _ member
      have apart : held ∉ comparedStrings payload.compared := by
        intro removed
        exact separated.2.2 held member held removed rfl
      obtain ⟨contents, current⟩ := live held original
      refine ⟨contents, ?_⟩
      rw [laws.store_strings _ _ _ _ stored, dropStrings_other laws.string_other dropped held apart]
      exact current

end Solanalib.Specs.Core.AnchorErrorOwned
