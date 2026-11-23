/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOwnedCallbackAdmission
public import Solanalib.Specs.Core.AnchorErrorOwnedTransport

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOwned

/-- Generic source types, primitive storage operations and actual ToString /
operand-drop providers. The frame obligation belongs to the initial call and
each callback site actually reached from it. -/
structure ValuesTypes where
  /-- Shared stable String/Box interpretation and explicit primitive providers. -/
  base : Types
  /-- First source operand interpretation. -/
  Left : Type
  /-- Second source operand interpretation. -/
  Right : Type
  /-- Trait and destructor unwind reasons. -/
  Unwind : Type
  /-- Two conversions, two drops and an explicit double-unwind policy. -/
  callbacks : ValuesCallbacks base.State base.StringResource Left Right Unwind base.Terminal

/-- Complete owned with_values family. Returned frames prove normal ownership;
reached nonterminal resource and ordinary-store premises prevent a finite
callback exit from disappearing at later local cleanup or assignment. Opaque
providers need not terminate, and all raw callback effects remain unchanged. -/
def withValuesFamily : Family where
  Index := ValuesTypes
  State := fun types => types.base.State
  Args := fun types => ValuesArgs types.base.BoxResource types.Left types.Right
  Value := fun types => Error types.base.BoxResource
  Unwind := ValuesTypes.Unwind
  Terminal := fun types => types.base.Terminal
  contract := fun types => {
    requires := fun before args => types.base.ops.ComparisonLaws ∧
      Ready types.base.ops before args.error ∧
      types.callbacks.CallReady types.base.ops args before
    post := fun before args outcome => withValues types.base.ops types.callbacks before args
      outcome ∧
      match outcome with
      | .returned error after => error = args.error ∧ Ready types.base.ops after error
      | .unwound _ _ | .terminated _ => True }

/-- Operational reference of the complete owned callback and cleanup model. -/
def withValuesRun : FamilyRun withValuesFamily :=
  fun types => withValues types.base.ops types.callbacks

/-- Every reference instantiation retains the Box identity of the receiver on a
normal return, with the complete finite dependency trace in its postcondition. -/
theorem withValues_reference : FamilyReference withValuesFamily withValuesRun := by
  intro types before args outcome admitted run
  refine ⟨run, ?_⟩
  cases outcome with
  | returned error after =>
    exact ⟨withValues_identity _ _ run,
      withValues_ready _ admitted.1 _ admitted.2.1 admitted.2.2.returned run⟩
  | unwound _ _ | terminated _ => trivial

variable {State StringResource BoxResource Unwind Terminal : Type}

/-- A real fresh String allocation frames any explicitly held, initialized
String footprint and the held Box. This helper imposes no frame on unrelated
ambient fields beyond the supplied primitive guarantees. -/
theorem allocation_stringFrame (ops : Ops State StringResource BoxResource Terminal)
    (allocate : Callback.Run State String StringResource Empty Terminal)
    (laws : AllocationLaws ops.currentString allocate)
    (boxes : ∀ before text resource after,
      allocate before text (.returned resource after) →
      ∀ box, ops.currentBox after box = ops.currentBox before box)
    {error : Error BoxResource} {strings : List StringResource} {before : State} {text : String}
    {outcome : Outcome State StringResource Unwind Terminal}
    (live : ∀ resource ∈ strings, ∃ contents, ops.currentString before resource = some contents)
    (run : lift allocate before text outcome) : StringFrame ops error strings before outcome := by
  obtain ⟨actual, called, equal⟩ := run
  cases actual with
  | unwound impossible _ => nomatch impossible
  | terminated _ => cases equal; trivial
  | returned resource after =>
    cases equal
    have fresh := laws.fresh _ _ _ _ called
    refine ⟨⟨boxes _ _ _ _ called error.resource, ?_⟩,
      ⟨text, laws.current _ _ _ _ called⟩, ?_⟩
    · intro other member
      obtain ⟨contents, present⟩ := live other member
      have different : other ≠ resource := by
        intro same
        subst other
        rw [fresh] at present
        cases present
      exact laws.other _ _ _ _ called other different
    · intro member
      obtain ⟨contents, present⟩ := live resource member
      rw [fresh] at present
      cases present

/-- A reflexive frame permits arbitrary initialized footprints. -/
theorem HeldFrame.refl (ops : Ops State StringResource BoxResource Terminal)
    (error : Error BoxResource) (strings : List StringResource) (state : State) :
    HeldFrame ops error strings state state := ⟨rfl, fun _ _ => rfl⟩

/-- An owned String operand can be retired while the error retains different
String resources. The existing primitive laws supply the frame; no destructor
success or final state is invented for a terminal outcome. -/
theorem retirement_dropFrame (ops : Ops State StringResource BoxResource Terminal)
    (string_other : ∀ before resource after,
      ops.dropString before resource (.returned () after) →
        ∀ other, other ≠ resource → ops.currentString after other = ops.currentString before other)
    (drop_boxes : ∀ before resource after,
      ops.dropString before resource (.returned () after) →
        ∀ box, ops.currentBox after box = ops.currentBox before box)
    {error : Error BoxResource} {strings : List StringResource}
    {before : State} {resource : StringResource}
    {outcome : Outcome State Unit Unwind Terminal}
    (separate : resource ∉ strings) (run : lift ops.dropString before resource outcome) :
    DropFrame ops error strings before outcome := by
  obtain ⟨actual, dropped, equal⟩ := run
  cases actual with
  | unwound impossible _ => nomatch impossible
  | terminated _ => cases equal; trivial
  | returned completed after =>
    cases completed
    cases equal
    refine ⟨drop_boxes _ _ _ dropped error.resource, ?_⟩
    intro other member
    exact string_other _ _ _ dropped other (by
      intro same
      exact separate (same ▸ member))

/-- A successful conversion leaves its disjoint result and the explicitly held
initialized Strings live in the actual returned state. -/
theorem StringFrame.returned_live (ops : Ops State StringResource BoxResource Terminal)
    {error : Error BoxResource} {strings : List StringResource} {before after : State}
    {resource : StringResource}
    (live : ∀ held ∈ strings, ∃ text, ops.currentString before held = some text)
    (frame : StringFrame (Unwind := Unwind) ops error strings before (.returned resource after)) :
    ∀ held ∈ resource :: strings, ∃ text, ops.currentString after held = some text := by
  intro held member
  rcases List.mem_cons.mp member with same | member
  · subst held
    exact frame.2.1
  · obtain ⟨text, present⟩ := live held member
    exact ⟨text, (frame.1.2 held member).trans present⟩

/-- Finite callback reference interprets operands as borrowed text, whose
reference drops carry no resources, and makes two actual String allocations.
This is a mathematical ToString interpretation, not a source-body proof. -/
def sampleValuesCallbacks :
    ValuesCallbacks Reference.State Reference.StringId String String Nat Nat where
  left := fun before value => lift Reference.natOps.copyLiteral before value
  right := fun before value => lift Reference.natOps.formatLiteral before value
  dropLeft := fun before _ outcome => outcome = .returned () before
  dropRight := fun before _ outcome => outcome = .returned () before
  double := fun _ _ _ terminal => terminal = 3

/-- The concrete conversions and trivial operand drops satisfy the held
footprint obligation for every receiver and actual heap state. -/
theorem sampleValuesCallbacks_admissible (args : ValuesArgs Reference.BoxId String String)
    (initial : Reference.State) :
    sampleValuesCallbacks.Admissible Reference.natOps args initial where
  left := by
    intro payload outcome _ ready run
    exact allocation_stringFrame Reference.natOps Reference.natOps.copyLiteral
      Reference.natOps_laws.copy Reference.natOps_laws.copy_boxes ready.2 run
  right := by
    intro payload retained afterLeft outcome _ ready first run
    have frame := allocation_stringFrame Reference.natOps Reference.natOps.copyLiteral
      Reference.natOps_laws.copy Reference.natOps_laws.copy_boxes (error := args.error) ready.2
        first
    exact allocation_stringFrame Reference.natOps Reference.natOps.formatLiteral
      Reference.natOps_laws.format Reference.natOps_laws.format_boxes
      (StringFrame.returned_live Reference.natOps ready.2 frame) run
  dropLeft := by
    intro before payload outcome _ _ _ run
    change outcome = .returned () before at run
    cases run
    exact HeldFrame.refl _ _ _ _
  dropRight := by
    intro before payload outcome _ _ _ run
    change outcome = .returned () before at run
    cases run
    exact HeldFrame.refl _ _ _ _

/-- Type index for the common owned with_values execution witness. -/
def withValues_sample : withValuesFamily.Index where
  base := ⟨Reference.State, Reference.StringId, Reference.BoxId, Nat,
    Reference.natOps⟩
  Left := String
  Right := String
  Unwind := Nat
  callbacks := sampleValuesCallbacks

/-- The sample starts with a live Box and two further String allocations. -/
def sampleValuesState : Reference.State := { sampleBoxState with remaining := 2 }

/-- Distinct borrowed texts demonstrate order and distinct allocated contents. -/
def sampleValuesArgs : ValuesArgs Reference.BoxId String String := ⟨sampleError, "12", "34"⟩

/-- Actual state after the first returned owned String. -/
def sampleValuesLeft : Reference.StringId × Reference.State :=
  Reference.stringResult false sampleValuesState "12"

/-- Actual state after the second returned owned String. -/
def sampleValuesRight : Reference.StringId × Reference.State :=
  Reference.stringResult true sampleValuesLeft.2 "34"

/-- The comparison store retains Box zero and both new String identities. -/
def sampleValuesAfter : Reference.State :=
  ⟨sampleValuesRight.2.strings,
    sampleValuesRight.2.boxes.set 0
      (some ((Payload.anchor sampleAnchor).withValues sampleValuesLeft.1 sampleValuesRight.1)),
    sampleValuesRight.2.remaining, sampleValuesRight.2.events ++ [.write ⟨0⟩]⟩

/-- A closed with_values execution calls both concrete allocations, moves their
resources into the same Box and completes both primitive operand drops. -/
theorem sampleValues_run :
    withValues Reference.natOps sampleValuesCallbacks sampleValuesState sampleValuesArgs
      (.returned sampleError sampleValuesAfter) := by
  refine ⟨.anchor sampleAnchor, rfl, ?_⟩
  apply protectReturnPlace_of_protect
  apply (protect_returned_iff _ _ _ _ _ _ _).mpr
  apply (scope_returned_iff _ _ _ _ _ _ _).mpr
  refine ⟨sampleValuesAfter, ?_, .cons _ _ _ _ _ rfl (.cons _ _ _ _ _ rfl (.nil _))⟩
  refine ⟨.returned sampleValuesLeft.1 sampleValuesLeft.2, ?_,
    .returned sampleValuesRight.1 sampleValuesRight.2, ?_, ?_⟩
  · exact ⟨.returned sampleValuesLeft.1 sampleValuesLeft.2,
      ⟨.returned sampleValuesLeft.1 sampleValuesLeft.2, rfl, rfl⟩, rfl⟩
  · apply (protect_returned_iff _ _ _ _ _ _ _).mpr
    exact ⟨.returned sampleValuesRight.1 sampleValuesRight.2,
      ⟨.returned sampleValuesRight.1 sampleValuesRight.2, rfl, rfl⟩, rfl⟩
  · refine ⟨.returned sampleError sampleValuesAfter, ?_, rfl⟩
    exact ⟨.anchor sampleAnchor, rfl, .returned () sampleValuesRight.2, rfl,
      .anchor sampleAnchor, rfl, sampleValuesAfter, rfl, rfl⟩

/-- The sample receiver and its two owned fields are initialized. -/
theorem sampleValues_ready : Ready Reference.natOps sampleValuesState sampleError :=
  ⟨.anchor sampleAnchor, rfl, sampleAnchor_ready⟩

/-- Every actual operand-scope exit of an admitted family call has the
resources required by its next nonterminal local step. This result consumes the
reached unwind and destructor premises, independently of a completed call. -/
theorem withValues_family_scope_resources (types : ValuesTypes)
    {before : types.base.State}
    {args : ValuesArgs types.base.BoxResource types.Left types.Right}
    (admitted : (withValuesFamily.contract types).requires before args)
    {outcome : Outcome types.base.State (Error types.base.BoxResource) types.Unwind
      types.base.Terminal}
    (run : Owned.scope types.callbacks.double
      [fun state result => types.callbacks.dropLeft state args.left result,
       fun state result => types.callbacks.dropRight state args.right result]
      (valuesBody types.base.ops types.callbacks args) before () outcome) :
    ValuesResources types.base.ops args.error outcome :=
  admitted.2.2.scope_resources admitted.1 admitted.2.1 run

/-- Returning conversions in an admitted family have an actual local
assignment continuation after every supplied finite old-field cleanup. This
prevents vacuous success when the local write provider has no result. -/
theorem withValues_family_assignment_continues (types : ValuesTypes)
    {before : types.base.State}
    {args : ValuesArgs types.base.BoxResource types.Left types.Right}
    (admitted : (withValuesFamily.contract types).requires before args)
    {left right : types.base.StringResource} {afterLeft afterRight : types.base.State}
    (first : types.callbacks.left before args.left (.returned left afterLeft))
    (second : types.callbacks.right afterLeft args.right (.returned right afterRight)) :
    ∃ payload, types.base.ops.currentBox afterRight args.error.resource = some payload ∧
      payload.Ready types.base.ops afterRight ∧
      ∀ fieldsExit, dropStrings types.base.ops (comparedStrings payload.compared) afterRight ()
        fieldsExit →
        match fieldsExit with
        | .returned () afterFields => ∃ after,
            types.base.ops.writeBox afterFields args.error.resource (payload.withValues left right)
              = some after ∧
            valuesBody types.base.ops types.callbacks args before () (.returned args.error after)
        | .unwound impossible _ => nomatch impossible
        | .terminated reason => valuesBody types.base.ops types.callbacks args before ()
          (.terminated reason) := by
  obtain ⟨payload, present, ready, continuation⟩ :=
    admitted.2.2.assignment_continues admitted.1 admitted.2.1 first second
  refine ⟨payload, present, ready, ?_⟩
  intro fieldsExit fieldsRun
  cases fieldsExit with
  | unwound impossible _ => nomatch impossible
  | returned completed _ => cases completed; exact continuation _ fieldsRun
  | terminated _ => exact continuation _ fieldsRun

/-- The actual operand-scope unwind of an admitted family has a current error to
clean. Every supplied field-drop and Box-free exit gives its exact full-call
continuation; terminal dependencies stop with their actual reasons. -/
theorem withValues_family_unwind_continues (types : ValuesTypes)
    {before afterScope : types.base.State}
    {args : ValuesArgs types.base.BoxResource types.Left types.Right} {reason : types.Unwind}
    (admitted : (withValuesFamily.contract types).requires before args)
    (scope : Owned.scope types.callbacks.double
      [fun state result => types.callbacks.dropLeft state args.left result,
       fun state result => types.callbacks.dropRight state args.right result]
      (valuesBody types.base.ops types.callbacks args) before () (.unwound reason afterScope)) :
    ∃ payload, types.base.ops.currentBox afterScope args.error.resource = some payload ∧
      payload.Ready types.base.ops afterScope ∧
      ∀ fieldsExit, dropStrings types.base.ops payload.strings afterScope () fieldsExit →
        match fieldsExit with
        | .returned () afterFields =>
            types.base.ops.currentBox afterFields args.error.resource = some payload ∧
            ∀ freeExit, types.base.ops.freeBox afterFields args.error.resource freeExit →
              match freeExit with
              | .returned () after => withValues types.base.ops types.callbacks before args
                (.unwound reason after)
              | .unwound impossible _ => nomatch impossible
              | .terminated terminal => withValues types.base.ops types.callbacks before args
                (.terminated terminal)
        | .unwound impossible _ => nomatch impossible
        | .terminated terminal => withValues types.base.ops types.callbacks before args
          (.terminated terminal) := by
  obtain ⟨payload, present, ready, continuation⟩ :=
    admitted.2.2.unwind_continues admitted.1 admitted.2.1 scope
  refine ⟨payload, present, ready, ?_⟩
  intro fieldsExit fieldsRun
  cases fieldsExit with
  | unwound impossible _ => nomatch impossible
  | terminated _ => exact continuation _ fieldsRun
  | returned completed afterFields =>
    cases completed
    obtain ⟨current, afterFieldsRun⟩ := continuation _ fieldsRun
    refine ⟨current, ?_⟩
    intro freeExit freed
    cases freeExit with
    | unwound impossible _ => nomatch impossible
    | returned completed _ => cases completed; exact afterFieldsRun _ freed
    | terminated _ => exact afterFieldsRun _ freed

/-- Actual permitted finite execution of the exact owned callback family. -/
theorem withValues_hasExecution :
    FamilyHasExecution withValuesFamily withValuesRun withValues_sample :=
  ⟨sampleValuesState, sampleValuesArgs, _,
    ⟨⟨Reference.natOps_laws.stringDrop.other, Reference.natOps_laws.drop_boxes,
      Reference.natOps_laws.store.current, Reference.natOps_laws.store_strings⟩,
      sampleValues_ready, ValuesCallbacks.CallReady.of_admissible sampleValues_ready
        (sampleValuesCallbacks_admissible sampleValuesArgs sampleValuesState)
        Reference.natOps_laws.drop_boxes Reference.natOps_laws.store.available⟩,
    sampleValues_run⟩

/-- The exact registered sample of the generic owned callback family is inhabited. -/
theorem withValues_satisfiable : FamilySatisfiable withValuesFamily withValues_sample :=
  withValues_hasExecution.satisfiable

end Solanalib.Specs.Core.AnchorErrorOwned
