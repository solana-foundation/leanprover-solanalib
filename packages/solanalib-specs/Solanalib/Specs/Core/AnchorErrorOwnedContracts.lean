/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOwnedReferenceLaws
public import Solanalib.Specs.Core.AnchorErrorOwnedAssignment
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOwned

/-- Source type interpretations and explicit String/Box providers. Required
primitive facts belong to the precondition of each family, not this shared index. -/
structure Types where
  /-- Full ambient model state, including captured effects if present. -/
  State : Type
  /-- Stable identities of owned String resources. -/
  StringResource : Type
  /-- Stable identities of Box allocations. -/
  BoxResource : Type
  /-- Explicit terminal dependency exits. -/
  Terminal : Type
  /-- Individually sequenced fixed-source dependencies. -/
  ops : Ops State StringResource BoxResource Terminal

/-- A normal From<AnchorError> exit is exactly one Box allocation; the owned
String fields are moved into that payload without another String allocation. -/
theorem fromAnchor_returned_iff {State StringResource BoxResource Terminal : Type}
    (ops : Ops State StringResource BoxResource Terminal)
    (before after : State) (payload : AnchorPayload StringResource) (error : Error BoxResource) :
    fromAnchor ops before payload (.returned error after) ↔
      ops.newBox before (.anchor payload) (.returned error.resource after) := by
  cases error with
  | mk resource =>
    constructor
    · rintro ⟨intermediate, allocated, returned⟩
      cases intermediate with
      | returned actual final => cases returned; exact allocated
      | unwound impossible _ => nomatch impossible
      | terminated _ => cases returned
    · intro allocated
      exact ⟨.returned resource after, allocated, rfl⟩

/-- Boxing an admitted payload preserves its initialized, distinct owned
Strings. The input readiness and primitive cross-store frame are both needed;
the allocation law for the new Box alone does not establish this property. -/
theorem fromAnchor_ready {State StringResource BoxResource Terminal : Type}
    {ops : Ops State StringResource BoxResource Terminal}
    (box_current : ∀ before payload resource after,
      ops.newBox before payload (.returned resource after) →
        ops.currentBox after resource = some payload)
    (box_strings : ∀ before payload resource after,
      ops.newBox before payload (.returned resource after) →
        ∀ string, ops.currentString after string = ops.currentString before string)
    {before after : State} {payload : AnchorPayload StringResource}
    {error : Error BoxResource}
    (ready : (Payload.anchor payload).Ready ops before)
    (run : fromAnchor ops before payload (.returned error after)) :
    Ready ops after error := by
  have allocated := (fromAnchor_returned_iff _ _ _ _ _).mp run
  refine ⟨.anchor payload, box_current _ _ _ _ allocated, ready.1, ?_⟩
  intro resource member
  obtain ⟨contents, current⟩ := ready.2 resource member
  exact ⟨contents, (box_strings _ _ _ _ allocated resource).trans current⟩

/-- Generic owned From<AnchorError> contract. Its normal postcondition records
the freshness of the new Box and the exact moved resource-bearing payload. -/
def fromAnchorFamily : Family where
  Index := Types
  State := Types.State
  Args := fun types => AnchorPayload types.StringResource
  Value := fun types => Error types.BoxResource
  Unwind := fun _ => Empty
  Terminal := Types.Terminal
  contract := fun types => {
    requires := fun before payload => types.ops.BoxingLaws ∧
      (Payload.anchor payload).Ready types.ops before
    post := fun before payload outcome => fromAnchor types.ops before payload outcome ∧
      match outcome with
      | .returned error after =>
          types.ops.currentBox before error.resource = none ∧
          types.ops.currentBox after error.resource = some (.anchor payload) ∧
          Ready types.ops after error
      | .unwound impossible _ => nomatch impossible
      | .terminated _ => True }

/-- Operational reference relation retaining the actual primitive Box call. -/
def fromAnchorRun : FamilyRun fromAnchorFamily := fun types => fromAnchor types.ops

/-- The primitive fresh-storage law proves the normal postcondition of every reference
instantiation; terminal outcomes remain explicit. -/
theorem fromAnchor_reference : FamilyReference fromAnchorFamily fromAnchorRun := by
  intro types before payload outcome admitted run
  refine ⟨run, ?_⟩
  cases outcome with
  | unwound impossible _ => nomatch impossible
  | terminated _ => trivial
  | returned error after =>
    have allocated := (fromAnchor_returned_iff _ _ _ _ _).mp run
    exact ⟨admitted.1.fresh _ _ _ _ allocated, admitted.1.current _ _ _ _ allocated,
      fromAnchor_ready admitted.1.current admitted.1.strings admitted.2 run⟩

/-- Generic comparison replacement consumes the receiver and returns its same
Box identity after source-ordered destruction and an in-place payload store. -/
def withPubkeysFamily : Family where
  Index := Types
  State := Types.State
  Args := fun types => Error types.BoxResource × Solanalib.Runtime.Pubkey × Solanalib.Runtime.Pubkey
  Value := fun types => Error types.BoxResource
  Unwind := fun _ => Empty
  Terminal := Types.Terminal
  contract := fun types => {
    requires := fun before args => types.ops.ComparisonLaws ∧ Ready types.ops before args.1 ∧
      ComparisonStoreReady types.ops before args.1
        (fun payload => payload.withPubkeys args.2.1 args.2.2)
    post := fun before args outcome => withPubkeys types.ops before args outcome ∧
      match outcome with
      | .returned error after => error = args.1 ∧
          (∀ payload, types.ops.currentBox before args.1.resource = some payload →
            types.ops.currentBox after args.1.resource = some (payload.withPubkeys args.2.1
              args.2.2)) ∧
          Ready types.ops after error
      | .unwound impossible _ => nomatch impossible
      | .terminated _ => True }

/-- Primitive comparison cleanup and store reference, without a whole-error
dependency standing in for the SDK operation. -/
def withPubkeysRun : FamilyRun withPubkeysFamily := fun types => withPubkeys types.ops

/-- Every normal reference replacement preserves identity and the resource
descriptors outside the comparison field. -/
theorem withPubkeys_reference : FamilyReference withPubkeysFamily withPubkeysRun := by
  intro types before args outcome admitted run
  refine ⟨run, ?_⟩
  cases outcome with
  | unwound impossible _ => nomatch impossible
  | terminated _ => trivial
  | returned error after =>
    refine ⟨withPubkeys_identity types.ops run, ?_, withPubkeys_ready admitted.1 admitted.2.1 run⟩
    intro payload present
    exact (withPubkeys_payload admitted.1.drop_boxes admitted.1.store_current present run).2

/-- Every actual old-comparison cleanup exit of an admitted call continues:
normal cleanup reaches an available same-Box assignment, while a terminal
cleanup remains terminal. This does not assume destructor termination. -/
theorem withPubkeys_family_cleanup_continues (types : Types)
    {before : types.State} {args : Error types.BoxResource × Solanalib.Runtime.Pubkey ×
      Solanalib.Runtime.Pubkey}
    (admitted : (withPubkeysFamily.contract types).requires before args)
    {payload : Payload types.StringResource}
    (present : types.ops.currentBox before args.1.resource = some payload)
    {outcome : Outcome types.State Unit Empty types.Terminal}
    (dropped : dropStrings types.ops (comparedStrings payload.compared) before () outcome) :
    match outcome with
    | .returned () afterDrops => ∃ after,
        types.ops.writeBox afterDrops args.1.resource
          (payload.withPubkeys args.2.1 args.2.2) = some after ∧
        withPubkeysRun types before args (.returned args.1 after)
    | .unwound impossible _ => nomatch impossible
    | .terminated reason => withPubkeysRun types before args (.terminated reason) := by
  rcases args with ⟨error, left, right⟩
  cases outcome with
  | unwound impossible _ => nomatch impossible
  | returned completed _ =>
    cases completed
    exact withPubkeys_cleanup_continues types.ops admitted.1.drop_boxes admitted.2.2 present dropped
  | terminated _ =>
    exact withPubkeys_cleanup_continues types.ops admitted.1.drop_boxes admitted.2.2 present dropped

/-- Concrete finite-heap instantiation shared by the closed common witnesses. -/
def sampleTypes : Types :=
  ⟨Reference.State, Reference.StringId, Reference.BoxId, Reference.Failure,
    Reference.ops⟩

/-- Existing distinct owned fields for the From<AnchorError> witness. -/
def sampleAnchor : AnchorPayload Reference.StringId :=
  ⟨⟨0⟩, 3007, ⟨1⟩, none, none⟩

/-- Input heap has both initialized Strings and one remaining Box allocation. -/
def sampleAnchorState : Reference.State :=
  ⟨[some "AccountOwnedByWrongProgram", some "The given account is owned by a different \
    program"],
    [], 1, []⟩

/-- The field resources of the witness are initialized and pairwise distinct. -/
theorem sampleAnchor_ready :
    (Payload.anchor sampleAnchor).Ready Reference.ops sampleAnchorState := by
  constructor
  · decide
  · intro resource member
    have either : resource = (⟨0⟩ : Reference.StringId) ∨ resource = ⟨1⟩ := by
      simpa [Payload.strings, sampleAnchor, originStrings, comparedStrings] using member
    rcases either with rfl | rfl
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- The concrete Box constructor really returns; this does not assume that
arbitrary primitive providers or arbitrary allocation budgets return. -/
theorem sampleAnchor_run : fromAnchor Reference.ops sampleAnchorState sampleAnchor
    (.returned ⟨(Reference.boxResult sampleAnchorState (.anchor sampleAnchor)).1⟩
      (Reference.boxResult sampleAnchorState (.anchor sampleAnchor)).2) := by
  apply (fromAnchor_returned_iff _ _ _ _ _).mpr
  rfl

/-- Closed From<AnchorError> sample index. -/
def fromAnchor_sample : fromAnchorFamily.Index := sampleTypes

/-- Actual permitted execution of the exact From<AnchorError> family sample. -/
theorem fromAnchor_hasExecution :
    FamilyHasExecution fromAnchorFamily fromAnchorRun fromAnchor_sample :=
  ⟨sampleAnchorState, sampleAnchor, _,
    ⟨⟨Reference.ops_laws.box.current, Reference.ops_laws.box.fresh, Reference.ops_laws.box_strings⟩,
      sampleAnchor_ready⟩, sampleAnchor_run⟩

/-- The exact From<AnchorError> sample precondition is inhabited. -/
theorem fromAnchor_satisfiable : FamilySatisfiable fromAnchorFamily fromAnchor_sample :=
  fromAnchor_hasExecution.satisfiable

/-- The same live Box supplies the comparison replacement witness. -/
def sampleBoxState : Reference.State :=
  (Reference.boxResult sampleAnchorState (.anchor sampleAnchor)).2

/-- Receiver identity used before and after the comparison store. -/
def sampleError : Error Reference.BoxId := ⟨⟨0⟩⟩

/-- Sample key; all key bytes remain data, without allocation dependencies. -/
def sampleKey : Solanalib.Runtime.Pubkey := Solanalib.Runtime.Pubkey.ofNat 7

/-- The boxed sample has a live Box and the same initialized String fields. -/
theorem sampleBox_ready : Ready Reference.ops sampleBoxState sampleError :=
  ⟨.anchor sampleAnchor, rfl, sampleAnchor_ready⟩

/-- Concrete comparison replacement performs its real in-place Box store. -/
theorem samplePubkeys_run :
    withPubkeys Reference.ops sampleBoxState (sampleError, sampleKey, sampleKey)
      (.returned sampleError
        ⟨sampleBoxState.strings,
          sampleBoxState.boxes.set 0 (some ((Payload.anchor sampleAnchor).withPubkeys sampleKey
            sampleKey)),
          sampleBoxState.remaining, sampleBoxState.events ++ [.write ⟨0⟩]⟩) := by
  refine ⟨.anchor sampleAnchor, rfl, .returned () sampleBoxState, rfl, ?_⟩
  exact ⟨.anchor sampleAnchor, rfl, _, rfl, rfl⟩

/-- Closed comparison-replacement sample index. -/
def withPubkeys_sample : withPubkeysFamily.Index := sampleTypes

/-- Actual reference execution at the exact comparison family sample. -/
theorem withPubkeys_hasExecution :
    FamilyHasExecution withPubkeysFamily withPubkeysRun withPubkeys_sample :=
  ⟨sampleBoxState, (sampleError, sampleKey, sampleKey), _,
    ⟨⟨Reference.ops_laws.stringDrop.other, Reference.ops_laws.drop_boxes,
      Reference.ops_laws.store.current, Reference.ops_laws.store_strings⟩, sampleBox_ready,
      ComparisonStoreReady.of_available Reference.ops Reference.ops_laws.drop_boxes
        Reference.ops_laws.store.available _ _ _⟩,
    samplePubkeys_run⟩

/-- The selected precondition of the comparison family is satisfiable. -/
theorem withPubkeys_satisfiable : FamilySatisfiable withPubkeysFamily withPubkeys_sample :=
  withPubkeys_hasExecution.satisfiable

end Solanalib.Specs.Core.AnchorErrorOwned
