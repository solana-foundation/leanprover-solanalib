/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorErrorOwnedLaws

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorErrorOwned

variable {State StringResource BoxResource Terminal : Type}

/-- The ordinary comparison-field assignment is available after every actual
normal return of its old-field cleanup. This is a condition on a reached local
store, not termination or success of an opaque destructor or conversion. -/
def ComparisonStoreReady (ops : Ops State StringResource BoxResource Terminal)
    (before : State) (error : Error BoxResource)
    (update : Payload StringResource → Payload StringResource) : Prop :=
  ∀ payload, ops.currentBox before error.resource = some payload →
    ∀ afterDrops, dropStrings ops (comparedStrings payload.compared)
      before () (.returned () afterDrops) →
      ∃ after, ops.writeBox afterDrops error.resource (update payload) = some after

/-- An independently supplied primitive live-Box store capability implies the
smaller reached-store condition. Only the actual String-drop Box frame is used. -/
theorem ComparisonStoreReady.of_available (ops : Ops State StringResource BoxResource Terminal)
    (drop_boxes : ∀ before resource after,
      ops.dropString before resource (.returned () after) →
        ∀ box, ops.currentBox after box = ops.currentBox before box)
    (available : ∀ before resource old value,
      ops.currentBox before resource = some old →
        ∃ after, ops.writeBox before resource value = some after)
    (before : State) (error : Error BoxResource)
    (update : Payload StringResource → Payload StringResource) :
    ComparisonStoreReady ops before error update := by
  intro payload present afterDrops dropped
  exact available afterDrops error.resource payload (update payload)
    ((dropStrings_boxes drop_boxes dropped error.resource).trans present)

/-- The current Box lookup and the ordinary store both have actual results
after each supplied finite normal old-comparison cleanup. -/
theorem ComparisonStoreReady.after_drops (ops : Ops State StringResource BoxResource Terminal)
    (drop_boxes : ∀ before resource after,
      ops.dropString before resource (.returned () after) →
        ∀ box, ops.currentBox after box = ops.currentBox before box)
    {before afterDrops : State} {error : Error BoxResource}
    {update : Payload StringResource → Payload StringResource}
    (stores : ComparisonStoreReady ops before error update)
    {payload : Payload StringResource}
    (present : ops.currentBox before error.resource = some payload)
    (dropped : dropStrings ops (comparedStrings payload.compared)
      before () (.returned () afterDrops)) :
    ops.currentBox afterDrops error.resource = some payload ∧
      ∃ after, ops.writeBox afterDrops error.resource (update payload) = some after :=
  ⟨(dropStrings_boxes drop_boxes dropped error.resource).trans present,
    stores payload present afterDrops dropped⟩

/-- Every supplied finite comparison-cleanup exit has its exact local
continuation: a real store after normal cleanup, or the same terminal exit.
No finite destructor outcome is assumed to exist. -/
theorem withPubkeys_cleanup_continues (ops : Ops State StringResource BoxResource Terminal)
    (drop_boxes : ∀ before resource after,
      ops.dropString before resource (.returned () after) →
        ∀ box, ops.currentBox after box = ops.currentBox before box)
    {before : State} {error : Error BoxResource} {left right : Solanalib.Runtime.Pubkey}
    (stores : ComparisonStoreReady ops before error (fun payload => payload.withPubkeys left right))
    {payload : Payload StringResource}
    (present : ops.currentBox before error.resource = some payload)
    {outcome : Outcome State Unit Empty Terminal}
    (dropped : dropStrings ops (comparedStrings payload.compared) before () outcome) :
    match outcome with
    | .returned () afterDrops => ∃ after,
        ops.writeBox afterDrops error.resource (payload.withPubkeys left right) = some after ∧
        withPubkeys ops before (error, left, right) (.returned error after)
    | .unwound impossible _ => nomatch impossible
    | .terminated reason => withPubkeys ops before (error, left, right) (.terminated reason) := by
  cases outcome with
  | unwound impossible _ => nomatch impossible
  | terminated reason =>
    exact ⟨payload, present, .terminated reason, dropped, rfl⟩
  | returned completed afterDrops =>
    cases completed
    obtain ⟨current, after, stored⟩ := stores.after_drops ops drop_boxes present dropped
    exact ⟨after, stored, payload, present, .returned () afterDrops, dropped,
      payload, current, after, stored, rfl⟩

end Solanalib.Specs.Core.AnchorErrorOwned
