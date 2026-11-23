/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionLegacySize

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Legacy

/-- Exactly the 28 old production variants, derived from their source tags. -/
def productionKinds : List ExtensionType := (List.range 28).filterMap ExtensionType.decode

/-- An old source enum value occurs in this finite list. -/
theorem mem_productionKinds (kind : Kind) : kind.val ∈ productionKinds := by
  exact List.mem_filterMap.mpr ⟨kind.val.tag, List.mem_range.mpr kind.property,
    ExtensionType.decode_tag kind.val⟩

/-- The maximum fixed Pod is the 295-byte confidential account, plus its
four-byte TLV header. Variable metadata produces an error instead of a width. -/
theorem tlvLength_bound (kind : ExtensionType) (length : Nat)
    (sized : kind.tlvLength = .ok length) : length ≤ 299 := by
  cases kind <;>
    simp only [ExtensionType.tlvLength, ExtensionType.fixedLength, Except.map,
      saturatingSizeAdd, Solanalib.Runtime.U64_MAX] at sized
  all_goals first | contradiction | cases sized; decide +kernel

/-- Every successful partial sum is bounded by its number of terms. This
also covers a prefix of the deduplicated source vector. -/
theorem sumLengths_bound (values : List ExtensionType) (total : Nat)
    (sized : sumLengths values = .ok total) : total ≤ 299 * values.length := by
  induction values generalizing total with
  | nil => cases sized; simp
  | cons kind rest ih =>
    cases head : kind.tlvLength with
    | error error => simp [sumLengths, head, bind, Except.bind] at sized
    | ok length =>
      cases tail : sumLengths rest with
      | error error => simp [sumLengths, head, tail, bind, Except.bind] at sized
      | ok remaining =>
        have hhead := tlvLength_bound kind length head
        have htail := ih remaining tail
        simp [sumLengths, head, tail, bind, pure, Except.bind, Except.pure] at sized
        simp only [List.length_cons]
        omega

/-- Source deduplication limits the accumulated vector to the finite old
enum. A binding derives these two premises from its actual empty/push/current
operations; neither is added to the admission predicate of the public function. -/
theorem distinct_length_bound (values : List ExtensionType) (distinct : values.Nodup)
    (old : ∀ kind ∈ values, kind.tag < 28) : values.length ≤ 28 := by
  have size : productionKinds.length = 28 := by decide +kernel
  rw [← size]
  apply distinct.length_le_of_subset
  intro kind member
  exact mem_productionKinds ⟨kind, old kind member⟩

/-- Consequently the ordinary usize summation and every successful prefix
fit the exact 64-bit source word, without an overflow-checks build assumption. -/
theorem sumLengths_fits (values : List ExtensionType) (total : Nat)
    (distinct : values.Nodup) (old : ∀ kind ∈ values, kind.tag < 28)
    (sized : sumLengths values = .ok total) : total < 2^64 := by
  have count := distinct_length_bound values distinct old
  have bound := sumLengths_bound values total sized
  omega

/-- The actual successful push-content law propagates through every source
push. There is no assumption about allocation termination or unwind effects. -/
theorem pushAll_current {State Resource Unwind Terminal : Type}
    (ops : Owned.VectorOps State ExtensionType Resource Unwind Terminal)
    (push_current : ∀ before resource kind values after,
      ops.current before resource = some values →
      ops.push before (resource, kind) (.returned () after) →
      ops.current after resource = some (values ++ [kind]))
    (resource : Resource) (additions values : List ExtensionType) (before after : State)
    (current : ops.current before resource = some values)
    (called : pushAll ops resource additions before (.returned () after)) :
    ops.current after resource = some (values ++ additions) := by
  induction additions generalizing before values with
  | nil => cases called; simpa using current
  | cons kind rest ih =>
    obtain ⟨pushed, method, continued⟩ := called
    cases pushed with
    | returned returnedUnit middle =>
      cases returnedUnit
      have next := push_current before resource kind values middle current method
      simpa [List.append_assoc] using ih (values ++ [kind]) middle next continued
    | unwound reason middle => cases continued
    | terminated reason => cases continued

/-- A normal deduplication result retains the same vector identity, only
old enum values, and no duplicates. These facts follow from actual source
pushes and reads; the function does not assume them as a semantic precondition. -/
theorem buildVector_distinct (types : TypeArray)
    (push_current : ∀ before resource kind values after,
      types.vectors.current before resource = some values →
      types.vectors.push before (resource, kind) (.returned () after) →
      types.vectors.current after resource = some (values ++ [kind]))
    (input : types.Reference) (resource result : types.Resource) (index : Nat)
    (before after : types.State) (values : List ExtensionType)
    (current : types.vectors.current before resource = some values)
    (distinct : values.Nodup) (old : ∀ kind ∈ values, kind.tag < 28)
    (called : buildVector .deduplicate types input resource index before (.returned result after)) :
    result = resource ∧ ∃ finalValues, types.vectors.current after result = some finalValues ∧
      finalValues.Nodup ∧ (∀ kind ∈ finalValues, kind.tag < 28) := by
  rw [buildVector] at called
  split at called
  · rename_i within
    obtain ⟨observed, read, pushed, method, continued⟩ := called
    have sameValues := Option.some.inj (current.symm.trans read)
    subst observed
    cases pushed with
    | returned returnedUnit middle =>
      cases returnedUnit
      let kind := types.kindAt before input ⟨index, within⟩
      have next := pushAll_current types.vectors push_current resource
        (pendingPushes .deduplicate kind.val values) values before middle current method
      by_cases present : kind.val ∈ values
      · simp only [pendingPushes, present, ↓reduceIte, List.append_nil] at next
        exact buildVector_distinct types push_current input resource result (index + 1)
          middle after values next distinct old continued
      · simp only [pendingPushes, present, ↓reduceIte] at next
        have nextDistinct : (values ++ [kind.val]).Nodup := by
          rw [List.nodup_append]
          refine ⟨distinct, by simp, ?_⟩
          intro value member other isKind
          simp only [List.mem_singleton] at isKind
          subst other
          intro same
          exact present (same ▸ member)
        have nextOld : ∀ value ∈ values ++ [kind.val], value.tag < 28 := by
          intro value member
          rcases List.mem_append.mp member with previous | latest
          · exact old value previous
          · have same : value = kind.val := List.mem_singleton.mp latest
            rw [same]
            exact kind.property
        exact buildVector_distinct types push_current input resource result (index + 1)
          middle after (values ++ [kind.val]) next nextDistinct nextOld continued
    | unwound reason middle =>
      obtain ⟨dropped, _, finished⟩ := continued
      cases dropped <;> simp_all [Owned.cleanup]
    | terminated reason => cases continued
  · cases called
    exact ⟨rfl, values, current, distinct, old⟩
termination_by types.length input - index

/-- Starting with the real empty-vector content law supplies the invariant
needed by the unchecked old-version usize sum of the source. -/
theorem allocated_dedup_fits (types : TypeArray)
    (empty_current : ∀ before,
      types.vectors.current (types.vectors.empty before).2 (types.vectors.empty before).1 = some [])
    (push_current : ∀ before resource kind values after,
      types.vectors.current before resource = some values →
      types.vectors.push before (resource, kind) (.returned () after) →
      types.vectors.current after resource = some (values ++ [kind]))
    (input : types.Reference) (before after : types.State) (resource : types.Resource)
    (values : List ExtensionType) (total : Nat)
    (built : buildVector .deduplicate types input (types.vectors.empty before).1 0
      (types.vectors.empty before).2 (.returned resource after))
    (current : types.vectors.current after resource = some values)
    (sized : sumLengths values = .ok total) : total < 2^64 := by
  obtain ⟨_, actual, observed, distinct, old⟩ := buildVector_distinct types push_current input
    (types.vectors.empty before).1 resource 0 (types.vectors.empty before).2 after []
    (empty_current before) (by simp) (by simp) built
  have same := Option.some.inj (current.symm.trans observed)
  subst actual
  exact sumLengths_fits values total distinct old sized

end Solanalib.Specs.Core.Token.Legacy
