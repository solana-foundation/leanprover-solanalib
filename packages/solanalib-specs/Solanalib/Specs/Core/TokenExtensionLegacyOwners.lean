/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionLegacyBounds
public import Solanalib.Specs.Core.TokenExtensionLegacyList

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Legacy

open Owned

/-- A normal exit after a single source destructor came from that same pending
return and a normal destructor exit. Cleanup cannot turn an error or unwind
into a successful value. -/
theorem cleanup_single_returned {State Value Unwind Terminal : Type}
    (double : DoubleUnwind State Unwind Terminal)
    (drop : DropAction State Unwind Terminal)
    (pending : Outcome State Value Unwind Terminal) (value : Value) (after : State)
    (called : cleanup double [drop] pending (.returned value after)) :
    ∃ before, pending = .returned value before ∧ drop before (.returned () after) := by
  cases pending with
  | returned initial before =>
    obtain ⟨dropped, method, continued⟩ := called
    cases dropped with
    | returned returnedUnit middle =>
      cases returnedUnit
      cases continued
      exact ⟨before, rfl, method⟩
    | unwound reason middle => cases continued
    | terminated reason => cases continued
  | unwound original before =>
    obtain ⟨dropped, method, continued⟩ := called
    cases dropped with
    | returned returnedUnit middle => cases continued
    | unwound reason middle =>
      obtain ⟨terminal, _, impossible⟩ := continued
      cases impossible
    | terminated reason => cases continued
  | terminated reason => cases called

/-- Both source array walks retain a real current vector on every normal
return. The source required-init walk itself does not read accumulated values;
this proof uses the primitive current-content law as an ownership invariant. -/
theorem buildVector_current (mode : BuildKind) (types : TypeArray)
    (push_current : ∀ before resource kind values after,
      types.vectors.current before resource = some values →
      types.vectors.push before (resource, kind) (.returned () after) →
      types.vectors.current after resource = some (values ++ [kind]))
    (input : types.Reference) (resource result : types.Resource) (index : Nat)
    (before after : types.State) (values : List ExtensionType)
    (current : types.vectors.current before resource = some values)
    (called : buildVector mode types input resource index before (.returned result after)) :
    result = resource ∧ ∃ finalValues, types.vectors.current after result = some finalValues := by
  rw [buildVector] at called
  split at called
  · rename_i within
    cases mode with
    | deduplicate =>
      obtain ⟨observed, read, pushed, method, continued⟩ := called
      have sameValues := Option.some.inj (current.symm.trans read)
      subst observed
      cases pushed with
      | returned returnedUnit middle =>
        cases returnedUnit
        have next := pushAll_current types.vectors push_current resource
          (pendingPushes .deduplicate (types.kindAt before input ⟨index, within⟩).val values)
          values before middle current method
        exact buildVector_current .deduplicate types push_current input resource result
          (index + 1) middle after _ next continued
      | unwound reason middle =>
        obtain ⟨_, impossible, _⟩ := cleanup_single_returned types.doubleUnwind
          (types.vectors.dropAction resource) _ result after continued
        cases impossible
      | terminated reason => cases continued
    | required =>
      obtain ⟨pushed, method, continued⟩ := called
      cases pushed with
      | returned returnedUnit middle =>
        cases returnedUnit
        have next := pushAll_current types.vectors push_current resource
          (types.kindAt before input ⟨index, within⟩).val.requiredAccountExtensions
          values before middle current method
        exact buildVector_current .required types push_current input resource result
          (index + 1) middle after _ next continued
      | unwound reason middle =>
        obtain ⟨_, impossible, _⟩ := cleanup_single_returned types.doubleUnwind
          (types.vectors.dropAction resource) _ result after continued
        cases impossible
      | terminated reason => cases continued
  · cases called
    exact ⟨rfl, values, current⟩
termination_by types.length input - index

/-- Actual empty/push executions provide the returned required-init owner.
No condition on a future result is placed in the public admission predicate. -/
theorem requiredInit_current (types : TypeArray)
    (empty_current : ∀ before,
      types.vectors.current (types.vectors.empty before).2 (types.vectors.empty before).1 = some [])
    (push_current : ∀ before resource kind values after,
      types.vectors.current before resource = some values →
      types.vectors.push before (resource, kind) (.returned () after) →
      types.vectors.current after resource = some (values ++ [kind]))
    (before after : types.State) (input : types.Reference) (resource : types.Resource)
    (called : requiredInit types before input (.returned resource after)) :
    ∃ values, types.vectors.current after resource = some values := by
  exact (buildVector_current .required types push_current input
    (types.vectors.empty before).1 resource 0 (types.vectors.empty before).2 after []
    (empty_current before) called).2

/-- A normal old scan either retains its actual current output vector or
returns its one concrete malformed-TLV error. This follows through each real
push and the source cleanup path; allocator exits are not assumed away. -/
def ScanOwner {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (resource : Resource) (after : State) : Except Error (Resource × Nat) → Prop
  | .ok (returnedResource, _) => returnedResource = resource ∧
      ∃ finalValues, ops.current after returnedResource = some finalValues
  | .error error => error = .InvalidAccountData

/-- Current vector contents follow the old scanner through each reached push
and cleanup; these are consequences of primitive executions. -/
theorem collectInfo_returned {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal)
    (push_current : ∀ before resource kind values after,
      ops.current before resource = some values →
      ops.push before (resource, kind) (.returned () after) →
      ops.current after resource = some (values ++ [kind]))
    (double : DoubleUnwind State Unwind Terminal) (resource : Resource)
    (length : Nat) (byteAt : State → Fin length → UInt8) (offset : Nat)
    (before after : State) (values : List ExtensionType)
    (result : Except Error (Resource × Nat))
    (current : ops.current before resource = some values)
    (called : collectInfo ops double resource length byteAt offset before (.returned result after))
      :
    ScanOwner ops resource after result := by
  rw [collectInfo] at called
  split at called
  · cases called
    exact ⟨rfl, values, current⟩
  · obtain ⟨_, same, _⟩ := cleanup_single_returned double (ops.dropAction resource)
      _ result after called
    cases same
    rfl
  · rename_i kind found
    obtain ⟨pushed, method, continued⟩ := called
    cases pushed with
    | returned returnedUnit middle =>
      cases returnedUnit
      have next := push_current before resource kind values middle current method
      change (if payloadEnd (currentExtensionBytes length byteAt middle) offset ≤ length then
        collectInfo ops double resource length byteAt
          (payloadEnd (currentExtensionBytes length byteAt middle) offset) middle
          (.returned result after)
        else cleanup double [ops.dropAction resource]
          (.returned (.error .InvalidAccountData) middle) (.returned result after)) at continued
      split at continued
      · exact collectInfo_returned ops push_current double resource length byteAt
          (payloadEnd (currentExtensionBytes length byteAt middle) offset) middle after
          (values ++ [kind]) result next continued
      · obtain ⟨_, same, _⟩ := cleanup_single_returned double (ops.dropAction resource)
          _ result after continued
        cases same
        rfl
    | unwound reason middle =>
      obtain ⟨_, impossible, _⟩ := cleanup_single_returned double (ops.dropAction resource)
        _ result after continued
      cases impossible
    | terminated reason => cases continued
termination_by length - offset
decreasing_by
  have progress := payloadEnd_progress (currentExtensionBytes length byteAt middle) offset
  omega

/-- The provided listing method uses the same returned vector owner from its
resolved accessor and scanner; it cannot invent a missing result allocation. -/
theorem getTypes_returned (reader : CurrentExtensionTypeReader)
    (empty_current : ∀ before,
      reader.vectors.current (reader.vectors.empty before).2 (reader.vectors.empty before).1 = some
        [])
    (push_current : ∀ before resource kind values after,
      reader.vectors.current before resource = some values →
      reader.vectors.push before (resource, kind) (.returned () after) →
      reader.vectors.current after resource = some (values ++ [kind]))
    (before after : reader.State) (result : Except Error reader.Resource)
    (called : getTypes reader before (.returned result after)) :
    match result with
    | .ok resource => ∃ values, reader.vectors.current after resource = some values
    | .error error => error = .InvalidAccountData := by
  obtain ⟨accessed, _, continued⟩ := called
  cases accessed with
  | returned reference middle =>
    obtain ⟨scanned, scan, same⟩ := continued
    cases scanned with
    | returned output final =>
      have observed := collectInfo_returned reader.vectors push_current reader.doubleUnwind
        (reader.vectors.empty middle).1 (reader.length reference)
        (fun state => reader.byteAt state reference) 0 (reader.vectors.empty middle).2 final []
        output (empty_current middle) scan
      cases output with
      | ok pair =>
        cases pair
        cases same
        exact observed.2
      | error error =>
        cases same
        exact observed
    | unwound reason final => cases same
    | terminated reason => cases same
  | unwound reason middle => cases continued
  | terminated reason => cases continued

end Solanalib.Specs.Core.Token.Legacy
