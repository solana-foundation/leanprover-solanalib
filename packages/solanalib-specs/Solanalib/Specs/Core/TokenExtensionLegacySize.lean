/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionLegacy
public import Solanalib.Specs.Core.OwnedCleanup
public import Solanalib.Specs.Core.OwnedVector

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.Legacy

open Owned

/-- Shared dependency interpretation for an old-version extension-type slice
and a local owned Vec. Source enum values exclude unsupported later variants. -/
structure TypeArray where
  State : Type
  Reference : Type
  Resource : Type
  Unwind : Type
  Terminal : Type
  /-- Fixed source slice metadata. -/
  length : Reference → Nat
  /-- Source enum reads use the current state of the same shared slice. -/
  kindAt : (state : State) → (input : Reference) → Fin (length input) → Kind
  /-- Allocation, ordered push and destruction dependencies. -/
  vectors : VectorOps State ExtensionType Resource Unwind Terminal
  /-- Source double-unwind policy for cleanup. -/
  doubleUnwind : DoubleUnwind State Unwind Terminal

/-- Run the exact list of individual source pushes. This helper does not own
cleanup: the enclosing array walk retains the vector while the helper runs. -/
def pushAll {State Resource Unwind Terminal : Type}
    (ops : VectorOps State ExtensionType Resource Unwind Terminal) (resource : Resource) :
    List ExtensionType → State → Outcome State Unit Unwind Terminal → Prop
  | [], before, final => final = .returned () before
  | value :: rest, before, final =>
    ∃ pushed, ops.push before (resource, value) pushed ∧
      match pushed with
      | .returned () after => pushAll ops resource rest after final
      | .unwound reason after => final = .unwound reason after
      | .terminated reason => final = .terminated reason

/-- The local vector is built either by source-order deduplication or by the
required-initialization mapping. In both cases all allocation precedes any
fixed-length validation performed by the caller. -/
inductive BuildKind where
  | deduplicate
  | required
  deriving DecidableEq, Repr

/-- Deduplication uses the actual current vector contents. Initialization
requirements preserve source duplicates and the two-push nontransferable case. -/
def pendingPushes (mode : BuildKind) (kind : ExtensionType) (current : List ExtensionType) :
    List ExtensionType :=
  match mode with
  | .deduplicate => if kind ∈ current then [] else [kind]
  | .required => kind.requiredAccountExtensions

/-- Walk the actual source slice one element at a time. The next source
element is observed after all pushes for the preceding element returned. -/
def buildVector (mode : BuildKind) (types : TypeArray) (input : types.Reference)
    (resource : types.Resource) (index : Nat) (before : types.State)
    (final : Outcome types.State types.Resource types.Unwind types.Terminal) : Prop :=
  if bound : index < types.length input then
    let kind := (types.kindAt before input ⟨index, bound⟩).val
    let runPushes := fun additions =>
      ∃ pushed, pushAll types.vectors resource additions before pushed ∧
        match pushed with
        | .returned () after => buildVector mode types input resource (index + 1) after final
        | .unwound reason after => cleanup types.doubleUnwind [types.vectors.dropAction resource]
            (.unwound reason after) final
        | .terminated reason => final = .terminated reason
    match mode with
    | .deduplicate => ∃ values, types.vectors.current before resource = some values ∧
        runPushes (pendingPushes .deduplicate kind values)
    | .required => runPushes kind.requiredAccountExtensions
  else final = .returned resource before
termination_by types.length input - index

/-- Deduplication reads the current vector, then performs its optional push
before inspecting the next source element. -/
theorem buildVector_step (types : TypeArray) (input : types.Reference)
    (resource : types.Resource) (index : Nat) (before after : types.State)
    (final : Outcome types.State types.Resource types.Unwind types.Terminal)
    (bound : index < types.length input) (values : List ExtensionType)
    (current : types.vectors.current before resource = some values)
    (pushed : pushAll types.vectors resource
      (pendingPushes .deduplicate (types.kindAt before input ⟨index, bound⟩).val values)
      before (.returned () after))
    (continued : buildVector .deduplicate types input resource (index + 1) after final) :
    buildVector .deduplicate types input resource index before final := by
  rw [buildVector, dite_eq_left bound]
  exact ⟨values, current, .returned () after, pushed, continued⟩

/-- A terminal push stops deduplication before any later source kind or
account-size validation is inspected. -/
theorem buildVector_push_terminal (types : TypeArray) (input : types.Reference)
    (resource : types.Resource) (index : Nat) (before : types.State)
    (terminal : types.Terminal) (bound : index < types.length input)
    (values : List ExtensionType)
    (current : types.vectors.current before resource = some values)
    (pushed : pushAll types.vectors resource
      (pendingPushes .deduplicate (types.kindAt before input ⟨index, bound⟩).val values)
      before (.terminated terminal)) :
    buildVector .deduplicate types input resource index before (.terminated terminal) := by
  rw [buildVector, dite_eq_left bound]
  exact ⟨values, current, .terminated terminal, pushed, rfl⟩

/-- Required-init construction never inspects its accumulated elements. Only
its actual ordered push dependencies precede the next input read. -/
theorem buildVector_required_step (types : TypeArray) (input : types.Reference)
    (resource : types.Resource) (index : Nat) (before after : types.State)
    (final : Outcome types.State types.Resource types.Unwind types.Terminal)
    (bound : index < types.length input)
    (pushed : pushAll types.vectors resource
      (types.kindAt before input ⟨index, bound⟩).val.requiredAccountExtensions
      before (.returned () after))
    (continued : buildVector .required types input resource (index + 1) after final) :
    buildVector .required types input resource index before final := by
  rw [buildVector, dite_eq_left bound]
  exact ⟨.returned () after, pushed, continued⟩

/-- Finishing the source slice moves its still-live result vector. -/
theorem buildVector_done (mode : BuildKind) (types : TypeArray) (input : types.Reference)
    (resource : types.Resource) (index : Nat) (before : types.State)
    (ended : types.length input ≤ index) :
    buildVector mode types input resource index before (.returned resource before) := by
  rw [buildVector, dite_eq_right (Nat.not_lt_of_ge ended)]

/-- Required initialization extensions return the owned Vec produced by the
walk. Neither sorting nor deduplication is added. -/
def requiredInit (types : TypeArray) (before : types.State) (input : types.Reference)
    (final : Outcome types.State types.Resource types.Unwind types.Terminal) : Prop :=
  let created := types.vectors.empty before
  buildVector .required types input created.1 0 created.2 final

/-- Fixed extension widths include their two-byte tag and two-byte length.
The first variable-width type produces InvalidArgument. The dedup phase has
already finished before this function is called. -/
def sumLengths : List ExtensionType → Except Error Nat
  | [] => .ok 0
  | kind :: rest => do
    let head ← kind.tlvLength
    let tail ← sumLengths rest
    pure (head + tail)

/-- Final account sizing performs the saturating base addition of the source and
the two-byte avoidance of the multisig length. -/
def accountSize (tlvLength : Nat) : Nat :=
  adjustMultisigLength (saturatingSizeAdd tlvLength (accountLength + 1))

/-- The fixed base type contributes only S::SIZE_OF to the empty-input branch. -/
structure Sizer where
  types : TypeArray
  /-- Exact source S::SIZE_OF; no parser is called by this API. -/
  baseLength : Nat

/-- Complete old account-length control flow. A nonempty input is fully
deduplicated before inspecting any variable-size type; its local Vec is then
dropped on both a returned length and an ordinary error. -/
def calculateAccountLength (sizer : Sizer) (before : sizer.types.State)
    (input : sizer.types.Reference)
    (final : Outcome sizer.types.State (Except Error Nat) sizer.types.Unwind sizer.types.Terminal) :
    Prop :=
  if sizer.types.length input = 0 then final = .returned (.ok sizer.baseLength) before
  else
    let created := sizer.types.vectors.empty before
    ∃ built, buildVector .deduplicate sizer.types input created.1 0 created.2 built ∧
      match built with
      | .returned resource after =>
        ∃ values, sizer.types.vectors.current after resource = some values ∧
          ∃ cleaned, cleanup sizer.types.doubleUnwind [sizer.types.vectors.dropAction resource]
            (.returned (sumLengths values) after) cleaned ∧
            final = Outcome.map (Except.map accountSize) cleaned
      | .unwound reason after => final = .unwound reason after
      | .terminated reason => final = .terminated reason

/-- Allocation-independent normal observation. Source-size overflow is
unreachable for the finite old enum after deduplication; the only width error
is the variable TokenMetadata variant. -/
def accountLengthValue (baseLength : Nat) (values : List Kind) : Except Error Nat :=
  if values.isEmpty then .ok baseLength
  else (sumLengths ((values.map Subtype.val).eraseDups)).map accountSize

/-- The copied required-types observation preserves source multiplicity. -/
def requiredInitValue (values : List Kind) : List ExtensionType :=
  (values.map Subtype.val).flatMap ExtensionType.requiredAccountExtensions

/-- A closed concrete slice/ledger interpretation with real ordered pushes
and live vector retirement. No actual allocator success is inferred. -/
def typeArrayReference : TypeArray where
  State := VectorState ExtensionType
  Reference := List Kind
  Resource := Nat
  Unwind := Empty
  Terminal := Empty
  length := List.length
  kindAt := fun _ values index => values[index.val]
  vectors := vectorReference
  doubleUnwind := fun _ _ _ _ => False

/-- Nontransferability contributes two requirements each time it occurs. -/
def requiredSample : List Kind :=
  [⟨.nonTransferable, by decide⟩, ⟨.transferFeeConfig, by decide⟩,
    ⟨.nonTransferable, by decide⟩]

/-- The explicit normal value control catches accidental deduplication and
the ordering of the nontransferable account and immutable-owner markers. -/
theorem requiredSample_value : requiredInitValue requiredSample =
    [.nonTransferableAccount, .immutableOwner, .transferFeeAmount,
      .nonTransferableAccount, .immutableOwner] := rfl

/-- The multisig-size adjustment is visible at the exact boundary. -/
theorem accountSize_multisig : accountSize 189 = 357 := rfl

end Solanalib.Specs.Core.Token.Legacy
