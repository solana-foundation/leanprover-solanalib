/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtension
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- The actual resolved `Self::get_extension_bytes::<V>` call. Its reference
identity, state changes and every finite exit remain explicit. A source binding
must identify this relation with the resolved trait method, including overrides. -/
structure ExtensionByteProvider where
  /-- State of the source interpretation. -/
  State : Type
  /-- Identity of the returned source byte-slice reference. -/
  Reference : Type
  /-- Reasons for unwinding from the resolved method. -/
  Unwind : Type
  /-- Reasons for terminal exits from the resolved method. -/
  Terminal : Type
  /-- Bytes observed through a returned reference in the actual returned state. -/
  bytes : State → Reference → Bytes
  /-- Pointer bits of the returned byte-slice reference. -/
  address : Reference → Nat
  /-- All finite outcomes of the selected method at the exact Pod type. -/
  getBytes : ExtensionPod → State →
    Outcome State (Except Error Reference) Unwind Terminal → Prop

/-- A typed immutable reference keeps the identity of the byte reference from
which it was cast. The logical value records its typed observation. -/
structure TypedExtensionReference (Reference Value : Type) where
  /-- The same source reference, after changing only its pointee type. -/
  reference : Reference
  /-- The value observed through the checked Pod representation. -/
  value : Value
  deriving DecidableEq, Repr

/-- Source `bytemuck::try_from_bytes` checks exact size before alignment. It
reads the bytes in the state actually returned by the dependency. -/
def castExtensionReference (provider : ExtensionByteProvider)
    (representation : ExtensionRepresentation) (after : provider.State)
    (reference : provider.Reference) :
    Except Error (TypedExtensionReference provider.Reference representation.Value) :=
  if (provider.bytes after reference).length = representation.pod.byteLength then
    if provider.address reference % representation.pod.alignment = 0 then
      .ok ⟨reference, representation.observe (provider.bytes after reference)⟩
    else .error .InvalidArgument
  else .error .InvalidArgument

/-- A successful typed cast retains the exact reference and checked layout. -/
theorem castExtensionReference_ok_iff (provider : ExtensionByteProvider)
    (representation : ExtensionRepresentation) (after : provider.State)
    (reference : provider.Reference)
    (typed : TypedExtensionReference provider.Reference representation.Value) :
    castExtensionReference provider representation after reference = .ok typed ↔
      (provider.bytes after reference).length = representation.pod.byteLength ∧
      provider.address reference % representation.pod.alignment = 0 ∧
      typed = ⟨reference, representation.observe (provider.bytes after reference)⟩ := by
  unfold castExtensionReference
  split
  · split
    · simp_all [eq_comm]
    · simp_all
  · simp_all

/-- Preserve the error of the dependency, changed state, unwind or terminal exit;
only a successful slice result is followed by the source Pod cast. -/
def finishExtensionGetter (provider : ExtensionByteProvider)
    (representation : ExtensionRepresentation) :
    Outcome provider.State (Except Error provider.Reference) provider.Unwind provider.Terminal →
      Outcome provider.State
        (Except Error (TypedExtensionReference provider.Reference representation.Value))
        provider.Unwind provider.Terminal
  | .returned (.error error) after => .returned (.error error) after
  | .returned (.ok reference) after =>
      .returned (castExtensionReference provider representation after reference) after
  | .unwound reason after => .unwound reason after
  | .terminated reason => .terminated reason

/-- Generic `get_extension` composes the actual resolved method with its Pod
cast. It never replaces an override with the default TLV lookup. -/
def getExtensionOperational (provider : ExtensionByteProvider)
    (representation : ExtensionRepresentation) (before : provider.State)
    (outcome : Outcome provider.State
      (Except Error (TypedExtensionReference provider.Reference representation.Value))
      provider.Unwind provider.Terminal) : Prop :=
  ∃ called, provider.getBytes representation.pod before called ∧
    outcome = finishExtensionGetter provider representation called

/-- A successful method return is followed by the cast in its actual state. -/
theorem getExtensionOperational_returned (provider : ExtensionByteProvider)
    (representation : ExtensionRepresentation) (before after : provider.State)
    (reference : provider.Reference)
    (called : provider.getBytes representation.pod before (.returned (.ok reference) after)) :
    getExtensionOperational provider representation before
      (.returned (castExtensionReference provider representation after reference) after) :=
  ⟨.returned (.ok reference) after, called, rfl⟩

/-- Every successful operational result comes from the returned
reference of the actual method in the same final state; no new reference identity can be fabricated.
-/
theorem getExtensionOperational_success (provider : ExtensionByteProvider)
    (representation : ExtensionRepresentation) (before after : provider.State)
    (typed : TypedExtensionReference provider.Reference representation.Value)
    (run : getExtensionOperational provider representation before (.returned (.ok typed) after)) :
    ∃ reference,
      provider.getBytes representation.pod before (.returned (.ok reference) after) ∧
      castExtensionReference provider representation after reference = .ok typed := by
  obtain ⟨called, method, finished⟩ := run
  cases called with
  | returned value state =>
    cases value with
    | error error => cases finished
    | ok reference =>
      simp only [finishExtensionGetter, Outcome.returned.injEq] at finished
      obtain ⟨valueEq, stateEq⟩ := finished
      subst state
      exact ⟨reference, method, valueEq.symm⟩
  | unwound reason state => cases finished
  | terminated reason => cases finished

/-- Every actual dependency error is propagated with its actual state. -/
theorem getExtensionOperational_error (provider : ExtensionByteProvider)
    (representation : ExtensionRepresentation) (before after : provider.State)
    (error : Error)
    (called : provider.getBytes representation.pod before (.returned (.error error) after)) :
    getExtensionOperational provider representation before (.returned (.error error) after) :=
  ⟨.returned (.error error) after, called, rfl⟩

/-- Every actual dependency unwind is propagated with its actual state. -/
theorem getExtensionOperational_unwound (provider : ExtensionByteProvider)
    (representation : ExtensionRepresentation) (before after : provider.State)
    (reason : provider.Unwind)
    (called : provider.getBytes representation.pod before (.unwound reason after)) :
    getExtensionOperational provider representation before (.unwound reason after) :=
  ⟨.unwound reason after, called, rfl⟩

/-- A terminal method exit cannot acquire an invented post-state. -/
theorem getExtensionOperational_terminated (provider : ExtensionByteProvider)
    (representation : ExtensionRepresentation) (before : provider.State)
    (reason : provider.Terminal)
    (called : provider.getBytes representation.pod before (.terminated reason)) :
    getExtensionOperational provider representation before (.terminated reason) :=
  ⟨.terminated reason, called, rfl⟩

/-- A nonreturning resolved method cannot be turned into a finite getter exit. -/
theorem getExtensionOperational_no_invented_exit (provider : ExtensionByteProvider)
    (representation : ExtensionRepresentation) (before : provider.State)
    (noExit : ∀ called, ¬ provider.getBytes representation.pod before called) :
    ∀ outcome, ¬ getExtensionOperational provider representation before outcome := by
  intro outcome run
  obtain ⟨called, method, _⟩ := run
  exact noExit called method

/-- The type and dependency interpretation indexing the primary getter family. -/
structure ExtensionGetter where
  /-- Exact source Pod type and its logical representation. -/
  representation : ExtensionRepresentation
  /-- Exact interpretation of the resolved byte-retrieval method. -/
  provider : ExtensionByteProvider

/-- Immutable receiver data for the concrete default TLV lookup. -/
structure ExtensionReceiver where
  /-- The association of the source base type. -/
  accountType : ExtensionAccountType
  /-- Start address of the returned TLV slice. -/
  address : Nat
  /-- Original TLV bytes. -/
  bytes : Bytes
  deriving DecidableEq, Repr

/-- The selected byte reference of the default lookup retains its original base
address and exact range within that slice. -/
structure LocatedExtensionView where
  /-- Address of the original TLV slice. -/
  baseAddress : Nat
  /-- Selected offset and exact bytes. -/
  view : ExtensionView
  deriving DecidableEq, Repr

/-- The free `get_extension_bytes` path performs base-kind and TLV checks,
leaving Pod-size and alignment checks to the caller. -/
def defaultExtensionBytes (receiver : ExtensionReceiver) (pod : ExtensionPod) :
    Except Error LocatedExtensionView :=
  if receiver.accountType = pod.kind.accountType then
    (findExtension pod.kind.tag 0 receiver.bytes).map (fun view => ⟨receiver.address, view⟩)
  else .error .InvalidAccountData

/-- An explicit specialization of the method dependency to default immutable
lookup. Overrides use other providers rather than silently inheriting this one. -/
def defaultExtensionByteProvider : ExtensionByteProvider where
  State := ExtensionReceiver
  Reference := LocatedExtensionView
  Unwind := Empty
  Terminal := Empty
  bytes := fun _ reference => reference.view.bytes
  address := fun reference => reference.baseAddress + reference.view.offset
  getBytes := fun pod before outcome =>
    returnsOf (fun receiver (_args : Unit) => (defaultExtensionBytes receiver pod, receiver))
      before () outcome

/-- Total mathematical value computation for the concrete default provider. -/
def getDefaultExtension (representation : ExtensionRepresentation) (receiver : ExtensionReceiver) :
    Except Error (TypedExtensionReference LocatedExtensionView representation.Value) :=
  (defaultExtensionBytes receiver representation.pod).bind
    (castExtensionReference defaultExtensionByteProvider representation receiver)

/-- The actual default specialization has a finite execution for every input,
independently of whether the byte lookup or cast succeeds. -/
theorem getDefaultExtension_execution (representation : ExtensionRepresentation)
    (receiver : ExtensionReceiver) :
    getExtensionOperational defaultExtensionByteProvider representation receiver
      (.returned (getDefaultExtension representation receiver) receiver) := by
  refine ⟨.returned (defaultExtensionBytes receiver representation.pod) receiver, rfl, ?_⟩
  cases result : defaultExtensionBytes receiver representation.pod <;>
    simp only [getDefaultExtension, result, finishExtensionGetter, Except.bind] <;> rfl

/-- Forget only the concrete base address when relating a default reference to
the existing pure TLV observation; the selected range and value remain intact. -/
def defaultExtensionObservation {Value : Type}
    (typed : TypedExtensionReference LocatedExtensionView Value) : ExtensionReference Value :=
  ⟨typed.reference.view, typed.value⟩

/-- The result of the concrete provider agrees with the original complete default
TLV lookup, for every input and every source Pod representation. -/
theorem getDefaultExtension_agrees (representation : ExtensionRepresentation)
    (receiver : ExtensionReceiver) :
    (getDefaultExtension representation receiver).map defaultExtensionObservation =
      getRepresentedExtension representation receiver.accountType receiver.address receiver.bytes
        := by
  by_cases matching : representation.pod.kind.accountType = receiver.accountType
  · cases found : findExtension representation.pod.kind.tag 0 receiver.bytes with
    | error error =>
      simp [getDefaultExtension, defaultExtensionBytes, getRepresentedExtension, getExtension,
        matching, found, Except.map, Except.bind]
    | ok view =>
      by_cases length : view.bytes.length = representation.pod.byteLength
      · by_cases align : (receiver.address + view.offset) % representation.pod.alignment = 0
        · simp [getDefaultExtension, defaultExtensionBytes, getRepresentedExtension, getExtension,
            matching, found, Except.map, Except.bind, castExtensionReference,
            defaultExtensionByteProvider, defaultExtensionObservation, length, align]
        · simp [getDefaultExtension, defaultExtensionBytes, getRepresentedExtension, getExtension,
            matching, found, Except.map, Except.bind, castExtensionReference,
            defaultExtensionByteProvider, length, align]
      · simp [getDefaultExtension, defaultExtensionBytes, getRepresentedExtension, getExtension,
          matching, found, Except.map, Except.bind, castExtensionReference,
          defaultExtensionByteProvider, length]
  · have reverse : receiver.accountType ≠ representation.pod.kind.accountType := Ne.symm matching
    simp [getDefaultExtension, defaultExtensionBytes, getRepresentedExtension, getExtension,
      matching, reverse, Except.map, Except.bind]

end Solanalib.Specs.Core.Token
