/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtensionLegacyWitness
public import Solanalib.Specs.Core.TokenExtensionLegacyBounds
public import Solanalib.Specs.Core.TokenExtensionFee
public import Solanalib.Specs.Core.Family

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Solanalib.Specs.Core.Token.Legacy

/-- Generic type parameters for the stored borrowed TLV field projection. -/
structure TlvTypes where
  /-- The source value interpretation of the owned base. -/
  Base : Type
  /-- Existing input slice identities. -/
  Reference : Type

/-- Concrete StateWithExtensions::get_tlv_data returns its stored tail
reference; it neither reparses the base nor validates the extension bytes. -/
def tlvFamily : Family where
  Index := TlvTypes
  State := fun types => ExtensionUnpacked types.Base types.Reference
  Args := fun _ => Unit
  Value := fun types => ExtensionTailReference types.Reference
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun _ => .returning (fun _ _ => True) fun before _ value after =>
    value = before.tlv ∧ after = before

/-- Exact unchanged-state field projection. -/
def tlvRun : FamilyRun tlvFamily := fun _ => returnsOf fun before _ => (before.tlv, before)

/-- Every source-type interpretation shares the same field projection. -/
theorem tlv_reference : FamilyReference tlvFamily tlvRun := by
  intro types
  apply (Solanalib.Contracts.Model.realized_iff_holds _ _).mp
  intro before args _
  exact ⟨rfl, rfl⟩

/-- A nonempty stored source range supplies a closed projection sample. -/
def tlvSample : TlvTypes := ⟨Nat, Nat⟩

/-- The sample transfers the stored range with its unchanged receiver. -/
theorem tlv_execution : FamilyHasExecution tlvFamily tlvRun tlvSample := by
  refine ⟨(⟨7, .borrowed ⟨9, 166, 4⟩⟩ : ExtensionUnpacked Nat Nat), (),
    .returned (.borrowed ⟨(9 : Nat), 166, 4⟩)
      (⟨7, .borrowed ⟨9, 166, 4⟩⟩ : ExtensionUnpacked Nat Nat), trivial, ?_⟩
  rfl

/-- The old vector scan remains generic over the resolved accessor and every
allocation/cleanup effect, with live slice observations at the correct stages. -/
def typesFamily : Family where
  Index := CurrentExtensionTypeReader
  State := CurrentExtensionTypeReader.State
  Args := fun _ => Unit
  Value := fun reader => Except Error reader.Resource
  Unwind := CurrentExtensionTypeReader.Unwind
  Terminal := CurrentExtensionTypeReader.Terminal
  contract := fun reader =>
    { requires := fun _ _ => True, post := fun before _ => getTypes reader before }

/-- The reference is the operational scanner, not the pure list observation. -/
def typesRun : FamilyRun typesFamily := fun reader before _ => getTypes reader before

/-- Universal reference correctness keeps every effectful provider index. -/
theorem types_reference : FamilyReference typesFamily typesRun := by
  intro reader before args outcome _ execution
  exact execution

/-- The same full two-entry sample used by the resource execution theorem. -/
def typesSample : CurrentExtensionTypeReader :=
  extensionTypeReaderReference (Unwind := Empty) (Terminal := Empty) extensionListSample

/-- A complete nonempty list execution transfers a live result owner. -/
theorem types_execution : FamilyHasExecution typesFamily typesRun typesSample :=
  ⟨[], (), .returned (.ok (0 : Nat)) [some extensionListSampleValues], trivial, sample_executes⟩

/-- Version-sensitive generic unpacking; both old profiles retain their
temporary zero-vector and owned-base cleanup behavior. -/
def unpackFamily (requiresTlvByte : Bool) : Family where
  Index := Unpacker
  State := fun model => model.base.State
  Args := fun model => model.base.Reference
  Value := fun model => Except Error (ExtensionUnpacked model.base.Base model.base.Reference)
  Unwind := fun model => model.base.Unwind
  Terminal := fun model => model.base.Terminal
  contract := fun model => { requires := fun _ _ => True, post := unpack requiresTlvByte model }

/-- Complete parser, allocation, reference and cleanup reference family. -/
def unpackRun (requiresTlvByte : Bool) : FamilyRun (unpackFamily requiresTlvByte) :=
  unpack requiresTlvByte

/-- The operational relation itself realizes the full contract of every index. -/
theorem unpack_reference (requiresTlvByte : Bool) :
    FamilyReference (unpackFamily requiresTlvByte) (unpackRun requiresTlvByte) := by
  intro model before args outcome _ execution
  exact execution

/-- The actual initialized Mint sample executes its padding allocation. -/
theorem unpack_execution (requiresTlvByte : Bool) :
    FamilyHasExecution (unpackFamily requiresTlvByte) (unpackRun requiresTlvByte) mintUnpacker :=
  ⟨[], mintSampleBytes, .returned (.ok ⟨mintSampleBase, .borrowed ⟨mintSampleBytes, 166, 1⟩⟩)
    [none],
    trivial, mintSample_executes requiresTlvByte⟩

/-- Whole fixed-size calculation above the old vector dependency. -/
def sizeFamily : Family where
  Index := Sizer
  State := fun model => model.types.State
  Args := fun model => model.types.Reference
  Value := fun _ => Except Error Nat
  Unwind := fun model => model.types.Unwind
  Terminal := fun model => model.types.Terminal
  contract := fun model => { requires := fun _ _ => True, post := calculateAccountLength model }

/-- The deduplicate-before-size relation is the registered reference. -/
def sizeRun : FamilyRun sizeFamily := calculateAccountLength

theorem size_reference : FamilyReference sizeFamily sizeRun := by
  intro model before args outcome _ execution
  exact execution

/-- Nonempty sizing allocates, computes and destroys its temporary vector. -/
theorem size_execution : FamilyHasExecution sizeFamily sizeRun sizeSample :=
  ⟨[], sizeSampleInput, .returned (.ok 170) [none], trivial, sizeSample_executes⟩

/-- Required-init construction retains its owned result and all source pushes. -/
def requiredFamily : Family where
  Index := TypeArray
  State := TypeArray.State
  Args := TypeArray.Reference
  Value := TypeArray.Resource
  Unwind := TypeArray.Unwind
  Terminal := TypeArray.Terminal
  contract := fun types => { requires := fun _ _ => True, post := requiredInit types }

/-- Required-list construction is interpreted through every actual provider. -/
def requiredRun : FamilyRun requiredFamily := requiredInit

/-- Reference correctness retains both success and dependency exits. -/
theorem required_reference : FamilyReference requiredFamily requiredRun := by
  intro model before args outcome _ execution
  exact execution

/-- Source duplicates survive a complete five-push result construction. -/
theorem required_execution : FamilyHasExecution requiredFamily requiredRun typeArrayReference :=
  ⟨[], requiredSample, .returned (0 : Nat) [some (requiredInitValue requiredSample)],
    trivial, requiredSample_executes⟩

/-- The variable-size wrapper preserves its two accessor stages and scoped
TLV vector, rather than assuming a serializer result or successful scan. -/
def newLengthFamily : Family where
  Index := NewLength
  State := fun model => model.reader.State
  Args := NewLength.NewReference
  Value := fun _ => Except Error Nat
  Unwind := fun model => model.reader.Unwind
  Terminal := fun model => model.reader.Terminal
  contract := fun model => { requires := fun _ _ => True, post := getNewLength model }

/-- Reference composition of access, measurement, scanning and cleanup. -/
def newLengthRun : FamilyRun newLengthFamily := getNewLength

/-- Every serializer and vector interpretation is covered by the family. -/
theorem newLength_reference : FamilyReference newLengthFamily newLengthRun := by
  intro model before args outcome _ execution
  exact execution

/-- A real nonempty scan, replacement and drop inhabit the family. -/
theorem newLength_execution : FamilyHasExecution newLengthFamily newLengthRun newLengthSample :=
  ⟨[], (12 : Nat), .returned (.ok 182) [none], trivial, newLengthSample_executes⟩

/-- The two optional-key wrappers share this control-flow family. A binding
fixes the appropriate resolved getter and field for each helper identity. -/
def keyFamily : Family where
  Index := ExtensionKeyGetter
  State := ExtensionKeyGetter.State
  Args := fun _ => Unit
  Value := fun _ => Option Solanalib.Runtime.Pubkey
  Unwind := ExtensionKeyGetter.Unwind
  Terminal := ExtensionKeyGetter.Terminal
  contract := fun getter =>
    { requires := fun _ _ => True, post := fun before _ => getExtensionKey getter before }

/-- The optional-key helpers preserve the abnormal exits of the actual getter. -/
def keyRun : FamilyRun keyFamily := fun getter before _ => getExtensionKey getter before

/-- Closed reference correctness for either field-selection interpretation. -/
theorem key_reference : FamilyReference keyFamily keyRun := by
  intro getter before args outcome _ execution
  exact execution

/-- Fixed Pod representation for the permanent delegate or hook program key.
Only the hook skips its first 32-byte authority field. -/
def keyRepresentation (hook : Bool) : ExtensionRepresentation where
  Value := Solanalib.Runtime.Pubkey
  pod := ⟨if hook then .transferHook else .permanentDelegate, if hook then 64 else 32, 1⟩
  observe := fun bytes => Solanalib.Runtime.Pubkey.ofBytes (Solanalib.Runtime.slice bytes (if hook
    then 32 else 0) 32)

/-- The concrete older default getter supplies a full fixed-key sample. -/
def keySample (hook : Bool) : ExtensionKeyGetter :=
  keyGetterOf ⟨keyRepresentation hook, defaultByteProvider⟩ id
    (fun before _ outcome => outcome = .returned () before)

/-- A nonzero nullable key in the selected fixed Pod payload. -/
def keySampleReceiver (hook : Bool) : ExtensionReceiver :=
  ⟨.mint, 4096, [if hook then 14 else 12, 0, if hook then 64 else 32, 0] ++
    List.replicate (if hook then 64 else 32) 7⟩

/-- The concrete default-method result of the helper for any fixed receiver. -/
def keyDefaultResult (hook : Bool) (receiver : ExtensionReceiver) : Option Solanalib.Runtime.Pubkey
  :=
  match getDefaultExtension (keyRepresentation hook) receiver with
  | .ok reference => nullableKey reference.value
  | .error _ => none

/-- The default getter produces no owned error payload. The concrete unit
error-drop interpretation therefore retains its receiver on either result. -/
theorem keySample_iff (hook : Bool) (receiver : ExtensionReceiver)
    (final : Outcome ExtensionReceiver (Option Solanalib.Runtime.Pubkey) Empty Empty) :
    getExtensionKey (keySample hook) receiver final ↔
      final = .returned (keyDefaultResult hook receiver) receiver := by
  constructor
  · rintro ⟨called, ran, finished⟩
    have actual := (getDefaultExtension_iff (keyRepresentation hook) receiver called).1 ran
    rw [actual] at finished
    cases found : getDefaultExtension (keyRepresentation hook) receiver <;>
      simpa [found, finishKey, keySample, keyGetterOf, keyDefaultResult, Outcome.map,
        defaultByteProvider] using finished
  · intro result
    refine ⟨.returned (getDefaultExtension (keyRepresentation hook) receiver) receiver,
      (getDefaultExtension_iff (keyRepresentation hook) receiver _).2 rfl, ?_⟩
    cases found : getDefaultExtension (keyRepresentation hook) receiver <;>
      simpa [found, finishKey, keySample, keyGetterOf, keyDefaultResult, Outcome.map,
        defaultByteProvider] using result

/-- Both key helpers have an actual composed fixed-Pod lookup execution. -/
theorem key_execution (hook : Bool) : FamilyHasExecution keyFamily keyRun (keySample hook) := by
  let receiver := keySampleReceiver hook
  exact ⟨receiver, (), .returned (keyDefaultResult hook receiver) receiver, trivial,
    (keySample_iff hook receiver _).2 rfl⟩

end Solanalib.Specs.Core.Token.Legacy
