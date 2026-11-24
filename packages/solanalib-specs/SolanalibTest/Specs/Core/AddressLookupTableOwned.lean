/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

import Solanalib.Specs.Core.AddressLookupTableOwned

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AddressLookupTableOwned

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AddressLookupTableOwned

private def emptyInput : Bytemuck.SliceRef := ⟨17, []⟩
private def uninitializedInput : Bytemuck.SliceRef := ⟨17, [0, 0, 0, 0]⟩

/-- A failed decode reaches allocation and destruction before the SDK error. -/
example : run sample (0 : Nat) emptyInput (.returned (.error .invalidAccountData) (2 : Nat)) :=
  (run_graph _ sampleExecutable _ _ _).mpr rfl

example : ¬ run sample (0 : Nat) emptyInput (.returned (.error .invalidAccountData) (0 : Nat)) := by
  intro execution
  have impossible := (run_graph _ sampleExecutable _ _ _).mp execution
  cases impossible

example : ¬ run sample (0 : Nat) emptyInput (.returned (.error .invalidAccountData) (1 : Nat)) := by
  intro execution
  have impossible := (run_graph _ sampleExecutable _ _ _).mp execution
  cases impossible

/-- The source rejects the decoded enum before the 56-byte suffix check, and
this successful metadata decode has no owned bincode error to destroy. -/
example : run sample (0 : Nat) uninitializedInput (.returned (.error .uninitializedAccount) (0 :
  Nat)) :=
  (run_graph _ sampleExecutable _ _ _).mpr rfl

example : ¬ run sample (0 : Nat) uninitializedInput (.returned (.error .uninitializedAccount) (2 :
  Nat)) := by
  intro execution
  have impossible := (run_graph _ sampleExecutable _ _ _).mp execution
  cases impossible

private def droppingUnwinds : Index := { sample with
  dropError := Callback.ofFunction fun (before : Nat) _ => .unwound (7 : Nat) (before + 10) }

private def droppingExecutable : Executable droppingUnwinds where
  decode := sampleDecode
  dropError := fun (before : Nat) _ => .unwound (7 : Nat) (before + 10)
  decode_eq := rfl
  drop_eq := rfl

/-- The reached destructor may unwind with its actual new state; the SDK does
not turn this into an ordinary InvalidAccountData return. -/
example : run droppingUnwinds (0 : Nat) emptyInput (.unwound (7 : Nat) (11 : Nat)) :=
  (run_graph _ droppingExecutable _ _ _).mpr rfl

example : ¬ run droppingUnwinds (0 : Nat) emptyInput (.returned (.error .invalidAccountData) (11 :
  Nat)) := by
  intro execution
  have impossible := (run_graph _ droppingExecutable _ _ _).mp execution
  cases impossible

private def table : AddressLookupTable.Value :=
  ⟨AddressLookupTable.defaultMeta, ⟨73, List.replicate 32 7⟩⟩

/-- Successful decoding exposes the nonempty suffix of the input and preserves the
state: neither the decoder error allocation nor its destructor is reached. -/
theorem successful_borrow_keeps_alias_and_state :
    run sample (5 : Nat) AddressLookupTable.sampleInput (.returned (.ok table) (5 : Nat)) :=
  (run_graph _ sampleExecutable _ _ _).mpr rfl

theorem successful_borrow_rejects_error_cleanup :
    ¬ run sample (5 : Nat) AddressLookupTable.sampleInput (.returned (.ok table) (7 : Nat)) := by
  intro execution
  have impossible := (run_graph _ sampleExecutable _ _ _).mp execution
  cases impossible

theorem successful_borrow_rejects_shifted_alias :
    ¬ run sample (5 : Nat) AddressLookupTable.sampleInput
      (.returned (.ok { table with addresses := ⟨74, List.replicate 32 7⟩ }) (5 : Nat)) := by
  intro execution
  have alias := returned_alias sample (5 : Nat) (5 : Nat) AddressLookupTable.sampleInput _ execution
  have address := congrArg Bytemuck.SliceRef.address alias
  change (74 : Nat) = 73 at address
  omega

private def droppingTerminates : Index := { sample with
  dropError := Callback.ofFunction fun _ _ => .terminated (19 : Nat) }

private def terminatingExecutable : Executable droppingTerminates where
  decode := sampleDecode
  dropError := fun _ _ => .terminated (19 : Nat)
  decode_eq := rfl
  drop_eq := rfl

theorem destructor_terminal_is_retained :
    run droppingTerminates (0 : Nat) emptyInput (.terminated (19 : Nat)) :=
  (run_graph _ terminatingExecutable _ _ _).mpr rfl

theorem destructor_terminal_does_not_return_sdk_error :
    ¬ run droppingTerminates (0 : Nat) emptyInput
      (.returned (.error .invalidAccountData) (1 : Nat)) := by
  intro execution
  have impossible := (run_graph _ terminatingExecutable _ _ _).mp execution
  cases impossible

end SolanalibTest.Specs.Core.AddressLookupTableOwned
