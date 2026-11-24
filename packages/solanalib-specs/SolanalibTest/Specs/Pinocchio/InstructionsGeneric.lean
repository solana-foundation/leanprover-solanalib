/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Pinocchio.InstructionsGeneric

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Pinocchio.InstructionsGeneric

open Solanalib.Contracts.Model Solanalib.Specs.Core
open InstructionsSysvar.Generic

/-- A nonempty lookup records all three actual callback states. -/
theorem successful_lookup_calls_deref_three_times :
    Solanalib.Specs.Pinocchio.sysvars.instructions.Instructions.Generic.load_instruction_at_run
      Sample.index (0 : Nat) ((), 0)
      (.returned (.ok ⟨(), 4⟩) (3 : Nat)) :=
  ⟨.returned Sample.slice (1 : Nat), rfl,
    ⟨.returned Sample.slice (2 : Nat), rfl,
      ⟨.returned Sample.slice (3 : Nat), rfl, rfl⟩⟩⟩

/-- An out-of-range result stops immediately after the real count read. -/
theorem out_of_range_calls_deref_once :
    instructionAt Sample.index (0 : Nat) ((), 1)
      (.returned (.error .invalidInstructionData) (1 : Nat)) :=
  ⟨.returned Sample.slice (1 : Nat), rfl, rfl⟩

/-- The current bytes of the second allocation differ from its earlier contents. -/
def changingMemory : Memory where
  State := Nat
  Allocation := Bool
  bytes := fun state allocation =>
    if allocation then some (if state = 2 then [9, 0, 33, 0, 77, 0] else [9, 0, 22, 0, 77, 0])
    else some [1, 0, 11, 0]
  baseAddress := fun _ allocation => if allocation then 8192 else 4096

/-- The first callback contributes this shorter length. -/
def firstSlice : Slice Bool := ⟨⟨false, 0⟩, 4⟩

/-- The second callback contributes a different pointer and larger extent. -/
def secondSlice : Slice Bool := ⟨⟨true, 0⟩, 6⟩

/-- Actual callback transitions choose both slice identity and current state. -/
def changingIndex : Index where
  memory := changingMemory
  Receiver := Unit
  Unwind := String
  Terminal := String
  deref := Callback.ofFunction fun (state : Nat) (_ : Unit) =>
    .returned (if state = 0 then firstSlice else secondSlice) (state + 1)

/-- The load uses the first length, second pointer and second-state bytes. -/
theorem current_uses_first_length_second_pointer_and_current_state :
    currentIndex changingIndex (0 : Nat) () (.returned (33 : UInt16) (2 : Nat)) :=
  ⟨.returned firstSlice (1 : Nat), rfl,
    ⟨.returned secondSlice (2 : Nat), rfl, rfl⟩⟩

/-- Both actual returned slices and the selected footer span are admitted. -/
theorem changing_current_admitted : CurrentReady changingIndex (0 : Nat) () := by
  intro first afterFirst firstRun
  cases firstRun
  constructor
  · dsimp [changingIndex, changingMemory, firstSlice, SliceReady, RawReady]
    decide
  · intro second afterSecond secondRun
    cases secondRun
    dsimp [changingIndex, changingMemory, firstSlice, secondSlice, SliceReady, RawReady, AddReady]
    decide

/-- The original distinct-pointer sample remains an admitted closed execution. -/
theorem changing_current_has_family_execution :
    FamilyHasExecution currentFamily currentRun changingIndex :=
  ⟨(0 : Nat), (), .returned (33 : UInt16) (2 : Nat), changing_current_admitted,
    current_uses_first_length_second_pointer_and_current_state⟩

/-- Admission discharges the checked read, preserving the same value and state. -/
theorem changing_current_has_checked_execution :
    checkedCurrent changingIndex (0 : Nat) () (.returned (33 : UInt16) (2 : Nat)) :=
  current_checked _ _ _ changing_current_admitted _
    current_uses_first_length_second_pointer_and_current_state

/-- The second callback unwinds after a nonempty first slice. -/
def unwindSecond : Index where
  memory := Sample.memory
  Receiver := Unit
  Unwind := String
  Terminal := String
  deref := Callback.ofFunction fun (state : Nat) (_ : Unit) =>
    if state = 0 then .returned Sample.slice (1 : Nat) else .unwound "second" (9 : Nat)

/-- The raw operation preserves the unwind state of the second callback. -/
theorem current_preserves_second_deref_unwind_state :
    currentIndex unwindSecond (0 : Nat) () (.unwound "second" (9 : Nat)) :=
  ⟨.returned Sample.slice (1 : Nat), rfl, ⟨.unwound "second" (9 : Nat), rfl, rfl⟩⟩

/-- No local source operation is reached after this first terminal exit. -/
def stopFirst : Index where
  memory := Sample.memory
  Receiver := Unit
  Unwind := String
  Terminal := String
  deref := fun _ _ outcome => outcome = .terminated "first"

/-- The first terminal exit retains its exact reason. -/
theorem lookup_preserves_first_terminal_exit :
    instructionAt stopFirst (0 : Nat) ((), 0) (.terminated "first") :=
  ⟨.terminated "first", rfl, rfl⟩

/-- Terminal-only callbacks require no fictitious successful count read. -/
theorem first_terminal_lookup_is_admitted_and_checked :
    AtReady stopFirst (0 : Nat) ((), 0) ∧
      checkedAt stopFirst (0 : Nat) ((), 0) (.terminated "first") := by
  constructor
  · intro first afterFirst impossible
    cases impossible
  · exact ⟨.terminated "first", rfl, rfl⟩

/-- Existing bytes are intentionally placed at an odd base address. -/
def oddMemory : Memory := { Sample.memory with baseAddress := fun _ _ => 4097 }

/-- The callback still returns the same real nonempty slice at that base. -/
def oddIndex : Index := { Sample.index with memory := oddMemory }

/-- Raw lookup retains its old total observation; this statement is not family admission. -/
theorem odd_table_address_retains_raw_execution :
    address oddMemory (2 : Nat) (Sample.slice.pointer.add 2) % 2 = 1 ∧
      instructionAt oddIndex (0 : Nat) ((), 0)
        (.returned (.ok ⟨(), 4⟩) (3 : Nat)) :=
  ⟨rfl, .returned Sample.slice (1 : Nat), rfl,
    ⟨.returned Sample.slice (2 : Nat), rfl,
      ⟨.returned Sample.slice (3 : Nat), rfl, rfl⟩⟩⟩

/-- Native table alignment is enforced by both admission and checked reading. -/
theorem odd_table_is_rejected :
    ¬ AtReady oddIndex (0 : Nat) ((), 0) ∧
      checkedTable oddMemory (2 : Nat) Sample.slice.pointer 0 = none := by
  constructor
  · intro ready
    have table := ((ready Sample.slice (1 : Nat) rfl).2.2.2 (by decide)
      Sample.slice (2 : Nat) rfl).2.2.2.1
    exact (show ¬ RawReady oddMemory (2 : Nat) (Sample.slice.pointer.add 2) 2 2 by
      dsimp [oddMemory, Sample.memory, Sample.slice, RawReady]
      decide) table
  · decide

/-- Byte-array footer reads require alignment one and therefore admit the same odd base. -/
theorem odd_current_is_admitted : CurrentReady oddIndex (0 : Nat) () := by
  intro first afterFirst firstRun
  cases firstRun
  constructor
  · dsimp [oddIndex, oddMemory, Sample.index, Sample.memory, Sample.slice, SliceReady, RawReady]
    decide
  · intro second afterSecond secondRun
    cases secondRun
    dsimp [oddIndex, oddMemory, Sample.index, Sample.memory, Sample.slice,
      SliceReady, RawReady, AddReady]
    decide

/-- The complete odd-address current-index execution succeeds through checked reads. -/
theorem odd_current_checked_execution :
    checkedCurrent oddIndex (0 : Nat) () (.returned (0 : UInt16) (2 : Nat)) :=
  current_checked _ _ _ odd_current_is_admitted _
    ⟨.returned Sample.slice (1 : Nat), rfl,
      ⟨.returned Sample.slice (2 : Nat), rfl, rfl⟩⟩

/-- A nonnull dangling address represents an empty slice, not readable bytes. -/
def emptyMemory : Memory where
  State := Unit
  Allocation := Unit
  bytes := fun _ _ => none
  baseAddress := fun _ _ => 8

/-- Empty memory may have a valid nonnull address without an allocation. -/
theorem empty_memory_has_address_without_allocation :
    address emptyMemory () ⟨(), 0⟩ = 8 ∧ emptyMemory.bytes () () = none := ⟨rfl, rfl⟩

/-- No two-byte observation is manufactured for the dangling empty pointer. -/
theorem dangling_empty_slice_has_no_word_bytes :
    readBytes emptyMemory () ⟨(), 0⟩ 2 = none := rfl

/-- The empty slice itself remains legal despite having no readable footer. -/
theorem dangling_empty_slice_is_admitted :
    SliceReady emptyMemory () ⟨⟨(), 0⟩, 0⟩ ∧
      checkedSlice emptyMemory () ⟨⟨(), 0⟩, 0⟩ = some ⟨⟨(), 0⟩, 0⟩ := by
  dsimp [emptyMemory, SliceReady, checkedSlice]
  decide

/-- Both callbacks return that same valid empty slice. -/
def emptyIndex : Index where
  memory := emptyMemory
  Receiver := Unit
  Unwind := Empty
  Terminal := Empty
  deref := Callback.ofFunction fun before _ => .returned ⟨⟨(), 0⟩, 0⟩ before

/-- The old zero fallback remains only a raw mathematical observation. -/
theorem empty_current_retains_raw_zero_fallback :
    currentIndex emptyIndex () () (.returned (0 : UInt16) ()) :=
  ⟨.returned ⟨⟨(), 0⟩, 0⟩ (), rfl,
    ⟨.returned ⟨⟨(), 0⟩, 0⟩ (), rfl, rfl⟩⟩

/-- A real second return reaches subtraction/footer access and is not admitted. -/
theorem empty_current_is_rejected :
    ¬ CurrentReady emptyIndex () () ∧
      checkedFooter emptyMemory () 0 ⟨⟨(), 0⟩, 0⟩ = none := by
  constructor
  · intro ready
    have length := ((ready ⟨⟨(), 0⟩, 0⟩ () rfl).2 ⟨⟨(), 0⟩, 0⟩ () rfl).2.1
    exact (show ¬ 2 ≤ 0 by decide) length
  · decide

/-- No-memory callback state is still observable through unwind effects. -/
def emptyCallbackMemory : Memory where
  State := Nat
  Allocation := Unit
  bytes := fun _ _ => none
  baseAddress := fun _ _ => 8

/-- The first slice is valid and empty; the second callback never returns normally. -/
def emptyExitSecond (terminal : Bool) : Index where
  memory := emptyCallbackMemory
  Receiver := Unit
  Unwind := String
  Terminal := String
  deref := Callback.ofFunction fun (state : Nat) (_ : Unit) =>
    if state = 0 then .returned ⟨⟨(), 0⟩, 0⟩ (1 : Nat)
    else if terminal then .terminated "second" else .unwound "second" (9 : Nat)

/-- The footer bound is not required before an actual second normal return. -/
theorem empty_first_abnormal_second_is_admitted (terminal : Bool) :
    CurrentReady (emptyExitSecond terminal) (0 : Nat) () := by
  intro first afterFirst firstRun
  cases firstRun
  refine ⟨by dsimp [emptyExitSecond, emptyCallbackMemory, SliceReady]; decide, ?_⟩
  intro second afterSecond secondRun
  cases terminal <;> cases secondRun

/-- A second unwind survives checking even though no footer could be read. -/
theorem empty_first_second_unwind_checked :
    checkedCurrent (emptyExitSecond false) (0 : Nat) () (.unwound "second" (9 : Nat)) :=
  current_checked _ _ _ (empty_first_abnormal_second_is_admitted false) _
    ⟨.returned ⟨⟨(), 0⟩, 0⟩ (1 : Nat), rfl,
      ⟨.unwound "second" (9 : Nat), rfl, rfl⟩⟩

/-- A second terminal exit also precedes subtraction and every footer access. -/
theorem empty_first_second_terminal_checked :
    checkedCurrent (emptyExitSecond true) (0 : Nat) () (.terminated "second") :=
  current_checked _ _ _ (empty_first_abnormal_second_is_admitted true) _
    ⟨.returned ⟨⟨(), 0⟩, 0⟩ (1 : Nat), rfl,
      ⟨.terminated "second", rfl, rfl⟩⟩

/-- One second-callback alternative returns a null slice, another a valid slice. -/
def alternativeMemory : Memory :=
  { Sample.memory with baseAddress := fun (state : Nat) (_ : Unit) => if state = 2 then 0 else 4096
    }

/-- This actual relation has a safe and an unsafe second normal return. -/
def alternativeIndex : Index where
  memory := alternativeMemory
  Receiver := Unit
  Unwind := String
  Terminal := String
  deref := fun (before : Nat) (_ : Unit) outcome =>
    if before = 0 then outcome = .returned Sample.slice (1 : Nat)
    else outcome = .returned Sample.slice (2 : Nat) ∨ outcome = .returned Sample.slice (3 : Nat)

/-- Selecting the safe alternative really does produce a checked finite execution. -/
theorem nondeterministic_provider_has_safe_checked_trace :
    checkedCurrent alternativeIndex (0 : Nat) () (.returned (0 : UInt16) (3 : Nat)) := by
  refine ⟨.returned Sample.slice (1 : Nat), rfl, ?_,
    .returned Sample.slice (3 : Nat), Or.inr rfl, 0, ?_, rfl⟩
  · dsimp [alternativeIndex, alternativeMemory, Sample.memory, Sample.slice, checkedSlice]
    decide
  · dsimp [alternativeIndex, alternativeMemory, Sample.memory, Sample.slice,
      checkedFooter, checkedAdd, AddReady]
    decide

/-- A chosen safe trace cannot justify universal admission of an unsafe alternative. -/
theorem nondeterministic_unsafe_alternative_rejects_admission :
    ¬ CurrentReady alternativeIndex (0 : Nat) () ∧
      ¬ AtReady alternativeIndex (0 : Nat) ((), 0) := by
  constructor
  · intro ready
    have invalid := ((ready Sample.slice (1 : Nat) rfl).2
      Sample.slice (2 : Nat) (Or.inl rfl)).1
    exact (show ¬ SliceReady alternativeMemory (2 : Nat) Sample.slice by
      dsimp [alternativeMemory, Sample.memory, Sample.slice, SliceReady, RawReady]
      decide) invalid
  · intro ready
    have invalid := ((ready Sample.slice (1 : Nat) rfl).2.2.2 (by decide)
      Sample.slice (2 : Nat) (Or.inl rfl)).1
    exact (show ¬ SliceReady alternativeMemory (2 : Nat) Sample.slice by
      dsimp [alternativeMemory, Sample.memory, Sample.slice, SliceReady, RawReady]
      decide) invalid

/-- A count is present but no offset-table entry exists. -/
def countOnlyMemory : Memory where
  State := Nat
  Allocation := Unit
  bytes := fun _ _ => some [1, 0]
  baseAddress := fun _ _ => 4096

/-- Exactly the two current count bytes form this returned slice. -/
def countOnlySlice : Slice Unit := ⟨⟨(), 0⟩, 2⟩

/-- Each actual call returns the short slice and increments the state counter. -/
def countOnlyIndex : Index where
  memory := countOnlyMemory
  Receiver := Unit
  Unwind := String
  Terminal := String
  deref := Callback.ofFunction fun (before : Nat) (_ : Unit) => .returned countOnlySlice (before +
    1)

/-- Out-of-range admission needs only the current count, not an absent table. -/
theorem count_only_out_of_range_admitted : AtReady countOnlyIndex (0 : Nat) ((), 1) := by
  intro first afterFirst firstRun
  cases firstRun
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [countOnlyIndex, countOnlyMemory, countOnlySlice, SliceReady, RawReady]
    decide
  · decide
  · dsimp [countOnlyIndex, countOnlyMemory, countOnlySlice, RawReady]
    decide
  · intro inside
    exact False.elim ((show ¬ (1 : Nat) < 1 by decide) inside)

/-- The early SDK error is reached through a successful checked count read. -/
theorem count_only_out_of_range_checked :
    checkedAt countOnlyIndex (0 : Nat) ((), 1)
      (.returned (.error .invalidInstructionData) (1 : Nat)) :=
  at_checked _ _ _ count_only_out_of_range_admitted _
    ⟨.returned countOnlySlice (1 : Nat), rfl, rfl⟩

/-- An in-range lookup keeps its raw fallback but is rejected by source admission. -/
theorem count_only_in_range_is_rejected :
    instructionAt countOnlyIndex (0 : Nat) ((), 0)
      (.returned (.ok ⟨(), 0⟩) (3 : Nat)) ∧
      ¬ AtReady countOnlyIndex (0 : Nat) ((), 0) := by
  constructor
  · exact ⟨.returned countOnlySlice (1 : Nat), rfl,
      ⟨.returned countOnlySlice (2 : Nat), rfl,
        ⟨.returned countOnlySlice (3 : Nat), rfl, rfl⟩⟩⟩
  · intro ready
    have table := ((ready countOnlySlice (1 : Nat) rfl).2.2.2 (by decide)
      countOnlySlice (2 : Nat) rfl).2.2.2.1
    exact (show ¬ RawReady countOnlyMemory (2 : Nat) (countOnlySlice.pointer.add 2) 2 2 by
      dsimp [countOnlyMemory, countOnlySlice, RawReady]
      decide) table

/-- A two-word table and a separate nonnull dangling allocation identity. -/
def boundaryMemory (offset : Nat) : Memory where
  State := Nat
  Allocation := Bool
  bytes := fun _ allocation => if allocation then none else some ([1, 0] ++ Solanalib.Runtime.u16le
    offset)
  baseAddress := fun _ allocation => if allocation then 8 else 4096

/-- The first two calls use real count/table storage. -/
def tableSlice : Slice Bool := ⟨⟨false, 0⟩, 4⟩

/-- The final callback may choose a dangling empty slice instead. -/
def danglingSlice : Slice Bool := ⟨⟨true, 0⟩, 0⟩

/-- The third callback independently selects its pointer after the saved offset read. -/
def boundaryIndex (offset : Nat) (dangling : Bool) : Index where
  memory := boundaryMemory offset
  Receiver := Unit
  Unwind := String
  Terminal := String
  deref := Callback.ofFunction fun (before : Nat) (_ : Unit) =>
    .returned (if before < 2 then tableSlice else if dangling then danglingSlice else tableSlice)
      (before + 1)

/-- Zero offset requires no allocation when the third returned slice is valid and empty. -/
theorem third_zero_offset_dangling_admitted :
    AtReady (boundaryIndex 0 true) (0 : Nat) ((), 0) := by
  intro first afterFirst firstRun
  cases firstRun
  refine ⟨?_, by decide, ?_, ?_⟩
  · dsimp [boundaryIndex, boundaryMemory, tableSlice, SliceReady, RawReady]
    decide
  · dsimp [boundaryIndex, boundaryMemory, tableSlice, RawReady]
    decide
  · intro _ second afterSecond secondRun
    cases secondRun
    refine ⟨?_, by decide, ?_, ?_, ?_⟩
    · dsimp [boundaryIndex, boundaryMemory, tableSlice, SliceReady, RawReady]
      decide
    · dsimp [boundaryIndex, boundaryMemory, tableSlice, AddReady]
      decide
    · dsimp [boundaryIndex, boundaryMemory, tableSlice, RawReady]
      decide
    · intro third afterThird thirdRun
      cases thirdRun
      dsimp [boundaryIndex, boundaryMemory, tableSlice, danglingSlice,
        SliceReady, RawReady, AddReady]
      decide

/-- A complete checked lookup may return a dangling pointer without dereferencing it. -/
theorem third_zero_offset_dangling_checked :
    checkedAt (boundaryIndex 0 true) (0 : Nat) ((), 0)
      (.returned (.ok ⟨true, 0⟩) (3 : Nat)) :=
  at_checked _ _ _ third_zero_offset_dangling_admitted _
    ⟨.returned tableSlice (1 : Nat), rfl,
      ⟨.returned tableSlice (2 : Nat), rfl,
        ⟨.returned danglingSlice (3 : Nat), rfl, rfl⟩⟩⟩

/-- A nonzero offset cannot be added to that same unallocated third pointer. -/
theorem third_nonzero_offset_dangling_rejected :
    ¬ AtReady (boundaryIndex 1 true) (0 : Nat) ((), 0) ∧
      checkedAdd (boundaryMemory 1) (3 : Nat) danglingSlice.pointer 1 = none := by
  constructor
  · intro ready
    have last := ((ready tableSlice (1 : Nat) rfl).2.2.2 (by decide)
      tableSlice (2 : Nat) rfl).2.2.2.2 danglingSlice (3 : Nat) rfl
    exact (show ¬ AddReady (boundaryMemory 1) (3 : Nat) danglingSlice.pointer 1 by
      dsimp [boundaryMemory, danglingSlice, AddReady]
      decide) last.2
  · decide

/-- A saved endpoint exactly one-past the third allocation is a legal raw pointer. -/
theorem one_past_lookup_admitted : AtReady (boundaryIndex 4 false) (0 : Nat) ((), 0) := by
  intro first afterFirst firstRun
  cases firstRun
  refine ⟨?_, by decide, ?_, ?_⟩
  · dsimp [boundaryIndex, boundaryMemory, tableSlice, SliceReady, RawReady]
    decide
  · dsimp [boundaryIndex, boundaryMemory, tableSlice, RawReady]
    decide
  · intro _ second afterSecond secondRun
    cases secondRun
    refine ⟨?_, by decide, ?_, ?_, ?_⟩
    · dsimp [boundaryIndex, boundaryMemory, tableSlice, SliceReady, RawReady]
      decide
    · dsimp [boundaryIndex, boundaryMemory, tableSlice, AddReady]
      decide
    · dsimp [boundaryIndex, boundaryMemory, tableSlice, RawReady]
      decide
    · intro third afterThird thirdRun
      cases thirdRun
      dsimp [boundaryIndex, boundaryMemory, tableSlice, SliceReady, RawReady, AddReady]
      decide

/-- Pointer formation succeeds at one-past, while neither later decoder is admitted. -/
theorem one_past_lookup_is_not_a_decoded_instruction :
    checkedAt (boundaryIndex 4 false) (0 : Nat) ((), 0)
      (.returned (.ok ⟨false, 4⟩) (3 : Nat)) ∧
      ¬ ProgramReady (boundaryMemory 4) (3 : Nat) ⟨false, 4⟩ ∧
      ¬ DataReady (boundaryMemory 4) (3 : Nat) ⟨false, 4⟩ := by
  refine ⟨at_checked _ _ _ one_past_lookup_admitted _ ?_, ?_, ?_⟩
  · exact ⟨.returned tableSlice (1 : Nat), rfl,
      ⟨.returned tableSlice (2 : Nat), rfl,
        ⟨.returned tableSlice (3 : Nat), rfl, rfl⟩⟩⟩
  · intro ready
    exact (show ¬ RawReady (boundaryMemory 4) (3 : Nat) ⟨false, 4⟩ 2 1 by
      dsimp [boundaryMemory, RawReady]
      decide) ready.1
  · intro ready
    exact (show ¬ RawReady (boundaryMemory 4) (3 : Nat) ⟨false, 4⟩ 2 1 by
      dsimp [boundaryMemory, RawReady]
      decide) ready.1

/-- The next offset crosses the same allocation boundary and cannot be formed. -/
theorem beyond_one_past_lookup_rejected :
    ¬ AtReady (boundaryIndex 5 false) (0 : Nat) ((), 0) := by
  intro ready
  have last := ((ready tableSlice (1 : Nat) rfl).2.2.2 (by decide)
    tableSlice (2 : Nat) rfl).2.2.2.2 tableSlice (3 : Nat) rfl
  exact (show ¬ AddReady (boundaryMemory 5) (3 : Nat) tableSlice.pointer 5 by
    dsimp [boundaryMemory, tableSlice, AddReady]
    decide) last.2

/-- Byte availability alone cannot turn a null address into a source reference. -/
def nullMemory : Memory := { Sample.memory with baseAddress := fun _ _ => 0 }

/-- Null reads and even null empty slices are rejected despite stored count bytes. -/
theorem null_address_rejected :
    readBytes nullMemory (0 : Nat) ⟨(), 0⟩ 2 = some [1, 0] ∧
      checkedWord nullMemory (0 : Nat) ⟨(), 0⟩ 1 = none ∧
      ¬ SliceReady nullMemory (0 : Nat) ⟨⟨(), 0⟩, 0⟩ := by
  dsimp [nullMemory, Sample.memory, SliceReady]
  decide

/-- The backing exists but its mathematical base would make a two-byte span wrap. -/
def wrappingMemory : Memory :=
  { Sample.memory with baseAddress := fun _ _ => Solanalib.Runtime.U64_LIMIT - 1 }

/-- Extent alone is insufficient when the reached address span is not representable. -/
theorem wrapping_span_rejected :
    readBytes wrappingMemory (0 : Nat) ⟨(), 0⟩ 2 = some [1, 0] ∧
      checkedWord wrappingMemory (0 : Nat) ⟨(), 0⟩ 1 = none ∧
      ¬ RawReady wrappingMemory (0 : Nat) ⟨(), 0⟩ 2 1 := by
  dsimp [wrappingMemory, Sample.memory, RawReady]
  decide

/-- The signed slice-size bound rejects oversized values independently of byte storage. -/
theorem oversized_slice_rejected (memory : Memory) (state : memory.State)
    (pointer : Pointer memory.Allocation) :
    ¬ SliceReady memory state ⟨pointer, ISIZE_LIMIT⟩ ∧
      checkedSlice memory state ⟨pointer, ISIZE_LIMIT⟩ = none := by
  simp [SliceReady, RawReady, checkedSlice, checkedBytes, show ISIZE_LIMIT ≠ 0 by decide]

/-- Pointer arithmetic has the same signed displacement restriction. -/
theorem oversized_add_rejected (memory : Memory) (state : memory.State)
    (pointer : Pointer memory.Allocation) :
    ¬ AddReady memory state pointer ISIZE_LIMIT ∧
      checkedAdd memory state pointer ISIZE_LIMIT = none := by
  simp [AddReady, checkedAdd]

/-- The second slice is shorter than the copied first length although its allocation is large. -/
def shortFooterIndex : Index where
  memory := changingMemory
  Receiver := Unit
  Unwind := String
  Terminal := String
  deref := Callback.ofFunction fun (before : Nat) (_ : Unit) =>
    .returned (if before = 0 then firstSlice else ⟨secondSlice.pointer, 2⟩) (before + 1)

/-- Backing bytes cannot justify a footer access outside the actual second slice. -/
theorem short_second_slice_rejects_footer :
    currentIndex shortFooterIndex (0 : Nat) () (.returned (33 : UInt16) (2 : Nat)) ∧
      ¬ CurrentReady shortFooterIndex (0 : Nat) () ∧
      checkedFooter changingMemory (2 : Nat) 4 ⟨secondSlice.pointer, 2⟩ = none := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨.returned firstSlice (1 : Nat), rfl,
      ⟨.returned ⟨secondSlice.pointer, 2⟩ (2 : Nat), rfl, rfl⟩⟩
  · intro ready
    have extent := ((ready firstSlice (1 : Nat) rfl).2
      ⟨secondSlice.pointer, 2⟩ (2 : Nat) rfl).2.2.1
    exact (show ¬ 4 ≤ 2 by decide) extent
  · dsimp [changingMemory, secondSlice, checkedFooter, checkedSlice]
    decide

/-- A one-byte source slice can sit inside an allocation containing both count bytes. -/
def shortCountIndex : Index where
  memory := Sample.memory
  Receiver := Unit
  Unwind := String
  Terminal := String
  deref := Callback.ofFunction fun (before : Nat) (_ : Unit) => .returned ⟨⟨(), 0⟩, 1⟩ (before + 1)

/-- Count admission uses the returned slice extent, not just the allocation extent. -/
theorem short_first_slice_rejects_count :
    readBytes Sample.memory (1 : Nat) ⟨(), 0⟩ 2 = some [1, 0] ∧
      ¬ AtReady shortCountIndex (0 : Nat) ((), 0) := by
  refine ⟨rfl, ?_⟩
  intro ready
  have extent := (ready ⟨⟨(), 0⟩, 1⟩ (1 : Nat) rfl).2.1
  exact (show ¬ 2 ≤ 1 by decide) extent

/-- The second returned slice omits a physically present table word. -/
def shortTableSlice : Slice Bool := ⟨tableSlice.pointer, 2⟩

/-- Count and table callbacks return distinct extents of the same allocation. -/
def shortTableIndex : Index where
  memory := boundaryMemory 0
  Receiver := Unit
  Unwind := String
  Terminal := String
  deref := Callback.ofFunction fun (before : Nat) (_ : Unit) =>
    .returned (if before = 0 then tableSlice else shortTableSlice) (before + 1)

/-- A present, aligned table word still needs to fit the actual second source slice. -/
theorem short_second_slice_rejects_table :
    readBytes (boundaryMemory 0) (2 : Nat) (tableSlice.pointer.add 2) 2 = some [0, 0] ∧
      ¬ AtReady shortTableIndex (0 : Nat) ((), 0) := by
  refine ⟨rfl, ?_⟩
  intro ready
  have extent := ((ready tableSlice (1 : Nat) rfl).2.2.2 (by decide)
    shortTableSlice (2 : Nat) rfl).2.1
  exact (show ¬ 4 ≤ 2 by decide) extent

/-- An entry with zero accounts and zero data has both real length words. -/
def emptyDataMemory : Memory where
  State := Unit
  Allocation := Unit
  bytes := fun _ _ => some (List.replicate 36 0)
  baseAddress := fun _ _ => 4096

/-- Empty data follows successful count/length reads and a legal one-past addition. -/
theorem empty_data_has_real_prefix_and_one_past_result :
    DataReady emptyDataMemory () ⟨(), 0⟩ ∧
      checkedData emptyDataMemory () ⟨(), 0⟩ = some ⟨⟨(), 36⟩, 0⟩ ∧
      readBytes emptyDataMemory () ⟨(), 36⟩ 1 = none := by
  dsimp [emptyDataMemory, DataReady, RawReady, AddReady, SliceReady, checkedData,
    checkedAdd, checkedSlice, instructionData, dataOffset, programOffset]
  decide

end SolanalibTest.Specs.Pinocchio.InstructionsGeneric
