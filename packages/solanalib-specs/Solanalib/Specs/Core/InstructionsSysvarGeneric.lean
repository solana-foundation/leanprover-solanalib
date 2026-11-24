/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Callback
public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.InstructionsSysvar

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.InstructionsSysvar.Generic

/-- Allocation identity and relative position of an interpreted source pointer. -/
structure Pointer (Allocation : Type) where
  /-- Allocation identity supplied by the source-memory interpretation. -/
  allocation : Allocation
  /-- Byte position relative to the base of that allocation. -/
  offset : Nat
  deriving DecidableEq, Repr

/-- The pointer and metadata of one actual returned Deref slice. -/
structure Slice (Allocation : Type) where
  /-- The source pointer of the returned slice. -/
  pointer : Pointer Allocation
  /-- The captured length of the returned slice, independent of later callbacks. -/
  length : Nat
  deriving DecidableEq, Repr

/-- A pure mathematical memory interface. Bytes are read from the current
callback state. Source allocation, permissions and representation are explicit
interpretation obligations; an arbitrary callback cannot replace a read with
an independently supplied decoded value. -/
structure Memory where
  /-- Current state visible to callbacks and subsequent reads. -/
  State : Type
  /-- Identities of source allocations, independent of their numeric addresses. -/
  Allocation : Type
  /-- Current initialized allocation bytes; tag permissions are a separate source binding. -/
  bytes : State → Allocation → Option Solanalib.Runtime.Bytes
  /-- Current numeric base address assigned to each source allocation. -/
  baseAddress : State → Allocation → Nat

/-- Raw mathematical forward offset; checkedAdd establishes when the corresponding source addition
is defined. -/
def Pointer.add {Allocation : Type} (pointer : Pointer Allocation) (delta : Nat) :
    Pointer Allocation := ⟨pointer.allocation, pointer.offset + delta⟩

/-- Current numeric address from allocation base and pointer offset. -/
def address (memory : Memory) (state : memory.State) (pointer : Pointer memory.Allocation) : Nat :=
  memory.baseAddress state pointer.allocation + pointer.offset

/-- Read a complete range from the current allocation, returning none for absent or short storage.
-/
def readBytes (memory : Memory) (state : memory.State) (pointer : Pointer memory.Allocation)
    (length : Nat) : Option Solanalib.Runtime.Bytes :=
  (memory.bytes state pointer.allocation).bind fun bytes =>
    if pointer.offset + length ≤ bytes.length then some (Solanalib.Runtime.slice bytes
      pointer.offset length)
    else none

/-- Unchanged mathematical word observation with zero fallback when its two bytes are absent. -/
def readWord (memory : Memory) (state : memory.State) (pointer : Pointer memory.Allocation) : Nat :=
  Solanalib.Runtime.leNat ((readBytes memory state pointer 2).getD [])

/-- The receiver is an identity/model value for arbitrary `T`. Each recorded
autoderef is a separate callback and can change state or unwind. -/
structure Index where
  /-- The shared current-memory interpretation for this receiver. -/
  memory : Memory
  /-- Values denoting the generic Rust receiver T. -/
  Receiver : Type
  /-- Reasons carried by an unwinding Deref callback. -/
  Unwind : Type
  /-- Terminal callback reasons, after which no continuation runs. -/
  Terminal : Type
  /-- Every finite outcome of each actual Deref call, including its current state. -/
  deref : Callback.Run memory.State Receiver (Slice memory.Allocation) Unwind Terminal

/-- Source order: deref for `len`, deref again for `as_ptr`, then load the
footer at the first length from the second pointer in the second state. -/
def currentIndex (index : Index) :
    Callback.Run index.memory.State index.Receiver UInt16 index.Unwind index.Terminal :=
  fun before receiver outcome =>
    Callback.bind index.deref (fun first afterFirst result =>
      Callback.bind index.deref (fun second afterSecond final =>
        final = .returned (UInt16.ofNat (readWord index.memory afterSecond
          (second.pointer.add (first.length - 2)))) afterSecond)
        afterFirst receiver result) before receiver outcome

/-- Source order: one deref and count read; an out-of-range error stops there.
The success branch dereferences again for the native u16 table read, then once
more for the base pointer used by the returned introspected instruction. -/
def instructionAt (index : Index) : Callback.Run index.memory.State (index.Receiver × UInt64)
    (Except ProgramError.Value (Pointer index.memory.Allocation)) index.Unwind index.Terminal :=
  fun before args outcome =>
    Callback.bind index.deref (fun first afterFirst result =>
      if readWord index.memory afterFirst first.pointer ≤ args.2.toNat then
        result = .returned (.error .invalidInstructionData) afterFirst
      else
        Callback.bind index.deref (fun second afterSecond secondResult =>
          let offset := readWord index.memory afterSecond (second.pointer.add (2 + 2 *
            args.2.toNat))
          Callback.bind index.deref (fun third afterThird final =>
            final = .returned (.ok (third.pointer.add offset)) afterThird)
            afterSecond args.1 secondResult)
          afterFirst args.1 result) before args.1 outcome

/-- Relative program-address offset from the current two-byte entry count. -/
def programOffset (memory : Memory) (state : memory.State)
    (instruction : Pointer memory.Allocation) : Nat :=
  2 + 33 * readWord memory state instruction

/-- Raw program pointer computed from the current entry bytes. -/
def programId (memory : Memory) (state : memory.State)
    (instruction : Pointer memory.Allocation) : Pointer memory.Allocation :=
  instruction.add (programOffset memory state instruction)

/-- Relative position of the data-length word of the current entry. -/
def dataOffset (memory : Memory) (state : memory.State)
    (instruction : Pointer memory.Allocation) : Nat :=
  programOffset memory state instruction + 32

/-- Raw data descriptor computed from the current count and length observations. -/
def instructionData (memory : Memory) (state : memory.State)
    (instruction : Pointer memory.Allocation) : Slice memory.Allocation :=
  let offset := dataOffset memory state instruction
  ⟨instruction.add (offset + 2), readWord memory state (instruction.add offset)⟩

/-- The positive signed pointer-offset limit of the selected 64-bit target. -/
def ISIZE_LIMIT : Nat := 2^63

/-- A current complete byte span, with the nonnull, nonwrapping address and
alignment required by this actual load/reference. Allocation identity and
read permission are the interpretation of `Memory.bytes`, not new callbacks. -/
def RawReady (memory : Memory) (state : memory.State)
    (pointer : Pointer memory.Allocation) (length alignment : Nat) : Prop :=
  (readBytes memory state pointer length).isSome = true ∧
    0 < address memory state pointer ∧
    address memory state pointer + length < Solanalib.Runtime.U64_LIMIT ∧
    length < ISIZE_LIMIT ∧ address memory state pointer % alignment = 0

instance (memory : Memory) (state : memory.State)
    (pointer : Pointer memory.Allocation) (length alignment : Nat) :
    Decidable (RawReady memory state pointer length alignment) := by
  unfold RawReady
  infer_instance

/-- Checked observation of exactly the current bytes; failure is undefined
source access, not a modeled Rust `Result::Err` or syscall failure. -/
def checkedBytes (memory : Memory) (state : memory.State)
    (pointer : Pointer memory.Allocation) (length alignment : Nat) : Option Solanalib.Runtime.Bytes
      :=
  if 0 < address memory state pointer ∧
      address memory state pointer + length < Solanalib.Runtime.U64_LIMIT ∧
      length < ISIZE_LIMIT ∧ address memory state pointer % alignment = 0 then
    readBytes memory state pointer length
  else none

/-- Checked little-endian decoding. The native table read uses this decoder
under the explicitly selected little-endian target binding and alignment two. -/
def checkedWord (memory : Memory) (state : memory.State)
    (pointer : Pointer memory.Allocation) (alignment : Nat) : Option Nat :=
  (checkedBytes memory state pointer 2 alignment).map Solanalib.Runtime.leNat

/-- A returned `Deref<Target = [u8]>` describes a valid current slice. Empty
slices may be dangling, but still have a nonnull representable address. -/
def SliceReady (memory : Memory) (state : memory.State)
    (slice : Slice memory.Allocation) : Prop :=
  if slice.length = 0 then
    0 < address memory state slice.pointer ∧ address memory state slice.pointer <
      Solanalib.Runtime.U64_LIMIT
  else RawReady memory state slice.pointer slice.length 1

instance (memory : Memory) (state : memory.State) (slice : Slice memory.Allocation) :
    Decidable (SliceReady memory state slice) := by
  unfold SliceReady
  infer_instance

/-- Validate a returned slice before using its length or base pointer. -/
def checkedSlice (memory : Memory) (state : memory.State)
    (slice : Slice memory.Allocation) : Option (Slice memory.Allocation) :=
  if slice.length = 0 then
    if 0 < address memory state slice.pointer ∧
        address memory state slice.pointer < Solanalib.Runtime.U64_LIMIT then some slice else none
  else (checkedBytes memory state slice.pointer slice.length 1).map fun _ => slice

/-- A legal forward `ptr.add`: representable signed offset, no address wrap,
and an endpoint in the same allocation or one-past. Adding zero is permitted
for the dangling nonnull pointer of an empty returned slice. -/
def AddReady (memory : Memory) (state : memory.State)
    (pointer : Pointer memory.Allocation) (delta : Nat) : Prop :=
  delta < ISIZE_LIMIT ∧ address memory state pointer + delta < Solanalib.Runtime.U64_LIMIT ∧
    (delta = 0 ∨ match memory.bytes state pointer.allocation with
      | none => False
      | some bytes => pointer.offset + delta ≤ bytes.length)

instance (memory : Memory) (state : memory.State)
    (pointer : Pointer memory.Allocation) (delta : Nat) :
    Decidable (AddReady memory state pointer delta) := by
  unfold AddReady
  cases memory.bytes state pointer.allocation <;> infer_instance

/-- Perform the modeled source pointer addition only when it is defined. -/
def checkedAdd (memory : Memory) (state : memory.State)
    (pointer : Pointer memory.Allocation) (delta : Nat) : Option (Pointer memory.Allocation) :=
  if AddReady memory state pointer delta then some (pointer.add delta) else none

/-- A successful complete read returns the requested number of actual bytes. -/
theorem readBytes_length {memory : Memory} {state : memory.State}
    {pointer : Pointer memory.Allocation} {length : Nat} {bytes : Solanalib.Runtime.Bytes}
    (read : readBytes memory state pointer length = some bytes) : bytes.length = length := by
  unfold readBytes at read
  cases present : memory.bytes state pointer.allocation with
  | none => simp [present] at read
  | some backing =>
    simp only [present, Option.bind_some] at read
    split at read
    next bound =>
      cases read
      exact Solanalib.Runtime.length_slice_of_le bound
    next => contradiction

/-- A successful checked read itself certifies the actual current bytes,
complete extent, address bounds and precise alignment, without a Ready premise. -/
theorem checkedBytes_reads {memory : Memory} {state : memory.State}
    {pointer : Pointer memory.Allocation} {length alignment : Nat} {bytes : Solanalib.Runtime.Bytes}
    (read : checkedBytes memory state pointer length alignment = some bytes) :
    readBytes memory state pointer length = some bytes ∧ bytes.length = length ∧
      0 < address memory state pointer ∧ address memory state pointer + length <
        Solanalib.Runtime.U64_LIMIT ∧
      length < ISIZE_LIMIT ∧ address memory state pointer % alignment = 0 := by
  unfold checkedBytes at read
  split at read
  next safe => exact ⟨read, readBytes_length read, safe⟩
  next => contradiction

/-- The mathematical check cannot manufacture a two-byte word from a missing
or short allocation; its value is the decode of exactly those current bytes. -/
theorem checkedWord_reads {memory : Memory} {state : memory.State}
    {pointer : Pointer memory.Allocation} {alignment value : Nat}
    (read : checkedWord memory state pointer alignment = some value) :
    ∃ bytes, readBytes memory state pointer 2 = some bytes ∧ bytes.length = 2 ∧
      value = Solanalib.Runtime.leNat bytes ∧ value < 65536 ∧ address memory state pointer %
        alignment = 0 := by
  unfold checkedWord at read
  cases checked : checkedBytes memory state pointer 2 alignment with
  | none => simp [checked] at read
  | some bytes =>
    simp only [checked, Option.map_some, Option.some.injEq] at read
    obtain ⟨present, length, _, _, _, aligned⟩ := checkedBytes_reads checked
    have bound := Solanalib.Runtime.leNat_lt bytes
    exact ⟨bytes, present, length, read.symm, by simpa [read, length] using bound, aligned⟩

/-- Read admission supplies actual bytes, not a padded or empty fallback. -/
theorem RawReady.checked {memory : Memory} {state : memory.State}
    {pointer : Pointer memory.Allocation} {length alignment : Nat}
    (ready : RawReady memory state pointer length alignment) :
    ∃ bytes, checkedBytes memory state pointer length alignment = some bytes ∧
      readBytes memory state pointer length = some bytes ∧ bytes.length = length := by
  obtain ⟨present, bounds⟩ := ready
  cases read : readBytes memory state pointer length with
  | none => simp [read] at present
  | some bytes =>
    exact ⟨bytes, by simp [checkedBytes, bounds, read], rfl, readBytes_length read⟩

/-- The checked two-byte read agrees with the unchanged raw observation and
proves its u16 width from those two bytes. -/
theorem RawReady.word {memory : Memory} {state : memory.State}
    {pointer : Pointer memory.Allocation} {alignment : Nat}
    (ready : RawReady memory state pointer 2 alignment) :
    checkedWord memory state pointer alignment = some (readWord memory state pointer) ∧
      readWord memory state pointer < 65536 := by
  obtain ⟨bytes, checked, read, length⟩ := ready.checked
  constructor
  · simp [checkedWord, checked, readWord, read]
  · have bound := Solanalib.Runtime.leNat_lt bytes
    simpa [readWord, read, length] using bound

/-- Valid slices survive checking with the same allocation identity and extent. -/
theorem SliceReady.checked {memory : Memory} {state : memory.State}
    {slice : Slice memory.Allocation} (ready : SliceReady memory state slice) :
    checkedSlice memory state slice = some slice := by
  unfold SliceReady at ready
  unfold checkedSlice
  split
  next empty => simp only [empty, ite_true] at ready; simp [ready]
  next nonempty =>
    simp only [nonempty, ite_false] at ready
    obtain ⟨bytes, checked, _, _⟩ := ready.checked
    simp [checked]

/-- Pointer checking preserves the original allocation and exact offset. -/
theorem AddReady.checked {memory : Memory} {state : memory.State}
    {pointer : Pointer memory.Allocation} {delta : Nat}
    (ready : AddReady memory state pointer delta) :
    checkedAdd memory state pointer delta = some (pointer.add delta) := by
  simp [checkedAdd, ready]

/-- Admission at every actual returned callback prefix. Footer bounds are
required only after the second callback returns; its unwind/terminal exits
occur before evaluating `first.length - 2`. -/
def CurrentReady (index : Index) (before : index.memory.State) (receiver : index.Receiver) : Prop :=
  ∀ first afterFirst, index.deref before receiver (.returned first afterFirst) →
    SliceReady index.memory afterFirst first ∧
    ∀ second afterSecond, index.deref afterFirst receiver (.returned second afterSecond) →
      SliceReady index.memory afterSecond second ∧ 2 ≤ first.length ∧ first.length ≤ second.length ∧
      AddReady index.memory afterSecond second.pointer (first.length - 2) ∧
      RawReady index.memory afterSecond (second.pointer.add (first.length - 2)) 2 1

/-- Execute precisely the reached footer operations after the second return. -/
def checkedFooter (memory : Memory) (state : memory.State) (firstLength : Nat)
    (second : Slice memory.Allocation) : Option UInt16 := do
  let _ ← checkedSlice memory state second
  if 2 ≤ firstLength ∧ firstLength ≤ second.length then
    let pointer ← checkedAdd memory state second.pointer (firstLength - 2)
    let value ← checkedWord memory state pointer 1
    pure (UInt16.ofNat value)
  else none

/-- The same two callback calls, with checked local operations at each reached
return. Abnormal callback exits keep their exact reason and state. -/
def checkedCurrent (index : Index) :
    Callback.Run index.memory.State index.Receiver UInt16 index.Unwind index.Terminal :=
  fun before receiver outcome =>
    Callback.bind index.deref (fun first afterFirst result =>
      checkedSlice index.memory afterFirst first = some first ∧
      Callback.bind index.deref (fun second afterSecond final =>
        ∃ value, checkedFooter index.memory afterSecond first.length second = some value ∧
          final = .returned value afterSecond)
        afterFirst receiver result) before receiver outcome

/-- Every finite raw exit has a defined checked derivation under admission;
this includes all provider alternatives, not one selected successful run. -/
theorem current_checked (index : Index) (before : index.memory.State)
    (receiver : index.Receiver) (ready : CurrentReady index before receiver)
    (outcome : Outcome index.memory.State UInt16 index.Unwind index.Terminal)
    (run : currentIndex index before receiver outcome) : checkedCurrent index before receiver
      outcome := by
  obtain ⟨firstExit, firstRun, tail⟩ := run
  refine ⟨firstExit, firstRun, ?_⟩
  cases firstExit with
  | unwound reason state => exact tail
  | terminated reason => exact tail
  | returned first afterFirst =>
    obtain ⟨firstReady, restReady⟩ := ready first afterFirst firstRun
    refine ⟨firstReady.checked, ?_⟩
    obtain ⟨secondExit, secondRun, final⟩ := tail
    refine ⟨secondExit, secondRun, ?_⟩
    cases secondExit with
    | unwound reason state => exact final
    | terminated reason => exact final
    | returned second afterSecond =>
      obtain ⟨secondReady, length, span, addition, load⟩ := restReady second afterSecond secondRun
      refine ⟨_, ?_, final⟩
      simp [checkedFooter, secondReady.checked, length, span, addition.checked, load.word.1]

/-- All actually reached count/table/base returns are admitted. An out-of-range
count result needs no table read, table alignment, or third callback. -/
def AtReady (index : Index) (before : index.memory.State)
    (args : index.Receiver × UInt64) : Prop :=
  ∀ first afterFirst, index.deref before args.1 (.returned first afterFirst) →
    SliceReady index.memory afterFirst first ∧ 2 ≤ first.length ∧
    RawReady index.memory afterFirst first.pointer 2 1 ∧
    (args.2.toNat < readWord index.memory afterFirst first.pointer →
      ∀ second afterSecond, index.deref afterFirst args.1 (.returned second afterSecond) →
        SliceReady index.memory afterSecond second ∧
        2 + 2 * args.2.toNat + 2 ≤ second.length ∧
        AddReady index.memory afterSecond second.pointer (2 + 2 * args.2.toNat) ∧
        RawReady index.memory afterSecond (second.pointer.add (2 + 2 * args.2.toNat)) 2 2 ∧
        ∀ third afterThird, index.deref afterSecond args.1 (.returned third afterThird) →
          SliceReady index.memory afterThird third ∧
          AddReady index.memory afterThird third.pointer
            (readWord index.memory afterSecond (second.pointer.add (2 + 2 * args.2.toNat))))

/-- The checked native-u16 table read, following its actual pointer addition. -/
def checkedTable (memory : Memory) (state : memory.State)
    (pointer : Pointer memory.Allocation) (index : UInt64) : Option Nat := do
  let target ← checkedAdd memory state pointer (2 + 2 * index.toNat)
  checkedWord memory state target 2

/-- The checked count, aligned table and third-state pointer computation,
sequenced with the same effectful callbacks and source-local early error. -/
def checkedAt (index : Index) : Callback.Run index.memory.State (index.Receiver × UInt64)
    (Except ProgramError.Value (Pointer index.memory.Allocation)) index.Unwind index.Terminal :=
  fun before args outcome =>
    Callback.bind index.deref (fun first afterFirst result =>
      checkedSlice index.memory afterFirst first = some first ∧ 2 ≤ first.length ∧
      ∃ count, checkedWord index.memory afterFirst first.pointer 1 = some count ∧
      if count ≤ args.2.toNat then result = .returned (.error .invalidInstructionData) afterFirst
      else
        Callback.bind index.deref (fun second afterSecond secondResult =>
          checkedSlice index.memory afterSecond second = some second ∧
          2 + 2 * args.2.toNat + 2 ≤ second.length ∧
          ∃ offset, checkedTable index.memory afterSecond second.pointer args.2 = some offset ∧
          Callback.bind index.deref (fun third afterThird final =>
            checkedSlice index.memory afterThird third = some third ∧
            ∃ target, checkedAdd index.memory afterThird third.pointer offset = some target ∧
              final = .returned (.ok target) afterThird)
            afterSecond args.1 secondResult)
          afterFirst args.1 result) before args.1 outcome

/-- Every finite lookup exit retains its exact count/error or all three
callback states while discharging every reached native load and addition. -/
theorem at_checked (index : Index) (before : index.memory.State)
    (args : index.Receiver × UInt64) (ready : AtReady index before args)
    (outcome : Outcome index.memory.State
      (Except ProgramError.Value (Pointer index.memory.Allocation)) index.Unwind index.Terminal)
    (run : instructionAt index before args outcome) : checkedAt index before args outcome := by
  obtain ⟨firstExit, firstRun, tail⟩ := run
  refine ⟨firstExit, firstRun, ?_⟩
  cases firstExit with
  | unwound reason state => exact tail
  | terminated reason => exact tail
  | returned first afterFirst =>
    obtain ⟨firstReady, countLength, countReady, restReady⟩ := ready first afterFirst firstRun
    refine ⟨firstReady.checked, countLength, _, countReady.word.1, ?_⟩
    dsimp only at tail
    split at tail
    next outside => simpa only [outside, ite_true] using tail
    next inside =>
      simp only [inside, ite_false]
      obtain ⟨secondExit, secondRun, rest⟩ := tail
      refine ⟨secondExit, secondRun, ?_⟩
      cases secondExit with
      | unwound reason state => exact rest
      | terminated reason => exact rest
      | returned second afterSecond =>
        obtain ⟨secondReady, tableLength, addition, tableReady, lastReady⟩ :=
          restReady (Nat.lt_of_not_ge inside) second afterSecond secondRun
        refine ⟨secondReady.checked, tableLength,
          readWord index.memory afterSecond (second.pointer.add (2 + 2 * args.2.toNat)), ?_, ?_⟩
        · simp [checkedTable, addition.checked, tableReady.word.1]
        · obtain ⟨thirdExit, thirdRun, final⟩ := rest
          refine ⟨thirdExit, thirdRun, ?_⟩
          cases thirdExit with
          | unwound reason state => exact final
          | terminated reason => exact final
          | returned third afterThird =>
            obtain ⟨thirdReady, finalAdd⟩ := lastReady third afterThird thirdRun
            exact ⟨thirdReady.checked, _, finalAdd.checked, final⟩

/-- Defined account-count read, pointer addition and complete Address region.
The caller has an introspected pointer, not a promised full serialization. -/
def ProgramReady (memory : Memory) (state : memory.State)
    (instruction : Pointer memory.Allocation) : Prop :=
  RawReady memory state instruction 2 1 ∧
    AddReady memory state instruction (programOffset memory state instruction) ∧
    RawReady memory state (programId memory state instruction) 32 1

instance (memory : Memory) (state : memory.State) (instruction : Pointer memory.Allocation) :
    Decidable (ProgramReady memory state instruction) := by
  unfold ProgramReady
  infer_instance

/-- Compute the program pointer only after a real count read and validate the
complete returned 32-byte reference in the same current memory. -/
def checkedProgram (memory : Memory) (state : memory.State)
    (instruction : Pointer memory.Allocation) : Option (Pointer memory.Allocation) := do
  let count ← checkedWord memory state instruction 1
  let target ← checkedAdd memory state instruction (2 + 33 * count)
  let _ ← checkedBytes memory state target 32 1
  pure target

/-- Admission yields the exact pointer through successful current-memory loads. -/
theorem program_checked (memory : Memory) (state : memory.State)
    (instruction : Pointer memory.Allocation) (ready : ProgramReady memory state instruction) :
    checkedProgram memory state instruction = some (programId memory state instruction) := by
  obtain ⟨count, addition, body⟩ := ready
  obtain ⟨bytes, checked, _, _⟩ := body.checked
  simp only [checkedProgram, count.word.1]
  change (checkedAdd memory state instruction (programOffset memory state instruction)).bind _ = _
  rw [addition.checked]
  change (checkedBytes memory state (programId memory state instruction) 32 1).bind _ = _
  rw [checked]
  rfl

/-- Defined count/length reads, pointer additions and the full returned slice.
An empty returned slice still requires both preceding two-byte reads. -/
def DataReady (memory : Memory) (state : memory.State)
    (instruction : Pointer memory.Allocation) : Prop :=
  RawReady memory state instruction 2 1 ∧
    AddReady memory state instruction (dataOffset memory state instruction) ∧
    RawReady memory state (instruction.add (dataOffset memory state instruction)) 2 1 ∧
    AddReady memory state instruction (dataOffset memory state instruction + 2) ∧
    SliceReady memory state (instructionData memory state instruction)

instance (memory : Memory) (state : memory.State) (instruction : Pointer memory.Allocation) :
    Decidable (DataReady memory state instruction) := by
  unfold DataReady
  infer_instance

/-- Decode from actual current count/length bytes, then form the checked slice. -/
def checkedData (memory : Memory) (state : memory.State)
    (instruction : Pointer memory.Allocation) : Option (Slice memory.Allocation) := do
  let count ← checkedWord memory state instruction 1
  let lengthPointer ← checkedAdd memory state instruction (2 + 33 * count + 32)
  let length ← checkedWord memory state lengthPointer 1
  let dataPointer ← checkedAdd memory state instruction (2 + 33 * count + 32 + 2)
  checkedSlice memory state ⟨dataPointer, length⟩

/-- Every admitted data observer returns the precise checked current slice. -/
theorem data_checked (memory : Memory) (state : memory.State)
    (instruction : Pointer memory.Allocation) (ready : DataReady memory state instruction) :
    checkedData memory state instruction = some (instructionData memory state instruction) := by
  obtain ⟨count, lengthAdd, lengthRead, dataAdd, slice⟩ := ready
  simp only [checkedData, count.word.1]
  change (checkedAdd memory state instruction (dataOffset memory state instruction)).bind _ = _
  rw [lengthAdd.checked]
  change (checkedWord memory state (instruction.add (dataOffset memory state instruction)) 1).bind
    _ = _
  rw [lengthRead.word.1]
  change (checkedAdd memory state instruction (dataOffset memory state instruction + 2)).bind _ = _
  rw [dataAdd.checked]
  exact slice.checked

/-- Generic source domain and exact raw/checked current-index execution postcondition. -/
def currentFamily : Family where
  Index := Index
  State := fun index => index.memory.State
  Args := Index.Receiver
  Value := fun _ => UInt16
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => ⟨CurrentReady index, fun before receiver outcome =>
    currentIndex index before receiver outcome ∧ checkedCurrent index before receiver outcome⟩

/-- The unchanged raw two-callback reference run used on the admitted domain of currentFamily. -/
def currentRun : FamilyRun currentFamily := currentIndex

theorem current_reference : FamilyReference currentFamily currentRun := by
  intro index before receiver outcome ready step
  exact ⟨step, current_checked index before receiver ready outcome step⟩

/-- Generic branch-sensitive lookup domain and exact raw/checked execution postcondition. -/
def atFamily : Family where
  Index := Index
  State := fun index => index.memory.State
  Args := fun index => index.Receiver × UInt64
  Value := fun index => Except ProgramError.Value (Pointer index.memory.Allocation)
  Unwind := Index.Unwind
  Terminal := Index.Terminal
  contract := fun index => ⟨AtReady index, fun before args outcome =>
    instructionAt index before args outcome ∧ checkedAt index before args outcome⟩

/-- The unchanged raw count/table/third-base reference relation. -/
def atRun : FamilyRun atFamily := instructionAt

theorem at_reference : FamilyReference atFamily atRun := by
  intro index before args outcome ready step
  exact ⟨step, at_checked index before args ready outcome step⟩

/-- Program-reference source domain with checked construction and all 32 current bytes. -/
def programFamily : Family where
  Index := Memory
  State := Memory.State
  Args := fun memory => Pointer memory.Allocation
  Value := fun memory => Pointer memory.Allocation
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun memory => .returning (ProgramReady memory)
    (fun before pointer value after => after = before ∧ value = programId memory before pointer ∧
      checkedProgram memory before pointer = some value ∧
      ∃ bytes, readBytes memory before value 32 = some bytes ∧ bytes.length = 32)

/-- The unchanged mathematical program-pointer result and preserved state. -/
def programRun : FamilyRun programFamily := fun memory =>
  returnsOf fun before pointer => (programId memory before pointer, before)

theorem program_reference : FamilyReference programFamily programRun := by
  intro memory
  apply (Solanalib.Contracts.Model.realized_iff_holds _ _).mp
  intro before pointer ready
  obtain ⟨bytes, _, read, length⟩ := ready.2.2.checked
  exact ⟨rfl, rfl, program_checked memory before pointer ready, bytes, read, length⟩

/-- Data-reference source domain with checked construction and complete current payload. -/
def dataFamily : Family where
  Index := Memory
  State := Memory.State
  Args := fun memory => Pointer memory.Allocation
  Value := fun memory => Slice memory.Allocation
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun memory => .returning (DataReady memory)
    (fun before pointer value after => after = before ∧ value = instructionData memory before
      pointer ∧
      checkedData memory before pointer = some value ∧
      (value.length = 0 ∨ ∃ bytes, readBytes memory before value.pointer value.length = some bytes ∧
        bytes.length = value.length))

/-- The unchanged mathematical data descriptor and preserved state. -/
def dataRun : FamilyRun dataFamily := fun memory =>
  returnsOf fun before pointer => (instructionData memory before pointer, before)

theorem data_reference : FamilyReference dataFamily dataRun := by
  intro memory
  apply (Solanalib.Contracts.Model.realized_iff_holds _ _).mp
  intro before pointer ready
  refine ⟨rfl, rfl, data_checked memory before pointer ready, ?_⟩
  by_cases empty : (instructionData memory before pointer).length = 0
  · exact Or.inl empty
  · have valid := ready.2.2.2.2
    simp only [SliceReady, empty, ite_false] at valid
    obtain ⟨bytes, _, read, length⟩ := valid.checked
    exact Or.inr ⟨bytes, read, length⟩

namespace Sample

/-- A concrete current-memory witness containing the 78-byte serialization. -/
def memory : Memory where
  State := Nat
  Allocation := Unit
  bytes := fun _ _ => some InstructionsSysvar.Witness.bytes
  baseAddress := fun _ _ => 4096

/-- The full nonempty slice returned by the mathematical witness callback. -/
def slice : Slice Unit := ⟨⟨(), 0⟩, 78⟩

/-- A concrete Deref interpretation advancing its state once for each call. -/
def index : Index where
  memory := memory
  Receiver := Unit
  Unwind := String
  Terminal := String
  deref := Callback.ofFunction fun (before : Nat) (_ : Unit) => .returned slice (before + 1)

theorem current_execution : FamilyHasExecution currentFamily currentRun index := by
  refine ⟨(0 : Nat), (), .returned (0 : UInt16) (2 : Nat), by
    intro first afterFirst firstRun
    cases firstRun
    refine ⟨by dsimp [index, memory, slice, SliceReady, RawReady, AddReady]; decide, ?_⟩
    intro second afterSecond secondRun
    cases secondRun
    dsimp [index, memory, slice, SliceReady, RawReady, AddReady]
    decide, ?_⟩
  exact ⟨.returned slice (1 : Nat), rfl,
    ⟨.returned slice (2 : Nat), rfl, rfl⟩⟩

theorem at_execution : FamilyHasExecution atFamily atRun index := by
  refine ⟨(0 : Nat), ((), 0), .returned (.ok ⟨(), 4⟩) (3 : Nat), by
    intro first afterFirst firstRun
    cases firstRun
    refine ⟨by dsimp [index, memory, slice, SliceReady, RawReady, AddReady]; decide, by decide,
      by dsimp [index, memory, slice, SliceReady, RawReady, AddReady]; decide, ?_⟩
    intro inside second afterSecond secondRun
    cases secondRun
    refine ⟨by dsimp [index, memory, slice, SliceReady, RawReady, AddReady]; decide, by decide,
      by dsimp [index, memory, slice, SliceReady, RawReady, AddReady]; decide,
      by dsimp [index, memory, slice, SliceReady, RawReady, AddReady]; decide, ?_⟩
    intro third afterThird thirdRun
    cases thirdRun
    dsimp [index, memory, slice, SliceReady, RawReady, AddReady]
    decide, ?_⟩
  exact ⟨.returned slice (1 : Nat), rfl,
    ⟨.returned slice (2 : Nat), rfl,
      ⟨.returned slice (3 : Nat), rfl, rfl⟩⟩⟩

theorem program_execution : FamilyHasExecution programFamily programRun memory :=
  ⟨(0 : Nat), ⟨(), 4⟩, .returned ⟨(), 39⟩ (0 : Nat),
    by change ProgramReady memory (0 : Nat) ⟨(), 4⟩; dsimp [memory, ProgramReady, DataReady,
      RawReady, AddReady, SliceReady]; decide, rfl⟩

theorem data_execution : FamilyHasExecution dataFamily dataRun memory :=
  ⟨(0 : Nat), ⟨(), 4⟩, .returned ⟨⟨(), 73⟩, 3⟩ (0 : Nat),
    by change DataReady memory (0 : Nat) ⟨(), 4⟩; dsimp [memory, ProgramReady, DataReady, RawReady,
      AddReady, SliceReady]; decide, rfl⟩

end Sample

end Solanalib.Specs.Core.InstructionsSysvar.Generic
