/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Family
public import Solanalib.Specs.Core.Log
public import Solanalib.Specs.Core.OwnedCleanup

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.FixedLogger

/-- Every byte records whether MaybeUninit storage has actually been written.
Bytes after the current prefix remain part of the same fixed allocation. -/
structure Buffer where
  storage : List (Option UInt8)
  len : Nat
  deriving DecidableEq, Repr

def Buffer.empty (capacity : Nat) : Buffer := ⟨List.replicate capacity none, 0⟩
def Buffer.bytes (buffer : Buffer) : Solanalib.Runtime.Bytes :=
  (buffer.storage.take buffer.len).map (fun byte => byte.getD 0)

def initialized (bytes : List (Option UInt8)) : Prop := ∀ byte ∈ bytes, byte.isSome = true

/-- Reading the prefix is legal without requiring initialization of unused
storage. Source pointer/ownership and usize bounds are separate obligations. -/
def Buffer.Valid (capacity : Nat) (buffer : Buffer) : Prop :=
  buffer.storage.length = capacity ∧ buffer.len ≤ capacity ∧
    initialized (buffer.storage.take buffer.len)

theorem Buffer.empty_valid (capacity : Nat) : (Buffer.empty capacity).Valid capacity := by
  simp [Buffer.Valid, Buffer.empty, initialized]

def defaultFamily : Family where
  Index := ULift.{1} Nat
  State := fun _ => Unit
  Args := fun _ => Unit
  Value := fun _ => Buffer
  Unwind := fun _ => Empty
  Terminal := fun _ => Empty
  contract := fun capacity => .returning (fun _ _ => True)
    (fun before _ value after => after = before ∧ value = Buffer.empty capacity.down ∧ value.Valid
      capacity.down)

def defaultRun : FamilyRun defaultFamily :=
  fun capacity => returnsOf (fun before _ => (Buffer.empty capacity.down, before))

theorem default_reference : FamilyReference defaultFamily defaultRun := by
  intro capacity
  apply (Solanalib.Contracts.Model.realized_iff_holds _ _).mp
  intro _ _ _
  exact ⟨rfl, rfl, Buffer.empty_valid capacity.down⟩

def defaultSample : ULift.{1} Nat := ⟨0⟩
theorem default_hasExecution : FamilyHasExecution defaultFamily defaultRun defaultSample :=
  ⟨(), (), .returned (Buffer.empty 0) (), trivial, rfl⟩

/-- Marking a full buffer changes only its final initialized byte. Zero-sized
loggers remain empty and do not perform the unchecked BUFFER - 1 access. -/
def Buffer.markFull (capacity : Nat) (buffer : Buffer) : Buffer :=
  if capacity = 0 then buffer
  else { buffer with storage := buffer.storage.set (capacity - 1) (some 64) }

/-- A default-argument formatter copies a byte prefix, replacing its final byte
by '@' exactly when the text itself does not fit. UTF-8 boundaries are not repaired. -/
def formatBytes (capacity : Nat) (bytes : Solanalib.Runtime.Bytes) : Solanalib.Runtime.Bytes :=
  let copied := bytes.take capacity
  if bytes.length ≤ capacity then copied else copied.set (capacity - 1) 64

def formatString (capacity : Nat) (value : String) : Solanalib.Runtime.Bytes :=
  formatBytes capacity (Log.utf8Bytes value)

/-- The unsigned decimal profile corresponds to the u64 Log implementation at
the empty formatting-argument slice used by Logger::append. -/
def formatU64 (capacity : Nat) (value : UInt64) : Solanalib.Runtime.Bytes :=
  formatBytes capacity (Log.utf8Bytes (toString value.toNat))

theorem formatBytes_length (capacity : Nat) (bytes : Solanalib.Runtime.Bytes) :
    (formatBytes capacity bytes).length = min capacity bytes.length := by
  unfold formatBytes
  split <;> simp

/-- A sink describes the actual logging dependency, including no finite
return, without giving it permission to overwrite the borrowed logger. -/
structure LogIndex where
  capacity : Nat
  Aux : Type
  Unwind : Type
  Terminal : Type
  sink : Callback.Run Aux Solanalib.Runtime.Bytes Unit Unwind Terminal

abbrev LogIndex.World (index : LogIndex) := Buffer × index.Aux

def liftSinkOutcome (index : LogIndex) (buffer : Buffer)
    (produced : Outcome index.Aux Unit index.Unwind index.Terminal) :
    Outcome index.World Unit index.Unwind index.Terminal :=
  match produced with
  | .returned value after => .returned value (buffer, after)
  | .unwound reason after => .unwound reason (buffer, after)
  | .terminated reason => .terminated reason

def logAt (index : LogIndex) (before : index.World) (_ : Unit)
    (outcome : Outcome index.World Unit index.Unwind index.Terminal) : Prop :=
  ∃ produced, index.sink before.2 before.1.bytes produced ∧
    outcome = liftSinkOutcome index before.1 produced

def logFamily : Family where
  Index := LogIndex
  State := LogIndex.World
  Args := fun _ => Unit
  Value := fun _ => Unit
  Unwind := LogIndex.Unwind
  Terminal := LogIndex.Terminal
  contract := fun index => {
    requires := fun before _ => before.1.Valid index.capacity
    post := fun before args outcome => logAt index before args outcome ∧
      match outcome with
      | .returned _ after | .unwound _ after => after.1 = before.1 ∧ after.1.Valid index.capacity
      | .terminated _ => True }

def logRun : FamilyRun logFamily := logAt

theorem log_reference : FamilyReference logFamily logRun := by
  rintro index before args outcome ready step
  refine ⟨step, ?_⟩
  obtain ⟨produced, _, rfl⟩ := step
  cases produced with
  | returned _ _ => exact ⟨rfl, ready⟩
  | unwound _ _ => exact ⟨rfl, ready⟩
  | terminated _ => trivial

def logSample : LogIndex :=
  ⟨0, List Solanalib.Runtime.Bytes, Empty, Unit,
    Callback.ofFunction (fun before bytes => .returned () (before ++ [bytes]))⟩

theorem log_hasExecution : FamilyHasExecution logFamily logRun logSample :=
  ⟨(Buffer.empty 0, []), (), .returned () (Buffer.empty 0, [[]]),
    Buffer.empty_valid 0, .returned () [[]], rfl, rfl⟩

/-- A terminal sink result is forwarded with no invented logger post-state. -/
theorem log_terminal (index : LogIndex) (before : index.World) (reason : index.Terminal)
    (called : index.sink before.2 before.1.bytes (.terminated reason)) :
    logAt index before () (.terminated reason) := ⟨.terminated reason, called, rfl⟩

end Solanalib.Specs.Core.FixedLogger
