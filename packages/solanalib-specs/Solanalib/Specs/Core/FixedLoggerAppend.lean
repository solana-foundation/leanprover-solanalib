/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.FixedLogger

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.FixedLogger

def StateValid {Aux Value Unwind Terminal : Type} (capacity : Nat) :
    Outcome (Buffer × Aux) Value Unwind Terminal → Prop
  | .returned _ after | .unwound _ after => after.1.Valid capacity
  | .terminated _ => True

/-- The unsafe Log trait must preserve the extent of the supplied slice and report
only bytes that it initialized. Unwind retains partial tail writes. -/
def WriterSafe {Aux Value Unwind Terminal : Type}
    (write : Callback.Run (List (Option UInt8) × Aux) Value Nat Unwind Terminal) : Prop :=
  ∀ before value produced, write before value produced →
    match produced with
    | .returned count after => after.1.length = before.1.length ∧
      count ≤ before.1.length ∧ initialized (after.1.take count)
    | .unwound _ after => after.1.length = before.1.length
    | .terminated _ => True

structure AppendIndex where
  capacity : Nat
  Ref : Type
  Value : Type
  Aux : Type
  Unwind : Type
  Terminal : Type
  write : Callback.Run (List (Option UInt8) × Aux) Value Nat Unwind Terminal
  writerSafe : WriterSafe write
  drop : Callback.Run Aux Value Unit Unwind Terminal
  double : Owned.DoubleUnwind Aux Unwind Terminal

abbrev AppendIndex.World (index : AppendIndex) := Buffer × index.Aux

/-- Reattach the actual tail after a callback. The prefix and length field were
outside its mutable slice and therefore retain their existing contents. -/
def Buffer.rejoin (before : Buffer) (tail : List (Option UInt8)) (count : Nat) : Buffer :=
  ⟨before.storage.take before.len ++ tail, before.len + count⟩

/-- The defensive overcount branch is retained in the operational model.
Under the truthful-count contract of the unsafe Log trait it is unreachable. -/
def Buffer.finishWrite (capacity : Nat) (before : Buffer) (tail : List (Option UInt8))
    (count : Nat) : Buffer :=
  let next := before.rejoin tail count
  if capacity < next.len then ({ next with len := capacity }).markFull capacity else next

def finishWriter (index : AppendIndex) (receiver : index.Ref) (before : Buffer)
    (produced : Outcome (List (Option UInt8) × index.Aux) Nat index.Unwind index.Terminal) :
    Outcome index.World index.Ref index.Unwind index.Terminal :=
  match produced with
  | .returned count after =>
    .returned receiver (before.finishWrite index.capacity after.1 count, after.2)
  | .unwound reason after => .unwound reason (before.rejoin after.1 0, after.2)
  | .terminated reason => .terminated reason

def appendBody (index : AppendIndex) (before : index.World) (args : index.Ref × index.Value)
    (outcome : Outcome index.World index.Ref index.Unwind index.Terminal) : Prop :=
  if before.1.len = index.capacity then
    outcome = .returned args.1 (before.1.markFull index.capacity, before.2)
  else ∃ produced, index.write (before.1.storage.drop before.1.len, before.2) args.2 produced ∧
    outcome = finishWriter index args.1 before.1 produced

def liftDrop (index : AppendIndex) (buffer : Buffer)
    (produced : Outcome index.Aux Unit index.Unwind index.Terminal) :
    Outcome index.World Unit index.Unwind index.Terminal :=
  match produced with
  | .returned value after => .returned value (buffer, after)
  | .unwound reason after => .unwound reason (buffer, after)
  | .terminated reason => .terminated reason

def dropAction (index : AppendIndex) (value : index.Value) :
    Owned.DropAction index.World index.Unwind index.Terminal :=
  fun before outcome => ∃ produced,
    index.drop before.2 value produced ∧ outcome = liftDrop index before.1 produced

def doubleUnwind (index : AppendIndex) : Owned.DoubleUnwind index.World index.Unwind index.Terminal
  :=
  fun before original later terminal => index.double before.2 original later terminal

/-- Even a full buffer drops the by-value argument once. A formatter unwind
drops it in the actual unwind state; a second unwind uses the terminal policy. -/
def appendAt (index : AppendIndex) (before : index.World) (args : index.Ref × index.Value)
    (outcome : Outcome index.World index.Ref index.Unwind index.Terminal) : Prop :=
  ∃ pending, appendBody index before args pending ∧
    Owned.cleanup (doubleUnwind index) [dropAction index args.2] pending outcome

theorem initialized_append {left right : List (Option UInt8)}
    (one : initialized left) (two : initialized right) : initialized (left ++ right) := by
  intro byte member
  rcases List.mem_append.mp member with member | member
  · exact one byte member
  · exact two byte member

theorem initialized_set {bytes : List (Option UInt8)} (ready : initialized bytes)
    (index : Nat) (value : UInt8) : initialized (bytes.set index (some value)) := by
  intro byte member
  rcases List.mem_or_eq_of_mem_set member with prior | equal
  · exact ready byte prior
  · subst byte
    rfl

theorem Buffer.markFull_valid {capacity : Nat} {buffer : Buffer}
    (ready : buffer.Valid capacity) (full : buffer.len = capacity) :
    (buffer.markFull capacity).Valid capacity := by
  by_cases zero : capacity = 0
  · simpa [Buffer.markFull, zero] using ready
  · have init : initialized buffer.storage := by
      simpa only [full, ← ready.1, List.take_length] using ready.2.2
    simp only [Buffer.markFull, zero, ↓reduceIte]
    refine ⟨by simp [ready.1], ready.2.1, ?_⟩
    change initialized ((buffer.storage.set (capacity - 1) (some 64)).take buffer.len)
    have length : (buffer.storage.set (capacity - 1) (some 64)).length = capacity := by
      simp [ready.1]
    rw [List.take_of_length_le (by rw [length, full]; exact Nat.le_refl _)]
    exact initialized_set init (capacity - 1) 64

theorem Buffer.rejoin_valid {capacity : Nat} {before : Buffer} {tail : List (Option UInt8)}
    {count : Nat} (ready : before.Valid capacity)
    (length : tail.length = capacity - before.len) (bound : count ≤ tail.length)
    (written : initialized (tail.take count)) : (before.rejoin tail count).Valid capacity := by
  have prefixLength : (before.storage.take before.len).length = before.len := by
    simp [List.length_take, ready.1, Nat.min_eq_left ready.2.1]
  have oldBound : before.len ≤ capacity := ready.2.1
  have countBound : before.len + count ≤ capacity := by omega
  refine ⟨?_, countBound, ?_⟩
  · simp only [Buffer.rejoin, List.length_append, prefixLength, length]
    omega
  · have takePrefix : (before.storage.take before.len).take (before.len + count) =
        before.storage.take before.len := by
      apply List.take_of_length_le
      omega
    simpa only [Buffer.rejoin, List.take_append, takePrefix, prefixLength,
      Nat.add_sub_cancel_left] using initialized_append ready.2.2 written

theorem finishWriter_valid (index : AppendIndex) (before : index.World) (args : index.Ref ×
  index.Value)
    (ready : before.1.Valid index.capacity)
    (produced : Outcome (List (Option UInt8) × index.Aux) Nat index.Unwind index.Terminal)
    (called : index.write (before.1.storage.drop before.1.len, before.2) args.2 produced) :
    StateValid index.capacity (finishWriter index args.1 before.1 produced) := by
  have safe := index.writerSafe _ _ _ called
  cases produced with
  | returned count after =>
    obtain ⟨same, countBound, initialized⟩ := safe
    have length : after.1.length = index.capacity - before.1.len := by
      simpa [List.length_drop, ready.1] using same
    have bound : count ≤ after.1.length := by omega
    have valid := Buffer.rejoin_valid ready length bound initialized
    simpa [finishWriter, StateValid, Buffer.finishWrite, Nat.not_lt.mpr valid.2.1] using valid
  | unwound reason after =>
    have length : after.1.length = index.capacity - before.1.len := by
      simpa [List.length_drop, ready.1] using safe
    exact Buffer.rejoin_valid ready length (Nat.zero_le _) (by simp [initialized])
  | terminated _ => trivial

theorem appendBody_valid (index : AppendIndex) {before : index.World} {args : index.Ref ×
  index.Value}
    {outcome : Outcome index.World index.Ref index.Unwind index.Terminal}
    (ready : before.1.Valid index.capacity) (step : appendBody index before args outcome) :
    StateValid index.capacity outcome := by
  unfold appendBody at step
  split at step
  · rename_i full
    cases step
    exact Buffer.markFull_valid ready full
  · obtain ⟨produced, called, rfl⟩ := step
    exact finishWriter_valid index before args ready produced called

theorem cleanup_valid (index : AppendIndex) (value : index.Value)
    {pending outcome : Outcome index.World index.Ref index.Unwind index.Terminal}
    (ready : StateValid index.capacity pending)
    (cleaned : Owned.cleanup (doubleUnwind index) [dropAction index value] pending outcome) :
    StateValid index.capacity outcome := by
  cases pending with
  | returned result before =>
    obtain ⟨dropped, ⟨produced, _, rfl⟩, continued⟩ := cleaned
    cases produced with
    | returned _ _ => cases continued; exact ready
    | unwound _ _ => cases continued; exact ready
    | terminated _ => cases continued; trivial
  | unwound reason before =>
    obtain ⟨dropped, ⟨produced, _, rfl⟩, continued⟩ := cleaned
    cases produced with
    | returned _ _ => cases continued; exact ready
    | unwound _ _ => obtain ⟨_, _, rfl⟩ := continued; trivial
    | terminated _ => cases continued; trivial
  | terminated reason => cases cleaned; trivial

def appendFamily : Family where
  Index := AppendIndex
  State := AppendIndex.World
  Args := fun index => index.Ref × index.Value
  Value := AppendIndex.Ref
  Unwind := AppendIndex.Unwind
  Terminal := AppendIndex.Terminal
  contract := fun index => {
    requires := fun before _ => before.1.Valid index.capacity
    post := fun before args outcome => appendAt index before args outcome ∧ StateValid
      index.capacity outcome }

def appendRun : FamilyRun appendFamily := appendAt

theorem append_reference : FamilyReference appendFamily appendRun := by
  rintro index before args outcome ready step
  obtain ⟨pending, ran, cleaned⟩ := step
  exact ⟨⟨pending, ran, cleaned⟩, cleanup_valid index args.2 (appendBody_valid index ready ran)
    cleaned⟩

/-- A concrete copying formatter is used by the string and unsigned profiles.
It writes exactly the formatted prefix and preserves the remaining tail. -/
def renderedWrite {Value : Type} (render : Value → Solanalib.Runtime.Bytes)
    (before : List (Option UInt8) × Unit) (value : Value) :
    Outcome (List (Option UInt8) × Unit) Nat Empty Unit :=
  let bytes := formatBytes before.1.length (render value)
  .returned bytes.length (bytes.map some ++ before.1.drop bytes.length, ())

theorem renderedWrite_safe {Value : Type} (render : Value → Solanalib.Runtime.Bytes) :
    WriterSafe (Callback.ofFunction (renderedWrite render)) := by
  rintro before value produced called
  cases called
  have bound : (formatBytes before.1.length (render value)).length ≤ before.1.length := by
    rw [formatBytes_length]
    exact Nat.min_le_left _ _
  refine ⟨?_, bound, ?_⟩
  · simp only [List.length_append, List.length_map, List.length_drop]
    omega
  · simp only [List.take_append, List.length_map,
      Nat.sub_self, List.take_zero, List.append_nil]
    rw [List.take_of_length_le (by simp)]
    intro byte member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
    rfl

def renderedIndex {Value : Type} (capacity : Nat) (render : Value → Solanalib.Runtime.Bytes) :
  AppendIndex where
  capacity := capacity
  Ref := Nat
  Value := Value
  Aux := Unit
  Unwind := Empty
  Terminal := Unit
  write := Callback.ofFunction (renderedWrite render)
  writerSafe := renderedWrite_safe render
  drop := Callback.ofFunction (fun before _ => .returned () before)
  double := fun _ reason _ _ => nomatch reason

def stringIndex (capacity : Nat) : AppendIndex := renderedIndex capacity Log.utf8Bytes
def u64Index (capacity : Nat) : AppendIndex :=
  renderedIndex capacity (fun (value : UInt64) => Log.utf8Bytes (toString value.toNat))

def appendSample : AppendIndex := stringIndex 0

theorem append_hasExecution : FamilyHasExecution appendFamily appendRun appendSample := by
  let before : appendSample.World := (Buffer.empty 0, ())
  let args : appendSample.Ref × appendSample.Value := ((17 : Nat), "a")
  let pending : Outcome appendSample.World appendSample.Ref Empty Unit := .returned args.1 before
  refine ⟨before, args, pending, Buffer.empty_valid 0, pending, ?_, ?_⟩
  · rfl
  · exact ⟨.returned () before, ⟨.returned () (), rfl, rfl⟩, rfl⟩

end Solanalib.Specs.Core.FixedLogger
