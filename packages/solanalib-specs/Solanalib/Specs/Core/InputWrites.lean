/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Memory

@[expose] public section

set_option autoImplicit false

/-!
# The input-buffer effect of source output stores

The runtime request model returns output bytes before the source stores them. This module
projects those stores onto the serialized input buffer. Private stack and heap output bytes
are outside that projection. Projection is total and grants no memory permission: successful
source translation and the relation between source pointers and VM addresses remain separate.

For an in-bounds store in configuration L, the projection agrees with
`Solanalib.Runtime.storeRegion`.
It does not model the translation-time account growth of configurations S and D.
-/

namespace Solanalib.Specs.Core.InputWrites

variable (inputStart : Nat)

/-- The part of a byte write that intersects the serialized input buffer. -/
def project (inputStart : Nat) (buffer : Solanalib.Runtime.Bytes) (address : Nat) (bytes :
  Solanalib.Runtime.Bytes) : Solanalib.Runtime.Bytes :=
  let offset := address - inputStart
  let written := (bytes.drop (inputStart - address)).take (buffer.length - offset)
  Solanalib.Runtime.writeAt buffer offset written

/-- An empty write leaves the complete buffer unchanged. -/
theorem project_empty (buffer : Solanalib.Runtime.Bytes) (address : Nat) : project inputStart
  buffer address [] = buffer := by
  simp [project, Solanalib.Runtime.writeAt]

/-- Projection preserves the length of the input allocation, including writes outside it. -/
theorem project_length (buffer : Solanalib.Runtime.Bytes) (address : Nat) (bytes :
  Solanalib.Runtime.Bytes) :
    (project inputStart buffer address bytes).length = buffer.length := by
  unfold project
  dsimp
  by_cases room : address - inputStart ≤ buffer.length
  · apply Solanalib.Runtime.length_writeAt
    simp only [List.length_take, List.length_drop]
    omega
  · have empty : buffer.length - (address - inputStart) = 0 := by omega
    simp [empty, Solanalib.Runtime.writeAt]

/-- A write wholly below the input region affects only private memory. -/
theorem project_below (buffer : Solanalib.Runtime.Bytes) (address : Nat) (bytes :
  Solanalib.Runtime.Bytes)
    (outside : address + bytes.length ≤ inputStart) :
    project inputStart buffer address bytes = buffer := by
  have empty : bytes.length ≤ inputStart - address := by omega
  simp [project, List.drop_eq_nil_of_le empty, Solanalib.Runtime.writeAt]

/-- A write wholly above the serialized buffer does not change its bytes. -/
theorem project_above (buffer : Solanalib.Runtime.Bytes) (address : Nat) (bytes :
  Solanalib.Runtime.Bytes)
    (outside : buffer.length ≤ address - inputStart) :
    project inputStart buffer address bytes = buffer := by
  have empty : buffer.length - (address - inputStart) = 0 := by omega
  simp [project, empty, Solanalib.Runtime.writeAt]

/-- Inside the input allocation, projection is exactly the ordinary byte overwrite. -/
theorem project_inside (buffer : Solanalib.Runtime.Bytes) (address : Nat) (bytes :
  Solanalib.Runtime.Bytes)
    (lower : inputStart ≤ address)
    (bounds : address - inputStart + bytes.length ≤ buffer.length) :
    project inputStart buffer address bytes = Solanalib.Runtime.writeAt buffer (address -
      inputStart) bytes := by
  have fits : bytes.length ≤ buffer.length - (address - inputStart) := by omega
  simp [project, Nat.sub_eq_zero_of_le lower, List.take_of_length_le fits]

/-- One actual source write, retaining every invocation field other than input bytes. -/
def store (inputStart : Nat) (before : Solanalib.Runtime.InvState) (address : Nat) (bytes :
  Solanalib.Runtime.Bytes) : Solanalib.Runtime.InvState :=
  { before with buf := project inputStart before.buf address bytes }

/-- The request-phase view uses one fixed buffer snapshot and all actual non-buffer fields. -/
def requestState (buffer : Solanalib.Runtime.Bytes) (actual : Solanalib.Runtime.InvState) :
  Solanalib.Runtime.InvState :=
  { actual with buf := buffer }

/-- Projecting an output store back to a fixed request-phase snapshot changes no other field. -/
theorem requestState_store (buffer : Solanalib.Runtime.Bytes) (before : Solanalib.Runtime.InvState)
    (address : Nat) (bytes : Solanalib.Runtime.Bytes) :
    requestState buffer (store inputStart before address bytes) = requestState buffer before := rfl

/-- Empty source stores preserve the actual invocation state. -/
theorem store_empty (before : Solanalib.Runtime.InvState) (address : Nat) : store inputStart before
  address [] = before := by
  simp [store, project_empty]

omit inputStart in
/-- The output-store projection agrees with the existing copying-memory interpreter. -/
theorem storeRegion_L (context : Solanalib.Runtime.InvCtx) (before : Solanalib.Runtime.InvState)
    (address : Nat) (bytes : Solanalib.Runtime.Bytes) (copying : context.cfg = .L)
    (inside : Solanalib.Runtime.inRegion before address bytes.length = true) :
    Solanalib.Runtime.storeRegion context before address bytes = .ok (store
      Solanalib.Runtime.MM_INPUT_START before address bytes) := by
  have bounds := inside
  simp only [Solanalib.Runtime.inRegion, decide_eq_true_eq] at bounds
  by_cases empty : bytes = []
  · subst bytes
    simp [Solanalib.Runtime.storeRegion, store_empty]
  · have nonempty : bytes.length ≠ 0 := by simpa using empty
    simp [Solanalib.Runtime.storeRegion, nonempty, inside, Solanalib.Runtime.storeAt, copying,
      store,
      project_inside Solanalib.Runtime.MM_INPUT_START before.buf address bytes bounds.1 bounds.2]

/-- An in-bounds written prefix is exactly the supplied bytes after the source store. -/
theorem store_reads_written (before : Solanalib.Runtime.InvState) (address : Nat) (bytes :
  Solanalib.Runtime.Bytes)
    (lower : inputStart ≤ address)
    (bounds : address - inputStart + bytes.length ≤ before.buf.length) :
    Solanalib.Runtime.slice (store inputStart before address bytes).buf (address - inputStart)
      bytes.length =
      bytes := by
  rw [store, project_inside inputStart before.buf address bytes lower bounds]
  exact Solanalib.Runtime.slice_writeAt_self bounds

/-- Reads ending before an in-bounds output prefix retain their prior bytes. -/
theorem store_reads_left (before : Solanalib.Runtime.InvState) (address : Nat) (bytes :
  Solanalib.Runtime.Bytes)
    (offset count : Nat) (lower : inputStart ≤ address)
    (bounds : address - inputStart + bytes.length ≤ before.buf.length)
    (outside : offset + count ≤ address - inputStart) :
    Solanalib.Runtime.slice (store inputStart before address bytes).buf offset count =
      Solanalib.Runtime.slice before.buf offset count := by
  rw [store, project_inside inputStart before.buf address bytes lower bounds]
  exact Solanalib.Runtime.slice_writeAt_left bounds outside

/-- Reads starting after an in-bounds output prefix retain their prior bytes. -/
theorem store_reads_right (before : Solanalib.Runtime.InvState) (address : Nat) (bytes :
  Solanalib.Runtime.Bytes)
    (offset count : Nat) (lower : inputStart ≤ address)
    (bounds : address - inputStart + bytes.length ≤ before.buf.length)
    (outside : address - inputStart + bytes.length ≤ offset) :
    Solanalib.Runtime.slice (store inputStart before address bytes).buf offset count =
      Solanalib.Runtime.slice before.buf offset count := by
  rw [store, project_inside inputStart before.buf address bytes lower bounds]
  exact Solanalib.Runtime.slice_writeAt_right bounds outside

/-- An ordered byte write with its actual VM destination. -/
structure Write where
  address : Nat
  bytes : Solanalib.Runtime.Bytes
  deriving Repr

/-- Apply writes in source order, including their effects on the shared input buffer. -/
def stores (inputStart : Nat) : List Write → Solanalib.Runtime.InvState → Solanalib.Runtime.InvState
  | [], before => before
  | write :: rest, before => stores inputStart rest (store inputStart before write.address
    write.bytes)

/-- Ordered output stores preserve the request-phase non-buffer state. -/
theorem requestState_stores (buffer : Solanalib.Runtime.Bytes) (writes : List Write) (before :
  Solanalib.Runtime.InvState) :
    requestState buffer (stores inputStart writes before) = requestState buffer before := by
  induction writes generalizing before with
  | nil => rfl
  | cons write rest ih =>
    simpa only [stores, requestState_store] using ih (store inputStart before write.address
      write.bytes)

/-- Input-buffer effects depend on the prior buffer and ordered writes, not other fields. -/
theorem stores_buf_congr (writes : List Write) (left right : Solanalib.Runtime.InvState)
    (same : left.buf = right.buf) : (stores inputStart writes left).buf = (stores inputStart writes
      right).buf := by
  induction writes generalizing left right with
  | nil => exact same
  | cons write rest ih =>
    apply ih
    change project inputStart left.buf write.address write.bytes = project inputStart right.buf
      write.address write.bytes
    rw [same]

/-- Stores cannot resize the serialized input allocation. -/
theorem stores_length (writes : List Write) (before : Solanalib.Runtime.InvState) :
    (stores inputStart writes before).buf.length = before.buf.length := by
  induction writes generalizing before with
  | nil => rfl
  | cons write rest ih =>
    rw [stores, ih]
    exact project_length inputStart before.buf write.address write.bytes

end Solanalib.Specs.Core.InputWrites
