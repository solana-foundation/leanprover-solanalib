/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.BorshCommon

/-!
# Heap requests of `Vec<T>` decoding (borsh `VecCall` providers)

The borsh `Vec<T>` models report their `Vec` calls (`VecCall`: `with_capacity`,
`push`, the zeroed `u8` buffer, `resize`) to the allocation provider of their
family index. The driver records the heap requests of the native call with a
tracking global allocator (`rust/codecs-borsh-0-10-4-bytemuck-1-25-2/src/heap.rs`): `alloc`,
`alloc_zeroed`, `realloc` (with its new size) and `dealloc`, each with size,
alignment and block (allocation order within the call; `null` for memory
allocated before it).

The provider below, `vecAllocator size align`, is the interpretation of the test of
the calls: the `Vec` of std at the element layout of the instantiation, as the
pinned toolchain implements it (`RawVec::try_allocate_in`, `grow_amortized`
with `min_non_zero_cap`, `Global::grow` through `realloc`). It always returns
(the host allocator does not fail at these sizes) and keeps the buffer of the vector, always block
0, and the heap requests made so far as its state.

A recorded run is compared through `heapObserved`:

- on `Ok` the recorded requests are exactly those of the provider (the vector is
  returned; nothing else is allocated or freed);
- on `Err` they are those of the provider, then the allocations of the returned
  `io::Error` (on blocks the vector does not own, never freed in the call;
  their sizes are the error representation of std and are not compared), then the
  drop of the vector: one `dealloc` of its final buffer if it has one. The
  model does not report deallocation; the drop is required here so that every
  request on the block of the vector is accounted for.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Borsh

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

/-! ## Heap requests -/

inductive HeapOp where
  | alloc
  | allocZeroed
  | realloc (newSize : Nat)
  | dealloc
  deriving DecidableEq, Repr

structure HeapEvent where
  op : HeapOp
  /-- Allocation order within the call; `none` for memory allocated before it. -/
  block : Option Nat
  size : Nat
  align : Nat
  deriving DecidableEq, Repr

def heapEvent (j : Json) : Result HeapEvent := do
  let op ← match ← (← field j "op").getStr? with
    | "alloc" => pure HeapOp.alloc
    | "alloc_zeroed" => pure .allocZeroed
    | "realloc" => pure (.realloc (← (← field j "new_size").getNat?))
    | "dealloc" => pure .dealloc
    | other => throw s!"unknown heap request {other}"
  let block ← match ← field j "block" with
    | .null => pure none
    | b => do pure (some (← b.getNat?))
  pure ⟨op, block, ← (← field j "size").getNat?, ← (← field j "align").getNat?⟩

def heapEventJson (e : HeapEvent) : Json :=
  let op := match e.op with
    | .alloc => "alloc" | .allocZeroed => "alloc_zeroed" | .realloc _ => "realloc" | .dealloc =>
      "dealloc"
  let base := [("op", Json.str op), ("block", match e.block with
    | none => Json.null
    | some b => toJson b),
    ("size", toJson e.size), ("align", toJson e.align)]
  Json.mkObj (match e.op with
    | .realloc n => base ++ [("new_size", toJson n)]
    | _ => base)

def vecCallJson : VecCall → Json
  | .withCapacity n => Json.mkObj [("with_capacity", toJson n)]
  | .push n => Json.mkObj [("push", toJson n)]
  | .zeroed n => Json.mkObj [("zeroed", toJson n)]
  | .resize n => Json.mkObj [("resize", toJson n)]

/-! ## The provider: the `Vec` of std at an element layout -/

/-- The buffer of the vector (block 0): capacity and length in elements, and the
heap requests made so far, in order. -/
structure VecBuffer where
  capacity : Nat
  length : Nat
  events : List HeapEvent
  deriving DecidableEq, Repr

/-- the smallest nonzero capacity of `RawVec` (`min_non_zero_cap`). -/
def minNonZeroCap (size : Nat) : Nat := if size = 1 then 8 else if size ≤ 1024 then 4 else 1

namespace VecBuffer

def empty : VecBuffer := ⟨0, 0, []⟩

/-- A fresh buffer of `capacity` elements holding `length`: one request unless
its size is zero (`RawVec::try_allocate_in`). -/
def fresh (size align : Nat) (op : HeapOp) (b : VecBuffer) (capacity length : Nat) : VecBuffer :=
  { capacity, length,
    events := b.events ++ (if capacity * size = 0 then [] else [⟨op, some 0, capacity * size,
      align⟩]) }

/-- `RawVec::grow_amortized` to hold `required` elements: capacity
`max(2 * capacity, required, min_non_zero_cap)`, by `realloc` of the current
buffer (`alloc` if it has none). -/
def grow (size align : Nat) (b : VecBuffer) (required : Nat) : VecBuffer :=
  let capacity := max (max (2 * b.capacity) required) (minNonZeroCap size)
  let request : HeapEvent :=
    if b.capacity * size = 0 then ⟨.alloc, some 0, capacity * size, align⟩
    else ⟨.realloc (capacity * size), some 0, b.capacity * size, align⟩
  { b with capacity, events := b.events ++ [request] }

/-- The heap requests of one `Vec` call: `Vec::with_capacity(n)`; `push` onto
`length` elements (grows when full); `vec![0u8; n]` (`alloc_zeroed`);
`resize(n, 0)` (`reserve`, so it grows only beyond the capacity). -/
def step (size align : Nat) (b : VecBuffer) : VecCall → VecBuffer
  | .withCapacity n => b.fresh size align .alloc n 0
  | .zeroed n => b.fresh size align .allocZeroed n n
  | .push length =>
    let b := if length < b.capacity then b else b.grow size align (length + 1)
    { b with length := length + 1 }
  | .resize n =>
    let b := if n ≤ b.capacity then b else b.grow size align n
    { b with length := n }

/-- The drop of the vector: one `dealloc` of its buffer, if it has one. -/
def release (size align : Nat) (b : VecBuffer) : List HeapEvent :=
  if b.capacity * size = 0 then [] else [⟨.dealloc, some 0, b.capacity * size, align⟩]

end VecBuffer

/-- The allocation provider of the heap-observed `Vec<T>` checks: the `Vec` of std
at element size `size` and alignment `align`. Every call returns. -/
def vecAllocator {Unwind Terminal : Type} (size align : Nat) : AllocateFn VecBuffer Unwind Terminal
  :=
  fun b call => .returned () (b.step size align call)

/-- the decoder of `T`, a registered member at state `()` that neither unwinds nor
terminates, at the caller state `S`, which it keeps. -/
def atState {S V : Type} (decode : DecodeFn Unit V Empty Empty) : DecodeFn S V Empty Empty :=
  fun s input => match decode () input with
    | .returned r _ => .returned r s
    | .unwound e _ => nomatch e
    | .terminated e => nomatch e

/-! ## Observation -/

/-- A request of the returned error value: on a block allocated in the call
that is not for the vector, and not freed. -/
def errorRequest (vectorAllocated : Bool) (e : HeapEvent) : Bool :=
  e.op != .dealloc && match e.block with
    | none => false
    | some k => !(vectorAllocated && k == 0)

/-- The recorded requests of a decode that returned `Ok` (`ok`) or `Err`,
against the final buffer of the provider `b` (see the module comment). -/
def heapObserved (size align : Nat) (ok : Bool) (b : VecBuffer) (recorded : List HeapEvent) : Bool
  :=
  if ok then recorded == b.events
  else
    let drop := b.release size align
    let n := b.events.length
    let errors := (recorded.drop n).take (recorded.length - n - drop.length)
    decide (n + drop.length ≤ recorded.length) && recorded.take n == b.events &&
      recorded.drop (recorded.length - drop.length) == drop &&
      errors.all (errorRequest (!b.events.isEmpty))

/-- A recorded `Vec<T>` decode: result and remaining slice, and the heap requests. -/
abbrev HeapRecord (V : Type) := (Except IoError V × Solanalib.Runtime.Bytes) × List HeapEvent

abbrev HeapOutcome (V : Type) := Outcome VecBuffer (Except IoError V × Solanalib.Runtime.Bytes)
  Empty Empty

def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- A model outcome observes a record when result and remaining slice are equal
and the recorded heap requests are those of the provider (`heapObserved`). -/
def heapObserves {V : Type} [DecidableEq V] (size align : Nat) : HeapOutcome V → HeapRecord V → Bool
  | .returned (result, remaining) b, ((result', remaining'), heap) =>
    decide (result = result') && decide (remaining = remaining') && heapObserved size align (isOk
      result) b heap
  | .unwound e _, _ => nomatch e
  | .terminated e, _ => nomatch e

/-- The state before a heap-observed decode: the slice, and no requests yet
(the provider starts without a buffer). -/
def heapBefore (c : Case) : Result (VecBuffer × Solanalib.Runtime.Bytes) := do
  let heap ← asList heapEvent (← field c.state "heap")
  unless heap.isEmpty do throw "the heap log before the call is not empty"
  pure (VecBuffer.empty, ← slice c)

def heapRecord {V : Type} (parse : Json → Result V) (j : Json) : Result (Option (HeapRecord V)) :=
  do
  match ← (← field j "exit").getStr? with
  | "returned" =>
    let result ← asExcept ioError parse (← field j "result")
    let state ← field j "state"
    return some ((result, ← asBytes (← field state "slice")), ← asList heapEvent (← field state
      "heap"))
  | "unwound" | "terminated" => return none
  | other => throw s!"unknown exit {other}"

def heapOutcomeJson {V : Type} (size align : Nat) (render : V → Json) : HeapOutcome V → Json
  | .returned (result, remaining) b =>
    returnedJson (exceptJson ioErrorJson render result) (Json.mkObj [
      ("slice", bytesJson remaining), ("heap", listJson heapEventJson b.events),
      ("on_error", Json.str "then the error allocations, then the release below"),
      ("release", listJson heapEventJson (b.release size align))])
  | .unwound e _ => nomatch e
  | .terminated e => nomatch e

/-- Decide "the registered relation admits an outcome that the record
observes" through the graph lemma of the model: by the graph, the only admitted
outcome is the computed one. -/
def decideObserved {S V U T R : Type} (relation : Outcome S V U T → Prop) (computed : Outcome S V U
  T)
    (graph : ∀ o, relation o ↔ computed = o) (observes : Outcome S V U T → R → Bool)
    (recorded : Option R) (render : Outcome S V U T → Json) : Verdict :=
  match recorded with
  | some r =>
    have : Decidable (∃ o, relation o ∧ observes o r = true) :=
      decidable_of_iff (observes computed r = true)
        ⟨fun h => ⟨computed, (graph computed).2 rfl, h⟩,
         fun ⟨o, ho, h⟩ => by rw [(graph o).1 ho]; exact h⟩
    ⟨decide (∃ o, relation o ∧ observes o r = true), render computed⟩
  | none => ⟨false, render computed⟩

/-- The `layout` of the record is `size_of`/`align_of` of the element `T`, the layout of the
index. -/
def checkElementLayout (c : Case) (rust : String) (size align : Nat) : Result Unit := do
  let some l := c.layout | throw "record has no layout"
  let s ← (← field l "size").getNat?
  let a ← (← field l "align").getNat?
  unless s = size ∧ a = align do
    throw s!"layout mismatch for {rust}: Rust size {s} align {a}, index size {size} align \
      {align}"

end SolanalibTest.Conformance.Library.Borsh
