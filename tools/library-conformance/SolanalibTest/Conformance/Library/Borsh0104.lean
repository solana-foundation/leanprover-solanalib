/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.BorshVecHeap
import Solanalib.Specs.Borsh.De

/-!
# borsh 0.10.4 decoding (`borsh.De`)

As for 1.6.1: primitive members are decided by the graph of their model; generic
members (`Option<T>`, `Vec<T>`, `deserialize`, `try_from_slice`,
`vec_from_reader`) through the graph lemmas of the model at the registered names.

`Vec<T>::deserialize_reader` records carry the heap requests of the call. The allocation provider of
their index is `vecAllocator` (the `Vec` of std at the element
layout, `BorshVecHeap`), its element callback the registered decoder of `T` at the state of that
provider; the checker decides that the registered relation admits an
outcome whose result, remaining slice and heap requests the record observes.
The wrappers at `Self = Vec<T>` keep the always-returning provider at state
`()`: their records do not observe allocation.

`de::hint::cautious` is private in borsh 0.10.4. Its records are derived by the
driver from the `Vec<T>` runs (argument `len`, result the capacity of the
first allocation, `with_capacity`); the checker decides the registered
reference at index `size_of::<T>()`, checking the layout and normal arithmetic
branch of these corpus instantiations.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Borsh.V0104

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

abbrev P := Solanalib.Specs.Borsh.invalid_input_profile

def u8 : Ty := primitive "u8" UInt8 u8Parse u8Json 1
  "Solanalib.Specs.Borsh.u8.invalid_input.deserialize_reader_model"
    Solanalib.Specs.Borsh.u8.invalid_input.deserialize_reader_model
def i8 : Ty := primitive "i8" Int8 i8Parse i8Json 1
  "Solanalib.Specs.Borsh.i8.invalid_input.deserialize_reader_model"
    Solanalib.Specs.Borsh.i8.invalid_input.deserialize_reader_model
def u32 : Ty := primitive "u32" UInt32 u32Parse u32Json 4
  "Solanalib.Specs.Borsh.u32.invalid_input.deserialize_reader_model"
    Solanalib.Specs.Borsh.u32.invalid_input.deserialize_reader_model
def u64 : Ty := primitive "u64" UInt64 u64Parse u64Json 8
  "Solanalib.Specs.Borsh.u64.invalid_input.deserialize_reader_model"
    Solanalib.Specs.Borsh.u64.invalid_input.deserialize_reader_model
def bool : Ty := primitive "bool" Bool boolParse boolJson 1
  "Solanalib.Specs.Borsh.bool.invalid_input.deserialize_reader_model"
    Solanalib.Specs.Borsh.bool.invalid_input.deserialize_reader_model

/-! ## The evaluated functions are the registered references -/

theorem option_evaluated {V : Type} (decode : DecodeFn Unit V Empty Empty) (before : Unit)
    (input : Solanalib.Runtime.Bytes) (o : DecodeOut (Option V)) :
    Solanalib.Specs.Borsh.Option.invalid_input.deserialize_reader_run ⟨Unit, Empty, Empty, V,
      Callback.ofFunction decode⟩
        before input o ↔ optionDecodeFn P decode before input = o :=
  optionDecodeRun_ofFunction P decode before input o

theorem byte_vec_evaluated (before : Unit) (input : Solanalib.Runtime.Bytes) (o : DecodeOut (List
  UInt8)) :
    Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run
        ⟨Unit, Empty, Empty, .byte, Callback.ofFunction allocateReturns, noDivisionPanic⟩ before
          input o ↔
      byteVecDecodeFn P allocateReturns before input = o :=
  vecDecodeRun_byte P allocateReturns before input o

theorem vec_evaluated {V : Type} (size : Nat) (safe : VecNoDivisionByZero size)
    (decode : DecodeFn Unit V Empty Empty) (before : Unit)
    (input : Solanalib.Runtime.Bytes) (o : DecodeOut (List V)) :
    Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run
        ⟨Unit, Empty, Empty, .other V size (Callback.ofFunction decode),
          Callback.ofFunction allocateReturns, noDivisionPanic⟩ before input o ↔
      vecDecodeFn P size safe decode allocateReturns before input = o :=
  vecDecodeRun_ofFunction P size safe decode allocateReturns before input o

theorem deserialize_evaluated {V : Type} (decode : DecodeFn Unit V Empty Empty) (before : Unit)
    (input : Solanalib.Runtime.Bytes) (o : DecodeOut V) :
    Solanalib.Specs.Borsh.de.BorshDeserialize.deserialize_run ⟨Unit, Empty, Empty, V,
      Callback.ofFunction decode⟩
        before input o ↔ deserializeFn decode before input = o :=
  deserializeRun_ofFunction decode before input o

theorem try_from_slice_evaluated {V : Type} (decode : DecodeFn Unit V Empty Empty) (before : Unit)
    (input : Solanalib.Runtime.Bytes) (o : Outcome Unit (Except IoError V) Empty Empty) :
    Solanalib.Specs.Borsh.de.BorshDeserialize.try_from_slice_run
        ⟨Unit, Empty, Empty, V, Callback.ofFunction decode⟩ before input o ↔
      tryFromSliceFn decode before input = o :=
  tryFromSliceRun_ofFunction decode before input o

theorem vec_from_reader_evaluated (V : Type) (before : Unit) (args : UInt32 ×
  Solanalib.Runtime.Bytes)
    (o : DecodeOut (Option (List V))) :
    Solanalib.Specs.Borsh.de.BorshDeserialize.vec_from_reader_run ⟨V⟩ before args o ↔
      .returned (.ok none, args.2) before = o :=
  eq_comm

/-! ## Generic instantiations -/

def option (e : Ty) : Ty where
  rust := s!"core::option::Option<{e.rust}>"
  Value := Option e.Value
  decEq := inferInstance
  parse := asOption e.parse
  render := optionJson e.render
  size := 0
  readerFunction := "<core::option::Option<T> as \
    borsh::de::BorshDeserialize>::deserialize_reader"
  readerGenerics := [("T", e.rust)]
  readerReference := "Solanalib.Specs.Borsh.Option.invalid_input.deserialize_reader_run"
  decode := optionDecodeFn P e.decode
  reader := Solanalib.Specs.Borsh.Option.invalid_input.deserialize_reader_run ⟨Unit, Empty, Empty,
    e.Value, Callback.ofFunction e.decode⟩
  reader_graph := option_evaluated e.decode

def byteVec : Ty where
  rust := "alloc::vec::Vec<u8>"
  Value := List UInt8
  decEq := inferInstance
  parse := asBytes
  render := bytesJson
  size := 0
  readerFunction := "<alloc::vec::Vec<T> as \
    borsh::de::BorshDeserialize>::deserialize_reader"
  readerGenerics := [("T", "u8")]
  readerReference := "Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run"
  decode := byteVecDecodeFn P allocateReturns
  reader := Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run ⟨Unit, Empty, Empty,
    .byte, Callback.ofFunction allocateReturns, noDivisionPanic⟩
  reader_graph := byte_vec_evaluated

def vec (e : Ty) (safe : VecNoDivisionByZero e.size) : Ty where
  rust := s!"alloc::vec::Vec<{e.rust}>"
  Value := List e.Value
  decEq := inferInstance
  parse := asList e.parse
  render := listJson e.render
  size := 0
  readerFunction := "<alloc::vec::Vec<T> as \
    borsh::de::BorshDeserialize>::deserialize_reader"
  readerGenerics := [("T", e.rust)]
  readerReference := "Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run"
  decode := vecDecodeFn P e.size safe e.decode allocateReturns
  reader := Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run
    ⟨Unit, Empty, Empty, .other e.Value e.size (Callback.ofFunction e.decode),
      Callback.ofFunction allocateReturns, noDivisionPanic⟩
  reader_graph := vec_evaluated e.size safe e.decode

def deserializeChecker (t : Ty) : Checker where
  function := "borsh::de::BorshDeserialize::deserialize"
  generics := [("Self", t.rust)]
  reference := "Solanalib.Specs.Borsh.de.BorshDeserialize.deserialize_run"
  decides := ["Solanalib.Specs.Borsh.de.BorshDeserialize.deserialize_run"]
  check := fun c => decideDecode t.parse t.render c
    (Solanalib.Specs.Borsh.de.BorshDeserialize.deserialize_run ⟨Unit, Empty, Empty, t.Value,
      Callback.ofFunction t.decode⟩ ())
    (deserializeFn t.decode ()) (deserialize_evaluated t.decode ())

/-- `try_from_slice` at `Self = t`; its index callback is `Self::deserialize`,
the default member above at the same `Self`. The state is `()` and the
argument is the whole slice. -/
def tryFromSliceChecker (t : Ty) : Checker where
  function := "borsh::de::BorshDeserialize::try_from_slice"
  generics := [("Self", t.rust)]
  reference := "Solanalib.Specs.Borsh.de.BorshDeserialize.try_from_slice_run"
  decides := ["Solanalib.Specs.Borsh.de.BorshDeserialize.try_from_slice_run"]
  check := fun c => do
    let input ← asBytes (← field c.args "bytes")
    let before ← asUnit c.state
    let recorded : Option (Outcome Unit (Except IoError t.Value) Empty Empty) ←
      parseOutcome (asExcept ioError t.parse) asUnit noReason noReason c.outcome
    let selfDeserialize := deserializeFn t.decode
    pure (decideGraph (S := Unit) (V := Except IoError t.Value) (U := Empty) (T := Empty)
      (Solanalib.Specs.Borsh.de.BorshDeserialize.try_from_slice_run
        ⟨Unit, Empty, Empty, t.Value, Callback.ofFunction selfDeserialize⟩ before input)
      (tryFromSliceFn selfDeserialize before input) (try_from_slice_evaluated selfDeserialize
        before input)
      recorded
      (fun o => match o with
        | .returned r _ => returnedJson (exceptJson ioErrorJson t.render r) Json.null
        | .unwound e _ => nomatch e
        | .terminated e => nomatch e))

def vecFromReaderChecker (t : Ty) : Checker where
  function := "borsh::de::BorshDeserialize::vec_from_reader"
  generics := [("Self", t.rust), ("R", "&[u8]")]
  reference := "Solanalib.Specs.Borsh.de.BorshDeserialize.vec_from_reader_run"
  decides := ["Solanalib.Specs.Borsh.de.BorshDeserialize.vec_from_reader_run"]
  check := fun c => do
    let len ← asUInt 32 (← field c.args "len")
    let parse : Json → Result (Option (List t.Value)) := asOption fun _ =>
      throw "the default vec_from_reader returned Some"
    decideDecode parse (optionJson fun _ => Json.str "<elements>") c
      (fun input => Solanalib.Specs.Borsh.de.BorshDeserialize.vec_from_reader_run ⟨t.Value⟩ ()
        (UInt32.ofNat len, input))
      (fun input => .returned (.ok none, input) ())
      (fun input => vec_from_reader_evaluated t.Value () (UInt32.ofNat len, input))

/-! ## `Vec<T>` with its heap requests -/

theorem byte_vec_heap_evaluated (before : VecBuffer) (input : Solanalib.Runtime.Bytes)
    (o : HeapOutcome (List UInt8)) :
    Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run
        ⟨VecBuffer, Empty, Empty, .byte, Callback.ofFunction (vecAllocator 1 1), noDivisionPanic⟩
          before input o ↔
      byteVecDecodeFn P (vecAllocator 1 1) before input = o :=
  vecDecodeRun_byte P (vecAllocator 1 1) before input o

theorem vec_heap_evaluated {V : Type} (size align : Nat) (safe : VecNoDivisionByZero size)
    (decode : DecodeFn Unit V Empty Empty)
    (before : VecBuffer) (input : Solanalib.Runtime.Bytes) (o : HeapOutcome (List V)) :
    Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run
        ⟨VecBuffer, Empty, Empty, .other V size (Callback.ofFunction (atState decode)),
          Callback.ofFunction (vecAllocator size align), noDivisionPanic⟩ before input o ↔
      vecDecodeFn P size safe (atState decode) (vecAllocator size align) before input = o :=
  vecDecodeRun_ofFunction P size safe (atState decode) (vecAllocator size align) before input o

def vecReaderFunction : String :=
  "<alloc::vec::Vec<T> as borsh::de::BorshDeserialize>::deserialize_reader"

/-- `Vec<u8>` (`u8::vec_from_reader`) with its heap requests; `u8` has size and
alignment 1. -/
def byteVecHeapChecker : Checker where
  function := vecReaderFunction
  generics := [("T", "u8"), ("R", "&[u8]")]
  reference := "Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run"
  decides := ["Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run"]
  check := fun c => do
    checkElementLayout c "u8" 1 1
    let (before, input) ← heapBefore c
    let recorded ← heapRecord asBytes c.outcome
    pure (decideObserved (S := VecBuffer) (V := Except IoError (List UInt8) ×
      Solanalib.Runtime.Bytes)
      (U := Empty) (T := Empty)
      (Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run
        ⟨VecBuffer, Empty, Empty, .byte, Callback.ofFunction (vecAllocator 1 1), noDivisionPanic⟩
          before input)
      (byteVecDecodeFn P (vecAllocator 1 1) before input) (byte_vec_heap_evaluated before input)
      (heapObserves 1 1) recorded (heapOutcomeJson 1 1 bytesJson))

/-- `Vec<T>` for an element without the `u8` override, with its heap requests:
`e.size` and `align` are `size_of`/`align_of` of `T`, checked against the
record. -/
def vecHeapChecker (e : Ty) (align : Nat) (safe : VecNoDivisionByZero e.size) : Checker where
  function := vecReaderFunction
  generics := [("T", e.rust), ("R", "&[u8]")]
  reference := "Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run"
  decides := ["Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run"]
  check := fun c => do
    checkElementLayout c e.rust e.size align
    let (before, input) ← heapBefore c
    let recorded ← heapRecord (asList e.parse) c.outcome
    pure (decideObserved (S := VecBuffer) (V := Except IoError (List e.Value) ×
      Solanalib.Runtime.Bytes)
      (U := Empty) (T := Empty)
      (Solanalib.Specs.Borsh.Vec.invalid_input.deserialize_reader_run
        ⟨VecBuffer, Empty, Empty, .other e.Value e.size (Callback.ofFunction (atState e.decode)),
          Callback.ofFunction (vecAllocator e.size align), noDivisionPanic⟩ before input)
      (vecDecodeFn P e.size safe (atState e.decode) (vecAllocator e.size align) before input)
      (vec_heap_evaluated e.size align safe e.decode before input)
      (heapObserves e.size align) recorded (heapOutcomeJson e.size align (listJson e.render)))

/-- `Option<u64>` as a `Vec` element: 16 bytes (`size_of::<Option<u64>>()`). -/
def optionU64Element : Ty := { option u64 with size := 16 }

/-! ## `hint::cautious` -/

theorem cautious_evaluated (size capacity : Nat) (before : Unit) (hint : UInt32)
    (returns : cautious size hint.toNat = some capacity)
    (o : Outcome Unit Nat Empty Empty) :
    Solanalib.Specs.Borsh.de.hint.cautious_run ⟨Unit, Empty, Empty, size, noDivisionPanic⟩ before
      hint o ↔
      (.returned capacity before : Outcome Unit Nat Empty Empty) = o := by
  change (match cautious size hint.toNat with | some n => _ | none => _) ↔ _
  rw [returns]
  exact eq_comm

/-- `hint::cautious::<T>` on records derived from the `Vec<T>` runs, at the
index `size_of::<T>()` the record states (its `layout`). The recorded layout
must be the layout of `T` (`e.size`, `align`). These corpus instantiations return normally;
the arithmetic branch is checked before applying the graph lemma of that adapter. -/
def cautiousChecker (e : Ty) (align : Nat) : Checker where
  function := "borsh::de::hint::cautious"
  generics := [("T", e.rust)]
  reference := "Solanalib.Specs.Borsh.de.hint.cautious_run"
  decides := ["Solanalib.Specs.Borsh.de.hint.cautious_run"]
  check := fun c => do
    let some l := c.layout | throw "record has no layout"
    let size ← (← field l "size").getNat?
    let before ← asUnit c.state
    let hint := UInt32.ofNat (← asUInt 32 (← field c.args "hint"))
    checkElementLayout c e.rust e.size align
    match result : cautious size hint.toNat with
    | none => throw "this returning corpus instantiation reaches the division-by-zero panic"
    | some capacity =>
      let recorded : Option (Outcome Unit Nat Empty Empty) ←
        parseOutcome (fun j => j.getNat?) asUnit noReason noReason c.outcome
      pure (decideGraph (S := Unit) (V := Nat) (U := Empty) (T := Empty)
        (Solanalib.Specs.Borsh.de.hint.cautious_run ⟨Unit, Empty, Empty, size, noDivisionPanic⟩
          before hint)
        (.returned capacity before) (cautious_evaluated size capacity before hint result) recorded
        (fun o => match o with
          | .returned n _ => returnedJson (toJson n) Json.null
          | .unwound e _ => nomatch e
          | .terminated e => nomatch e))

/-! ## Checkers -/

/-- The instantiations recorded in `borsh_0_10_4.json` with all three
decoding entry points (the `deserialize_reader` of `Vec<T>` is heap-observed). -/
def types : List Ty :=
  [u8, i8, bool, u32, u64, option u8, option u32, option u64, option bool, byteVec,
    vec u32 (by right; decide), vec bool (by right; decide)]

def plainReaderTypes : List Ty :=
  [u8, i8, bool, u32, u64, option u8, option u32, option u64, option bool]

def checkers : List Checker :=
  plainReaderTypes.map readerChecker ++
    [byteVecHeapChecker, vecHeapChecker u32 4 (by right; decide),
      vecHeapChecker bool 1 (by right; decide), vecHeapChecker optionU64Element 8 (by
        right; decide)] ++
    types.map deserializeChecker ++ types.map tryFromSliceChecker ++
    [vecFromReaderChecker u32, vecFromReaderChecker bool] ++
    [cautiousChecker u32 4, cautiousChecker bool 1, cautiousChecker optionU64Element 8]

end SolanalibTest.Conformance.Library.Borsh.V0104
