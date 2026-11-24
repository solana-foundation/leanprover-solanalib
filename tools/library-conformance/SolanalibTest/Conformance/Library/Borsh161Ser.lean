/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.BorshCommon
import Solanalib.Specs.Borsh.Ser

/-!
# borsh 1.6.1 serialization (`borsh.Ser`)

Every serializer family is indexed by the writer `W` (its `write_all` as a callback) and, for
`Option<T>` and `[T; N]`, by the serializer of `T`. The checker instantiates `W` with the
recorded writer and the serializer of `T` with the function form of the registered primitive
member of `T` at the same writer (`element_*` theorems), and decides the registered relation
through the `_ofFunction`/`_byte` graph lemma of the model. -/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Borsh.V161Ser

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

/-- A primitive member `primitiveSerializeRun encoder` registered as `run`. -/
structure Primitive where
  rust : String
  Value : Type
  parse : Json → Result Value
  encoder : Encoder Value
  reference : String
  run : (index : WriterIndex) → index.State → Value →
    Outcome index.State (Except IoError Unit) index.Unwind index.Terminal → Prop
  run_eq : run = primitiveSerializeRun encoder

def Primitive.at (p : Primitive) {S : Type} (w : WriterFn S Empty Empty) : SerializerAt S p.Value
  where
  relation := p.run ⟨S, Empty, Empty, Callback.ofFunction w⟩
  serialize := primitiveSerializeFn p.encoder w
  graph := fun before value o => by
    rw [p.run_eq]; exact primitiveSerializeRun_ofFunction p.encoder w before value o

/-- The registered names unfold to the shared primitive relation (by `rfl`). -/
def u8 : Primitive := ⟨"u8", UInt8, u8Parse, encodeU8, "Solanalib.Specs.Borsh.u8.serialize_\
  run",
  Solanalib.Specs.Borsh.u8.serialize_run, rfl⟩
def bool : Primitive := ⟨"bool", Bool, boolParse, encodeBool,
  "Solanalib.Specs.Borsh.bool.serialize_run",
  Solanalib.Specs.Borsh.bool.serialize_run, rfl⟩
def u32 : Primitive := ⟨"u32", UInt32, u32Parse, encodeU32,
  "Solanalib.Specs.Borsh.u32.serialize_run",
  Solanalib.Specs.Borsh.u32.serialize_run, rfl⟩
def u64 : Primitive := ⟨"u64", UInt64, u64Parse, encodeU64,
  "Solanalib.Specs.Borsh.u64.serialize_run",
  Solanalib.Specs.Borsh.u64.serialize_run, rfl⟩
def i64 : Primitive := ⟨"i64", Int64, i64Parse, encodeI64,
  "Solanalib.Specs.Borsh.i64.serialize_run",
  Solanalib.Specs.Borsh.i64.serialize_run, rfl⟩
def f64 : Primitive := ⟨"f64", Float64.Bits, asF64Bits, encodeF64,
  "Solanalib.Specs.Borsh.f64.serialize_run",
  Solanalib.Specs.Borsh.f64.serialize_run, rfl⟩

def primitiveChecker (p : Primitive) : Checker where
  function := s!"<{p.rust} as borsh::ser::BorshSerialize>::serialize"
  generics := []
  reference := p.reference
  decides := [p.reference]
  check := fun c => decideSerialize p.parse c fun w => p.at w

/-- The element callback used in `Option<T>`/`[T; N]` indices is, extensionally,
the registered serializer of `T` at the same writer. -/
theorem element_is_registered (p : Primitive) {S : Type} (w : WriterFn S Empty Empty)
    (before : S) (value : p.Value) (o : Outcome S (Except IoError Unit) Empty Empty) :
    Callback.ofFunction (primitiveSerializeFn p.encoder w) before value o ↔
      p.run ⟨S, Empty, Empty, Callback.ofFunction w⟩ before value o :=
  ((p.at w).graph before value o).symm

theorem option_evaluated {S V : Type} (w : WriterFn S Empty Empty)
    (serialize : SerializeFn S V Empty Empty) (before : S) (value : Option V)
    (o : Outcome S (Except IoError Unit) Empty Empty) :
    Solanalib.Specs.Borsh.Option.serialize_run
        ⟨S, Empty, Empty, Callback.ofFunction w, V, Callback.ofFunction serialize⟩ before value o ↔
      optionSerializeFn w serialize before value = o :=
  optionSerializeRun_ofFunction w serialize before value o

theorem byte_array_evaluated {S : Type} (n : Nat) (w : WriterFn S Empty Empty) (before : S)
    (bytes : FixedArray UInt8 n) (o : Outcome S (Except IoError Unit) Empty Empty) :
    Solanalib.Specs.Borsh.Array.serialize_run ⟨S, Empty, Empty, Callback.ofFunction w, n, .byte⟩
      before bytes o ↔
      byteArraySerializeFn n w before bytes = o :=
  arraySerializeRun_byte n w before bytes o

theorem array_evaluated {S V : Type} (n : Nat) (w : WriterFn S Empty Empty)
    (serialize : SerializeFn S V Empty Empty) (before : S) (values : FixedArray V n)
    (o : Outcome S (Except IoError Unit) Empty Empty) :
    Solanalib.Specs.Borsh.Array.serialize_run
        ⟨S, Empty, Empty, Callback.ofFunction w, n, .other V (Callback.ofFunction serialize)⟩
        before values o ↔
      arraySerializeFn n w serialize before values = o :=
  arraySerializeRun_ofFunction n w serialize before values o

theorem u8_slice_evaluated :
    returnsOf Solanalib.Specs.Borsh.u8.u8_slice_model = returnsOf (Unwind := Empty) (Terminal :=
      Empty) u8SliceModel :=
  rfl

def optionChecker (p : Primitive) : Checker where
  function := "<core::option::Option<T> as borsh::ser::BorshSerialize>::serialize"
  generics := [("T", p.rust)]
  reference := "Solanalib.Specs.Borsh.Option.serialize_run"
  decides := ["Solanalib.Specs.Borsh.Option.serialize_run"]
  check := fun c => decideSerialize (asOption p.parse) c fun w => {
    relation := Solanalib.Specs.Borsh.Option.serialize_run
      ⟨_, Empty, Empty, Callback.ofFunction w, p.Value, Callback.ofFunction (primitiveSerializeFn
        p.encoder w)⟩
    serialize := optionSerializeFn w (primitiveSerializeFn p.encoder w)
    graph := option_evaluated w _ }

def byteArrayChecker (n : Nat) : Checker where
  function := "<[T; N] as borsh::ser::BorshSerialize>::serialize"
  generics := [("T", "u8"), ("N", toString n)]
  reference := "Solanalib.Specs.Borsh.Array.serialize_run"
  decides := ["Solanalib.Specs.Borsh.Array.serialize_run"]
  check := fun c => decideSerialize (asFixedBytes n) c fun w => {
    relation := Solanalib.Specs.Borsh.Array.serialize_run ⟨_, Empty, Empty, Callback.ofFunction w,
      n, .byte⟩
    serialize := byteArraySerializeFn n w
    graph := byte_array_evaluated n w }

def arrayChecker (n : Nat) (p : Primitive) : Checker where
  function := "<[T; N] as borsh::ser::BorshSerialize>::serialize"
  generics := [("T", p.rust), ("N", toString n)]
  reference := "Solanalib.Specs.Borsh.Array.serialize_run"
  decides := ["Solanalib.Specs.Borsh.Array.serialize_run"]
  check := fun c => decideSerialize (asFixedArray n p.parse) c fun w => {
    relation := Solanalib.Specs.Borsh.Array.serialize_run
      ⟨_, Empty, Empty, Callback.ofFunction w, n, .other p.Value (Callback.ofFunction
        (primitiveSerializeFn p.encoder w))⟩
    serialize := arraySerializeFn n w (primitiveSerializeFn p.encoder w)
    graph := array_evaluated n w _ }

def u8SliceChecker : Checker where
  function := "<u8 as borsh::ser::BorshSerialize>::u8_slice"
  generics := []
  reference := "Solanalib.Specs.Borsh.u8.u8_slice_model"
  decides := ["Solanalib.Specs.Borsh.u8.u8_slice_model"]
  check := fun c => do
    let slice ← asBytes (← field c.args "slice")
    let before ← asUnit c.state
    let recorded : Option (Outcome Unit (Option Solanalib.Runtime.Bytes) Empty Empty) ←
      parseOutcome (asOption asBytes) asUnit noReason noReason c.outcome
    let model := Solanalib.Specs.Borsh.u8.u8_slice_model
    pure (decideGraph (returnsOf model before slice) (.returned (model before slice).1 (model
      before slice).2)
      (returnsOf_iff model before slice) recorded
      (fun o => match o with
        | .returned v _ => returnedJson (optionJson bytesJson v) Json.null
        | .unwound e _ => nomatch e
        | .terminated e => nomatch e))

/-- Each serializer is recorded at both writers; `W` is part of the key. -/
def withWriters (c : Checker) : List Checker :=
  ["conformance_recorder::RecordingWriter", "alloc::vec::Vec<u8>"].map fun w =>
    { c with generics := c.generics ++ [("W", w)] }

def checkers : List Checker :=
  [u8SliceChecker] ++
    (([u8, bool, u32, u64, i64, f64].map primitiveChecker ++
      [u8, bool, u32, u64, i64, f64].map optionChecker ++
      [0, 1, 16, 32].map byteArrayChecker ++
      [arrayChecker 0 u64, arrayChecker 3 u64, arrayChecker 2 bool, arrayChecker 2 f64]).flatMap
        withWriters)

end SolanalibTest.Conformance.Library.Borsh.V161Ser
