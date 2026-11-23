/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.BorshCommon
import Solanalib.Specs.Borsh.De

/-!
# borsh 1.6.1 decoding (`borsh.De`)

Primitive `deserialize_reader` members are plain contracts realized by their
`deserialize_reader_model`; the checker decides the graph of that model. The
generic members (`Option<T>`, `[T; N]`, the default `deserialize`) are
relations over the callback of the element; at an index whose callback is the
graph of a function, the `_ofFunction`/`_byte` lemma of the model states that the
registered relation is the graph of the executable combinator evaluated here.
The theorems below instantiate those lemmas at the registered names, so they
also check that each registered name unfolds to the shared definition.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Borsh.V161

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

abbrev P := Solanalib.Specs.Borsh.invalid_data_profile

def u8 : Ty := primitive "u8" UInt8 u8Parse u8Json 1
  "Solanalib.Specs.Borsh.u8.invalid_data.deserialize_reader_model"
    Solanalib.Specs.Borsh.u8.invalid_data.deserialize_reader_model
def u32 : Ty := primitive "u32" UInt32 u32Parse u32Json 4
  "Solanalib.Specs.Borsh.u32.invalid_data.deserialize_reader_model"
    Solanalib.Specs.Borsh.u32.invalid_data.deserialize_reader_model
def i32 : Ty := primitive "i32" Int32 i32Parse i32Json 4
  "Solanalib.Specs.Borsh.i32.invalid_data.deserialize_reader_model"
    Solanalib.Specs.Borsh.i32.invalid_data.deserialize_reader_model
def u64 : Ty := primitive "u64" UInt64 u64Parse u64Json 8
  "Solanalib.Specs.Borsh.u64.invalid_data.deserialize_reader_model"
    Solanalib.Specs.Borsh.u64.invalid_data.deserialize_reader_model
def i64 : Ty := primitive "i64" Int64 i64Parse i64Json 8
  "Solanalib.Specs.Borsh.i64.invalid_data.deserialize_reader_model"
    Solanalib.Specs.Borsh.i64.invalid_data.deserialize_reader_model
def f64 : Ty := primitive "f64" Float64.Bits asF64Bits f64BitsJson 8
  "Solanalib.Specs.Borsh.f64.invalid_data.deserialize_reader_model"
    Solanalib.Specs.Borsh.f64.invalid_data.deserialize_reader_model
def bool : Ty := primitive "bool" Bool boolParse boolJson 1
  "Solanalib.Specs.Borsh.bool.invalid_data.deserialize_reader_model"
    Solanalib.Specs.Borsh.bool.invalid_data.deserialize_reader_model

/-! ## The evaluated functions are the registered references -/

theorem option_evaluated {V : Type} (decode : DecodeFn Unit V Empty Empty) (before : Unit)
    (input : Solanalib.Runtime.Bytes) (o : DecodeOut (Option V)) :
    Solanalib.Specs.Borsh.Option.invalid_data.deserialize_reader_run ⟨Unit, Empty, Empty, V,
      Callback.ofFunction decode⟩
        before input o ↔ optionDecodeFn P decode before input = o :=
  optionDecodeRun_ofFunction P decode before input o

theorem byte_array_evaluated (n : Nat) (before : Unit) (input : Solanalib.Runtime.Bytes)
    (o : DecodeOut (FixedArray UInt8 n)) :
    Solanalib.Specs.Borsh.Array.invalid_data.deserialize_reader_run ⟨Unit, Empty, Empty, n, .byte⟩
      before input o ↔
      byteArrayDecodeFn P n before input = o :=
  arrayDecodeRun_byte P n before input o

theorem array_evaluated {V : Type} (n size : Nat) (decode : DecodeFn Unit V Empty Empty)
    (before : Unit) (input : Solanalib.Runtime.Bytes) (o : DecodeOut (FixedArray V n)) :
    Solanalib.Specs.Borsh.Array.invalid_data.deserialize_reader_run
        ⟨Unit, Empty, Empty, n, .other V size (Callback.ofFunction decode)⟩ before input o ↔
      arrayDecodeFn n decode before input = o :=
  arrayDecodeRun_ofFunction P n size decode before input o

theorem deserialize_evaluated {V : Type} (decode : DecodeFn Unit V Empty Empty) (before : Unit)
    (input : Solanalib.Runtime.Bytes) (o : DecodeOut V) :
    Solanalib.Specs.Borsh.de.BorshDeserialize.deserialize_run ⟨Unit, Empty, Empty, V,
      Callback.ofFunction decode⟩
        before input o ↔ deserializeFn decode before input = o :=
  deserializeRun_ofFunction decode before input o

theorem array_from_reader_evaluated (n : Nat) (before : Unit) (input : Solanalib.Runtime.Bytes)
    (o : DecodeOut (Option (FixedArray UInt8 n))) :
    Solanalib.Specs.Borsh.u8.invalid_data.array_from_reader_run ⟨n⟩ before input o ↔
      .returned (byteArrayFromReader P n input) before = o :=
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
  readerReference := "Solanalib.Specs.Borsh.Option.invalid_data.deserialize_reader_run"
  decode := optionDecodeFn P e.decode
  reader := Solanalib.Specs.Borsh.Option.invalid_data.deserialize_reader_run ⟨Unit, Empty, Empty,
    e.Value, Callback.ofFunction e.decode⟩
  reader_graph := option_evaluated e.decode

def byteArray (n : Nat) : Ty where
  rust := s!"[u8; {n}]"
  Value := FixedArray UInt8 n
  decEq := inferInstance
  parse := asFixedBytes n
  render := fun v => bytesJson v.val
  size := n
  readerFunction := "<[T; N] as borsh::de::BorshDeserialize>::deserialize_reader"
  readerGenerics := [("T", "u8"), ("N", toString n)]
  readerReference := "Solanalib.Specs.Borsh.Array.invalid_data.deserialize_reader_run"
  decode := byteArrayDecodeFn P n
  reader := Solanalib.Specs.Borsh.Array.invalid_data.deserialize_reader_run ⟨Unit, Empty, Empty, n,
    .byte⟩
  reader_graph := byte_array_evaluated n

def array (n : Nat) (e : Ty) : Ty where
  rust := s!"[{e.rust}; {n}]"
  Value := FixedArray e.Value n
  decEq := inferInstance
  parse := asFixedArray n e.parse
  render := fun v => listJson e.render v.val
  size := n * e.size
  readerFunction := "<[T; N] as borsh::de::BorshDeserialize>::deserialize_reader"
  readerGenerics := [("T", e.rust), ("N", toString n)]
  readerReference := "Solanalib.Specs.Borsh.Array.invalid_data.deserialize_reader_run"
  decode := arrayDecodeFn n e.decode
  reader := Solanalib.Specs.Borsh.Array.invalid_data.deserialize_reader_run
    ⟨Unit, Empty, Empty, n, .other e.Value e.size (Callback.ofFunction e.decode)⟩
  reader_graph := array_evaluated n e.size e.decode

/-- The default `deserialize` at `Self = t`, whose index callback is the `deserialize_reader` of
`t`. -/
def deserializeChecker (t : Ty) : Checker where
  function := "borsh::de::BorshDeserialize::deserialize"
  generics := [("Self", t.rust)]
  reference := "Solanalib.Specs.Borsh.de.BorshDeserialize.deserialize_run"
  decides := ["Solanalib.Specs.Borsh.de.BorshDeserialize.deserialize_run"]
  check := fun c => decideDecode t.parse t.render c
    (Solanalib.Specs.Borsh.de.BorshDeserialize.deserialize_run ⟨Unit, Empty, Empty, t.Value,
      Callback.ofFunction t.decode⟩ ())
    (deserializeFn t.decode ()) (deserialize_evaluated t.decode ())

def arrayFromReaderChecker (n : Nat) : Checker where
  function := "<u8 as borsh::de::BorshDeserialize>::array_from_reader"
  generics := [("R", "&[u8]"), ("N", toString n)]
  reference := "Solanalib.Specs.Borsh.u8.invalid_data.array_from_reader_run"
  decides := ["Solanalib.Specs.Borsh.u8.invalid_data.array_from_reader_run"]
  check := fun c => decideDecode (asOption (asFixedBytes n)) (optionJson fun v => bytesJson v.val) c
    (Solanalib.Specs.Borsh.u8.invalid_data.array_from_reader_run ⟨n⟩ ()) (fun input => .returned
      (byteArrayFromReader P n input) ())
    (array_from_reader_evaluated n ())

/-- Every instantiation recorded in `borsh_1_6_1.json` by the decoder cases. -/
def types : List Ty :=
  [u8, bool, u32, i32, u64, i64, f64, option u8, option u64, byteArray 32, array 2 u64]

def checkers : List Checker :=
  types.map readerChecker ++ types.map deserializeChecker ++
    [arrayFromReaderChecker 32, arrayFromReaderChecker 16, arrayFromReaderChecker 0]

end SolanalibTest.Conformance.Library.Borsh.V161
