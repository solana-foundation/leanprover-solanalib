/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Core
import Solanalib.Specs.Core.BorshFamily

/-!
# Shared borsh record mappings

Decoders are recorded at `R = &[u8]`: the `state.slice` of the record is the slice
before the call and the `state.slice` of the outcome the slice after it. The models
take that slice as their argument and return `(result, remaining slice)` with
state `()`, so a record maps to `before := ()`, `input := state.slice` and the
returned value `(result, outcome.state.slice)`.

Serializers are recorded over two writers `W`: the `RecordingWriter` of the recorder (state: every
`write_all` call with its result; argument: the
call index at which it fails) and `Vec<u8>` (state: the bytes of the vector). The
`WriterFn`s below are the interpretations of those writers, the index of the
serializer families; they are test choices, not models.

A type `T` used as a family index (`Option<T>`, `[T; N]`, `Vec<T>`, `Self`) is
interpreted by the registered model of the member of `T`, so a generic member is
checked as the composition of registered models.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Borsh

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh

/-! ## Errors and values -/

def ioError (j : Json) : Result IoError := do
  pure ⟨⟨← (← field j "kind").getStr?⟩, ← (← field j "message").getStr?⟩

def ioErrorJson (e : IoError) : Json :=
  Json.mkObj [("kind", Json.str e.kind.debugName), ("message", Json.str e.message)]

def asOption {α : Type} (value : Json → Result α) (j : Json) : Result (Option α) :=
  match j with
  | .null => pure none
  | _ => do pure (some (← value (← field j "some")))

def optionJson {α : Type} (render : α → Json) : Option α → Json
  | none => Json.null
  | some v => Json.mkObj [("some", render v)]

def asFixedBytes (n : Nat) (j : Json) : Result (FixedArray UInt8 n) := do
  let b ← asBytes j
  if h : b.length = n then pure ⟨b, h⟩ else throw s!"expected {n} bytes, got {b.length}"

def asFixedArray {α : Type} (n : Nat) (value : Json → Result α) (j : Json) :
    Result (FixedArray α n) := do
  let items ← (← j.getArr?).toList.mapM value
  if h : items.length = n then pure ⟨items, h⟩ else throw s!"expected {n} elements"

def asList {α : Type} (value : Json → Result α) (j : Json) : Result (List α) := do
  (← j.getArr?).toList.mapM value

def listJson {α : Type} (render : α → Json) (xs : List α) : Json := Json.arr (xs.map render).toArray

/-- A decoded type `T` with the function form of its `deserialize_reader` at
`R = &[u8]`, the registered relation of that member at this instantiation and
the graph lemma of the model relating them. -/
structure Ty where
  rust : String
  Value : Type
  decEq : DecidableEq Value
  parse : Json → Result Value
  render : Value → Json
  /-- `size_of::<T>()`, for `Vec<T>` and `[T; N]` element indices. -/
  size : Nat
  /-- Item path and generic parameters of `<T as BorshDeserialize>::deserialize_reader`. -/
  readerFunction : String
  readerGenerics : List (String × String)
  /-- The registered reference of that member, for the report. -/
  readerReference : String
  decode : DecodeFn Unit Value Empty Empty
  reader : Unit → Solanalib.Runtime.Bytes → Outcome Unit (Except IoError Value ×
    Solanalib.Runtime.Bytes) Empty Empty → Prop
  reader_graph : ∀ before input outcome, reader before input outcome ↔ decode before input = outcome

instance (t : Ty) : DecidableEq t.Value := t.decEq

abbrev DecodeOut (V : Type) := Outcome Unit (Except IoError V × Solanalib.Runtime.Bytes) Empty Empty

/-- A plain decoder member `model : Unit → Bytes → (result, remaining) × Unit`,
registered with `contract.RealizedBy model`: its graph is decided. -/
def primitive (rust : String) (Value : Type) [DecidableEq Value] (parse : Json → Result Value)
    (render : Value → Json) (size : Nat) (reference : String)
    (model : Unit → Solanalib.Runtime.Bytes → (Except IoError Value × Solanalib.Runtime.Bytes) ×
      Unit) : Ty where
  rust := rust
  Value := Value
  decEq := inferInstance
  parse := parse
  render := render
  size := size
  readerFunction := s!"<{rust} as borsh::de::BorshDeserialize>::deserialize_reader"
  readerGenerics := []
  readerReference := reference
  decode := fun before input => .returned (model before input).1 (model before input).2
  reader := returnsOf model
  reader_graph := fun before input outcome => returnsOf_iff model before input outcome

def uintParse (bits : Nat) (j : Json) : Result Nat := asUInt bits j

def u8Parse (j : Json) : Result UInt8 := do pure (UInt8.ofNat (← asUInt 8 j))
def u32Parse (j : Json) : Result UInt32 := do pure (UInt32.ofNat (← asUInt 32 j))
def u64Parse (j : Json) : Result UInt64 := do pure (UInt64.ofNat (← asUInt 64 j))
def i8Parse (j : Json) : Result Int8 := do pure (Int8.ofInt (← asSInt 8 j))
def i32Parse (j : Json) : Result Int32 := do pure (Int32.ofInt (← asSInt 32 j))
def i64Parse (j : Json) : Result Int64 := do pure (Int64.ofInt (← asSInt 64 j))
def boolParse (j : Json) : Result Bool := j.getBool?

def u8Json (v : UInt8) : Json := toJson v.toNat
def u32Json (v : UInt32) : Json := toJson v.toNat
def u64Json (v : UInt64) : Json := toJson v.toNat
def i8Json (v : Int8) : Json := toJson v.toInt
def i32Json (v : Int32) : Json := toJson v.toInt
def i64Json (v : Int64) : Json := toJson v.toInt
def boolJson (v : Bool) : Json := toJson v

/-! ## Decoder records -/

def decodeOutcome {V : Type} (parse : Json → Result V) (j : Json) : Result (Option (DecodeOut V))
  := do
  match ← (← field j "exit").getStr? with
  | "returned" =>
    let result ← asExcept ioError parse (← field j "result")
    let remaining ← asBytes (← field (← field j "state") "slice")
    return some (.returned (result, remaining) ())
  | "unwound" | "terminated" => return none
  | other => throw s!"unknown exit {other}"

def decodeOutcomeJson {V : Type} (render : V → Json) : DecodeOut V → Json
  | .returned (result, remaining) () =>
    returnedJson (exceptJson ioErrorJson render result) (Json.mkObj [("slice", bytesJson
      remaining)])
  | .unwound e _ => nomatch e
  | .terminated e => nomatch e

def slice (c : Case) : Result Solanalib.Runtime.Bytes := do asBytes (← field c.state "slice")

/-- Decide a decoder record against `relation () input`, given the graph lemma of the model for the
computed outcome. -/
def decideDecode {V : Type} [DecidableEq V] (parse : Json → Result V) (render : V → Json)
    (c : Case) (relation : Solanalib.Runtime.Bytes → DecodeOut V → Prop) (decode :
      Solanalib.Runtime.Bytes → DecodeOut V)
    (graph : ∀ input o, relation input o ↔ decode input = o) : Result Verdict := do
  let input ← slice c
  pure (decideGraph (relation input) (decode input) (graph input) (← decodeOutcome parse c.outcome)
    (decodeOutcomeJson render))

/-- `<T as BorshDeserialize>::deserialize_reader::<&[u8]>`. -/
def readerChecker (t : Ty) : Checker where
  function := t.readerFunction
  generics := t.readerGenerics ++ [("R", "&[u8]")]
  reference := t.readerReference
  decides := [t.readerReference]
  check := fun c => decideDecode t.parse t.render c (t.reader ()) (t.decode ()) (t.reader_graph ())

/-! ## Writers -/

/-- One `write_all` call received by the recording writer. -/
structure WriteEvent where
  bytes : Solanalib.Runtime.Bytes
  failure : Option IoError
  deriving DecidableEq

/-- The `RecordingWriter` of the recorder: logs every chunk and fails at call
`failAt` (0-based) with `injected`, without accepting the chunk. -/
def recordingWriterFn (failAt : Option Nat) (injected : IoError) :
    WriterFn (List WriteEvent) Empty Empty :=
  fun events chunk =>
    if failAt = some events.length then .returned (.error injected) (events ++ [⟨chunk, some
      injected⟩])
    else .returned (.ok ()) (events ++ [⟨chunk, none⟩])

/-- `<Vec<u8> as Write>::write_all`: appends, never fails. -/
def vecWriterFn : WriterFn Solanalib.Runtime.Bytes Empty Empty :=
  fun contents chunk => .returned (.ok ()) (contents ++ chunk)

def writeEvent (j : Json) : Result WriteEvent := do
  let op ← (← field j "op").getStr?
  unless op == "write_all" do throw s!"writer received {op}, which no serializer model \
    issues"
  let bytes ← asBytes (← field j "bytes")
  let failure ← match ← asExcept ioError asUnit (← field j "result") with
    | .ok () => pure none
    | .error e => pure (some e)
  pure ⟨bytes, failure⟩

def writeEventJson (e : WriteEvent) : Json :=
  Json.mkObj [("op", "write_all"), ("bytes", bytesJson e.bytes),
    ("result", match e.failure with | none => okJson Json.null | some f => errJson (ioErrorJson f))]

def eventsState (j : Json) : Result (List WriteEvent) := do asList writeEvent (← field j
  "events")
def eventsJson (events : List WriteEvent) : Json := Json.mkObj [("events", listJson writeEventJson
  events)]

def vecState (j : Json) : Result Solanalib.Runtime.Bytes := do asBytes (← field j "vec")
def vecJson (contents : Solanalib.Runtime.Bytes) : Json := Json.mkObj [("vec", bytesJson contents)]

/-- The writer `W` of a serializer record. -/
inductive WriterKind where
  | recording
  | vec

def writerKind (c : Case) : Result WriterKind :=
  match c.generics.lookup "W" with
  | some "conformance_recorder::RecordingWriter" => pure .recording
  | some "alloc::vec::Vec<u8>" => pure .vec
  | other => throw s!"unknown writer {other}"

def writerPlan (c : Case) : Result (Option Nat × IoError) := do
  let w ← field c.args "writer"
  let failAt ← match ← field w "fail_at" with
    | .null => pure none
    | j => do pure (some (← j.getNat?))
  pure (failAt, ← ioError (← field w "error"))

abbrev SerOut (S : Type) := Outcome S (Except IoError Unit) Empty Empty

def serOutcome {S : Type} (state : Json → Result S) (j : Json) : Result (Option (SerOut S)) := do
  match ← (← field j "exit").getStr? with
  | "returned" =>
    return some (.returned (← asExcept ioError asUnit (← field j "result")) (← state (← field j
      "state")))
  | "unwound" | "terminated" => return none
  | other => throw s!"unknown exit {other}"

def serOutcomeJson {S : Type} (render : S → Json) : SerOut S → Json
  | .returned result after => returnedJson (exceptJson ioErrorJson (fun _ => Json.null) result)
    (render after)
  | .unwound e _ => nomatch e
  | .terminated e => nomatch e

/-- A serializer instantiated at a writer: the registered relation at the index of the
writer, the function form, and the graph lemma of the model. -/
structure SerializerAt (S Value : Type) where
  relation : S → Value → SerOut S → Prop
  serialize : SerializeFn S Value Empty Empty
  graph : ∀ before value o, relation before value o ↔ serialize before value = o

/-- Decide a serializer record at either writer. `at` builds the instantiated
serializer from a writer function. -/
def decideSerialize {Value : Type} (parse : Json → Result Value) (c : Case)
    (at_ : {S : Type} → WriterFn S Empty Empty → SerializerAt S Value) : Result Verdict := do
  let value ← parse (← field c.args "value")
  match ← writerKind c with
  | .recording =>
    let (failAt, injected) ← writerPlan c
    let s := at_ (recordingWriterFn failAt injected)
    let before ← eventsState c.state
    pure (decideGraph (s.relation before value) (s.serialize before value) (s.graph before value)
      (← serOutcome eventsState c.outcome) (serOutcomeJson eventsJson))
  | .vec =>
    let s := at_ vecWriterFn
    let before ← vecState c.state
    pure (decideGraph (s.relation before value) (s.serialize before value) (s.graph before value)
      (← serOutcome vecState c.outcome) (serOutcomeJson vecJson))

end SolanalibTest.Conformance.Library.Borsh
