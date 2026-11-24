/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Core
import Solanalib.Specs.Bytemuck.Bytes

/-!
# bytemuck 1.25.2 and 1.25.0

The families are indexed by a `Bytemuck.Encoding` (`T: NoUninit`) or
`Bytemuck.Decoding` (`T: AnyBitPattern`, `T: Zeroable`). Each `Pod` below is
the index for one Rust instantiation recorded by the driver. Its layout is
checked against the `size_of`/`align_of` recorded with every case, and its
byte order is exercised by the cases themselves; the instance is the interpretation of the test of
the Rust type, not part of the model.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Bytemuck

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Bytemuck

/-- One recorded instantiation `T`, with the conversions between its JSON
encoding and its Lean values. -/
structure Pod where
  rust : String
  Value : Type
  layout : Layout
  encode : Value → Solanalib.Runtime.Bytes
  encode_length : ∀ value, (encode value).length = layout.size
  decode : Solanalib.Runtime.Bytes → Value
  parse : Json → Result Value
  render : Value → Json
  decEq : DecidableEq Value
  /-- The instantiations the driver records for `try_from_bytes`/`zeroed`. -/
  anyBitPattern : Bool := true

def Pod.encoding (p : Pod) : Encoding := ⟨p.Value, p.layout, p.encode, p.encode_length⟩
def Pod.decoding (p : Pod) : Decoding := ⟨p.Value, p.layout, p.decode⟩

/-- Little-endian unsigned integers of `n` bytes, stored as `Nat` below `256 ^ n`. -/
def unsigned (rust : String) (n : Nat) (align : Nat) (k : Nat) (h : align = 2 ^ k)
    (aligned : n % align = 0) : Pod where
  rust := rust
  Value := Fin (256 ^ n)
  layout := ⟨n, align, ⟨k, h⟩, aligned⟩
  encode := fun v => Solanalib.Runtime.leBytes n v.val
  encode_length := fun _ => Solanalib.Runtime.length_leBytes _ _
  decode := fun b => ⟨Solanalib.Runtime.leNat b % 256 ^ n, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩
  parse := fun j => do
    let v ← asUInt (8 * n) j
    if h : v < 256 ^ n then pure ⟨v, h⟩ else throw s!"{v} out of range"
  render := fun v => toJson v.val
  decEq := inferInstance

def u8 : Pod := unsigned "u8" 1 1 0 rfl rfl
def u16 : Pod := unsigned "u16" 2 2 1 rfl rfl
def u32 : Pod := unsigned "u32" 4 4 2 rfl rfl
def u64 : Pod := unsigned "u64" 8 8 3 rfl rfl

/-- `i64`: binary radix complement, little-endian. -/
def i64 : Pod where
  rust := "i64"
  Value := Fin (2 ^ 64)
  layout := ⟨8, 8, ⟨3, rfl⟩, rfl⟩
  encode := fun v => Solanalib.Runtime.leBytes 8 v.val
  encode_length := fun _ => Solanalib.Runtime.length_leBytes _ _
  decode := fun b => ⟨Solanalib.Runtime.leNat b % 2 ^ 64, Nat.mod_lt _ (by decide)⟩
  parse := fun j => do
    let v ← asSInt 64 j
    let n := (v % (2 ^ 64 : Int)).toNat
    if h : n < 2 ^ 64 then pure ⟨n, h⟩ else throw s!"{v} out of range"
  render := fun v => toJson (if v.val < 2 ^ 63 then (v.val : Int) else (v.val : Int) - 2 ^ 64)
  decEq := inferInstance

/-- `f64`, by its IEEE-754 bit pattern: bytemuck moves bits, never values. -/
def f64 : Pod where
  rust := "f64"
  Value := UInt64
  layout := ⟨8, 8, ⟨3, rfl⟩, rfl⟩
  encode := fun v => Solanalib.Runtime.leBytes 8 v.toNat
  encode_length := fun _ => Solanalib.Runtime.length_leBytes _ _
  decode := fun b => UInt64.ofNat (Solanalib.Runtime.leNat b)
  parse := asF64Bits
  render := f64BitsJson
  decEq := inferInstance

/-- `[u8; 32]`. -/
def bytes32 : Pod where
  rust := "[u8; 32]"
  Value := Vector UInt8 32
  layout := ⟨32, 1, ⟨0, rfl⟩, rfl⟩
  encode := fun v => v.toList
  encode_length := fun v => by simp
  decode := fun b => Vector.ofFn fun i => b.getD i.val 0
  parse := fun j => do
    let b ← asBytes j
    if h : b.length = 32 then pure ⟨b.toArray, by simpa using h⟩ else throw "expected 32 \
      bytes"
  render := fun v => bytesJson v.toList
  decEq := inferInstance

/-- `[u64; 4]`. -/
def u64x4 : Pod where
  rust := "[u64; 4]"
  Value := Vector (Fin (2 ^ 64)) 4
  layout := ⟨32, 8, ⟨3, rfl⟩, rfl⟩
  encode := fun v => v.toList.flatMap fun x => Solanalib.Runtime.leBytes 8 x.val
  encode_length := fun v => by
    have h4 : v.toList.length = 4 := by simp
    show (v.toList.flatMap fun x => Solanalib.Runtime.leBytes 8 x.val).length = 32
    generalize v.toList = l at h4 ⊢
    match l, h4 with
    | [_, _, _, _], _ => simp
  decode := fun b => Vector.ofFn fun i =>
    ⟨Solanalib.Runtime.leNat ((b.drop (8 * i.val)).take 8) % 2 ^ 64, Nat.mod_lt _ (by decide)⟩
  parse := fun j => do
    let items ← j.getArr?
    let values ← items.toList.mapM fun x => do
      let n ← asUInt 64 x
      if h : n < 2 ^ 64 then pure (⟨n, h⟩ : Fin (2 ^ 64)) else throw "u64 out of range"
    if h : values.length = 4 then pure ⟨values.toArray, by simpa using h⟩
    else throw "expected 4 elements"
  render := fun v => Json.arr (v.toArray.map fun x => toJson x.val)
  decEq := inferInstance

/-- `bool`: `NoUninit` (recorded for `bytes_of`) and `Zeroable` (for
`zeroed`), but not `AnyBitPattern`; `decode` is applied only to valid
patterns, 0 and 1. -/
def bool : Pod where
  rust := "bool"
  Value := Bool
  layout := ⟨1, 1, ⟨0, rfl⟩, rfl⟩
  encode := fun v => [if v then 1 else 0]
  encode_length := fun _ => rfl
  decode := fun b => b.headD 0 != 0
  parse := fun j => j.getBool?
  render := fun v => toJson v
  decEq := inferInstance
  anyBitPattern := false

/-- `()`, the zero-sized `NoUninit` type. -/
def unit : Pod where
  rust := "()"
  Value := Unit
  layout := ⟨0, 1, ⟨0, rfl⟩, rfl⟩
  encode := fun _ => []
  encode_length := fun _ => rfl
  decode := fun _ => ()
  parse := asUnit
  render := fun _ => Json.null
  decEq := inferInstance

/-- `[u64; 0]`, zero-sized with alignment eight. -/
def u64x0 : Pod where
  rust := "[u64; 0]"
  Value := Unit
  layout := ⟨0, 8, ⟨3, rfl⟩, rfl⟩
  encode := fun _ => []
  encode_length := fun _ => rfl
  decode := fun _ => ()
  parse := fun j => do
    let items ← j.getArr?
    if items.isEmpty then pure () else throw "expected []"
  render := fun _ => Json.arr #[]
  decEq := inferInstance

def pods : List Pod := [u8, u16, u32, u64, i64, f64, bytes32, u64x4]

def checkLayout (p : Pod) (c : Case) : Result Unit := do
  let some l := c.layout | throw "record has no layout"
  let size ← (← field l "size").getNat?
  let align ← (← field l "align").getNat?
  unless size = p.layout.size ∧ align = p.layout.align do
    throw
      s!"layout mismatch for {p.rust}: Rust size {size} align {align}, index size \
        {p.layout.size} align {p.layout.align}"

def sliceRef (j : Json) : Result SliceRef := do
  pure ⟨← (← field j "address").getNat?, ← asBytes (← field j "bytes")⟩

def sliceRefJson (s : SliceRef) : Json :=
  Json.mkObj [("address", toJson s.address), ("bytes", bytesJson s.bytes)]

def typedRef {V : Type} (value : Json → Result V) (j : Json) : Result (TypedRef V) := do
  pure ⟨← (← field j "address").getNat?, ← value (← field j "value")⟩

def typedRefJson {V : Type} (render : V → Json) (t : TypedRef V) : Json :=
  Json.mkObj [("address", toJson t.address), ("value", render t.value)]

def podCastError (j : Json) : Result PodCastError := do
  match ← j.getStr? with
  | "TargetAlignmentGreaterAndInputNotAligned" => pure .TargetAlignmentGreaterAndInputNotAligned
  | "OutputSliceWouldHaveSlop" => pure .OutputSliceWouldHaveSlop
  | "SizeMismatch" => pure .SizeMismatch
  | "AlignmentMismatch" => pure .AlignmentMismatch
  | other => throw s!"unknown PodCastError {other}"

def podCastErrorJson : PodCastError → Json
  | .TargetAlignmentGreaterAndInputNotAligned => "TargetAlignmentGreaterAndInputNotAligned"
  | .OutputSliceWouldHaveSlop => "OutputSliceWouldHaveSlop"
  | .SizeMismatch => "SizeMismatch"
  | .AlignmentMismatch => "AlignmentMismatch"

/-! ## The evaluated functions are the registered references -/

theorem bytes_of_evaluated (e : Encoding) :
    Solanalib.Specs.Bytemuck.bytes_of_run e = returnsOf (Solanalib.Specs.Bytemuck.bytes_of_model e)
      := rfl

theorem try_from_bytes_evaluated (d : Decoding) :
    Solanalib.Specs.Bytemuck.try_from_bytes_run d = returnsOf
      (Solanalib.Specs.Bytemuck.try_from_bytes_model d) := rfl

theorem zeroed_evaluated (d : Decoding) :
    Solanalib.Specs.Bytemuck.zeroable.Zeroable.zeroed_run d =
      returnsOf (Solanalib.Specs.Bytemuck.zeroable.Zeroable.zeroed_model d) := rfl

/-! ## Checkers -/

def bytesOfChecker (p : Pod) : Checker where
  function := "bytemuck::bytes_of"
  generics := [("T", p.rust)]
  reference := "Solanalib.Specs.Bytemuck.bytes_of_run"
  decides := ["Solanalib.Specs.Bytemuck.bytes_of_run"]
  check := fun c => do
    checkLayout p c
    have := p.decEq
    decideReturns (State := Unit) (Args := TypedRef p.Value) (Value := SliceRef)
      (Solanalib.Specs.Bytemuck.bytes_of_run p.encoding) (Solanalib.Specs.Bytemuck.bytes_of_model
        p.encoding)
      (bytes_of_evaluated p.encoding) (← asUnit c.state) (← typedRef p.parse c.args)
      sliceRef asUnit sliceRefJson (fun _ => Json.null) c.outcome

def tryFromBytesChecker (p : Pod) : Checker where
  function := "bytemuck::try_from_bytes"
  generics := [("T", p.rust)]
  reference := "Solanalib.Specs.Bytemuck.try_from_bytes_run"
  decides := ["Solanalib.Specs.Bytemuck.try_from_bytes_run"]
  check := fun c => do
    checkLayout p c
    have := p.decEq
    decideReturns (State := Unit) (Args := SliceRef) (Value := Except PodCastError (TypedRef
      p.Value))
      (Solanalib.Specs.Bytemuck.try_from_bytes_run p.decoding)
        (Solanalib.Specs.Bytemuck.try_from_bytes_model p.decoding)
      (try_from_bytes_evaluated p.decoding) (← asUnit c.state) (← sliceRef c.args)
      (asExcept podCastError (typedRef p.parse)) asUnit
      (exceptJson podCastErrorJson (typedRefJson p.render)) (fun _ => Json.null) c.outcome

def zeroedChecker (p : Pod) : Checker where
  function := "bytemuck::zeroable::Zeroable::zeroed"
  generics := [("Self", p.rust)]
  reference := "Solanalib.Specs.Bytemuck.zeroable.Zeroable.zeroed_run"
  decides := ["Solanalib.Specs.Bytemuck.zeroable.Zeroable.zeroed_run"]
  check := fun c => do
    checkLayout p c
    have := p.decEq
    decideReturns (State := Unit) (Args := Unit) (Value := p.Value)
      (Solanalib.Specs.Bytemuck.zeroable.Zeroable.zeroed_run p.decoding)
      (Solanalib.Specs.Bytemuck.zeroable.Zeroable.zeroed_model p.decoding)
      (zeroed_evaluated p.decoding) (← asUnit c.state) (← asUnit c.args)
      p.parse asUnit p.render (fun _ => Json.null) c.outcome

/-- Checkers per corpus file. -/
def bytemuck_1_25_2 : List Checker :=
  (pods ++ [bool, unit]).map bytesOfChecker ++ (pods ++ [bool]).map zeroedChecker

def bytemuck_1_25_0 : List Checker :=
  (pods ++ [u64x0]).map tryFromBytesChecker ++ (pods ++ [bool]).map zeroedChecker

end SolanalibTest.Conformance.Library.Bytemuck
