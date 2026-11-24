/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Runtime.Basic
public import Solanalib.Specs.Core.Float64

@[expose] public section

set_option autoImplicit false

/-! Version-independent borsh wire format over byte slices.

Decoders are stated at `R = &[u8]`: a decoder maps the current slice to the
result and the remaining slice. With the default `std` feature, a short
`read_exact` on a slice empties the slice before reporting the error; every
short read below therefore returns the empty remainder. Versions differ only in
the `io::ErrorKind` of their decoding errors and in the zero-sized collection
message, which a `Profile` supplies. -/

namespace Solanalib.Specs.Core.Borsh

/-- A `std::io::ErrorKind`, identified by its `Debug` name. -/
structure ErrorKind where
  debugName : String
  deriving DecidableEq, Repr

namespace ErrorKind

def invalidInput : ErrorKind := ⟨"InvalidInput"⟩
def invalidData : ErrorKind := ⟨"InvalidData"⟩

end ErrorKind

/-- The observation of a `std::io::Error`: its kind and its `to_string()`. For
`io::Error::new(kind, msg)` the string is `msg`. -/
structure IoError where
  kind : ErrorKind
  message : String
  deriving DecidableEq, Repr

/-! ## Exact source messages -/

def unexpectedLengthMessage : String := "Unexpected length of input"
def notAllBytesReadMessage : String := "Not all bytes read"
def deserializeNaNMessage : String :=
  "For portability reasons we do not allow to deserialize NaNs."
def serializeNaNMessage : String :=
  "For portability reasons we do not allow to serialize NaNs."
/-- `format!("Invalid bool representation: {}", b)` with a decimal `u8`. -/
def invalidBoolMessage (tag : UInt8) : String :=
  "Invalid bool representation: " ++ toString tag.toNat
/-- `format!("Invalid Option representation: {}. The first byte must be 0 or 1", flag)`. -/
def invalidOptionMessage (tag : UInt8) : String :=
  "Invalid Option representation: " ++ toString tag.toNat ++ ". The first byte must be 0 \
    or 1"
/-- borsh 0.10.x `Vec<T>` rejection of a zero-sized `T`. -/
def zeroSizedVectorMessage : String :=
  "Vectors of zero-sized types are not allowed due to deny-of-service concerns on \
    deserialization."
/-- borsh 1.x `check_zst` (`ERROR_ZST_FORBIDDEN`). -/
def zeroSizedCollectionMessage : String :=
  "Collections of zero-sized types are not allowed due to deny-of-service concerns on \
    deserialization."

/-- Version data. `decodeErrorKind` is the kind of short-input, invalid tag,
NaN and zero-sized-collection decoding errors. -/
structure Profile where
  decodeErrorKind : ErrorKind
  zeroSizedMessage : String
  deriving DecidableEq, Repr

namespace Profile

def unexpectedLength (profile : Profile) : IoError :=
  ⟨profile.decodeErrorKind, unexpectedLengthMessage⟩
def invalidBool (profile : Profile) (tag : UInt8) : IoError :=
  ⟨profile.decodeErrorKind, invalidBoolMessage tag⟩
def invalidOption (profile : Profile) (tag : UInt8) : IoError :=
  ⟨profile.decodeErrorKind, invalidOptionMessage tag⟩
def deserializeNaN (profile : Profile) : IoError :=
  ⟨profile.decodeErrorKind, deserializeNaNMessage⟩
def zeroSized (profile : Profile) : IoError :=
  ⟨profile.decodeErrorKind, profile.zeroSizedMessage⟩

end Profile

/-- `try_from_slice` leftover bytes, `InvalidData` in both selected versions. -/
def notAllBytesRead : IoError := ⟨.invalidData, notAllBytesReadMessage⟩
/-- borsh 1.x float serialization of a NaN. -/
def serializeNaN : IoError := ⟨.invalidData, serializeNaNMessage⟩

/-! ## Values -/

/-- A Rust `[T; N]` value. -/
abbrev FixedArray (α : Type) (n : Nat) := { values : List α // values.length = n }

def FixedArray.cons {α : Type} {n : Nat} (head : α) (tail : FixedArray α n) :
    FixedArray α (n + 1) :=
  ⟨head :: tail.val, by simp [tail.property]⟩

/-- Binary64 NaN test on the exact bit pattern (`f64::is_nan`). -/
def isNaN (bits : Float64.Bits) : Bool :=
  match Float64.decode bits with
  | .nan => true
  | _ => false

/-! ## Pure decoders at `R = &[u8]` -/

/-- A decoder at `R = &[u8]`: result and remaining slice. -/
abbrev Decoder (α : Type) := Solanalib.Runtime.Bytes → Except IoError α × Solanalib.Runtime.Bytes

namespace Decoder

def map {α β : Type} (f : α → β) (decoder : Decoder α) : Decoder β := fun input =>
  match decoder input with
  | (result, remaining) => (result.map f, remaining)

/-- Sequencing with `?`: an error returns at once with the slice it left. -/
def bind {α β : Type} (decoder : Decoder α) (next : α → Decoder β) : Decoder β := fun input =>
  match decoder input with
  | (.error error, remaining) => (.error error, remaining)
  | (.ok value, remaining) => next value remaining

def pure {α : Type} (value : α) : Decoder α := fun input => (.ok value, input)

end Decoder

/-- `read_exact` of `n` bytes with the borsh error mapping: a short slice is
emptied and reports `Unexpected length of input`. -/
def takeExact (profile : Profile) (n : Nat) : Decoder Solanalib.Runtime.Bytes := fun input =>
  if n ≤ input.length then (.ok (input.take n), input.drop n)
  else (.error profile.unexpectedLength, [])

def decodeU8 (profile : Profile) : Decoder UInt8 :=
  (takeExact profile 1).map fun bytes => UInt8.ofNat (Solanalib.Runtime.leNat bytes)
def decodeU16 (profile : Profile) : Decoder UInt16 :=
  (takeExact profile 2).map fun bytes => UInt16.ofNat (Solanalib.Runtime.leNat bytes)
def decodeU32 (profile : Profile) : Decoder UInt32 :=
  (takeExact profile 4).map fun bytes => UInt32.ofNat (Solanalib.Runtime.leNat bytes)
def decodeU64 (profile : Profile) : Decoder UInt64 :=
  (takeExact profile 8).map fun bytes => UInt64.ofNat (Solanalib.Runtime.leNat bytes)
def decodeI8 (profile : Profile) : Decoder Int8 := (decodeU8 profile).map UInt8.toInt8
def decodeI16 (profile : Profile) : Decoder Int16 := (decodeU16 profile).map UInt16.toInt16
def decodeI32 (profile : Profile) : Decoder Int32 := (decodeU32 profile).map UInt32.toInt32
def decodeI64 (profile : Profile) : Decoder Int64 := (decodeU64 profile).map UInt64.toInt64

/-- `f64` from its little-endian bits; a NaN is rejected after its 8 bytes. -/
def decodeF64 (profile : Profile) : Decoder Float64.Bits := fun input =>
  match decodeU64 profile input with
  | (.error error, remaining) => (.error error, remaining)
  | (.ok bits, remaining) =>
    if isNaN bits then (.error profile.deserializeNaN, remaining) else (.ok bits, remaining)

def decodeBool (profile : Profile) : Decoder Bool := fun input =>
  match decodeU8 profile input with
  | (.error error, remaining) => (.error error, remaining)
  | (.ok tag, remaining) =>
    if tag = 0 then (.ok false, remaining)
    else if tag = 1 then (.ok true, remaining)
    else (.error (profile.invalidBool tag), remaining)

/-- `[u8; N]` through `u8::array_from_reader`: one `read_exact` of `N` bytes. -/
def decodeByteArray (profile : Profile) (n : Nat) : Decoder (FixedArray UInt8 n) := fun input =>
  if h : n ≤ input.length then
    (.ok ⟨input.take n, by simp [List.length_take, h]⟩, input.drop n)
  else (.error profile.unexpectedLength, [])


/-! ## Contract agreement with a reference decoding -/

/-- The contract-level agreement of an actual decoding with the reference
decoding of the same slice: the same result, and on success the same remaining
slice. After an error the remaining slice is unconstrained. The reference
follows the `std` slice reader, which empties the slice on a short read;
the `nostd_io` reader of borsh leaves it unchanged, and callers that propagate the
error with `?` or discard the slice do not observe the difference. -/
def DecodeMatches {α : Type} (expected actual : Except IoError α × Solanalib.Runtime.Bytes) : Prop
  :=
  match expected with
  | (.ok value, remaining) => actual = (.ok value, remaining)
  | (.error error, _) => actual.1 = .error error

theorem DecodeMatches.refl {α : Type} (result : Except IoError α × Solanalib.Runtime.Bytes) :
    DecodeMatches result result := by
  rcases result with ⟨_ | _, _⟩ <;> rfl

/-- Structural decidability of `Except`, for finite controls and differential
checks (`local instance` at the use site). -/
def exceptDecEq {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok x, .ok y => if same : x = y then isTrue (same ▸ rfl)
      else isFalse (fun equal => same (Except.ok.inj equal))
  | .error x, .error y => if same : x = y then isTrue (same ▸ rfl)
      else isFalse (fun equal => same (Except.error.inj equal))
  | .ok _, .error _ => isFalse (by intro equal; cases equal)
  | .error _, .ok _ => isFalse (by intro equal; cases equal)

/-! ## Pure encoders

Each encoder returns its exact sequence of `write_all` chunks, or a borsh
error raised before any write. -/

abbrev Encoder (α : Type) := α → Except IoError (List Solanalib.Runtime.Bytes)

def encodeU8 : Encoder UInt8 := fun value => .ok [[value]]
def encodeBool : Encoder Bool := fun value => .ok [[if value then 1 else 0]]
def encodeU16 : Encoder UInt16 := fun value => .ok [Solanalib.Runtime.leBytes 2 value.toNat]
def encodeU32 : Encoder UInt32 := fun value => .ok [Solanalib.Runtime.leBytes 4 value.toNat]
def encodeU64 : Encoder UInt64 := fun value => .ok [Solanalib.Runtime.leBytes 8 value.toNat]
def encodeI8 : Encoder Int8 := fun value => .ok [Solanalib.Runtime.leBytes 1 value.toUInt8.toNat]
def encodeI16 : Encoder Int16 := fun value => .ok [Solanalib.Runtime.leBytes 2 value.toUInt16.toNat]
def encodeI32 : Encoder Int32 := fun value => .ok [Solanalib.Runtime.leBytes 4 value.toUInt32.toNat]
def encodeI64 : Encoder Int64 := fun value => .ok [Solanalib.Runtime.leBytes 8 value.toUInt64.toNat]
/-- borsh 1.x float serialization: NaN fails before any write. -/
def encodeF64 : Encoder Float64.Bits := fun bits =>
  if isNaN bits then .error serializeNaN else .ok [Solanalib.Runtime.leBytes 8 bits.toNat]

/-- The concatenated output of an encoder whose writes all succeed. -/
def Encoder.bytes {α : Type} (encoder : Encoder α) (value : α) : Except IoError
  Solanalib.Runtime.Bytes :=
  (encoder value).map List.flatten

end Solanalib.Specs.Core.Borsh
