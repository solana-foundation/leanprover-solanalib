/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorCodec
public import Solanalib.Specs.Core.AnchorErrorOperations
public import Solanalib.Specs.Core.OwnedVector

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorCodec

/-- The exact IDL discriminants in Anchor 0.27. The Write variant owns its byte
vector; no vector observation is substituted for that owner in the full model. -/
inductive IdlValue (BytesOwner : Type) where
  | create (dataLength : UInt64)
  | createBuffer
  | write (data : BytesOwner)
  | setBuffer
  | setAuthority (authority : Solanalib.Runtime.Pubkey)
  | close
  | resize (dataLength : UInt64)
  deriving DecidableEq, Repr

def idlUnexpectedLength : Borsh.IoError :=
  ⟨.invalidInput, Borsh.unexpectedLengthMessage⟩

/-- Borsh 0.9.3 checks the entire field length before touching the cursor.
This differs from a later the short-read behavior of std read_exact. -/
def legacyTake (count : Nat) : Borsh.Decoder Solanalib.Runtime.Bytes := fun input =>
  if count ≤ input.length then (.ok (input.take count), input.drop count)
  else (.error idlUnexpectedLength, input)

def legacyU32 : Borsh.Decoder UInt32 :=
  (legacyTake 4).map fun bytes => UInt32.ofNat (Solanalib.Runtime.leNat bytes)

def legacyU64 : Borsh.Decoder UInt64 :=
  (legacyTake 8).map fun bytes => UInt64.ofNat (Solanalib.Runtime.leNat bytes)

/-- On the reviewed 64-bit source target the u32 length always fits usize.
The Vec<u8> specialization checks the payload before its one to_vec call. -/
def legacyByteVec : Borsh.Decoder Solanalib.Runtime.Bytes :=
  legacyU32.bind fun length => legacyTake length.toNat

/-- The generated Borsh 0.9.3 enum decoder, with all seven arms and the exact
unknown-tag error. Successful decoding permits and retains trailing input. -/
def decodeIdl : Borsh.Decoder (IdlValue Solanalib.Runtime.Bytes) := fun input =>
  match input with
  | [] => (.error idlUnexpectedLength, [])
  | tag :: rest =>
    match tag.toNat with
    | 0 => (legacyU64.map IdlValue.create) rest
    | 1 => (.ok .createBuffer, rest)
    | 2 => (legacyByteVec.map IdlValue.write) rest
    | 3 => (.ok .setBuffer, rest)
    | 4 => ((legacyTake 32).map (IdlValue.setAuthority ∘ Solanalib.Runtime.Pubkey.ofBytes)) rest
    | 5 => (.ok .close, rest)
    | 6 => (legacyU64.map IdlValue.resize) rest
    | _ => (.error ⟨.invalidInput, "Unexpected variant index: " ++ toString tag.toNat⟩, rest)

/-- Relocate only a Write payload to its actual vector owner. All other enum
arms are copied without allocating a fictitious byte vector. -/
def IdlValue.withOwner {Owner : Type} (owner : Owner) : IdlValue Solanalib.Runtime.Bytes → IdlValue
  Owner
  | .create length => .create length
  | .createBuffer => .createBuffer
  | .write _ => .write owner
  | .setBuffer => .setBuffer
  | .setAuthority authority => .setAuthority authority
  | .close => .close
  | .resize length => .resize length

/-- The returned vector and diagnostic error have explicit owned identities.
Only the reached dependency is called; malformed input never allocates a Vec. -/
structure IdlTypes where
  State : Type
  Vector : Type
  Error : Type
  Terminal : Type
  vectors : Owned.VectorOps State UInt8 Vector Empty Terminal
  makeError : Callback.Run State Borsh.IoError Error Empty Terminal

def idlRun (types : IdlTypes) : Callback.Run types.State Solanalib.Runtime.Bytes
    (Except types.Error (IdlValue types.Vector) × Solanalib.Runtime.Bytes) Empty types.Terminal :=
  fun before input outcome =>
    match decodeIdl input with
    | (.error error, remaining) =>
      Callback.map (fun owned => (.error owned, remaining)) types.makeError before error outcome
    | (.ok value, remaining) =>
      match value with
      | .write [] =>
        let allocated := types.vectors.empty before
        outcome = .returned (.ok (.write allocated.1), remaining) allocated.2
      | .write (byte :: rest) =>
        Callback.map (fun owner => (.ok (.write owner), remaining)) types.vectors.fromList
          before (byte :: rest) outcome
      | .create length => outcome = .returned (.ok (.create length), remaining) before
      | .createBuffer => outcome = .returned (.ok .createBuffer, remaining) before
      | .setBuffer => outcome = .returned (.ok .setBuffer, remaining) before
      | .setAuthority authority => outcome = .returned (.ok (.setAuthority authority), remaining)
        before
      | .close => outcome = .returned (.ok .close, remaining) before
      | .resize length => outcome = .returned (.ok (.resize length), remaining) before

def idlFamily : Family where
  Index := IdlTypes
  State := IdlTypes.State
  Args := fun _ => Solanalib.Runtime.Bytes
  Value := fun types => Except types.Error (IdlValue types.Vector) × Solanalib.Runtime.Bytes
  Unwind := fun _ => Empty
  Terminal := IdlTypes.Terminal
  contract := fun types => { requires := fun _ _ => True, post := idlRun types }

theorem idl_reference : FamilyReference idlFamily idlRun := fun _ _ _ _ _ run => run

abbrev idlSample : IdlTypes where
  State := Owned.VectorState UInt8
  Vector := Nat
  Error := Borsh.IoError
  Terminal := Empty
  vectors := Owned.vectorReference
  makeError := fun before error outcome => outcome = .returned error before

theorem idl_execution : FamilyHasExecution idlFamily idlRun idlSample := by
  refine ⟨[], [2, 2, 0, 0, 0, 17, 18, 99],
    .returned (.ok (.write (0 : Nat)), [99]) [some [17, 18]], trivial, ?_⟩
  exact ⟨.returned (0 : Nat) [some [17, 18]], rfl, rfl⟩

theorem idl_satisfiable : FamilySatisfiable idlFamily idlSample := idl_execution.satisfiable

/-- The loader state has no trailing data buffer field. Extra bytes in an
account are allowed by the selected allow_trailing_bytes configuration of bincode. -/
inductive LoaderState where
  | uninitialized
  | buffer (authority : Option Solanalib.Runtime.Pubkey)
  | program (programData : Solanalib.Runtime.Pubkey)
  | programData (slot : UInt64) (authority : Option Solanalib.Runtime.Pubkey)
  deriving DecidableEq, Repr

/-- The distinguishable bincode failure sites. Their owned diagnostic objects
are created and dropped by explicit dependency operations in the full model. -/
inductive LoaderFailure where
  | unexpectedEof
  | invalidVariant (tag : UInt32)
  | invalidOption (tag : UInt8)
  deriving DecidableEq, Repr

def loaderTake (count : Nat) (input : Solanalib.Runtime.Bytes) :
    Except LoaderFailure (Solanalib.Runtime.Bytes × Solanalib.Runtime.Bytes) :=
  if count ≤ input.length then .ok (input.take count, input.drop count)
  else .error .unexpectedEof

def loaderPubkey (input : Solanalib.Runtime.Bytes) :
    Except LoaderFailure (Solanalib.Runtime.Pubkey × Solanalib.Runtime.Bytes) := do
  let (key, rest) ← loaderTake 32 input
  pure (Solanalib.Runtime.Pubkey.ofBytes key, rest)

/-- The Option encoding of Serde under bincode is one byte, even though enum
variant indices use fixed-width little-endian u32. -/
def loaderOption (input : Solanalib.Runtime.Bytes) :
    Except LoaderFailure (Option Solanalib.Runtime.Pubkey × Solanalib.Runtime.Bytes) :=
  match input with
  | [] => .error .unexpectedEof
  | tag :: rest =>
    if tag = 0 then .ok (none, rest)
    else if tag = 1 then (loaderPubkey rest).map fun (key, tail) => (some key, tail)
    else .error (.invalidOption tag)

/-- The exact fixed-int little-endian loader decoder used by the bincode 1.3.3
deserialize convenience function. The &mut slice of the caller is never advanced. -/
def decodeLoader (input : Solanalib.Runtime.Bytes) : Except LoaderFailure LoaderState := do
  let (tagBytes, rest) ← loaderTake 4 input
  let tag := UInt32.ofNat (Solanalib.Runtime.leNat tagBytes)
  match tag.toNat with
  | 0 => pure .uninitialized
  | 1 => pure (.buffer (← loaderOption rest).1)
  | 2 => pure (.program (← loaderPubkey rest).1)
  | 3 =>
    let (slot, rest) ← loaderTake 8 rest
    pure (.programData (UInt64.ofNat (Solanalib.Runtime.leNat slot)) (← loaderOption rest).1)
  | _ => .error (.invalidVariant tag)

/-- Actual bincode diagnostics and the modern Box/String dependencies of Anchor.
The mapper always selects InvalidAccountData, but it does not erase the
original boxed bincode error before its source-ordered destruction. -/
structure LoaderTypes where
  State : Type
  StringResource : Type
  BoxResource : Type
  DecodeError : Type
  Terminal : Type
  errors : AnchorErrorOperations.Ops State ProgramError.Value StringResource BoxResource Terminal
  makeDecodeError : Callback.Run State LoaderFailure DecodeError Empty Terminal
  dropDecodeError : Callback.Run State DecodeError Unit Empty Terminal

abbrev LoaderTypes.Error (types : LoaderTypes) :=
  AnchorErrorOperations.Error .boxed ProgramError.Value types.StringResource types.BoxResource

/-- Decode, map the error, then drop the consumed bincode diagnostic. Both
normal results carry the original slice unchanged; there is no discriminator
test or cursor update in this wrapper. -/
def loaderRun (types : LoaderTypes) : Callback.Run types.State Solanalib.Runtime.Bytes
    (Except types.Error LoaderState × Solanalib.Runtime.Bytes) Empty types.Terminal :=
  fun before input outcome =>
    match decodeLoader input with
    | .ok value => outcome = .returned (.ok value, input) before
    | .error failure =>
      Callback.bind types.makeDecodeError (fun original allocated =>
        Callback.bind (AnchorErrorOperations.fromProgram .boxed types.errors)
          (fun error mapped => Callback.map (fun _ => (.error error, input))
            types.dropDecodeError mapped original) allocated .invalidAccountData)
        before failure outcome

def loaderFamily : Family where
  Index := LoaderTypes
  State := LoaderTypes.State
  Args := fun _ => Solanalib.Runtime.Bytes
  Value := fun types => Except types.Error LoaderState × Solanalib.Runtime.Bytes
  Unwind := fun _ => Empty
  Terminal := LoaderTypes.Terminal
  contract := fun types => { requires := fun _ _ => True, post := loaderRun types }

theorem loader_reference : FamilyReference loaderFamily loaderRun := fun _ _ _ _ _ run => run

/-- The caller retains all bytes even when bincode permits a trailing region. -/
theorem loader_success (types : LoaderTypes) (before : types.State) (input :
  Solanalib.Runtime.Bytes)
    (value : LoaderState) (decoded : decodeLoader input = .ok value) :
    loaderRun types before input (.returned (.ok value, input) before) := by
  simp only [loaderRun, decoded]

end Solanalib.Specs.Core.AnchorCodec
