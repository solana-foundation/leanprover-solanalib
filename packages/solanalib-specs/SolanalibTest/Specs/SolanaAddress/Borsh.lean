/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaAddress.Borsh

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaAddress

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh
open Solanalib.Specs.SolanaAddress.Address

/-! Controls for the derived Address Borsh serializer and decoder. -/

/-- 32 bytes whose only nonzero byte is the last one. -/
def lastMarked : _root_.Solanalib.Runtime.Pubkey := ⟨List.replicate 31 0 ++ [9], by simp⟩

/-! ## Serialization -/

theorem borsh_error_retains_partial_write :
    serialize_run serialize_sample ([] : _root_.Solanalib.Runtime.Bytes) sampleAddress
      (.returned (.error sampleWriteError) ([7, 0, 0] : _root_.Solanalib.Runtime.Bytes)) :=
  (serialize_run_iff serialize_sample _ _ _).2 rfl

def appendWriter : WriterIndex :=
  ⟨_root_.Solanalib.Runtime.Bytes, Nat, Nat, fun before bytes outcome =>
    outcome = .returned (.ok ()) (before ++ bytes)⟩

theorem borsh_writes_all_address_bytes :
    serialize_run appendWriter ([8] : _root_.Solanalib.Runtime.Bytes) lastMarked
      (.returned (.ok ()) (([8] ++ lastMarked.bytes) : _root_.Solanalib.Runtime.Bytes)) :=
  (serialize_run_iff appendWriter _ _ _).2 rfl

def unwindWriter : WriterIndex :=
  ⟨_root_.Solanalib.Runtime.Bytes, Nat, Nat, fun _ bytes outcome => outcome = .unwound (11 : Nat)
    bytes⟩

theorem borsh_retains_unwind_state :
    serialize_run unwindWriter ([] : _root_.Solanalib.Runtime.Bytes) lastMarked
      (.unwound (11 : Nat) lastMarked.bytes) :=
  (serialize_run_iff unwindWriter _ _ _).2 rfl

def terminalWriter : WriterIndex :=
  ⟨_root_.Solanalib.Runtime.Bytes, Nat, Nat, fun _ _ outcome => outcome = .terminated (13 : Nat)⟩

theorem borsh_retains_terminal_reason :
    serialize_run terminalWriter ([] : _root_.Solanalib.Runtime.Bytes) lastMarked (.terminated (13
      : Nat)) :=
  (serialize_run_iff terminalWriter _ _ _).2 rfl

/-- A writer that logs every `write_all` chunk. -/
def recording : WriterIndex :=
  ⟨List _root_.Solanalib.Runtime.Bytes, Empty, Empty, Callback.ofFunction recordingWriter⟩

/-- Exactly one `write_all`, containing all 32 bytes; two chunks or a shorter
chunk are not permitted executions. -/
theorem borsh_single_write_call :
    serialize_run recording [] lastMarked (.returned (.ok ()) [lastMarked.bytes]) ∧
      ¬ serialize_run recording [] lastMarked
        (.returned (.ok ()) [lastMarked.bytes.take 16, lastMarked.bytes.drop 16]) ∧
      ¬ serialize_run recording [] lastMarked
        (.returned (.ok ()) [lastMarked.bytes.take 31]) := by
  refine ⟨(serialize_run_iff recording _ _ _).2 rfl, ?_, ?_⟩
  · intro step
    have written := (serialize_run_iff recording _ _ _).1 step
    have := congrArg (fun outcome : Outcome (List _root_.Solanalib.Runtime.Bytes) (Except IoError
      Unit)
      Empty Empty => match outcome with
        | .returned _ log => log.length
        | _ => 0) written
    exact absurd this (by decide)
  · intro step
    have written := (serialize_run_iff recording _ _ _).1 step
    have := congrArg (fun outcome : Outcome (List _root_.Solanalib.Runtime.Bytes) (Except IoError
      Unit)
      Empty Empty => match outcome with
        | .returned _ log => log.map List.length
        | _ => []) written
    exact absurd this (by decide)

/-! ## Decoding -/

theorem borsh_decode_exact : decoder lastMarked.bytes = (.ok lastMarked, []) := rfl

/-- Bytes after the address are not read. -/
theorem borsh_decode_leaves_trailing :
    decoder (lastMarked.bytes ++ [1, 2]) = (.ok lastMarked, [1, 2]) := rfl

/-- 31 bytes are rejected with the Borsh 1.6.1 length error; the std reference
empties the slice. -/
theorem borsh_decode_truncated :
    decoder (List.replicate 31 7) =
      (.error ⟨⟨"InvalidData"⟩, "Unexpected length of input"⟩, []) := rfl

/-- The address is the first 32 bytes, not the last. -/
theorem borsh_decode_reads_first_32 :
    decoder (List.replicate 32 0 ++ [9]) = (.ok _root_.Solanalib.Runtime.Pubkey.zero, [9]) ∧
      _root_.Solanalib.Runtime.Pubkey.zero ≠ lastMarked := ⟨rfl, by decide⟩

/-- The single chunk of the serializer decodes back to the address, for every address. -/
theorem borsh_roundtrip (address : _root_.Solanalib.Runtime.Pubkey) (rest :
  _root_.Solanalib.Runtime.Bytes) :
    serialize_run recording [] address (.returned (.ok ()) [address.bytes]) ∧
      decoder (address.bytes ++ rest) = (.ok address, rest) := by
  refine ⟨(serialize_run_iff recording _ _ _).2 rfl, ?_⟩
  have long : 32 ≤ (address.bytes ++ rest).length := by
    simp [address.length_eq]
  rw [decoder_ok long]
  have take : (address.bytes ++ rest).take 32 = address.bytes := by
    rw [List.take_append_of_le_length (by simp [address.length_eq])]
    exact List.take_of_length_le (by simp [address.length_eq])
  have drop : (address.bytes ++ rest).drop 32 = rest := by
    rw [← address.length_eq]
    exact List.drop_left
  cases address with
  | mk bytes length =>
    simp only at take drop
    simp only [take, drop]

/-- The contract fixes the result and the remaining slice on success, and
leaves the slice free after an error. -/
theorem borsh_decode_contract_controls :
    ¬ deserialize_reader_contract.post () lastMarked.bytes
        (.returned (.ok _root_.Solanalib.Runtime.Pubkey.zero, []) ()) ∧
      deserialize_reader_contract.post () (List.replicate 31 7)
        (.returned (.error Solanalib.Specs.Borsh.invalid_data_profile.unexpectedLength, [7]) ()) :=
          by
  refine ⟨?_, ⟨rfl, rfl⟩⟩
  rintro ⟨agrees, -⟩
  have := congrArg (fun result : Except IoError _root_.Solanalib.Runtime.Pubkey ×
    _root_.Solanalib.Runtime.Bytes =>
    result.1.toOption) agrees
  exact absurd this (by decide)

end SolanalibTest.Specs.SolanaAddress
