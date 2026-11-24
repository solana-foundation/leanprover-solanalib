/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenExtension

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token

/-- One allocation-neutral step through the extension-type listing of the source.
This does not perform a vector operation or invoke the listing callback. -/
inductive ExtensionScanStep where
  /-- Empty input, one trailing realloc byte, or an uninitialized sentinel. -/
  | done
  /-- An unknown type, incomplete nonzero header, or out-of-bounds payload. -/
  | invalid
  /-- A complete initialized entry, its consumed byte count and remaining input. -/
  | next (kind : ExtensionType) (consumed : Nat) (tail : Bytes)
  deriving DecidableEq, Repr

/-- Scan exactly one TLV entry as `try_for_each_tlv_extension_type` does.
A zero tag terminates before a length is required; a known nonzero tag reaches
the caller only after its complete declared payload has been bounded. -/
def nextExtension (bytes : Bytes) : ExtensionScanStep :=
  match bytes with
  | [] | [_] => .done
  | low :: high :: rest =>
    match ExtensionType.decode (tlvU16 low high) with
    | none => .invalid
    | some .uninitialized => .done
    | some kind =>
      match rest with
      | lenLow :: lenHigh :: value =>
        let length := tlvU16 lenLow lenHigh
        if length ≤ value.length then
          .next kind (4 + length) (value.drop length)
        else .invalid
      | _ => .invalid

/-- The existing pure fold factors through the same one-entry scan. The
callback runs only in the `next` branch, before examining the remaining input. -/
theorem foldExtensionTypes_scan {State : Type}
    (step : State → ExtensionType → Except Error State)
    (state : State) (offset : Nat) (bytes : Bytes) :
    foldExtensionTypes step state offset bytes =
      match nextExtension bytes with
      | .done => .ok (state, offset)
      | .invalid => .error .InvalidAccountData
      | .next kind consumed tail =>
        (step state kind).bind (fun next => foldExtensionTypes step next (offset + consumed) tail)
          := by
  rw [foldExtensionTypes.eq_def]
  unfold nextExtension
  split <;> simp_all only []
  split <;> simp_all only []
  split <;> simp_all only []
  split <;> simp_all only [Nat.add_assoc]
  rfl

/-- Every yielded entry consumes its complete four-byte header and at most a
u16 payload. Its consumed prefix and remaining suffix partition the input. -/
theorem nextExtension_next_geometry (bytes : Bytes) (kind : ExtensionType)
    (consumed : Nat) (tail : Bytes)
    (scanned : nextExtension bytes = .next kind consumed tail) :
    4 ≤ consumed ∧ consumed ≤ 65539 ∧ consumed + tail.length = bytes.length := by
  unfold nextExtension at scanned
  split at scanned <;> try cases scanned
  split at scanned <;> try cases scanned
  split at scanned <;> try cases scanned
  dsimp only at scanned
  split at scanned <;> try cases scanned
  rename_i lenLow lenHigh value bounded notZero decoded
  have lengthBound := tlvU16_le lenLow lenHigh
  simp only [List.length_cons, List.length_drop]
  omega

/-- A yielded TLV entry always leaves fewer bytes for the next scan. -/
theorem nextExtension_next_tail_shorter (bytes : Bytes) (kind : ExtensionType)
    (consumed : Nat) (tail : Bytes)
    (scanned : nextExtension bytes = .next kind consumed tail) :
    tail.length < bytes.length := by
  have geometry := nextExtension_next_geometry bytes kind consumed tail scanned
  omega

/-- The consumed byte count of a successful scan fits within the original input. -/
theorem nextExtension_next_consumed_le (bytes : Bytes) (kind : ExtensionType)
    (consumed : Nat) (tail : Bytes)
    (scanned : nextExtension bytes = .next kind consumed tail) :
    consumed ≤ bytes.length := by
  have geometry := nextExtension_next_geometry bytes kind consumed tail scanned
  omega

/-- A yielded entry leaves exactly the source slice after its consumed prefix. -/
theorem nextExtension_next_tail_eq (bytes : Bytes) (kind : ExtensionType)
    (consumed : Nat) (tail : Bytes)
    (scanned : nextExtension bytes = .next kind consumed tail) :
    tail = bytes.drop consumed := by
  unfold nextExtension at scanned
  split at scanned <;> try cases scanned
  split at scanned <;> try cases scanned
  split at scanned <;> try cases scanned
  dsimp only at scanned
  split at scanned <;> try cases scanned
  simp [Nat.add_comm 4]

end Solanalib.Specs.Core.Token
