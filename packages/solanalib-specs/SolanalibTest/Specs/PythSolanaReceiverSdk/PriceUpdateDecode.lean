/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.PythSolanaReceiverSdk.PriceUpdateDecode

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

set_option maxRecDepth 20000

namespace SolanalibTest.Specs.PythSolanaReceiverSdk

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh
  Solanalib.Specs.Core.Oracle
open Solanalib.Specs.PythSolanaReceiverSdk.price_update

/-! Byte-level controls for the derived `VerificationLevel` and `PriceUpdateV2`
decoders. The encoders below are test helpers written from the Borsh wire
format, not models. -/

def u64le (value : UInt64) : _root_.Solanalib.Runtime.Bytes := _root_.Solanalib.Runtime.leBytes 8
  value.toNat
def i64le (value : Int64) : _root_.Solanalib.Runtime.Bytes := _root_.Solanalib.Runtime.leBytes 8
  value.toUInt64.toNat
def i32le (value : Int32) : _root_.Solanalib.Runtime.Bytes := _root_.Solanalib.Runtime.leBytes 4
  value.toUInt32.toNat

def encodeLevel : Pyth.VerificationLevel → _root_.Solanalib.Runtime.Bytes
  | .partialVerification signatures => [0, signatures]
  | .full => [1]

def encodeMessage (message : Pyth.PriceFeedMessage) : _root_.Solanalib.Runtime.Bytes :=
  message.feedId.bytes ++ i64le message.price ++ u64le message.confidence ++
    i32le message.exponent ++ i64le message.publishTime ++ i64le message.previousPublishTime ++
    i64le message.emaPrice ++ u64le message.emaConfidence

def encodeUpdate (update : Pyth.PriceUpdate) : _root_.Solanalib.Runtime.Bytes :=
  update.writeAuthority.bytes ++ encodeLevel update.verification ++
    encodeMessage update.message ++ u64le update.postedSlot

local instance : DecidableEq (Except IoError Pyth.VerificationLevel) := exceptDecEq
local instance : DecidableEq (Except IoError Pyth.PriceUpdate) := exceptDecEq

/-! ## VerificationLevel -/

theorem verification_partial_decodes :
    VerificationLevel.decoder [0, 5, 9] = (.ok (.partialVerification 5), [9]) := rfl

theorem verification_full_decodes :
    VerificationLevel.decoder [1, 9] = (.ok .full, [9]) := rfl

/-- An unknown tag is rejected after the tag byte, with the message of the derive. -/
theorem verification_bad_tag_rejected :
    VerificationLevel.decoder [2, 5] =
        (.error ⟨⟨"InvalidData"⟩, "Unexpected variant tag: 2"⟩, [5]) ∧
      VerificationLevel.decoder [255] =
        (.error ⟨⟨"InvalidData"⟩, "Unexpected variant tag: 255"⟩, []) := by
  have two : VerificationLevel.unexpectedVariantTagMessage 2 = "Unexpected variant tag: 2" := by
    decide
  have high : VerificationLevel.unexpectedVariantTagMessage 255 =
      "Unexpected variant tag: 255" := by
    decide
  have decodedTwo : VerificationLevel.decoder [2, 5] =
      (.error ⟨.invalidData, VerificationLevel.unexpectedVariantTagMessage 2⟩, [5]) := rfl
  have decodedHigh : VerificationLevel.decoder [255] =
      (.error ⟨.invalidData, VerificationLevel.unexpectedVariantTagMessage 255⟩, []) := rfl
  rw [decodedTwo, decodedHigh, two, high]
  exact ⟨rfl, rfl⟩

theorem verification_partial_truncated :
    VerificationLevel.decoder [0] = (.error
      Solanalib.Specs.Borsh.invalid_data_profile.unexpectedLength, []) ∧
      VerificationLevel.decoder [] = (.error
        Solanalib.Specs.Borsh.invalid_data_profile.unexpectedLength, []) :=
  ⟨rfl, rfl⟩

/-! ## PriceUpdateV2 -/

/-- The nonzero partially verified sample update in the repository. -/
theorem decode_partial_sample :
    PriceUpdateV2.decoder (encodeUpdate Pyth.sampleUpdate) = (.ok Pyth.sampleUpdate, []) := rfl

def fullUpdate : Pyth.PriceUpdate := { Pyth.sampleUpdate with verification := .full }

theorem decode_full_sample :
    PriceUpdateV2.decoder (encodeUpdate fullUpdate) = (.ok fullUpdate, []) := rfl

/-- Partial bodies have 126 bytes, which with the 8-byte discriminator is `LEN = 134` in the source;
full bodies have 125. -/
theorem encoded_lengths :
    (encodeUpdate Pyth.sampleUpdate).length = 126 ∧ (encodeUpdate fullUpdate).length = 125 ∧
      8 + 32 + 2 + 32 + 8 + 8 + 4 + 8 + 8 + 8 + 8 + 8 = 8 + 126 := by decide

/-- Input cut short inside any field is rejected with the Borsh 1.6.1 length error. -/
theorem decode_truncated_each_field :
    ∀ length, length < 126 →
      (PriceUpdateV2.decoder ((encodeUpdate Pyth.sampleUpdate).take length)).1 =
        .error Solanalib.Specs.Borsh.invalid_data_profile.unexpectedLength := by
  decide

/-- A bad verification tag inside an update returns the error of the enum; the
reference leaves the slice just after the tag byte. -/
theorem decode_bad_tag_rejected :
    PriceUpdateV2.decoder (_root_.Solanalib.Runtime.Pubkey.zero.bytes ++ [2] ++ [1, 2, 3]) =
      (.error (VerificationLevel.unexpectedVariantTag 2), [1, 2, 3]) := rfl

/-- Distinct authority and feed identifiers: swapping their 32-byte blocks
swaps the decoded fields, so the field order is observable. -/
def authority : _root_.Solanalib.Runtime.Pubkey := _root_.Solanalib.Runtime.Pubkey.ofNat 1
def feedId : _root_.Solanalib.Runtime.Pubkey := _root_.Solanalib.Runtime.Pubkey.ofNat 2

def orderedUpdate : Pyth.PriceUpdate :=
  { Pyth.sampleUpdate with
    writeAuthority := authority
    message := { Pyth.sampleUpdate.message with feedId := feedId } }

def swappedBytes : _root_.Solanalib.Runtime.Bytes :=
  feedId.bytes ++ encodeLevel orderedUpdate.verification ++ authority.bytes ++
    (encodeMessage orderedUpdate.message).drop 32 ++ u64le orderedUpdate.postedSlot

theorem decode_field_order_observable :
    (PriceUpdateV2.decoder (encodeUpdate orderedUpdate)).1.toOption.map
        (fun update => (update.writeAuthority, update.message.feedId)) = some (authority, feedId) ∧
      (PriceUpdateV2.decoder swappedBytes).1.toOption.map
        (fun update => (update.writeAuthority, update.message.feedId)) = some (feedId, authority) ∧
      authority ≠ feedId :=
  ⟨rfl, rfl, by decide⟩

/-- Bytes after the update are not read; a client that discards the slice
therefore accepts them. -/
theorem decode_leaves_trailing :
    PriceUpdateV2.decoder (encodeUpdate Pyth.sampleUpdate ++ [7, 7]) =
      (.ok Pyth.sampleUpdate, [7, 7]) := rfl

/-- the Borsh 1.6.1 default `deserialize::<PriceUpdateV2>` on the sample body
returns the decoded update. -/
theorem deserialize_entry_returns_update :
    Solanalib.Specs.Borsh.de.BorshDeserialize.deserialize_run PriceUpdateV2.decodeIndex ()
      (encodeUpdate Pyth.sampleUpdate) (.returned (.ok Pyth.sampleUpdate, []) ()) :=
  (PriceUpdateV2.deserialize_forwards _ _).2 rfl

/-- A decoded update is the value the selected price getter reads. -/
theorem decoded_update_feeds_getter :
    (match (PriceUpdateV2.decoder (encodeUpdate Pyth.sampleUpdate)).1 with
      | .ok update => some (Pyth.evaluate { Pyth.sampleArgs with update := update })
      | .error _ => none) =
      some (.ok (.ok Pyth.sampleUpdate.message.toPrice)) := rfl

/-- The contract fixes the result and, on success, the remaining slice. -/
theorem contract_rejects_other_slot :
    ¬ PriceUpdateV2.deserialize_reader_contract.post () (encodeUpdate Pyth.sampleUpdate)
      (.returned (.ok { Pyth.sampleUpdate with postedSlot := 18 }, []) ()) := by
  rintro ⟨agrees, -⟩
  have := congrArg (fun result : Except IoError Pyth.PriceUpdate × _root_.Solanalib.Runtime.Bytes =>
    result.1.toOption.map Pyth.PriceUpdate.postedSlot) agrees
  exact absurd this (by decide)

/-- After an error the contract leaves the remaining slice unconstrained. -/
theorem contract_allows_any_slice_after_error :
    PriceUpdateV2.deserialize_reader_contract.post () [0, 1]
      (.returned (.error Solanalib.Specs.Borsh.invalid_data_profile.unexpectedLength, [9]) ()) :=
  ⟨rfl, rfl⟩

end SolanalibTest.Specs.PythSolanaReceiverSdk
