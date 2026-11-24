/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.PythnetSdk.Messages

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.PythnetSdk

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh
  Solanalib.Specs.Core.Oracle
open Solanalib.Specs.PythnetSdk.messages.PriceFeedMessage

/-! Byte-level controls for the derived `PriceFeedMessage` decoder. The encoder
below is a test helper written from the Borsh wire format, not a model. -/

def u64le (value : UInt64) : _root_.Solanalib.Runtime.Bytes := _root_.Solanalib.Runtime.leBytes 8
  value.toNat
def i64le (value : Int64) : _root_.Solanalib.Runtime.Bytes := _root_.Solanalib.Runtime.leBytes 8
  value.toUInt64.toNat
def i32le (value : Int32) : _root_.Solanalib.Runtime.Bytes := _root_.Solanalib.Runtime.leBytes 4
  value.toUInt32.toNat

def encode (message : Pyth.PriceFeedMessage) : _root_.Solanalib.Runtime.Bytes :=
  message.feedId.bytes ++ i64le message.price ++ u64le message.confidence ++
    i32le message.exponent ++ i64le message.publishTime ++ i64le message.previousPublishTime ++
    i64le message.emaPrice ++ u64le message.emaConfidence

def feed : _root_.Solanalib.Runtime.Bytes := (List.range 32).map fun index => UInt8.ofNat (index +
  1)

/-- Distinct field values, a negative price and a negative exponent. -/
def sample : Pyth.PriceFeedMessage :=
  ⟨⟨feed, by decide⟩, -4700, 23, -8, 100, 80, 4690, 29⟩

theorem encoded_length : (encode sample).length = encodedLength := by decide

theorem negative_exponent_is_i32 : i32le (-8) = [248, 255, 255, 255] := by decide

theorem decode_sample : decoder (encode sample) = (.ok sample, []) := rfl

/-- Bytes after the 84-byte message are not read. -/
theorem trailing_left : decoder (encode sample ++ [9, 9]) = (.ok sample, [9, 9]) := rfl

/-- A message cut short inside its last field is rejected with the Borsh 1.6.1
length error; the std reference empties the slice. -/
theorem truncated_in_last_field :
    decoder ((encode sample).take 83) = (.error
      Solanalib.Specs.Borsh.invalid_data_profile.unexpectedLength, []) := rfl

theorem truncated_in_feed_id :
    decoder ((encode sample).take 31) = (.error
      Solanalib.Specs.Borsh.invalid_data_profile.unexpectedLength, []) := rfl

theorem truncated_in_exponent :
    decoder ((encode sample).take 50) = (.error
      Solanalib.Specs.Borsh.invalid_data_profile.unexpectedLength, []) := rfl

local instance : DecidableEq (Except IoError Pyth.PriceFeedMessage) := exceptDecEq

/-- Every proper prefix is rejected with the same error. -/
theorem every_proper_prefix_rejected :
    ∀ length, length < encodedLength →
      (decoder ((encode sample).take length)).1 = .error
        Solanalib.Specs.Borsh.invalid_data_profile.unexpectedLength := by
  decide

/-- Swapping the price and confidence fields changes the decoded price, so the
field order is observable. -/
def swapped : _root_.Solanalib.Runtime.Bytes :=
  feed ++ u64le 23 ++ i64le (-4700) ++ (encode sample).drop 48

theorem field_order_observable :
    ((decoder swapped).1.toOption.map Pyth.PriceFeedMessage.price) = some 23 ∧
    ((decoder (encode sample)).1.toOption.map Pyth.PriceFeedMessage.price) = some (-4700) :=
  ⟨rfl, rfl⟩

/-- The contract fixes the result and, on success, the remaining slice. -/
theorem contract_rejects_other_value :
    ¬ deserialize_reader_contract.post () (encode sample)
      (.returned (.ok { sample with emaConfidence := 30 }, []) ()) := by
  rintro ⟨agrees, -⟩
  have := congrArg (fun result : Except IoError Pyth.PriceFeedMessage ×
    _root_.Solanalib.Runtime.Bytes =>
    result.1.toOption.map Pyth.PriceFeedMessage.emaConfidence) agrees
  exact absurd this (by decide)

/-- After an error the contract leaves the remaining slice unconstrained. -/
theorem contract_allows_any_slice_after_error :
    deserialize_reader_contract.post () ((encode sample).take 10)
      (.returned (.error Solanalib.Specs.Borsh.invalid_data_profile.unexpectedLength, [1, 2, 3])
        ()) :=
  ⟨rfl, rfl⟩

end SolanalibTest.Specs.PythnetSdk
