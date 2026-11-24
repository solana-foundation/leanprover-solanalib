/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OraclePyth
public import Solanalib.Specs.Core.BorshFamily
public import Solanalib.Specs.Borsh.De

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! The `BorshDeserialize` implementation derived for `PriceFeedMessage` in
pythnet-sdk 3.0.0 (`messages.rs` lines 84–91, feature `solana-program`, so the
Anchor derive and Borsh-derive 1.6.1). The eight fields are read in declaration
order with the Borsh 1.6.1 decoders at `R = &[u8]`. -/

namespace Solanalib.Specs.PythnetSdk.messages.PriceFeedMessage

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh
open Solanalib.Specs.Core.Oracle

/-- `feed_id: [u8; 32]`, then `price: i64`, `conf: u64`, `exponent: i32`,
`publish_time`, `prev_publish_time`, `ema_price: i64` and `ema_conf: u64`.
The error of the first failing field is returned at once. -/
def decoder : Decoder Pyth.PriceFeedMessage :=
  (decodeByteArray Solanalib.Specs.Borsh.invalid_data_profile 32).bind fun feedId =>
  (decodeI64 Solanalib.Specs.Borsh.invalid_data_profile).bind fun price =>
  (decodeU64 Solanalib.Specs.Borsh.invalid_data_profile).bind fun confidence =>
  (decodeI32 Solanalib.Specs.Borsh.invalid_data_profile).bind fun exponent =>
  (decodeI64 Solanalib.Specs.Borsh.invalid_data_profile).bind fun publishTime =>
  (decodeI64 Solanalib.Specs.Borsh.invalid_data_profile).bind fun previousPublishTime =>
  (decodeI64 Solanalib.Specs.Borsh.invalid_data_profile).bind fun emaPrice =>
  (decodeU64 Solanalib.Specs.Borsh.invalid_data_profile).bind fun emaConfidence =>
  Decoder.pure ⟨⟨feedId.val, feedId.property⟩, price, confidence, exponent, publishTime,
    previousPublishTime, emaPrice, emaConfidence⟩

/-- The encoded size of every message. -/
def encodedLength : Nat := 32 + 8 + 8 + 4 + 8 + 8 + 8 + 8

def deserialize_reader_contract :
    Solanalib.Contracts.Model Unit _root_.Solanalib.Runtime.Bytes
      (Except IoError Pyth.PriceFeedMessage × _root_.Solanalib.Runtime.Bytes) :=
  decoderContract decoder

def deserialize_reader_model :
    Unit → _root_.Solanalib.Runtime.Bytes → (Except IoError Pyth.PriceFeedMessage ×
      _root_.Solanalib.Runtime.Bytes) × Unit :=
  decoderModel decoder

theorem deserialize_reader_reference :
    deserialize_reader_contract.RealizedBy deserialize_reader_model :=
  decoderContract_realized _

theorem deserialize_reader_satisfiable : deserialize_reader_contract.Satisfiable :=
  decoderContract_satisfiable _

end Solanalib.Specs.PythnetSdk.messages.PriceFeedMessage
