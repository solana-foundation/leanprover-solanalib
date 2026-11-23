/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.StakeAddress
import Solanalib.Specs.PythnetSdk.Messages
import Solanalib.Specs.PythSolanaReceiverSdk.PriceUpdateDecode

/-!
# pythnet-sdk 3.0.0 and pyth-solana-receiver-sdk 2.0.0 Borsh decoding

All three members are plain decoder contracts realized by their
`deserialize_reader_model`. The selected entry point, the default `deserialize`
at `Self = PriceUpdateV2` on `data[8..]`, is the borsh 1.6.1 family with the graph of the
`PriceUpdateV2` member as callback, decided through
`V161.deserialize_evaluated` (the same index as the `decodeIndex` of the model).
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

open Solanalib.Specs.PythSolanaReceiverSdk

namespace SolanalibTest.Conformance.Library.Pyth

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh
open SolanalibTest.Conformance.Library.Borsh SolanalibTest.Conformance.Library.StakeAddress

abbrev Message := Solanalib.Specs.Core.Oracle.Pyth.PriceFeedMessage
abbrev Level := Solanalib.Specs.Core.Oracle.Pyth.VerificationLevel
abbrev Update := Solanalib.Specs.Core.Oracle.Pyth.PriceUpdate

def message (j : Json) : Result Message := do
  pure ⟨← keyField j "feed_id", ← i64Field j "price", ← u64Field j "conf", ← i32Parse (← field j
    "exponent"),
    ← i64Field j "publish_time", ← i64Field j "prev_publish_time", ← i64Field j "ema_price",
    ← u64Field j "ema_conf"⟩

def messageJson (m : Message) : Json := Json.mkObj [
  ("feed_id", pubkeyJson m.feedId), ("price", i64Json m.price), ("conf", u64Json m.confidence),
  ("exponent", i32Json m.exponent), ("publish_time", i64Json m.publishTime),
  ("prev_publish_time", i64Json m.previousPublishTime), ("ema_price", i64Json m.emaPrice),
  ("ema_conf", u64Json m.emaConfidence)]

def level (j : Json) : Result Level := do
  match ← (← field j "variant").getStr? with
  | "Partial" => pure (.partialVerification (← u8Parse (← field (← field j "fields")
    "num_signatures")))
  | "Full" => pure .full
  | other => throw s!"unknown VerificationLevel {other}"

def levelJson : Level → Json
  | .partialVerification n => Json.mkObj [("variant", "Partial"),
      ("fields", Json.mkObj [("num_signatures", u8Json n)])]
  | .full => Json.mkObj [("variant", "Full"), ("fields", Json.arr #[])]

def update (j : Json) : Result Update := do
  pure ⟨← keyField j "write_authority", ← level (← field j "verification_level"),
    ← message (← field j "price_message"), ← u64Field j "posted_slot"⟩

def updateJson (u : Update) : Json := Json.mkObj [
  ("write_authority", pubkeyJson u.writeAuthority), ("verification_level", levelJson
    u.verification),
  ("price_message", messageJson u.message), ("posted_slot", u64Json u.postedSlot)]

/-! These three types are only ever `Self` types here, never `Vec` or array
elements, so their `Ty.size` (documented as `size_of::<T>()`) is never read.
It records their Borsh-encoded lengths, not their in-memory `size_of`. -/

def priceFeedMessage : Ty := primitive "pythnet_sdk::messages::PriceFeedMessage" Message message
  messageJson 84
  "Solanalib.Specs.PythnetSdk.messages.PriceFeedMessage.deserialize_reader_model"
  Solanalib.Specs.PythnetSdk.messages.PriceFeedMessage.deserialize_reader_model

def verificationLevel : Ty := primitive "pyth_solana_receiver_sdk::price_update::Verificati\
  onLevel"
  Level level
  levelJson 2
    "Solanalib.Specs.PythSolanaReceiverSdk.price_update.VerificationLevel.deserialize_reade\
      r_model"
  price_update.VerificationLevel.deserialize_reader_model

def priceUpdateV2 : Ty := primitive "pyth_solana_receiver_sdk::price_update::PriceUpdateV2" Update
  update
  updateJson 126
    "Solanalib.Specs.PythSolanaReceiverSdk.price_update.PriceUpdateV2.deserialize_reader_mo\
      del"
  price_update.PriceUpdateV2.deserialize_reader_model

def pythnetCheckers : List Checker :=
  [readerChecker priceFeedMessage, V161.deserializeChecker priceFeedMessage]

def receiverCheckers : List Checker :=
  [readerChecker verificationLevel, readerChecker priceUpdateV2, V161.deserializeChecker
    priceUpdateV2]

end SolanalibTest.Conformance.Library.Pyth
