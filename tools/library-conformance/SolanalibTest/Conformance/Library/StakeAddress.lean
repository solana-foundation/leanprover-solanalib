/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Borsh161De
import SolanalibTest.Conformance.Library.Borsh161Ser
import Solanalib.Specs.SolanaAddress.Borsh
import Solanalib.Specs.SolanaStakeInterface.State

/-!
# solana-address 2.6.0 and solana-stake-interface 3.1.0 Borsh members

`Address` decoding is a plain decoder member (the graph of its model is decided);
`Address` serialization is a writer-indexed family decided through
`serialize_run_iff`. `StakeStateV2::deserialize_reader` is registered as the
graph of `Decoder.lift StakeStateV2.decode`; the default `deserialize` at
`Self = StakeStateV2` is the borsh 1.6.1 family with that member as callback.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.StakeAddress

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Borsh
  Solanalib.Specs.Core.StakeState
open SolanalibTest.Conformance.Library.Borsh

def pubkey (j : Json) : Result Solanalib.Runtime.Pubkey := do
  let b ← asBytes j
  if h : b.length = 32 then pure ⟨b, h⟩ else throw s!"address must have 32 bytes, got \
    {b.length}"

def pubkeyJson (k : Solanalib.Runtime.Pubkey) : Json := bytesJson k.bytes

/-! ## Address -/

def address : Ty := primitive "solana_address::Address" Solanalib.Runtime.Pubkey pubkey pubkeyJson
  32
  "Solanalib.Specs.SolanaAddress.Address.deserialize_reader_model"
  Solanalib.Specs.SolanaAddress.Address.deserialize_reader_model

theorem address_serialize_evaluated {S : Type} (w : WriterFn S Empty Empty) (before : S)
    (a : Solanalib.Runtime.Pubkey) (o : Outcome S (Except IoError Unit) Empty Empty) :
    Solanalib.Specs.SolanaAddress.Address.serialize_run ⟨S, Empty, Empty, Callback.ofFunction w⟩
      before a o ↔
      w before a.bytes = o :=
  Solanalib.Specs.SolanaAddress.Address.serialize_run_iff (⟨S, Empty, Empty, Callback.ofFunction w⟩
    : WriterIndex)
    before a o

def addressSerializeChecker (writer : String) : Checker where
  function := "<solana_address::Address as borsh::ser::BorshSerialize>::serialize"
  generics := [("W", writer)]
  reference := "Solanalib.Specs.SolanaAddress.Address.serialize_run"
  decides := ["Solanalib.Specs.SolanaAddress.Address.serialize_run"]
  check := fun c => decideSerialize pubkey c fun w => {
    relation := Solanalib.Specs.SolanaAddress.Address.serialize_run ⟨_, Empty, Empty,
      Callback.ofFunction w⟩
    serialize := fun before a => w before a.bytes
    graph := address_serialize_evaluated w }

def addressCheckers : List Checker :=
  [readerChecker address, V161.deserializeChecker address] ++
    ["conformance_recorder::RecordingWriter", "alloc::vec::Vec<u8>"].map addressSerializeChecker

/-! ## StakeStateV2 -/

def i64Field (j : Json) (k : String) : Result Int64 := do i64Parse (← field j k)
def u64Field (j : Json) (k : String) : Result UInt64 := do u64Parse (← field j k)
def keyField (j : Json) (k : String) : Result Solanalib.Runtime.Pubkey := do pubkey (← field j k)

def lockup (j : Json) : Result Lockup := do
  pure ⟨← i64Field j "unix_timestamp", ← u64Field j "epoch", ← keyField j "custodian"⟩

def authorized (j : Json) : Result Authorized := do
  pure ⟨← keyField j "staker", ← keyField j "withdrawer"⟩

def meta_ (j : Json) : Result Meta := do
  pure ⟨← u64Field j "rent_exempt_reserve", ← authorized (← field j "authorized"), ← lockup (←
    field j "lockup")⟩

def delegation (j : Json) : Result Delegation := do
  pure ⟨← keyField j "voter_pubkey", ← u64Field j "stake", ← u64Field j "activation_epoch",
    ← u64Field j "deactivation_epoch", ← asF64Bits (← field j "warmup_cooldown_rate")⟩

def stake (j : Json) : Result Stake := do
  pure ⟨← delegation (← field j "delegation"), ← u64Field j "credits_observed"⟩

def flags (j : Json) : Result StakeFlags := do pure ⟨← u8Parse (← field j "bits")⟩

def stakeState (j : Json) : Result StakeStateV2 := do
  let fields ← (← field j "fields").getArr?
  match ← (← field j "variant").getStr?, fields.toList with
  | "Uninitialized", [] => pure .uninitialized
  | "Initialized", [m] => pure (.initialized (← meta_ m))
  | "Stake", [m, s, f] => pure (.stake (← meta_ m) (← stake s) (← flags f))
  | "RewardsPool", [] => pure .rewardsPool
  | v, _ => throw s!"unknown StakeStateV2 value {v}"

def metaJson (m : Meta) : Json := Json.mkObj [
  ("rent_exempt_reserve", u64Json m.rentExemptReserve),
  ("authorized", Json.mkObj [("staker", pubkeyJson m.authorized.staker),
    ("withdrawer", pubkeyJson m.authorized.withdrawer)]),
  ("lockup", Json.mkObj [("unix_timestamp", i64Json m.lockup.unixTimestamp),
    ("epoch", u64Json m.lockup.epoch), ("custodian", pubkeyJson m.lockup.custodian)])]

def stakeJson (s : Stake) : Json := Json.mkObj [
  ("delegation", Json.mkObj [("voter_pubkey", pubkeyJson s.delegation.voterPubkey),
    ("stake", u64Json s.delegation.stake), ("activation_epoch", u64Json
      s.delegation.activationEpoch),
    ("deactivation_epoch", u64Json s.delegation.deactivationEpoch),
    ("warmup_cooldown_rate", f64BitsJson s.delegation.warmupCooldownRate)]),
  ("credits_observed", u64Json s.creditsObserved)]

def variantJson (name : String) (fields : List Json) : Json :=
  Json.mkObj [("variant", Json.str name), ("fields", Json.arr fields.toArray)]

def stakeStateJson : StakeStateV2 → Json
  | .uninitialized => variantJson "Uninitialized" []
  | .initialized m => variantJson "Initialized" [metaJson m]
  | .stake m s f => variantJson "Stake" [metaJson m, stakeJson s, Json.mkObj [("bits", u8Json
    f.bits)]]
  | .rewardsPool => variantJson "RewardsPool" []

/-- The registered member is the graph of the lifted decoder, by definition. -/
theorem stake_reader_evaluated (before : Unit) (input : Solanalib.Runtime.Bytes) (o : DecodeOut
  StakeStateV2) :
    Solanalib.Specs.SolanaStakeInterface.state.StakeStateV2.deserialize_reader_run before input o ↔
      Decoder.lift Solanalib.Specs.SolanaStakeInterface.state.StakeStateV2.decode before input = o
        :=
  Iff.rfl

def stakeStateV2 : Ty where
  rust := "solana_stake_interface::state::StakeStateV2"
  Value := StakeStateV2
  decEq := inferInstance
  parse := stakeState
  render := stakeStateJson
  size := 200
  readerFunction :=
    "<solana_stake_interface::state::StakeStateV2 as \
      borsh::de::BorshDeserialize>::deserialize_reader"
  readerGenerics := []
  readerReference :=
    "Solanalib.Specs.SolanaStakeInterface.state.StakeStateV2.deserialize_reader_run"
  decode := Decoder.lift Solanalib.Specs.SolanaStakeInterface.state.StakeStateV2.decode
  reader := Solanalib.Specs.SolanaStakeInterface.state.StakeStateV2.deserialize_reader_run
  reader_graph := stake_reader_evaluated

def stakeCheckers : List Checker :=
  [readerChecker stakeStateV2, V161.deserializeChecker stakeStateV2]

end SolanalibTest.Conformance.Library.StakeAddress
