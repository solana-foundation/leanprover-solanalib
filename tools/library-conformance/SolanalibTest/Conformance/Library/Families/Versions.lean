/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Runtime.Values
import Solanalib.Specs.SolanaHash.Hash
import Solanalib.Specs.SolanaZeroCopy.Unaligned

/-! Native calls at each newly supported version use the same complete value
contracts and deciders. The specs package separately checks whole-contract
equality; each corpus here is recorded from its own exact Rust dependency. -/

namespace SolanalibTest.Conformance.Library.Families.Versions

open Solanalib.Contracts.Model Solanalib.Specs.Core
  _root_.SolanalibTest.Conformance.Library.Families.Runtime

private def toBytes (reference : String) (model : Unit → Hash.Value → Hash.Array32 × Unit) :
  Checker where
  function := "solana_hash::Hash::to_bytes"
  generics := []
  reference := reference
  decides := [reference]
  check := fun c => do
    Values.unitState c
    decideReturns (returnsOf model) model rfl () (← Values.hashValue (← field c.args "hash"))
      Values.array32 asUnit (fun a => bytesJson a.val) (fun _ => Lean.Json.null) c.outcome

private def intoU64 (reference : String) (model : Unit → Unaligned.U64 → UInt64 × Unit) : Checker
  where
  function :=
    "solana_zero_copy::unaligned::<impl \
      core::convert::From<solana_zero_copy::unaligned::U64> for u64>::from"
  generics := []
  reference := reference
  decides := [reference]
  check := fun c => do
    Values.unitState c
    decideReturns (returnsOf model) model rfl () (← bytesN 8 (← field c.args "value"))
      u64 asUnit u64Json (fun _ => Lean.Json.null) c.outcome

def corpora : List (String × List Checker) := [
  ("solana_hash_4_3_0", [toBytes "Solanalib.Specs.SolanaHash.Hash.to_bytes_model"
    Solanalib.Specs.SolanaHash.Hash.to_bytes_model]),
  ("solana_hash_4_4_0", [toBytes "Solanalib.Specs.SolanaHash.Hash.to_bytes_model"
    Solanalib.Specs.SolanaHash.Hash.to_bytes_model]),
  ("solana_zero_copy_1_0_1", [intoU64 "Solanalib.Specs.SolanaZeroCopy.unaligned.U64.into_u6\
    4_model"
    Solanalib.Specs.SolanaZeroCopy.unaligned.U64.into_u64_model]),
  ("solana_zero_copy_1_1_0", [intoU64 "Solanalib.Specs.SolanaZeroCopy.unaligned.U64.into_u6\
    4_model"
    Solanalib.Specs.SolanaZeroCopy.unaligned.U64.into_u64_model]),
  ("solana_zero_copy_1_1_1", [intoU64 "Solanalib.Specs.SolanaZeroCopy.unaligned.U64.into_u6\
    4_model"
    Solanalib.Specs.SolanaZeroCopy.unaligned.U64.into_u64_model])
]

end SolanalibTest.Conformance.Library.Families.Versions
