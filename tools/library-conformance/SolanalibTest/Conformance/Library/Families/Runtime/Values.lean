/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Runtime.Common
import Solanalib.Specs.SolanaHash.Hash
import Solanalib.Specs.SolanaSdkIds.SystemProgram
import Solanalib.Specs.SolanaZeroCopy.Unaligned
import Solanalib.Specs.SolanaProgramOption.COption

/-!
# Total value functions: `Hash::to_bytes`, `system_program::id`,
# `From<U64> for u64` and `COption::is_some`

Each is registered as a total function (`RealizedBy`) or as `returnsOf` of
one at every family index (`COption::is_some`), and is decided through
`decideReturns` with an `rfl` proof that the decided relation is the
registered one. `COption<T>` is checked at `T = u64, u8, ()` and `[u8; 32]`,
mapped to the Lean payload types `UInt64`, `UInt8`, `Unit` and 32-byte lists.
-/

set_option autoImplicit false

open Lean (Json ToJson toJson)

namespace SolanalibTest.Conformance.Library.Families.Runtime.Values

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime

def unitState (c : Case) : Result Unit := asUnit c.state

/-! ## solana-hash 4.5.0 -/

def hashValue (j : Json) : Result Hash.Value := do
  let b ← bytesN 32 j
  pure ⟨b.val, b.property⟩

def array32 (j : Json) : Result Hash.Array32 := bytesN 32 j

def toBytes : Checker where
  function := "solana_hash::Hash::to_bytes"
  generics := []
  reference := "Solanalib.Specs.SolanaHash.Hash.to_bytes_model"
  decides := ["Solanalib.Specs.SolanaHash.Hash.to_bytes_model"]
  check := fun c => do
    unitState c
    decideReturns (returnsOf Solanalib.Specs.SolanaHash.Hash.to_bytes_model)
      Solanalib.Specs.SolanaHash.Hash.to_bytes_model rfl () (← hashValue (← field c.args
        "hash"))
      array32 asUnit (fun a => bytesJson a.val) (fun _ => Json.null) c.outcome

/-! ## solana-sdk-ids 3.1.0 -/

def systemProgramId : Checker where
  function := "solana_sdk_ids::system_program::id"
  generics := []
  reference := "Solanalib.Specs.SolanaSdkIds.system_program.id_model"
  decides := ["Solanalib.Specs.SolanaSdkIds.system_program.id_model"]
  check := fun c => do
    unitState c
    asUnit c.args
    decideReturns (returnsOf Solanalib.Specs.SolanaSdkIds.system_program.id_model)
      Solanalib.Specs.SolanaSdkIds.system_program.id_model rfl () ()
      pubkey asUnit pubkeyJson (fun _ => Json.null) c.outcome

/-! ## solana-zero-copy 1.2.0 -/

def intoU64 : Checker where
  function :=
    "solana_zero_copy::unaligned::<impl \
      core::convert::From<solana_zero_copy::unaligned::U64> for u64>::from"
  generics := []
  reference := "Solanalib.Specs.SolanaZeroCopy.unaligned.U64.into_u64_model"
  decides := ["Solanalib.Specs.SolanaZeroCopy.unaligned.U64.into_u64_model"]
  check := fun c => do
    unitState c
    decideReturns (returnsOf Solanalib.Specs.SolanaZeroCopy.unaligned.U64.into_u64_model)
      Solanalib.Specs.SolanaZeroCopy.unaligned.U64.into_u64_model rfl () (← bytesN 8 (← field
        c.args "value"))
      u64 asUnit u64Json (fun _ => Json.null) c.outcome

/-! ## solana-program-option 3.1.0 -/

def cOption {T : Type} (payload : Json → Result T) (j : Json) : Result (ProgramOption.Value T) :=
  match j with
  | .null => pure .none
  | _ => do pure (.some (← payload (← field j "some")))

/-- `is_some_run T` is, by definition, `returnsOf` of the variant inspection. -/
theorem is_some_evaluated (T : Type) :
    Solanalib.Specs.SolanaProgramOption.COption.is_some_run T =
      returnsOf (fun (before : Unit) (option : ProgramOption.Value T) =>
        (ProgramOption.isSome option, before)) := rfl

def isSome (rust : String) (T : Type) [DecidableEq T] (payload : Json → Result T) : Checker where
  function := "solana_program_option::COption::<T>::is_some"
  generics := [("T", rust)]
  reference := "Solanalib.Specs.SolanaProgramOption.COption.is_some_run"
  decides := ["Solanalib.Specs.SolanaProgramOption.COption.is_some_run"]
  check := fun c => do
    unitState c
    decideReturns (State := Unit) (Args := ProgramOption.Value T) (Value := Bool)
      (Solanalib.Specs.SolanaProgramOption.COption.is_some_run T)
      (fun (before : Unit) (option : ProgramOption.Value T) => (ProgramOption.isSome option,
        before))
      (is_some_evaluated T) () (← cOption payload (← field c.args "option"))
      bool asUnit Json.bool (fun _ => Json.null) c.outcome

def isSomeCheckers : List Checker := [
  isSome "u64" UInt64 u64,
  isSome "u8" UInt8 u8,
  isSome "()" Unit asUnit,
  isSome "[u8; 32]" { b : Solanalib.Runtime.Bytes // b.length = 32 } (bytesN 32)]

end SolanalibTest.Conformance.Library.Families.Runtime.Values
