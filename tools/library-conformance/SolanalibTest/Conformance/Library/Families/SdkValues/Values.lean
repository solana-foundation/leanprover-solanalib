/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.SolanaProgram.ProgramOption
import Solanalib.Specs.SolanaZeroCopy.U16
import Solanalib.Specs.SplPod.OptionalKeys
import Solanalib.Specs.SolanaSdkIds.AdditionalIds
import SolanalibTest.Conformance.Library.Families.SdkValues.Encoding
import Solanalib.Specs.SplPod.Primitives
import Solanalib.Specs.SolanaProgramOption.COption

/-! Pure SDK value checkers use the exact registered total reference. Variant
and borrowed-field checkers instantiate their family at the native payload
carrier while retaining the same parent identity for as_ref. -/

set_option autoImplicit false

open Lean (Json toJson)

namespace SolanalibTest.Conformance.Library.Families.SdkValues.Values

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Values

def podU16 : Checker where
  function :=
    "spl_pod::primitives::<impl core::convert::From<spl_pod::primitives::PodU16> for \
      u16>::from"
  generics := []
  reference := "Solanalib.Specs.SplPod.primitives.PodU16.into_u16_model"
  decides := ["Solanalib.Specs.SplPod.primitives.PodU16.into_u16_model"]
  check := fun c => do
    unitState c
    decideReturns (returnsOf Solanalib.Specs.SplPod.primitives.PodU16.into_u16_model)
      Solanalib.Specs.SplPod.primitives.PodU16.into_u16_model rfl () (← bytesN 2 (← field c.args
        "value"))
      (u16) asUnit (fun n => toJson n.toNat) (fun _ => Json.null) c.outcome

def podU64 : Checker where
  function :=
    "spl_pod::primitives::<impl core::convert::From<spl_pod::primitives::PodU64> for \
      u64>::from"
  generics := []
  reference := "Solanalib.Specs.SplPod.primitives.PodU64.into_u64_model"
  decides := ["Solanalib.Specs.SplPod.primitives.PodU64.into_u64_model"]
  check := fun c => do
    unitState c
    decideReturns (returnsOf Solanalib.Specs.SplPod.primitives.PodU64.into_u64_model)
      Solanalib.Specs.SplPod.primitives.PodU64.into_u64_model rfl () (← bytesN 8 (← field c.args
        "value"))
      (u64) asUnit (u64Json) (fun _ => Json.null) c.outcome

def isNone221 : Checker where
  function := "solana_program_option::COption::<T>::is_none"
  generics := [("T", "u64")]
  reference := "Solanalib.Specs.SolanaProgramOption.COption.is_none_run"
  decides := ["Solanalib.Specs.SolanaProgramOption.COption.is_none_run"]
  check := fun c => do
    unitState c
    decideReturns (State := Unit) (Args := ProgramOption.Value UInt64) (Value := Bool)
      (Solanalib.Specs.SolanaProgramOption.COption.is_none_run UInt64)
      (fun before value => (ProgramOption.isNone value, before)) rfl
      () (← cOption u64 (← field c.args "option"))
      bool asUnit Json.bool (fun _ => Json.null) c.outcome

def asRef : Checker where
  function := "solana_program_option::COption::<T>::as_ref"
  generics := [("T", "u64")]
  reference := "Solanalib.Specs.SolanaProgramOption.COption.as_ref_run"
  decides := ["Solanalib.Specs.SolanaProgramOption.COption.as_ref_run"]
  check := fun c => do
    unitState c
    let args ← pure (← (← field c.args "parent").getNat?, ← bool (← field c.args "present"))
    decideReturns (State := Unit) (Args := Nat × Bool) (Value := ProgramOption.Value
      (FieldReference Nat Unit)) (Solanalib.Specs.SolanaProgramOption.COption.as_ref_run Nat)
      (fun before args => (ProgramOption.asRef args.1 args.2, before)) rfl () args
      (cOption fun j => do pure (⟨← j.getNat?, ()⟩ : FieldReference Nat Unit)) asUnit
      (cOptionJson fun value => toJson value.parent) (fun _ => Json.null) c.outcome

end SolanalibTest.Conformance.Library.Families.SdkValues.Values

namespace SolanalibTest.Conformance.Library.Families.SdkValues.Values

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Values

def zero111 : Checker where
  function :=
    "solana_zero_copy::unaligned::<impl \
      core::convert::From<solana_zero_copy::unaligned::U16> for u16>::from"
  generics := []
  reference := "Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_model"
  decides := ["Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_model"]
  check := fun c => do
    unitState c
    decideReturns (returnsOf Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_model)
      Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_model rfl () (← bytesN 2 (← field
        c.args "value"))
      (u16) asUnit (fun n => toJson n.toNat) (fun _ => Json.null) c.outcome

def loaderId : Checker where
  function := "solana_sdk_ids::bpf_loader_upgradeable::id"
  generics := []
  reference := "Solanalib.Specs.SolanaSdkIds.bpf_loader_upgradeable.id_model"
  decides := ["Solanalib.Specs.SolanaSdkIds.bpf_loader_upgradeable.id_model"]
  check := fun c => do
    unitState c
    asUnit c.args
    decideReturns (returnsOf Solanalib.Specs.SolanaSdkIds.bpf_loader_upgradeable.id_model)
      Solanalib.Specs.SolanaSdkIds.bpf_loader_upgradeable.id_model rfl () ()
      pubkey asUnit pubkeyJson (fun _ => Json.null) c.outcome

def ed25519Id : Checker where
  function := "solana_sdk_ids::ed25519_program::id"
  generics := []
  reference := "Solanalib.Specs.SolanaSdkIds.ed25519_program.id_model"
  decides := ["Solanalib.Specs.SolanaSdkIds.ed25519_program.id_model"]
  check := fun c => do
    unitState c
    asUnit c.args
    decideReturns (returnsOf Solanalib.Specs.SolanaSdkIds.ed25519_program.id_model)
      Solanalib.Specs.SolanaSdkIds.ed25519_program.id_model rfl () ()
      pubkey asUnit pubkeyJson (fun _ => Json.null) c.outcome

end SolanalibTest.Conformance.Library.Families.SdkValues.Values

namespace SolanalibTest.Conformance.Library.Families.SdkValues.Values

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Values

def zero101 : Checker where
  function :=
    "solana_zero_copy::unaligned::<impl \
      core::convert::From<solana_zero_copy::unaligned::U16> for u16>::from"
  generics := []
  reference := "Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_model"
  decides := ["Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_model"]
  check := fun c => do
    unitState c
    decideReturns (returnsOf Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_model)
      Solanalib.Specs.SolanaZeroCopy.unaligned.U16.into_u16_model rfl () (← bytesN 2 (← field
        c.args "value"))
      (u16) asUnit (fun n => toJson n.toNat) (fun _ => Json.null) c.outcome

def optionalKey : Checker where
  function :=
    "spl_pod::optional_keys::<impl \
      core::convert::From<spl_pod::optional_keys::OptionalNonZeroPubkey> for \
      core::option::Option<solana_address::Address>>::from"
  generics := []
  reference := "Solanalib.Specs.SplPod.optional_keys.OptionalNonZeroPubkey.into_option_mode\
    l"
  decides := ["Solanalib.Specs.SplPod.optional_keys.OptionalNonZeroPubkey.into_option_model"]
  check := fun c => do
    unitState c
    decideReturns (returnsOf
      Solanalib.Specs.SplPod.optional_keys.OptionalNonZeroPubkey.into_option_model)
      Solanalib.Specs.SplPod.optional_keys.OptionalNonZeroPubkey.into_option_model rfl () (← pubkey
        (← field c.args "key"))
      (option pubkey) asUnit (optionJson pubkeyJson) (fun _ => Json.null) c.outcome

def instructionsId : Checker where
  function := "solana_sdk_ids::sysvar::instructions::id"
  generics := []
  reference := "Solanalib.Specs.SolanaSdkIds.sysvar.instructions.id_model"
  decides := ["Solanalib.Specs.SolanaSdkIds.sysvar.instructions.id_model"]
  check := fun c => do
    unitState c
    asUnit c.args
    decideReturns (returnsOf Solanalib.Specs.SolanaSdkIds.sysvar.instructions.id_model)
      Solanalib.Specs.SolanaSdkIds.sysvar.instructions.id_model rfl () ()
      pubkey asUnit pubkeyJson (fun _ => Json.null) c.outcome

def voteId : Checker where
  function := "solana_sdk_ids::vote::id"
  generics := []
  reference := "Solanalib.Specs.SolanaSdkIds.vote.id_model"
  decides := ["Solanalib.Specs.SolanaSdkIds.vote.id_model"]
  check := fun c => do
    unitState c
    asUnit c.args
    decideReturns (returnsOf Solanalib.Specs.SolanaSdkIds.vote.id_model)
      Solanalib.Specs.SolanaSdkIds.vote.id_model rfl () ()
      pubkey asUnit pubkeyJson (fun _ => Json.null) c.outcome

end SolanalibTest.Conformance.Library.Families.SdkValues.Values

namespace SolanalibTest.Conformance.Library.Families.SdkValues.Values

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Values

def intoOption : Checker where
  function :=
    "solana_program::program_option::<impl \
      core::convert::From<solana_program::program_option::COption<T>> for \
      core::option::Option<T>>::from"
  generics := [("T", "u64")]
  reference := "Solanalib.Specs.SolanaProgram.program_option.COption.into_option_run"
  decides := ["Solanalib.Specs.SolanaProgram.program_option.COption.into_option_run"]
  check := fun c => do
    unitState c
    decideReturns (State := Unit) (Args := ProgramOption.Value UInt64) (Value := Option UInt64)
      (Solanalib.Specs.SolanaProgram.program_option.COption.into_option_run UInt64)
      (fun before value => (ProgramOption.toOption value, before)) rfl
      () (← cOption u64 (← field c.args "option"))
      (option u64) asUnit (optionJson u64Json) (fun _ => Json.null) c.outcome

end SolanalibTest.Conformance.Library.Families.SdkValues.Values

namespace SolanalibTest.Conformance.Library.Families.SdkValues.Values

open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Values

def isNone115 : Checker where
  function := "solana_program::program_option::COption::<T>::is_none"
  generics := [("T", "u64")]
  reference := "Solanalib.Specs.SolanaProgram.program_option.COption.is_none_run"
  decides := ["Solanalib.Specs.SolanaProgram.program_option.COption.is_none_run"]
  check := fun c => do
    unitState c
    decideReturns (State := Unit) (Args := ProgramOption.Value UInt64) (Value := Bool)
      (Solanalib.Specs.SolanaProgram.program_option.COption.is_none_run UInt64)
      (fun before value => (ProgramOption.isNone value, before)) rfl
      () (← cOption u64 (← field c.args "option"))
      bool asUnit Json.bool (fun _ => Json.null) c.outcome

end SolanalibTest.Conformance.Library.Families.SdkValues.Values
