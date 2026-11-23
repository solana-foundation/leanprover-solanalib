/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import SolanalibTest.Conformance.Library.Families.Runtime.Values
import Solanalib.Specs.SolanaProgramError.ProgramError
import Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull.Address

/-! Exact modern error conversions and the reviewed pure Address nullable instance. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.ErrorNullable

open Lean (Json)
open Solanalib.Contracts.Model Solanalib.Specs.Core
open SolanalibTest.Conformance.Library.Families.Runtime
open SolanalibTest.Conformance.Library.Families.Runtime.Values

def option {T : Type} (payload : Json → Result T) : Json → Result (Option T)
  | .null => pure none
  | value => do pure (some (← payload (← field value "some")))

def optionJson {T : Type} (payload : T → Json) : Option T → Json
  | none => .null
  | some value => Json.mkObj [("some", payload value)]

def errorFrom : Checker where
  function := "<solana_program_error::ProgramError as core::convert::From<u64>>::from"
  generics := []
  reference := "Solanalib.Specs.SolanaProgramError.ProgramError.from_u64_model"
  decides := ["Solanalib.Specs.SolanaProgramError.ProgramError.from_u64_model"]
  check := fun c => do
    unitState c
    decideReturns (returnsOf Solanalib.Specs.SolanaProgramError.ProgramError.from_u64_model)
      Solanalib.Specs.SolanaProgramError.ProgramError.from_u64_model rfl () (← u64 (← field c.args
        "status"))
      (programError) asUnit (programErrorJson) (fun _ => Json.null) c.outcome

def errorInto : Checker where
  function :=
    "solana_program_error::<impl core::convert::From<solana_program_error::ProgramError> \
      for u64>::from"
  generics := []
  reference := "Solanalib.Specs.SolanaProgramError.ProgramError.into_u64_model"
  decides := ["Solanalib.Specs.SolanaProgramError.ProgramError.into_u64_model"]
  check := fun c => do
    unitState c
    decideReturns (returnsOf Solanalib.Specs.SolanaProgramError.ProgramError.into_u64_model)
      Solanalib.Specs.SolanaProgramError.ProgramError.into_u64_model rfl () (← programError (←
        field c.args "error"))
      (u64) asUnit (u64Json) (fun _ => Json.null) c.outcome

def nullableAddress : Checker where
  function := "solana_nullable::maybe_null::MaybeNull::<T>::get"
  generics := [("T", "solana-address-2.6.1::Address")]
  reference := "Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull.get_run"
  decides := ["Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull.get_run"]
  check := fun c => do
    unitState c
    let key ← pubkey (← field c.args "key")
    let model := Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull.get_run
      Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull.address_index
    decideReturns (State := Unit) (Args := Solanalib.Runtime.Pubkey) (Value := Option
      Solanalib.Runtime.Pubkey)
      model (fun before value => (Nullable.Value.addressGet value, before))
      (by
        funext before value outcome
        apply propext
        exact (Nullable.Value.address_graph before value outcome).trans
          (eq_comm.trans (returnsOf_iff
            (fun before value => (Nullable.Value.addressGet value, before))
            before value outcome).symm))
      () key (option pubkey) asUnit (optionJson pubkeyJson) (fun _ => Json.null) c.outcome

def corpora : List (String × List Checker) := [
  ("error_nullable_program_error_3_0_1", [errorFrom, errorInto]),
  ("nullable_address_2_6_1", [nullableAddress])]

end SolanalibTest.Conformance.Library.Families.ErrorNullable
