/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressOperations
public import Solanalib.Specs.Core.AddressBorsh

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! These Program models retain their exact source profiles. The current
catalog selection admits solana-program 1.18.26; releases and build conditions
are checked per member. The namespace alone grants no release admission. -/

namespace Solanalib.Specs.SolanaProgram.pubkey.Pubkey

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Address.Operations

/-! The reached Borsh implementation delegates one fixed byte array field.
The provider is the actual writer/read_exact method, including overrides,
ordinary IO errors, partial effects and abnormal exits. -/

def serialize_contract : Family := Borsh.serializeFamily
def serialize_run : FamilyRun serialize_contract := Borsh.serializeReference
def serialize_sample : serialize_contract.Index := Borsh.writeSample

theorem serialize_reference : FamilyReference serialize_contract serialize_run :=
  Borsh.serializeReference_correct

theorem serialize_has_execution :
    FamilyHasExecution serialize_contract serialize_run serialize_sample :=
  Borsh.writeSample_execution

theorem serialize_satisfiable :
    FamilySatisfiable serialize_contract serialize_sample :=
  serialize_has_execution.satisfiable

end Solanalib.Specs.SolanaProgram.pubkey.Pubkey

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.pubkey.Pubkey

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Address.Operations

/-! The reached Borsh implementation delegates one fixed byte array field.
The provider is the actual writer/read_exact method, including overrides,
ordinary IO errors, partial effects and abnormal exits. -/

def deserialize_reader_contract : Family := Borsh.readFamily .invalidInput
def deserialize_reader_run : FamilyRun deserialize_reader_contract := Borsh.readReference
  .invalidInput
def deserialize_reader_sample : deserialize_reader_contract.Index := Borsh.readSample

theorem deserialize_reader_reference : FamilyReference deserialize_reader_contract
  deserialize_reader_run :=
  Borsh.readReference_correct .invalidInput

theorem deserialize_reader_has_execution :
    FamilyHasExecution deserialize_reader_contract deserialize_reader_run deserialize_reader_sample
      :=
  Borsh.readSample_execution .invalidInput

theorem deserialize_reader_satisfiable :
    FamilySatisfiable deserialize_reader_contract deserialize_reader_sample :=
  deserialize_reader_has_execution.satisfiable

end Solanalib.Specs.SolanaProgram.pubkey.Pubkey

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.pubkey.Pubkey

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Address.Operations

def deserialize_contract : Solanalib.Contracts.Model Unit (_root_.Solanalib.Runtime.Bytes) (Except
  Solanalib.Specs.Core.Borsh.IoError Value × _root_.Solanalib.Runtime.Bytes) :=
  valueContract (Borsh.legacyDecode)

def deserialize_model : Unit → (_root_.Solanalib.Runtime.Bytes) → (Except
  Solanalib.Specs.Core.Borsh.IoError Value × _root_.Solanalib.Runtime.Bytes) × Unit := valueModel
  (Borsh.legacyDecode)

theorem deserialize_reference : deserialize_contract.RealizedBy deserialize_model :=
  valueReference (Borsh.legacyDecode)

theorem deserialize_satisfiable : deserialize_contract.Satisfiable :=
  valueSatisfiable (Borsh.legacyDecode) ([])

end Solanalib.Specs.SolanaProgram.pubkey.Pubkey
