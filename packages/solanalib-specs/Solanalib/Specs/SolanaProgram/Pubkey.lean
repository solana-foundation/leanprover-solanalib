/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AddressOperations

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

/-! These Program models retain their exact source profiles. The current
catalog selection admits solana-program 1.15.2 and 1.18.26; releases and build conditions
are checked per member. The namespace alone grants no release admission. -/

namespace Solanalib.Specs.SolanaProgram.pubkey.Pubkey

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Address
open Solanalib.Specs.Core.Address.Operations

/-! Exact 32-byte value observations and the selected Solana syscall branch.
The shared Pubkey family starts a zeroed destination, preserves actual
provider exits and uses the selected legacy Pubkey status conversion. -/

def to_bytes_contract : Solanalib.Contracts.Model Unit (Value) (Array32) :=
  valueContract (asArray)

def to_bytes_model : Unit → (Value) → (Array32) × Unit := valueModel (asArray)

theorem to_bytes_reference : to_bytes_contract.RealizedBy to_bytes_model :=
  valueReference (asArray)

theorem to_bytes_satisfiable : to_bytes_contract.Satisfiable :=
  valueSatisfiable (asArray) (_root_.Solanalib.Runtime.Pubkey.zero)

def as_ref_contract : Solanalib.Contracts.Model Unit (Value) (_root_.Solanalib.Runtime.Bytes) :=
  valueContract (fun value : Value => value.bytes)

def as_ref_model : Unit → (Value) → (_root_.Solanalib.Runtime.Bytes) × Unit := valueModel (fun
  value : Value => value.bytes)

theorem as_ref_reference : as_ref_contract.RealizedBy as_ref_model :=
  valueReference (fun value : Value => value.bytes)

theorem as_ref_satisfiable : as_ref_contract.Satisfiable :=
  valueSatisfiable (fun value : Value => value.bytes) (_root_.Solanalib.Runtime.Pubkey.zero)

def default_contract : Solanalib.Contracts.Model Unit (Unit) (Value) :=
  valueContract (fun _ : Unit => _root_.Solanalib.Runtime.Pubkey.zero)

def default_model : Unit → (Unit) → (Value) × Unit := valueModel (fun _ : Unit =>
  _root_.Solanalib.Runtime.Pubkey.zero)

theorem default_reference : default_contract.RealizedBy default_model :=
  valueReference (fun _ : Unit => _root_.Solanalib.Runtime.Pubkey.zero)

theorem default_satisfiable : default_contract.Satisfiable :=
  valueSatisfiable (fun _ : Unit => _root_.Solanalib.Runtime.Pubkey.zero) (())

def eq_contract : Solanalib.Contracts.Model Unit (Value × Value) (Bool) :=
  valueContract (fun args : Value × Value => equal args.1 args.2)

def eq_model : Unit → (Value × Value) → (Bool) × Unit := valueModel (fun args : Value × Value =>
  equal args.1 args.2)

theorem eq_reference : eq_contract.RealizedBy eq_model :=
  valueReference (fun args : Value × Value => equal args.1 args.2)

theorem eq_satisfiable : eq_contract.Satisfiable :=
  valueSatisfiable (fun args : Value × Value => equal args.1 args.2)
    ((_root_.Solanalib.Runtime.Pubkey.zero, _root_.Solanalib.Runtime.Pubkey.zero))

def clone_contract : Solanalib.Contracts.Model Unit (Value) (Value) :=
  valueContract (id)

def clone_model : Unit → (Value) → (Value) × Unit := valueModel (id)

theorem clone_reference : clone_contract.RealizedBy clone_model :=
  valueReference (id)

theorem clone_satisfiable : clone_contract.Satisfiable :=
  valueSatisfiable (id) (_root_.Solanalib.Runtime.Pubkey.zero)

def create_program_address_solana_contract : Family := createFamily .zeroed .legacyPubkey
def create_program_address_solana_run : FamilyRun create_program_address_solana_contract :=
  createReference .zeroed .legacyPubkey
def create_program_address_solana_sample : create_program_address_solana_contract.Index :=
  createSample .zeroed

theorem create_program_address_solana_reference : FamilyReference
  create_program_address_solana_contract create_program_address_solana_run :=
  createReference_correct .zeroed .legacyPubkey

theorem create_program_address_solana_has_execution :
    FamilyHasExecution create_program_address_solana_contract create_program_address_solana_run
      create_program_address_solana_sample :=
  createSample_execution .zeroed .legacyPubkey

theorem create_program_address_solana_satisfiable :
    FamilySatisfiable create_program_address_solana_contract create_program_address_solana_sample :=
  create_program_address_solana_has_execution.satisfiable

def find_program_address_solana_contract : Family := zeroFindFamily
def find_program_address_solana_run : FamilyRun find_program_address_solana_contract :=
  zeroFindReference
def find_program_address_solana_sample : find_program_address_solana_contract.Index :=
  zeroFindSample

theorem find_program_address_solana_reference : FamilyReference
  find_program_address_solana_contract find_program_address_solana_run :=
  zeroFindReference_correct

theorem find_program_address_solana_has_execution :
    FamilyHasExecution find_program_address_solana_contract find_program_address_solana_run
      find_program_address_solana_sample :=
  zeroFindSample_execution

theorem find_program_address_solana_satisfiable :
    FamilySatisfiable find_program_address_solana_contract find_program_address_solana_sample :=
  find_program_address_solana_has_execution.satisfiable

def create_with_seed_contract : Family := seedFamily
def create_with_seed_run : FamilyRun create_with_seed_contract := seedReference
def create_with_seed_sample : create_with_seed_contract.Index := seedSample

theorem create_with_seed_reference : FamilyReference create_with_seed_contract create_with_seed_run
  :=
  seedReference_correct

theorem create_with_seed_has_execution :
    FamilyHasExecution create_with_seed_contract create_with_seed_run create_with_seed_sample :=
  seedSample_execution

theorem create_with_seed_satisfiable :
    FamilySatisfiable create_with_seed_contract create_with_seed_sample :=
  create_with_seed_has_execution.satisfiable

end Solanalib.Specs.SolanaProgram.pubkey.Pubkey
