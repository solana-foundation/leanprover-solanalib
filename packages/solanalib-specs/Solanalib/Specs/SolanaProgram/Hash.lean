/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Hash
public import Solanalib.Specs.Core.HashSingle

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.hash.Hash

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The legacy Copy receiver is consumed at the source boundary; its exact
32-byte mathematical observation is the common value-copy contract. -/
abbrev to_bytes_contract := Solanalib.Specs.Core.Hash.toBytesContract

abbrev to_bytes_run := Solanalib.Specs.Core.Hash.toBytesModel

theorem to_bytes_reference : to_bytes_contract.RealizedBy to_bytes_run :=
  Solanalib.Specs.Core.Hash.toBytesReference

theorem to_bytes_satisfiable : to_bytes_contract.Satisfiable :=
  Solanalib.Specs.Core.Hash.toBytesSatisfiable

end Solanalib.Specs.SolanaProgram.hash.Hash

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgram.hash

open Solanalib.Contracts.Model Solanalib.Specs.Core

def hash_contract : Family := Hash.Single.initialized
def hash_run : FamilyRun hash_contract := Hash.Single.initializedRun
def hash_sample : hash_contract.Index := Hash.Initialized.sample

theorem hash_reference : FamilyReference hash_contract hash_run :=
  Hash.Single.initialized_reference

theorem hash_hasExecution :
    FamilyHasExecution hash_contract hash_run hash_sample :=
  Hash.Single.initialized_hasExecution

theorem hash_satisfiable : FamilySatisfiable hash_contract hash_sample :=
  hash_hasExecution.satisfiable

end Solanalib.Specs.SolanaProgram.hash
