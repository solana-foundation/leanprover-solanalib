/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.HashSyscall

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaSha256Hasher

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Selected Solana/BPF hashv, including its uninitialized destination and
mandatory initialization on every normal provider return, regardless of status. -/
def hashv_contract : Family := Hash.Syscall.family

/-- The common callback sequence at every supplied source profile. -/
def hashv_model : FamilyRun hashv_contract := Hash.Syscall.reference

/-- An inhabited initialized provider for the consistency witness. -/
def hashv_sample : hashv_contract.Index := Hash.Syscall.sample

theorem hashv_reference : FamilyReference hashv_contract hashv_model :=
  Hash.Syscall.reference_correct

theorem hashv_hasExecution : FamilyHasExecution hashv_contract hashv_model hashv_sample :=
  Hash.Syscall.sample_hasExecution

theorem hashv_satisfiable : FamilySatisfiable hashv_contract hashv_sample :=
  hashv_hasExecution.satisfiable

end Solanalib.Specs.SolanaSha256Hasher
