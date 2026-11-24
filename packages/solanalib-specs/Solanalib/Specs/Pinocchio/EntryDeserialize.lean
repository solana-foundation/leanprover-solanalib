/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.EntryDeserializePinocchio
public import Solanalib.Specs.Core.EntryDeserializePinocchioAccount

@[expose] public section

open Solanalib.Contracts.Model

namespace Solanalib.Specs.Pinocchio.entrypoint

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- the allocation-free aligned-loader deserializer of Pinocchio at its exact const-generic bound.
-/
def deserialize_contract := EntryDeserialize.Pinocchio.family
def deserialize_run := EntryDeserialize.Pinocchio.run
def deserialize_sample := EntryDeserialize.Pinocchio.sample

theorem deserialize_reference : FamilyReference deserialize_contract deserialize_run :=
  EntryDeserialize.Pinocchio.reference

theorem deserialize_has_execution :
    FamilyHasExecution deserialize_contract deserialize_run deserialize_sample :=
  EntryDeserialize.Pinocchio.hasExecution

theorem deserialize_satisfiable : FamilySatisfiable deserialize_contract deserialize_sample :=
  EntryDeserialize.Pinocchio.satisfiable

end Solanalib.Specs.Pinocchio.entrypoint
