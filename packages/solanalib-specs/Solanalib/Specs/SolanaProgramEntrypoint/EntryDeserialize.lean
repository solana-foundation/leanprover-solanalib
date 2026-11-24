/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.EntryDeserializeSDK
public import Solanalib.Specs.Core.EntryDeserializeSDKOrigins

@[expose] public section

open Solanalib.Contracts.Model

namespace Solanalib.Specs.SolanaProgramEntrypoint

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The SDK aligned-loader deserializer, with explicit allocation outcomes and owned aliases. -/
def deserialize_contract := EntryDeserialize.SDK.family
def deserialize_run := EntryDeserialize.SDK.run
def deserialize_sample := EntryDeserialize.SDK.sample

theorem deserialize_reference : FamilyReference deserialize_contract deserialize_run :=
  EntryDeserialize.SDK.reference

theorem deserialize_has_execution :
    FamilyHasExecution deserialize_contract deserialize_run deserialize_sample :=
  EntryDeserialize.SDK.hasExecution

theorem deserialize_satisfiable : FamilySatisfiable deserialize_contract deserialize_sample :=
  EntryDeserialize.SDK.satisfiable

end Solanalib.Specs.SolanaProgramEntrypoint
