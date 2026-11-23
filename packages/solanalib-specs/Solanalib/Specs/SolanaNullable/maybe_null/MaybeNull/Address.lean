/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull
public import Solanalib.Specs.Core.NullableValue

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Address 2.6.1 with feature nullable: the default query compares
the complete key to NONE, and both the temporary and payload have trivial drop. -/
abbrev address_index := Nullable.Value.addressIndex

theorem address_reference : (get_contract.contract address_index).Holds (get_run address_index) :=
  get_reference address_index

theorem address_has_execution : FamilyHasExecution get_contract get_run address_index :=
  Nullable.Value.address_execution

theorem address_satisfiable : (get_contract.contract address_index).Satisfiable :=
  Nullable.Value.address_satisfiable

end Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull
