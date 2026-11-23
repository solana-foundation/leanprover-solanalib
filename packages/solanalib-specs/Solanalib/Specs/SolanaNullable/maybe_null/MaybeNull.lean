/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.NullableOperations

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Nullable::is_none followed by a move or source-ordered cleanup, including panic exits. -/
abbrev get_contract : Family := Nullable.getFamily

/-- Exact relational reference at every source interpretation. -/
abbrev get_run : FamilyRun get_contract := Nullable.getRun

theorem get_reference : FamilyReference get_contract get_run :=
  Nullable.getReference

/-- Closed registered source-type and callback sample. -/
abbrev get_sample := Nullable.sample

theorem get_has_execution : FamilyHasExecution get_contract get_run get_sample :=
  Nullable.getExecution

theorem get_satisfiable : FamilySatisfiable get_contract get_sample :=
  Nullable.getSatisfiable


end Solanalib.Specs.SolanaNullable.maybe_null.MaybeNull
