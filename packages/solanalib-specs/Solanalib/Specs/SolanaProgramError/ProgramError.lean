/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.ErrorValue

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SolanaProgramError.ProgramError

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- The exact ProgramError 3.0.1 decoder, including custom-zero and upper-word truncation. -/
abbrev from_u64_contract := SdkValue.errorFromStatusContract

/-- Exact total value reference. -/
abbrev from_u64_model := SdkValue.errorFromStatusModel

theorem from_u64_reference : from_u64_contract.RealizedBy from_u64_model :=
  SdkValue.errorFromStatusReference

theorem from_u64_satisfiable : from_u64_contract.Satisfiable :=
  SdkValue.errorFromStatusSatisfiable

/-- Encode each builtin and Custom value with its source-defined status. -/
abbrev into_u64_contract := SdkValue.errorToStatusContract

/-- Exact total value reference. -/
abbrev into_u64_model := SdkValue.errorToStatusModel

theorem into_u64_reference : into_u64_contract.RealizedBy into_u64_model :=
  SdkValue.errorToStatusReference

theorem into_u64_satisfiable : into_u64_contract.Satisfiable :=
  SdkValue.errorToStatusSatisfiable


end Solanalib.Specs.SolanaProgramError.ProgramError
