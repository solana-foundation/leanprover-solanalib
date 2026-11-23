/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.SdkValue

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.SplPod.optional_keys.OptionalNonZeroPubkey

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Interpret exactly the all-zero key as None and retain every other key. -/
abbrev into_option_contract := SdkValue.optionalKeyContract

/-- Exact total value reference. -/
abbrev into_option_model := SdkValue.optionalKeyModel

theorem into_option_reference : into_option_contract.RealizedBy into_option_model :=
  SdkValue.optionalKeyReference

theorem into_option_satisfiable : into_option_contract.Satisfiable :=
  SdkValue.optionalKeySatisfiable


end Solanalib.Specs.SplPod.optional_keys.OptionalNonZeroPubkey
