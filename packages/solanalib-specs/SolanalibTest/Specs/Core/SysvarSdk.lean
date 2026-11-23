/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.Core.Sysvar
public import Solanalib.Specs.Core.SysvarSdk

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.Sysvar

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem typed_get_folds_same_status_to_unsupported :
    Sysvar.get Sysvar.sdkClockConfig (errorBackend 1) (4 : Nat) ()
      (.returned (.error .unsupportedSysvar) (5 : Nat)) :=
  ⟨.returned ⟨1, none⟩ (5 : Nat), rfl, rfl⟩

theorem typed_stub_preserves_unwind_effect :
    Sysvar.get Sysvar.sdkClockConfig unwindBackend (4 : Nat) ()
      (.unwound "stub" (6 : Nat)) :=
  ⟨.unwound "stub" (6 : Nat), rfl, rfl⟩


end SolanalibTest.Specs.Core.Sysvar
