/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import SolanalibTest.Specs.Core.Sysvar
public import Solanalib.Specs.Core.SysvarRent102Getter

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.Sysvar

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem clock_and_rent_request_different_lengths :
    Sysvar.pinClockConfig.request.kind = .generic Solanalib.Runtime.Ids.sysvarClock 0 40 ∧
      Sysvar.pinRent102Config.request.kind = .generic Solanalib.Runtime.Ids.sysvarRent 0 16 :=
  ⟨rfl, rfl⟩

end SolanalibTest.Specs.Core.Sysvar
