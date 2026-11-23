/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SolanaSdkIds

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SolanaSdkIds

theorem exact_system_id_bytes :
    (Solanalib.Specs.SolanaSdkIds.system_program.id_model () ()).1.bytes = List.replicate 32 0 := by
  decide

end SolanalibTest.Specs.SolanaSdkIds
