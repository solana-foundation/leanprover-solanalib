/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Sysvar
public import Solanalib.Specs.Core.SysvarRent102

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Sysvar

def pinRent102Config : GetterConfig Rent102 where
  request := ⟨.generic Solanalib.Runtime.Ids.sysvarRent 0 16, none⟩
  valid := fun _ => True
  error := genericError


end Solanalib.Specs.Core.Sysvar
