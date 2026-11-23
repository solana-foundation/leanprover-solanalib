/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.Sysvar
public import Solanalib.Specs.Core.SysvarRentArithmetic

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Sysvar

def typedError (status : UInt64) : Option ProgramError.Value :=
  if status = 0 then none else some .unsupportedSysvar

def sdkClockConfig : GetterConfig Clock where
  request := ⟨.typed .clock, some zeroClock⟩
  valid := clockValid
  error := typedError

def sdkRentConfig : GetterConfig Rent300 where
  request := ⟨.typed .rent, some defaultRent300⟩
  valid := fun _ => True
  error := typedError

end Solanalib.Specs.Core.Sysvar
