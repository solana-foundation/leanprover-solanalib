/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.CpiRequestCheckedSlice

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.CpiRequest.Checked

universe u v w

/-- The v1 maximum check precedes allocation and every account observation. -/
theorem sliceV1_too_many {State : Type u} {Resource : Type v}
    {Unwind Terminal : Type}
    (pool : State → AccountView.State) (storage : Storage State Resource Unwind Terminal)
    (invoke : Syscall State Unwind Terminal) (before : State)
    (request : Request AccountView.Handle) (tooMany : 128 < request.instruction.metas.length)
    (outcome : Outcome State (Except Error Unit) Unwind Terminal) :
    sliceV1 pool storage invoke before request outcome ↔
      outcome = .returned (.error .InvalidArgument) before := by
  simp [sliceV1, tooMany]


end Solanalib.Specs.Core.CpiRequest.Checked
