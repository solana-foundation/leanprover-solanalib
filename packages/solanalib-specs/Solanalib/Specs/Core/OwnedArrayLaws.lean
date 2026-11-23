/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OwnedArray

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Owned.Array

universe u v w x y

/-- The completion dependency returns the current ordered vector contents.
This is a local dependency obligation, separate from construction scheduling,
element ownership, or correspondence with an actual Rust macro expansion. -/
structure Provider.CurrentLaw {State : Type u} {Element : Type v} {Resource : Type w}
    {Unwind : Type x} {Terminal : Type y}
    (provider : Provider State Element Resource Unwind Terminal)
    (vectors : VectorOps State Element Resource Unwind Terminal) : Prop where
  /-- Completion moves the exact supplied values, retaining duplicates/order. -/
  finish_current : ∀ before values resource after,
    provider.finish before values (.returned resource after) →
      vectors.current after resource = some values

end Solanalib.Specs.Core.Owned.Array
