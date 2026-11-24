/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedCollectReference

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedCollect

/-- A finite collector-internal effect preserves the complete account guard
world while allowing its actual auxiliary state to change. This is an explicit
strong frame option for a dependency binding, not a consequence of a vector
identity or of arbitrary allocator behavior. -/
def PreservesAccounts {Extra Value Unwind Terminal : Type} (before : World Extra) :
    Outcome (World Extra) Value Unwind Terminal → Prop
  | .returned _ after | .unwound _ after => after.1 = before.1
  | .terminated _ => True

/-- Equal account states preserve the current read of a retained guard, even
when the auxiliary allocation state of the collector changed. -/
theorem read_of_account_state {Extra : Type} (reference : AllocatedControl.DataRef)
    (before after : World Extra) (same : after.1 = before.1) :
    reference.read after = reference.read before := by
  simp only [AllocatedControl.DataRef.read, same]

/-- A normal internal dependency effect under the explicit frame keeps the
same current reference observation; it cannot silently invalidate the guard. -/
theorem internal_read {Extra Resource Unwind Terminal : Type}
    {protocol : Protocol Extra Resource Unwind Terminal}
    (index : Nat) (acquired : List Element)
    (frame : ∀ before outcome,
      protocol.internal index acquired before outcome → PreservesAccounts before outcome)
    (before after : World Extra)
    (reference : AllocatedControl.DataRef)
    (stepped : protocol.internal index acquired before (.returned () after)) :
    reference.read after = reference.read before :=
  read_of_account_state reference before after (frame before _ stepped)

/-- An internal unwind retains reference observations until the separately
sequenced element cleanup actually retires them. -/
theorem unwind_read {Extra Resource Unwind Terminal : Type}
    {protocol : Protocol Extra Resource Unwind Terminal}
    (index : Nat) (acquired : List Element)
    (frame : ∀ before outcome,
      protocol.internal index acquired before outcome → PreservesAccounts before outcome)
    (before after : World Extra)
    (reference : AllocatedControl.DataRef) (reason : Unwind)
    (stepped : protocol.internal index acquired before (.unwound reason after)) :
    reference.read after = reference.read before :=
  read_of_account_state reference before after (frame before _ stepped)

/-- The explicit finish frame preserves the live current references whose
identities the resource law records in the returned vector. -/
theorem finish_read {Extra Resource Unwind Terminal : Type}
    {protocol : Protocol Extra Resource Unwind Terminal} (acquired : List Element)
    (frame : ∀ before outcome,
      protocol.finish before acquired outcome → PreservesAccounts before outcome)
    (before after : World Extra) (resource : Resource)
    (reference : AllocatedControl.DataRef)
    (finished : protocol.finish before acquired (.returned resource after)) :
    reference.read after = reference.read before :=
  read_of_account_state reference before after (frame before _ finished)

end Solanalib.Specs.Core.Token.AllocatedCollect
