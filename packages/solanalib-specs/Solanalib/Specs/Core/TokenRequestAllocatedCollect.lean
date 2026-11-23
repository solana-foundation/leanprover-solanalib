/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.TokenRequestAllocatedControl

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.Token.AllocatedCollect

/-- Actual account-borrow state and the remaining mathematical state of the consumer. -/
abbrev World (Extra : Type) := AccountInfo.State × Extra

/-- The copied key and the live shared reference returned by the source closure. -/
abbrev Element := Solanalib.Runtime.Pubkey × AllocatedControl.DataRef

/-- The source iterator retains its length and re-reads the same account-info
vector in the actual state. Its source borrow/lifetime is a binding obligation. -/
structure Iterator (Extra : Type) where
  /-- Length captured by the source iterator. -/
  length : Nat
  /-- A current element, or a failed representation check. -/
  elementAt : World Extra → Nat → Option AccountInfo.Value

/-- Explicit higher-order collection dependency. This is the actual std call
boundary, not an SDK-level allocation/push loop. Its primitive protocol laws
are separate from the operational relation of the enclosing token helper. -/
structure Provider (Extra Resource Unwind Terminal : Type) where
  /-- The dependency receives the source iterator and its exact callback,
preserving ordinary errors, unwinds and terminal outcomes. -/
  run : Iterator Extra →
    Callback.Run (World Extra) AccountInfo.Value (Except Error Element) Unwind Terminal →
    AllocatedControl.Run (World Extra) Resource Unwind Terminal

/-- The ordinary resolution0.11.1 closure copies the key before attempting the
checked shared borrow. It returns a live reference identity, not saved bytes. -/
def borrowElement {Extra Unwind Terminal : Type}
    (raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal) :
    Callback.Run (World Extra) AccountInfo.Value (Except Error Element) Unwind Terminal :=
  fun before info => AllocatedControl.bind (AllocatedControl.borrow raise true info)
    (fun reference => AllocatedControl.pure (info.key, reference)) before

/-- A real successful shared acquisition returns that reference with the key
copied from the account-info argument of this callback. -/
theorem borrowElement_ok {Extra Unwind Terminal : Type}
    (raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal)
    (before after : World Extra) (info : AccountInfo.Value) (reference : AllocatedControl.DataRef)
    (borrowed : AllocatedControl.borrow raise true info before (.returned (.ok reference) after)) :
    borrowElement raise before info (.returned (.ok (info.key, reference)) after) :=
  ⟨.returned (.ok reference) after, borrowed, rfl⟩

/-- A real checked-borrow failure is preserved exactly, without attempting
the next source callback or manufacturing a vector resource. -/
theorem borrowElement_error {Extra Unwind Terminal : Type}
    (raise : Callback.Run (World Extra) Onchain.Panic Empty Unwind Terminal)
    (before after : World Extra) (info : AccountInfo.Value) (error : Error)
    (failed : AllocatedControl.borrow raise true info before (.returned (.error error) after)) :
    borrowElement raise before info (.returned (.error error) after) :=
  ⟨.returned (.error error) after, failed, rfl⟩

end Solanalib.Specs.Core.Token.AllocatedCollect
