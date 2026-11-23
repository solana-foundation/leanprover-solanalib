/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OwnedFocus

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorViewsAssignment

variable {State Payload Unwind Terminal : Type}

/-- A Rust assignment installs its already evaluated right-hand side after
the destructor of the old value, including the unwind cleanup edge of the destructor.
Terminal exits have no state. The store receives the actual destructor state.
This models the drop-and-replace behavior of the selected compiler, not a proof of
the destructor of Rust or of the selected state projection. -/
def replaceAfter (store : State → Payload → State) (replacement : Payload) :
    Outcome State Unit Unwind Terminal → Outcome State Unit Unwind Terminal
  | .returned () after => .returned () (store after replacement)
  | .unwound reason after => .unwound reason (store after replacement)
  | .terminated reason => .terminated reason

/-- The destructor is called once on the old focused value. Its finite state
effects precede installation of the new owner, even when it unwinds. -/
def run (focus : Owned.Focus State Payload)
    (drop : Callback.Run State Payload Unit Unwind Terminal) :
    Callback.Run State Payload Unit Unwind Terminal :=
  fun before replacement final => ∃ dropped,
    drop before (focus.get before) dropped ∧
      replaceAfter focus.set replacement dropped = final

/-- A successful assignment has exactly the new field and the actual
destructor effects in every surrounding component selected by the focus. -/
theorem returned (focus : Owned.Focus State Payload)
    (drop : Callback.Run State Payload Unit Unwind Terminal)
    {before after : State} {replacement : Payload}
    (called : drop before (focus.get before) (.returned () after)) :
    run focus drop before replacement (.returned () (focus.set after replacement)) ∧
      focus.get (focus.set after replacement) = replacement :=
  ⟨⟨.returned () after, called, rfl⟩, focus.get_set after replacement⟩

/-- An unwinding old-value destructor also leaves the replacement installed;
the later cleanup of the caller must drop that owner, not the already dropped one. -/
theorem unwound (focus : Owned.Focus State Payload)
    (drop : Callback.Run State Payload Unit Unwind Terminal)
    {before after : State} {replacement : Payload} {reason : Unwind}
    (called : drop before (focus.get before) (.unwound reason after)) :
    run focus drop before replacement (.unwound reason (focus.set after replacement)) ∧
      focus.get (focus.set after replacement) = replacement :=
  ⟨⟨.unwound reason after, called, rfl⟩, focus.get_set after replacement⟩

/-- A terminal destructor outcome supplies no fabricated replacement state. -/
theorem terminated (focus : Owned.Focus State Payload)
    (drop : Callback.Run State Payload Unit Unwind Terminal)
    {before : State} {replacement : Payload} {reason : Terminal}
    (called : drop before (focus.get before) (.terminated reason)) :
    run focus drop before replacement (.terminated reason) :=
  ⟨.terminated reason, called, rfl⟩

end Solanalib.Specs.Core.AnchorViewsAssignment
