/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewFacts
public import Solanalib.Specs.Core.AccountViewRevision

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

/-- Successful close changes only the specified header fields of the selected account. -/
theorem close_account {state : State} {handle : Handle} (present : state.HasAccount handle)
    (revision : Revision) (free : isBorrowed state handle = false) :
    (close revision state handle).2.account handle = (state.account handle).close revision := by
  obtain ⟨cell, present⟩ := present
  simp only [close, free, Bool.false_eq_true, ↓reduceIte]
  rw [State.account_of_lookup (modify_lookup present _), State.account_of_lookup present]

/-- Any previously valid owner reference to a successfully closed account is
invalidated even though the separate data lease was free. -/
theorem owner_invalidated_by_close {state : State} {handle : Handle} {reference : OwnerRef}
    (alias : reference.account = handle)
    (valid : reference.Valid state) (revision : Revision)
    (free : isBorrowed state handle = false) :
    ¬ reference.Valid (close revision state handle).2 := by
  intro later
  have old := valid.2
  have next := later.2
  have present : state.HasAccount handle := by simpa only [alias] using valid.1
  rw [alias] at old next
  rw [close_account present revision free] at next
  change (state.account handle).ownerEpoch + 1 = reference.epoch at next
  omega


end Solanalib.Specs.Core.AccountView
