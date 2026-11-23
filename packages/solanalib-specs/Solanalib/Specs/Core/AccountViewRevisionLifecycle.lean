/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewLifecycle
public import Solanalib.Specs.Core.AccountViewRevisionFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

/-- Success and borrow failure of close both retain the ordinary account domain. -/
theorem close_ready {state : State} {handle : Handle} (ready : Ready state handle)
    (revision : Revision) : Ready (close revision state handle).2 handle := by
  unfold close
  split
  · exact ready
  · exact modify_ready ready _ (Account.close_valid ready.account_valid.2.2.1 revision)

/-- Closing v1 retains the signed resize invariant, including negative growth
after the logical length becomes zero. -/
theorem close_v1_resize_valid {state : State} {handle : Handle}
    (present : state.HasAccount handle) (valid : (state.account handle).ResizeValid) :
    ((close .v1 state handle).2.account handle).ResizeValid := by
  by_cases busy : isBorrowed state handle = true
  · simpa [close, busy] using valid
  · have free : isBorrowed state handle = false := by simpa using busy
    rw [close_account present .v1 free]
    exact Account.close_resize_valid valid.2.2.1 valid.2.2.2

/-- Each v1 resize branch retains the complete account domain. Mathematical
backing may grow; this result does not assert a fixed physical allocation. -/
theorem resize_ready {state : State} {args : Handle × Nat} (ready : Ready state args.1) :
    Ready (resize state args).2 args.1 := by
  simp only [resize]
  split
  · exact ready
  · split
    · exact ready
    · rename_i signed
      split
      · exact ready
      · split
        · exact ready
        · have signedBound : args.2 ≤ I32_MAX := by omega
          have valid := ready.account_valid
          have contents : ((state.account args.1).resize args.2).Valid :=
            ⟨valid.1, Nat.lt_of_le_of_lt signedBound (by decide), valid.2.2.1,
              Account.resize_data_fits valid.2.2.2 args.2⟩
          exact modify_ready ready _ contents

/-- The v1 signed counter remains available for a following resize or close. -/
theorem resize_preserves_signed_domain {state : State} {args : Handle × Nat}
    (present : state.HasAccount args.1) (valid : (state.account args.1).ResizeValid) :
    ((resize state args).2.account args.1).ResizeValid := by
  simp only [resize]
  split
  · exact valid
  · split
    · exact valid
    · rename_i signed
      split
      · exact valid
      · split
        · exact valid
        · have signedBound : args.2 ≤ I32_MAX := by omega
          obtain ⟨cell, present⟩ := present
          rw [State.account_of_lookup (modify_lookup present _)]
          have original := valid
          rw [State.account_of_lookup present] at original
          exact Account.resize_valid original.1.1 original.2.2.1 original.1.2.2.2
            original.2.2.2 signedBound


end Solanalib.Specs.Core.AccountView
