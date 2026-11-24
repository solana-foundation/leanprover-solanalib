/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewProjection

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

/-- Acquisition preserves the representation of every account on both success and
failure; leases remain in the single identified registry. -/
theorem acquire_wellFormed {state : State} (valid : state.WellFormed)
    (handle : Handle) (mode : Mode) : (acquire state handle mode).2.WellFormed :=
  valid.sameCells
    (Borrow.acquire_valid valid.1 handle mode (state.account handle).whole)
    (Borrow.acquire_cells state handle mode (state.account handle).whole)

/-- A local handle remains usable after any checked acquisition. -/
theorem acquire_ready {state : State} {handle : Handle}
    (ready : Ready state handle) (mode : Mode) : Ready (acquire state handle mode).2 handle := by
  refine ⟨acquire_wellFormed ready.1 handle mode, ?_⟩
  obtain ⟨cell, present⟩ := ready.2
  refine ⟨cell, ?_⟩
  simpa [acquire, Borrow.State.lookupCell, Borrow.acquire_cells] using present

/-- A valid direct modification retains the selected handle and pool invariant. -/
theorem modify_ready {state : State} {handle : Handle} (ready : Ready state handle)
    (update : Account → Account) (valid : (update (state.account handle)).Valid) :
    Ready (Borrow.modifyCell state handle update).2 handle := by
  refine ⟨modify_wellFormed ready update valid, ?_⟩
  obtain ⟨cell, present⟩ := ready.2
  exact ⟨_, modify_lookup present update⟩

/-- Bounded balance replacement is composable with subsequent account operations. -/
theorem setLamports_ready {state : State} {handle : Handle} (ready : Ready state handle)
    {value : Nat} (bound : value < Solanalib.Runtime.U64_LIMIT) :
    Ready (setLamports state (handle, value)).2 handle :=
  modify_ready ready _ (Account.setLamports_valid ready.account_valid.2 bound)

/-- Release keeps every current account and allows later use of existing aliases. -/
theorem release_ready {state : State} {handle : Handle} (ready : Ready state handle)
    (guard : Guard) : Ready (Borrow.release state guard).2 handle := by
  refine ⟨ready.1.release guard, ?_⟩
  obtain ⟨cell, present⟩ := ready.2
  exact ⟨cell, by simpa [Borrow.State.lookupCell, Borrow.release_cells] using present⟩

/-- A same-size write through a valid mutable reference preserves the pool and
the current range of the reference. No destructor or copy-back is needed to commit it. -/
theorem writeReference_guardReady {state : State} {guard : Guard}
    (ready : GuardReady state .exclusive guard) {bytes : Solanalib.Runtime.Bytes}
    (length : ∀ slot, state.resolve guard = some slot → bytes.length = slot.view.length) :
    GuardReady (writeReference state ⟨guard, true⟩ bytes).2 .exclusive guard := by
  obtain ⟨wellFormed, slot, cell, live, present, exclusive, inside⟩ := ready
  have valid := (wellFormed.lookup present).2
  have written := Account.write_valid valid inside (length slot live)
  have preserved := wellFormed.replace slot.cell written
  have slots := Borrow.replaceCell_slots state slot.cell (cell.value.write slot.view bytes)
  have stillLive : (Borrow.replaceCell state slot.cell (cell.value.write slot.view bytes)).2.resolve
      guard = some slot := by
    simpa [Borrow.State.resolve, Borrow.State.lookupSlot, slots] using live
  simp only [writeReference, live, present, ↓reduceIte, Borrow.write, exclusive]
  exact ⟨preserved, slot, _, stillLive, Borrow.replaceCell_lookup present _, exclusive, inside⟩

/-- Success and lease failure of header-only close retain the account domain. -/
theorem closeHeader_ready {state : State} {handle : Handle} (ready : Ready state handle) :
    Ready (closeHeader state handle).2 handle := by
  unfold closeHeader
  split
  · exact ready
  · exact modify_ready ready _ (Account.closeHeader_valid ready.account_valid.2.2.1)

end Solanalib.Specs.Core.AccountView
