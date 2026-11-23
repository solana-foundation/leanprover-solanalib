/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleExit

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AnchorLifecycle

open AnchorAccount (World)

/-- Replacing bytes through the held mutable slice preserves its guard and
the mutable serializer footprint exactly when its source slice length stays
fixed. The actual cell and every other cell policy are retained. -/
theorem mutable_write_frame {before : AccountInfo.State} {guard : Borrow.Guard}
    {slot : Borrow.Slot AccountInfo.View} {old bytes : Solanalib.Runtime.Bytes} {policy :
      Borrow.Policy}
    (valid : before.Valid) (live : before.resolve guard = some slot)
    (exclusive : slot.mode = .exclusive)
    (current : before.lookupCell slot.cell = some ⟨.data old, policy⟩)
    (length : bytes.length = old.length) :
    Borrow.CallbackFrame mutableDataFootprint before
      (Borrow.write before guard (.data bytes)).2 guard := by
  simp only [Borrow.write, live, exclusive, ↓reduceIte]
  apply Borrow.CallbackFrame.of_slots
    (Borrow.replaceCell_valid valid _ _) (Borrow.replaceCell_slots _ _ _)
    (fun handle => Borrow.replaceCell_policy _ _ handle _)
  intro selected first last held foundFirst foundLast
  rw [live] at held
  cases held
  rw [current] at foundFirst
  cases foundFirst
  rw [Borrow.replaceCell_lookup current] at foundLast
  cases foundLast
  simpa only [mutableDataFootprint, exclusive] using length

/-- The selected typed data cell supplies the actual writer input on a
successful mutable borrow, including its original whole-slice length. -/
theorem SerializeReady.callback_input {types : ExitTypes} {before : World types.Aux}
    {account : AnchorAccount.Account types.Payload} {profile : AccountInfo.Profile}
    (ready : SerializeReady types before account profile)
    {guard : Borrow.Guard} {during : AccountInfo.State}
    (acquired : AccountInfo.tryBorrowMutData before.1 ⟨profile, account.info⟩ = (.ok guard,
      during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) :=
  AccountInfo.GuardCallback.data_current ready.1 acquired

/-- A real owner and nonclosed prefix selects the precise serializer
admission. A locally owned AccountInfo is followed through its actual clone
return, so no pre-clone state is substituted for the reached state. -/
theorem exitExpected_ready {cloneLocal : Bool} {types : ExitTypes}
    {before checked : World types.Aux} {account : AnchorAccount.Account types.Payload}
    {profile : AccountInfo.Profile} {programId expected : Solanalib.Runtime.Pubkey}
    (ready : ExitExpectedReady cloneLocal types before account profile programId expected)
    (equal : expected = programId)
    (openAccount : isClosed (Unwind := types.Unwind) (Terminal := types.Terminal) types.ownerAt
      before ⟨profile, account.info⟩ (.returned false checked)) :
    SerializeScopedReady cloneLocal types checked account profile :=
  (ready equal).2 checked openAccount

end Solanalib.Specs.Core.AnchorLifecycle
