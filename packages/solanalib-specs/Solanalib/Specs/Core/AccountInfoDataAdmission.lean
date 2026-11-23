/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoGuardCallback

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountInfo.DataBorrow

/-- Admission for a source-local data read after checked acquisition. Borrow
errors need no data read; a successful acquisition must expose current data.
No unrelated cell, target-width or whole-store invariant is required. -/
def Ready (mode : Borrow.Mode) (before : State) (handle : Borrow.Handle) : Prop :=
  match tryBorrow mode handle before with
  | (.error _, _) => True
  | (.ok guard, during) =>
    match Borrow.current during guard with
    | .ok (_, .data _) => True
    | .error _ | .ok (_, .lamports _) => False

/-- Every reached successful acquisition in the admitted domain supplies its
actual whole-data read. The source-local continuation cannot disappear for a
missing cell, consumed token or wrong content kind at this point. -/
theorem ready_current {mode : Borrow.Mode} {before during : State}
    {handle : Borrow.Handle} {guard : Borrow.Guard}
    (ready : Ready mode before handle)
    (acquired : tryBorrow mode handle before = (.ok guard, during)) :
    ∃ bytes, Borrow.current during guard = .ok (.whole, .data bytes) := by
  have live := GuardCallback.tryBorrow_live acquired
  cases present : during.lookupCell handle with
  | none => simp [Ready, acquired, Borrow.current, live, present] at ready
  | some cell =>
    cases cell with
    | mk value policy =>
      cases value with
      | lamports value => simp [Ready, acquired, Borrow.current, live, present] at ready
      | data bytes => exact ⟨bytes, by simp [Borrow.current, live, present]⟩

/-- Presence of the selected data cell is a sufficient reusable input
condition. Actual borrow conflicts and saturation still follow the raw path. -/
theorem ready_of_data {mode : Borrow.Mode} {before : State} {handle : Borrow.Handle}
    {bytes : _root_.Solanalib.Runtime.Bytes} {policy : Borrow.Policy}
    (typed : before.lookupCell handle = some ⟨.data bytes, policy⟩) :
    Ready mode before handle := by
  cases acquired : tryBorrow mode handle before with
  | mk result during =>
    cases result with
    | error failure => simp [Ready, acquired]
    | ok guard =>
      have current := Borrow.acquire_current (GuardCallback.tryBorrow_acquire acquired) typed
      simp [Ready, acquired, current]

end Solanalib.Specs.Core.AccountInfo.DataBorrow
