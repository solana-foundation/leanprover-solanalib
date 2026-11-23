/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoSdk
public import Solanalib.Specs.Core.BorrowContentProjection
public import Solanalib.Specs.Core.OpaqueCpiBorrowFacts

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.OpaqueCpi.Sdk.AccountState

/-- CPI observes leases in the same AccountInfo world. It does not retain a
second snapshot of lamports, data, owner storage or the typed target of a guard. -/
def erase (state : AccountInfo.State) : BorrowState :=
  (state.mapContent fun _ => ()).mapView fun _ => ()

theorem erase_count (state : AccountInfo.State) (handle : Borrow.Handle) (mode : Borrow.Mode) :
    (erase state).count handle mode = state.count handle mode :=
  (state.mapContent fun _ => ()).mapView_count (fun _ => ()) handle mode

theorem erase_valid (state : AccountInfo.State) : (erase state).Valid ↔ state.Valid :=
  ((state.mapContent fun _ => ()).mapView_valid (fun _ => ())).trans
    (state.mapContent_valid (fun _ => ()))

theorem erase_acquire (state : AccountInfo.State) (handle : Borrow.Handle) (mode : Borrow.Mode) :
    Borrow.acquire (erase state) handle mode () =
      ((Borrow.acquire state handle mode .whole).1,
        erase (Borrow.acquire state handle mode .whole).2) := by
  unfold erase
  rw [show () = (fun _ : AccountInfo.View => ()) .whole from rfl]
  rw [Borrow.State.mapView_acquire, Borrow.State.mapContent_acquire]

theorem erase_release (state : AccountInfo.State) (guard : Borrow.Guard) :
    Borrow.release (erase state) guard =
      ((Borrow.release state guard).1, erase (Borrow.release state guard).2) := by
  unfold erase
  rw [Borrow.State.mapView_release, Borrow.State.mapContent_release]

/-- A source temporary uses the native whole-cell view and retires the exact
issued guard. Successful checks leave its tombstone in the existing world. -/
def probe (mode : Borrow.Mode) (handle : Borrow.Handle) (state : AccountInfo.State) :
    Bool × AccountInfo.State :=
  let (result, during) := Borrow.acquire state handle mode .whole
  match result with
  | .error _ => (false, during)
  | .ok guard =>
    let (result, after) := Borrow.release during guard
    (result.isOk, after)

theorem erase_probe (state : AccountInfo.State) (handle : Borrow.Handle) (mode : Borrow.Mode) :
    Sdk.probe mode handle (erase state) =
      ((probe mode handle state).1, erase (probe mode handle state).2) := by
  simp only [Sdk.probe, probe, erase_acquire]
  cases Borrow.acquire state handle mode .whole with
  | mk result during =>
    cases result with
    | error error => rfl
    | ok guard => dsimp only; rw [erase_release]

def probeAccount (writable : Bool) (account : Account) (state : AccountInfo.State) :
    Bool × AccountInfo.State :=
  let mode := if writable then Borrow.Mode.exclusive else .shared
  let (result, during) := probe mode account.lamports state
  if result then probe mode account.data during else (false, during)

theorem erase_probeAccount (state : AccountInfo.State) (account : Account) (writable : Bool) :
    Sdk.probeAccount writable account (erase state) =
      ((probeAccount writable account state).1, erase (probeAccount writable account state).2) := by
  simp only [Sdk.probeAccount, probeAccount, erase_probe]
  cases probe (if writable then .exclusive else .shared) account.lamports state with
  | mk result during => cases result <;> simp only [Bool.false_eq_true, ↓reduceIte]

/-- The same instruction order, first matching AccountInfo, lamports-before-
data check and early error operate directly on the shared native ledger. -/
def preflight (accounts : List Account) :
    AccountInfo.State → List Solanalib.Runtime.CpiMeta → Bool × AccountInfo.State
  | before, [] => (true, before)
  | before, item :: metas =>
    match accounts.find? (fun account => account.info.key == item.key) with
    | none => preflight accounts before metas
    | some account =>
      let (result, after) := probeAccount (item.writableByte == 1) account before
      if result then preflight accounts after metas else (false, after)

theorem erase_preflight (accounts : List Account) (state : AccountInfo.State)
    (metas : List Solanalib.Runtime.CpiMeta) :
    Sdk.preflight accounts (erase state) metas =
      ((preflight accounts state metas).1, erase (preflight accounts state metas).2) := by
  induction metas generalizing state with
  | nil => rfl
  | cons item metas ih =>
    simp only [Sdk.preflight, preflight]
    cases accounts.find? (fun account => account.info.key == item.key) with
    | none => exact ih state
    | some account =>
      dsimp only
      rw [erase_probeAccount]
      cases probeAccount (item.writableByte == 1) account state with
      | mk result during =>
        cases result with
        | false => rfl
        | true => exact ih during

/-- Both normal preflight outcomes retain every native physical counter. -/
theorem preflight_count (accounts : List Account) (state : AccountInfo.State)
    (metas : List Solanalib.Runtime.CpiMeta) (handle : Borrow.Handle) (mode : Borrow.Mode) :
    state.count handle mode = (preflight accounts state metas).2.count handle mode := by
  have same := (Sdk.preflight_counters accounts (erase state) metas).2 handle mode
  simpa only [erase_preflight, erase_count] using same

theorem probe_cells (mode : Borrow.Mode) (handle : Borrow.Handle) (state : AccountInfo.State) :
    (probe mode handle state).2.cells = state.cells := by
  have cells := Borrow.acquire_cells state handle mode AccountInfo.View.whole
  unfold probe
  cases acquired : Borrow.acquire state handle mode AccountInfo.View.whole with
  | mk result during =>
    have unchanged : during.cells = state.cells := by simpa only [acquired] using cells
    cases result with
    | error error => exact unchanged
    | ok guard => exact (Borrow.release_cells during guard).trans unchanged

theorem probeAccount_cells (writable : Bool) (account : Account) (state : AccountInfo.State) :
    (probeAccount writable account state).2.cells = state.cells := by
  unfold probeAccount
  generalize (if writable then Borrow.Mode.exclusive else Borrow.Mode.shared) = mode
  dsimp only
  split
  · exact (probe_cells mode account.data _).trans (probe_cells mode account.lamports state)
  · exact probe_cells mode account.lamports state

theorem preflight_cells (accounts : List Account) (state : AccountInfo.State)
    (metas : List Solanalib.Runtime.CpiMeta) :
    (preflight accounts state metas).2.cells = state.cells := by
  induction metas generalizing state with
  | nil => rfl
  | cons item metas ih =>
    unfold preflight
    split
    · exact ih state
    · dsimp only
      split
      · exact (ih _).trans (probeAccount_cells _ _ state)
      · exact probeAccount_cells _ _ state

end Solanalib.Specs.Core.OpaqueCpi.Sdk.AccountState
