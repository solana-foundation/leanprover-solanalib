/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.OpaqueCpiSdk

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.OpaqueCpi.Sdk

/-- Releasing the just-issued temporary guard leaves only a tombstone. -/
theorem release_issue (before : BorrowState) (handle : Borrow.Handle) (mode : Borrow.Mode) :
    Borrow.release (before.issue handle mode ()).2 (before.issue handle mode ()).1 =
      (.ok (), { before with slots := before.slots ++ [none] }) := by
  rw [Borrow.release_live (Borrow.State.issue_resolves before handle mode ())]
  simp [Borrow.State.issue]

/-- A temporary preflight probe either fails without changing the lease world
or adds exactly one retired identity; it never leaves a live temporary guard. -/
theorem probe_shape (before : BorrowState) (handle : Borrow.Handle) (mode : Borrow.Mode) :
    probe mode handle before = (false, before) ∨
      probe mode handle before = (true, { before with slots := before.slots ++ [none] }) := by
  cases found : before.lookupCell handle with
  | none => exact Or.inl (by simp [probe, Borrow.acquire, found])
  | some cell =>
    cases mode with
    | shared =>
      by_cases busy : before.exclusiveCount handle ≠ 0
      · exact Or.inl (by simp [probe, Borrow.acquire, found, busy])
      · by_cases full : cell.policy.sharedLimit ≤ before.sharedCount handle
        · exact Or.inl (by simp [probe, Borrow.acquire, found, busy, full])
        · right
          simp only [probe, Borrow.acquire, found, busy, full, ↓reduceIte]
          rw [release_issue]
          rfl
    | exclusive =>
      by_cases busy : before.exclusiveCount handle ≠ 0 ∨ before.sharedCount handle ≠ 0
      · exact Or.inl (by simp [probe, Borrow.acquire, found, busy])
      · right
        simp only [probe, Borrow.acquire, found, busy, ↓reduceIte]
        rw [release_issue]
        rfl

/-- The source-observable cells and live lease counts agree. Retired logical
identities may differ without changing a physical RefCell borrow counter. -/
def SameCounters (before after : BorrowState) : Prop :=
  before.cells = after.cells ∧ ∀ handle mode, before.count handle mode = after.count handle mode

theorem SameCounters.refl (before : BorrowState) : SameCounters before before :=
  ⟨rfl, fun _ _ => rfl⟩

theorem SameCounters.trans {before middle after : BorrowState}
    (first : SameCounters before middle) (second : SameCounters middle after) :
    SameCounters before after :=
  ⟨first.1.trans second.1, fun handle mode => (first.2 handle mode).trans (second.2 handle mode)⟩

theorem probe_counters (before : BorrowState) (handle : Borrow.Handle) (mode : Borrow.Mode) :
    SameCounters before (probe mode handle before).2 := by
  rcases probe_shape before handle mode with failed | checked
  · rw [failed]; exact .refl _
  · rw [checked]
    exact ⟨rfl, fun _ _ => by simp [Borrow.State.count]⟩

theorem probeAccount_counters (before : BorrowState) (account : Account) (writable : Bool) :
    SameCounters before (probeAccount writable account before).2 := by
  unfold probeAccount
  generalize (if writable then Borrow.Mode.exclusive else Borrow.Mode.shared) = mode
  dsimp only
  split
  · exact (probe_counters before account.lamports _).trans (probe_counters _ account.data _)
  · exact probe_counters before account.lamports _

/-- Both successful and failed local preflights restore every physical borrow
counter. This supports retaining the actual source RefCell words in an adapter. -/
theorem preflight_counters (accounts : List Account) (before : BorrowState)
    (metas : List Solanalib.Runtime.CpiMeta) :
    SameCounters before (preflight accounts before metas).2 := by
  induction metas generalizing before with
  | nil => exact .refl _
  | cons item metas ih =>
    unfold preflight
    split
    · exact ih _
    · dsimp only
      split
      · exact (probeAccount_counters before _ _).trans (ih _)
      · exact probeAccount_counters before _ _

end Solanalib.Specs.Core.OpaqueCpi.Sdk
