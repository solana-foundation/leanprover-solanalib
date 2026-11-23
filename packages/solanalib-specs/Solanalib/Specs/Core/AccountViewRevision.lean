/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountView
public import Solanalib.Specs.Core.AccountViewRevisionData

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

/-- A checked close fails on any data lease. Success zeros the header fields,
leaves backing data untouched and performs only the update of the selected revision. -/
def close (revision : Revision) (state : State) (handle : Handle) :
    Except Error Unit × State :=
  if isBorrowed state handle then (.error .accountBorrowFailed, state)
  else (.ok (), (Borrow.modifyCell state handle (Account.close revision)).2)

/-- V1 resize preserves the failure precedence of the source and does not acquire a
guard: borrow conflict, signed conversion, unchanged length, then growth limit. -/
def resize (state : State) (args : Handle × Nat) : Except Error Unit × State :=
  let account := state.account args.1
  if isBorrowed state args.1 then (.error .accountBorrowFailed, state)
  else if I32_MAX < args.2 then (.error .invalidRealloc, state)
  else if args.2 = account.dataLen then (.ok (), state)
  else if (Solanalib.Runtime.MAX_PERMITTED_DATA_INCREASE : Int) <
      account.resizeDelta + ((args.2 : Int) - account.dataLen) then
    (.error .invalidRealloc, state)
  else (.ok (), (Borrow.modifyCell state args.1 (fun value => value.resize args.2)).2)

/-- The signed 32-bit range of the v1 header arithmetic. -/
abbrev InI32 (value : Int) : Prop := -((I32_MAX : Int) + 1) ≤ value ∧ value ≤ I32_MAX

/-- The `i32` arithmetic of the source of v1 resize is defined on this input. Where
resize reaches it (a free lease and a converted length), `data_len as i32` is
exact and, for a changed length, `resize_delta + (new_len - data_len)` fits
`i32`. Elsewhere the source conversion wraps or its addition overflows, which
panics with overflow checks; the returning model describes neither. A
loader-created header satisfies this (`resizeArithmetic_of_resizeValid`). -/
def ResizeArithmetic (state : State) (args : Handle × Nat) : Prop :=
  isBorrowed state args.1 = false → args.2 ≤ I32_MAX →
    (state.account args.1).dataLen ≤ I32_MAX ∧
      (args.2 ≠ (state.account args.1).dataLen →
        InI32 ((state.account args.1).resizeDelta +
          ((args.2 : Int) - (state.account args.1).dataLen)))

/-- The `i32` update of the source of v1 close is defined on this input. Where v1
close reaches it (a free lease), `data_len as i32` is exact and
`resize_delta - data_len` fits `i32`. V2 close performs no such update. -/
def CloseArithmetic (revision : Revision) (state : State) (handle : Handle) : Prop :=
  revision = .v1 → isBorrowed state handle = false →
    (state.account handle).dataLen ≤ I32_MAX ∧
      InI32 ((state.account handle).resizeDelta - (state.account handle).dataLen)

instance (state : State) (args : Handle × Nat) : Decidable (ResizeArithmetic state args) := by
  unfold ResizeArithmetic; infer_instance

instance (revision : Revision) (state : State) (handle : Handle) :
    Decidable (CloseArithmetic revision state handle) := by
  unfold CloseArithmetic; infer_instance

/-- On an existing account whose v1 signed update is defined, close preserves
backing bytes and rejects live data leases. -/
def close_contract (revision : Revision) :
    Solanalib.Contracts.Model State Handle (Except Error Unit) :=
  .returning (fun state handle => state.HasAccount handle ∧ CloseArithmetic revision state handle)
    (fun before handle result after =>
      if isBorrowed before handle then
        result = .error .accountBorrowFailed ∧ after = before
      else result = .ok () ∧
        Borrow.modifyCell before handle (Account.close revision) = (.ok (), after))

/-- On an existing account whose signed arithmetic is defined, resize preserves
the check order of the source and signed growth bound. Representation preservation
needs the separate lifecycle premises. -/
def resize_contract : Solanalib.Contracts.Model State (Handle × Nat) (Except Error Unit) :=
  .returning (fun state args => state.HasAccount args.1 ∧ ResizeArithmetic state args)
    (fun before args result after =>
      let account := before.account args.1
      if isBorrowed before args.1 then
        result = .error .accountBorrowFailed ∧ after = before
      else if I32_MAX < args.2 then
        result = .error .invalidRealloc ∧ after = before
      else if args.2 = account.dataLen then result = .ok () ∧ after = before
      else if (Solanalib.Runtime.MAX_PERMITTED_DATA_INCREASE : Int) <
          account.resizeDelta + ((args.2 : Int) - account.dataLen) then
        result = .error .invalidRealloc ∧ after = before
      else result = .ok () ∧
        Borrow.modifyCell before args.1 (fun value => value.resize args.2) = (.ok (), after))

theorem close_reference (revision : Revision) :
    (close_contract revision).RealizedBy (close revision) := by
  intro before handle ready
  have update := modify_success ready.1 (Account.close revision)
  by_cases borrowed : isBorrowed before handle = true
  · simp [close_contract, close, borrowed]
  · simp only [close_contract, Solanalib.Contracts.Model.ensures,
      Solanalib.Contracts.Model.returning, close, borrowed]
    exact ⟨rfl, update⟩

theorem resize_reference : resize_contract.RealizedBy resize := by
  intro before args ready
  have update := modify_success ready.1 (fun value => value.resize args.2)
  simp only [resize_contract, Solanalib.Contracts.Model.ensures,
    Solanalib.Contracts.Model.returning, resize]
  by_cases borrowed : isBorrowed before args.1 = true
  · simp only [borrowed]
    exact ⟨by trivial, rfl⟩
  · simp only [borrowed]
    by_cases tooLarge : I32_MAX < args.2
    · simp only [tooLarge]
      exact ⟨rfl, rfl⟩
    · simp only [tooLarge]
      by_cases unchanged : args.2 = (before.account args.1).dataLen
      · simp only [unchanged]
        exact ⟨rfl, rfl⟩
      · simp only [unchanged]
        by_cases growth : (Solanalib.Runtime.MAX_PERMITTED_DATA_INCREASE : Int) <
            (before.account args.1).resizeDelta +
              ((args.2 : Int) - (before.account args.1).dataLen)
        · simp only [growth]
          exact ⟨rfl, rfl⟩
        · simp only [growth]
          exact ⟨rfl, update⟩

/-- A loader-consistent v1 header (`ResizeValid`) has defined resize arithmetic. -/
theorem resizeArithmetic_of_resizeValid {state : State} {handle : Handle}
    (valid : (state.account handle).ResizeValid) (newLength : Nat) :
    ResizeArithmetic state (handle, newLength) := by
  intro _ converted
  obtain ⟨_, dataBound, entryBound, counter⟩ := valid
  have limit : I32_MAX = 2147483647 := rfl
  refine ⟨dataBound, fun _ => ?_⟩
  change -((I32_MAX : Int) + 1) ≤ _ ∧ _ ≤ (I32_MAX : Int)
  rw [counter]
  simp only [limit] at dataBound entryBound converted ⊢
  omega

/-- A loader-consistent v1 header (`ResizeValid`) has a defined close update. -/
theorem closeArithmetic_of_resizeValid {state : State} {handle : Handle}
    (valid : (state.account handle).ResizeValid) (revision : Revision) :
    CloseArithmetic revision state handle := by
  intro _ _
  obtain ⟨_, dataBound, entryBound, counter⟩ := valid
  have limit : I32_MAX = 2147483647 := rfl
  refine ⟨dataBound, ?_⟩
  change -((I32_MAX : Int) + 1) ≤ _ ∧ _ ≤ (I32_MAX : Int)
  rw [counter]
  simp only [limit] at dataBound entryBound ⊢
  omega

/-- The existing versioned operation agrees exactly with header-only close. -/
theorem close_v2_eq_closeHeader (state : State) (handle : Handle) :
    close .v2 state handle = closeHeader state handle := rfl

end Solanalib.Specs.Core.AccountView
