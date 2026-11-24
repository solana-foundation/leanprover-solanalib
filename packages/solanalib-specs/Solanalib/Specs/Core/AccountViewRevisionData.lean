/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountViewData

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.Core.AccountView

/-- The two source profiles. The first tracks signed resizing in its account
header. The second has no resize method or observable resize counter. -/
inductive Revision where
  /-- AccountView 1.0.0, with a signed resize counter. -/
  | v1
  /-- AccountView 2.0.0, with no exposed resize counter or resize method. -/
  | v2
  deriving DecidableEq, Repr

/-- The maximum signed length accepted by the v1 checked conversion. -/
def I32_MAX : Nat := 2^31 - 1

/-- The v1 counter agrees with growth since entry; source integer arithmetic is
represented by mathematical integers on this explicitly bounded domain. -/
def Account.ResizeValid (account : Account) : Prop :=
  account.Valid ∧ account.dataLen ≤ I32_MAX ∧ account.entryLen ≤ I32_MAX ∧
    account.resizeDelta = (account.dataLen : Int) - account.entryLen

/-- Closing changes the header, invalidates owner references and keeps the
physical data bytes. Only v1 updates the signed resize counter. -/
def Account.close (revision : Revision) (account : Account) : Account :=
  { account.closeHeader with
    resizeDelta := match revision with
      | .v1 => account.resizeDelta - account.dataLen
      | .v2 => account.resizeDelta }

/-- The successful v1 resize: truncation preserves backing bytes, while growth
zeroes exactly the newly exposed range. Lease checks are supplied by the caller. -/
def Account.resize (account : Account) (newLength : Nat) : Account :=
  { account with
    dataLen := newLength
    resizeDelta := account.resizeDelta + ((newLength : Int) - account.dataLen)
    backing := if account.dataLen < newLength then
      Solanalib.Runtime.writeAt account.backing account.dataLen
        (List.replicate (newLength - account.dataLen) 0)
      else account.backing }

/-- A successful close leaves every allocated data byte untouched. -/
theorem Account.close_backing (revision : Revision) (account : Account) :
    (account.close revision).backing = account.backing := rfl

/-- A successful close exposes empty logical data even when backing bytes remain. -/
theorem Account.close_bytes (revision : Revision) (account : Account) :
    (account.close revision).bytes = [] := by
  simp [close, closeHeader, bytes]

/-- Shrinking does not erase the bytes beyond the new logical end. -/
theorem Account.resize_shrink_backing {account : Account} {newLength : Nat}
    (shrinks : newLength ≤ account.dataLen) :
    (account.resize newLength).backing = account.backing := by
  simp [resize, Nat.not_lt.mpr shrinks]

/-- A counter recording growth from entry keeps that relation after resize. -/
theorem Account.resize_delta {account : Account}
    (counter : account.resizeDelta = (account.dataLen : Int) - account.entryLen)
    (newLength : Nat) :
    (account.resize newLength).resizeDelta = (newLength : Int) - account.entryLen := by
  simp only [resize, counter]
  omega

/-- Closing preserves the finite header/data representation without erasing
the allocated bytes or imposing a runtime balance-conservation condition. -/
theorem Account.close_valid {account : Account} (entry : account.entryLen <
  Solanalib.Runtime.U64_LIMIT)
    (revision : Revision) : (account.close revision).Valid :=
  ⟨by change 0 < Solanalib.Runtime.U64_LIMIT; decide,
    by change 0 < Solanalib.Runtime.U64_LIMIT; decide, entry, Nat.zero_le _⟩

/-- V1 close leaves its signed counter at negative entry length. -/
theorem Account.close_resize_valid {account : Account} (entry : account.entryLen ≤ I32_MAX)
    (counter : account.resizeDelta = (account.dataLen : Int) - account.entryLen) :
    (account.close .v1).ResizeValid := by
  refine ⟨account.close_valid (Nat.lt_of_le_of_lt entry (by decide)) _, Nat.zero_le _, entry, ?_⟩
  simp only [close, closeHeader, counter]
  omega

/-- Successful in-capacity resizing never changes allocated backing length. -/
theorem Account.resize_backing_length {account : Account}
    {newLength : Nat} (capacity : newLength ≤ account.backing.length) :
    (account.resize newLength).backing.length = account.backing.length := by
  by_cases growth : account.dataLen < newLength
  · have bound : account.dataLen +
        (List.replicate (newLength - account.dataLen) (0 : UInt8)).length ≤
        account.backing.length := by simp only [List.length_replicate]; omega
    simpa only [resize, growth, ite_true] using Solanalib.Runtime.length_writeAt bound
  · simp [resize, growth]

/-- The mathematical write can extend backing, so represented initial data
always leaves the new logical range inside the resulting backing. -/
theorem Account.resize_data_fits {account : Account}
    (inside : account.dataLen ≤ account.backing.length) (newLength : Nat) :
    newLength ≤ (account.resize newLength).backing.length := by
  by_cases growth : account.dataLen < newLength
  · simp only [resize, growth, ite_true, Solanalib.Runtime.writeAt, List.length_append,
      List.length_take, List.length_replicate, List.length_drop]
    omega
  · simpa only [resize, growth, ite_false] using
      Nat.le_trans (Nat.le_of_not_gt growth) inside

/-- The successful signed-length branch preserves every v1 representation
condition, including the relation of the counter to the invocation entry length. -/
theorem Account.resize_valid {account : Account}
    (balance : account.lamports < Solanalib.Runtime.U64_LIMIT) (entry : account.entryLen ≤ I32_MAX)
    (inside : account.dataLen ≤ account.backing.length)
    (counter : account.resizeDelta = (account.dataLen : Int) - account.entryLen)
    {newLength : Nat} (signed : newLength ≤ I32_MAX) :
    (account.resize newLength).ResizeValid := by
  refine ⟨⟨balance, ?_, Nat.lt_of_le_of_lt entry (by decide), account.resize_data_fits inside _⟩,
    signed, entry, account.resize_delta counter newLength⟩
  · change newLength < Solanalib.Runtime.U64_LIMIT
    have limits : I32_MAX < Solanalib.Runtime.U64_LIMIT := by decide
    omega

/-- The logical-byte effect is the canonical zero-extending resize, despite
the separate physical backing and free-lease calling convention of the SDK. -/
theorem Account.resize_bytes {account : Account}
    (inside : account.dataLen ≤ account.backing.length)
    (newLength : Nat) :
    (account.resize newLength).bytes = Solanalib.Runtime.resizeZero account.bytes newLength := by
  have length : account.bytes.length = account.dataLen := by
    simp only [bytes, List.length_take, Nat.min_eq_left inside]
  by_cases growth : account.dataLen < newLength
  · have prefixLength : (account.backing.take account.dataLen ++
        List.replicate (newLength - account.dataLen) (0 : UInt8)).length = newLength := by
      simp only [List.length_append, List.length_take, List.length_replicate]
      omega
    simp only [resize, growth, ite_true, bytes, Solanalib.Runtime.writeAt]
    rw [List.take_left' prefixLength]
    change account.bytes ++ _ = Solanalib.Runtime.resizeZero account.bytes newLength
    rw [Solanalib.Runtime.resizeZero, List.take_of_length_le (by rw [length]; omega), length]
  · have shrinks : newLength ≤ account.dataLen := by omega
    simp [resize, growth, bytes, Solanalib.Runtime.resizeZero, List.take_take,
      Nat.min_eq_left shrinks, List.length_take, Nat.min_eq_left inside,
      Nat.sub_eq_zero_of_le shrinks]

/-- Every integer intermediate used by the v1 source update fits signed i32 on
the explicit representation domain; the model does not silently wrap overflow. -/
theorem Account.resize_arithmetic_bounds {account : Account}
    (current : account.dataLen ≤ I32_MAX) (entry : account.entryLen ≤ I32_MAX)
    (counter : account.resizeDelta = (account.dataLen : Int) - account.entryLen)
    {newLength : Nat} (signed : newLength ≤ I32_MAX) :
    -(I32_MAX : Int) ≤ (newLength : Int) - account.dataLen ∧
    (newLength : Int) - account.dataLen ≤ I32_MAX ∧
    -(I32_MAX : Int) ≤ account.resizeDelta + ((newLength : Int) - account.dataLen) ∧
    account.resizeDelta + ((newLength : Int) - account.dataLen) ≤ I32_MAX := by
  rw [counter]
  omega

/-- The versioned wrapper has exactly the former direct header update. This
equation checks the factoring for both supported source revisions. -/
theorem Account.close_factoring (revision : Revision) (account : Account) :
    account.close revision =
      { account with
        owner := .zero
        lamports := 0
        dataLen := 0
        resizeDelta := match revision with
          | .v1 => account.resizeDelta - account.dataLen
          | .v2 => account.resizeDelta
        ownerEpoch := account.ownerEpoch + 1 } := rfl

/-- The non-resizing revision is exactly the shared header-only operation. -/
theorem Account.close_v2_eq_closeHeader (account : Account) :
    account.close .v2 = account.closeHeader := rfl

end Solanalib.Specs.Core.AccountView
