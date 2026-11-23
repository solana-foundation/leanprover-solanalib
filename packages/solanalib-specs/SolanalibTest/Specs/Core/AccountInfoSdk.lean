/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AccountInfoResize

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AccountInfoSdk

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AccountInfoSdk

def sharedLamports := (borrowLamports .shared AccountInfo.sampleState AccountInfo.sampleArgs).2
def mutableData := (AccountInfo.tryBorrowMutData sharedLamports AccountInfo.sampleArgs).2

theorem independent_cells_can_be_borrowed_together :
    Borrow.current mutableData ⟨0, 0⟩ = .ok (.whole, .lamports 40) ∧
    Borrow.current mutableData ⟨1, 0⟩ = .ok (.whole, .data [10, 20, 30]) := ⟨rfl, rfl⟩

theorem aliased_shared_lamports_block_exclusive :
    borrowLamports .exclusive sharedLamports
      { AccountInfo.sampleArgs with info := AccountInfo.clone AccountInfo.sampleInfo } =
      (.error .accountBorrowFailed, sharedLamports) := rfl

theorem mutable_borrow_ignores_metadata_flags :
    (borrowLamports .exclusive AccountInfo.sampleState AccountInfo.sampleArgs).1 = .ok ⟨0, 0⟩ ∧
      AccountInfo.sampleInfo.isWritable = false := ⟨rfl, rfl⟩

theorem checked_length_reports_error_without_panic :
    tryDataLen mutableData AccountInfo.sampleArgs = some (.error .accountBorrowFailed, mutableData)
      := rfl

theorem unchecked_empty_getter_unwinds_on_same_conflict :
    dataIsEmptyReference mutableData AccountInfo.sampleArgs (.unwound .borrowFailed mutableData) :=
      rfl

theorem unchecked_empty_getter_can_abort :
    dataIsEmptyReference mutableData
      { AccountInfo.sampleArgs with profile := ⟨64, true⟩ } (.terminated .borrowFailed) := rfl

theorem conflicting_empty_getter_cannot_return_false :
    ¬ dataIsEmptyReference mutableData AccountInfo.sampleArgs (.returned false mutableData) := by
  intro impossible
  cases impossible

theorem releasing_data_guard_restores_checked_getter :
    (tryDataLen (Borrow.release mutableData ⟨1, 0⟩).2 AccountInfo.sampleArgs).map
      (fun (value, _) => value) = some (.ok 3) := rfl

theorem temporary_getter_guard_is_released :
    (AccountInfo.observe .dataLen AccountInfo.sampleState AccountInfo.sampleInfo).2.slots = [none]
      := rfl

theorem self_reference_preserves_existing_world :
    asRef mutableData ⟨42⟩ = (⟨42⟩, mutableData) := rfl

def assigned := (assign { sample with borrow := mutableData }
  (AccountInfo.sampleInfo, ⟨List.replicate 32 7, by simp⟩)).2

theorem assignment_does_not_borrow_data_or_lamports : assigned.borrow = mutableData := rfl

theorem assignment_updates_alias_owner_storage :
    assigned.owner (AccountInfo.clone AccountInfo.sampleInfo).ownerRef =
      some ⟨List.replicate 32 7, by simp⟩ := rfl

def shrinkArgs : ResizeArgs := ⟨AccountInfo.sampleInfo, 1, false⟩
def shrunk : State := (resizeNormal sample shrinkArgs).getD (.error .invalidRealloc, sample) |>.2
def regrowArgs : ResizeArgs := ⟨AccountInfo.sampleInfo, 3, false⟩
def regrown : State := (resizeNormal shrunk regrowArgs).getD (.error .invalidRealloc, sample) |>.2
def zeroRegrown : State :=
  (resizeNormal shrunk { regrowArgs with zeroInit := true }).getD (.error .invalidRealloc, sample)
    |>.2

theorem shrinking_retains_hidden_bytes :
    shrunk.borrow.lookupCell AccountInfo.sampleInfo.data =
      some ⟨.data [10], AccountInfo.sampleProfile.policy⟩ ∧
    shrunk.buffer AccountInfo.sampleInfo.data = some ⟨3, 1, [20, 30, 40, 50, 60]⟩ := ⟨rfl, rfl⟩

theorem nonzeroing_regrowth_recovers_retained_bytes :
    regrown.borrow.lookupCell AccountInfo.sampleInfo.data =
      some ⟨.data [10, 20, 30], AccountInfo.sampleProfile.policy⟩ ∧
    regrown.buffer AccountInfo.sampleInfo.data = some ⟨3, 3, [40, 50, 60]⟩ := ⟨rfl, rfl⟩

theorem zeroing_regrowth_overwrites_only_exposed_bytes :
    zeroRegrown.borrow.lookupCell AccountInfo.sampleInfo.data =
      some ⟨.data [10, 0, 0], AccountInfo.sampleProfile.policy⟩ ∧
    zeroRegrown.buffer AccountInfo.sampleInfo.data = some ⟨3, 3, [40, 50, 60]⟩ := ⟨rfl, rfl⟩

theorem repeated_resize_preserves_original_length :
    (zeroRegrown.buffer AccountInfo.sampleInfo.data).map Buffer.originalLen = some 3 := rfl

theorem repeated_resize_leaves_no_live_guards :
    zeroRegrown.borrow.sharedCount AccountInfo.sampleInfo.data = 0 ∧
    zeroRegrown.borrow.exclusiveCount AccountInfo.sampleInfo.data = 0 ∧
    zeroRegrown.borrow.slots = [none, none] := ⟨rfl, rfl, rfl⟩

theorem zeroing_is_reached_after_shared_lengths_change :
    ∃ during, prepareResize shrunk { regrowArgs with zeroInit := true } = .zero ⟨1, 0⟩ 1 2 during ∧
      during.borrow.lookupCell AccountInfo.sampleInfo.data =
        some ⟨.data [10, 20, 30], AccountInfo.sampleProfile.policy⟩ ∧
      during.buffer AccountInfo.sampleInfo.data = some ⟨3, 3, [40, 50, 60]⟩ ∧
      during.borrow.exclusiveCount AccountInfo.sampleInfo.data = 1 := by
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem zeroing_terminal_exit_is_retained :
    resizeReference shrunk { regrowArgs with zeroInit := true } (.terminated .zeroing) := Or.inr rfl

theorem shrink_does_not_call_zeroing :
    ¬ resizeReference sample { shrinkArgs with zeroInit := true } (.terminated .zeroing) := by
  intro impossible
  cases impossible

def busy : State := { sample with borrow := mutableData }

theorem borrowed_input_needs_no_resize_storage :
    ResizeReady { busy with buffers := [] } ⟨AccountInfo.sampleInfo, 2^64 - 1, true⟩ := by
  refine ⟨?_, [10, 20, 30], AccountInfo.sampleProfile.policy, rfl, ?_⟩
  · exact Borrow.acquire_valid
      (Borrow.acquire_valid AccountInfo.sample_valid.2.1 AccountInfo.sampleInfo.lamports
        .shared AccountInfo.View.whole)
      AccountInfo.sampleInfo.data .exclusive AccountInfo.View.whole
  · intro exclusive _ _
    change 1 = 0 at exclusive
    cases exclusive

theorem unchanged_input_needs_no_resize_storage :
    ResizeReady { sample with buffers := [] } ⟨AccountInfo.sampleInfo, 3, true⟩ := by
  refine ⟨AccountInfo.sample_valid.2.1, [10, 20, 30], AccountInfo.sampleProfile.policy, rfl, ?_⟩
  intro _ _ changed
  exact False.elim (changed rfl)

theorem borrow_conflict_precedes_excessive_growth :
    resizeNormal busy ⟨AccountInfo.sampleInfo, 10244, true⟩ =
      some (.error .accountBorrowFailed, busy) := rfl

theorem borrow_conflict_precedes_unchanged_length :
    resizeNormal busy ⟨AccountInfo.sampleInfo, 3, true⟩ =
      some (.error .accountBorrowFailed, busy) := rfl

theorem growth_error_releases_temporary_guard :
    resizeNormal sample ⟨AccountInfo.sampleInfo, 10244, true⟩ =
      some (.error .invalidRealloc, { sample with borrow := { sample.borrow with slots := [none] }
        }) := rfl

def beyondLimit : State := {
  sample with
  borrow := { sample.borrow with cells := [⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data (List.replicate 10241 1), AccountInfo.sampleProfile.policy⟩] }
  buffers := [none, some ⟨0, 10241, []⟩] }

theorem unchanged_length_precedes_growth_limit :
    (resizeNormal beyondLimit ⟨AccountInfo.sampleInfo, 10241, true⟩).map
      (fun (result, _) => result) = some (.ok ()) := by
  simp [resizeNormal, prepareResize, beyondLimit, sample, AccountInfo.sampleState,
    AccountInfo.sampleInfo, Borrow.acquire, Borrow.State.lookupCell, Borrow.State.exclusiveCount,
    Borrow.State.sharedCount, Borrow.State.count, Borrow.State.issue, Borrow.current,
    Borrow.State.resolve, Borrow.State.lookupSlot, -List.reduceReplicate]

end SolanalibTest.Specs.Core.AccountInfoSdk
