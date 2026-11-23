/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorLifecycleCloseSamples

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Core.AnchorLifecycleClose

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorLifecycle

def distinctArgs : CloseArgs :=
  ⟨AccountInfo.sampleProfile, AccountInfo.sampleInfo, { AccountInfo.sampleInfo with lamports := ⟨2⟩
    }⟩

def overflowState : AccountInfoSdk.State :=
  { AccountInfoSdk.sample with borrow :=
    ⟨[⟨.lamports (UInt64.ofNat (2^64 - 1)), AccountInfo.sampleProfile.policy⟩,
      ⟨.data [10, 20, 30], AccountInfo.sampleProfile.policy⟩,
      ⟨.lamports 1, AccountInfo.sampleProfile.policy⟩], []⟩ }

def overflowAfter : AccountInfoSdk.State :=
  { overflowState with borrow := { overflowState.borrow with slots := [none, none] } }

theorem legacy_overflow_panics :
    commonCloseCore .legacy overflowState distinctArgs =
      some (.unwound .arithmeticOverflow overflowAfter) := by rfl

theorem modern_overflow_returns_program_error :
    commonCloseCore .checked overflowState distinctArgs =
      some (.returned (.error .arithmeticOverflow) overflowAfter) := by rfl

theorem legacy_abort_profile_retained :
    commonCloseCore .legacy overflowState { distinctArgs with profile := ⟨64, true⟩ } =
      some (.terminated .arithmeticOverflow) := by rfl

def destinationExclusive : AccountInfoSdk.State :=
  { overflowState with borrow := { overflowState.borrow with slots :=
    [some ⟨⟨2⟩, .exclusive, 0, .whole⟩] } }

theorem legacy_destination_read_precedes_source :
    commonCloseCore .legacy destinationExclusive distinctArgs =
      some (.unwound .borrowFailed destinationExclusive) := by rfl

theorem modern_source_read_precedes_destination :
    commonCloseCore .checked destinationExclusive distinctArgs = some (.unwound .borrowFailed
      { destinationExclusive with borrow := { destinationExclusive.borrow with slots :=
        [some ⟨⟨2⟩, .exclusive, 0, .whole⟩, none] } }) := by rfl

def resizeConflict : AccountInfoSdk.State :=
  { AccountInfoSdk.sample with borrow := { AccountInfoSdk.sample.borrow with slots :=
    [some ⟨⟨1⟩, .shared, 0, .whole⟩] } }

def afterResizeFailure : AccountInfoSdk.State :=
  { resizeConflict with owners := [.zero], borrow :=
    ⟨[⟨.lamports 0, AccountInfo.sampleProfile.policy⟩,
      ⟨.data [10, 20, 30], AccountInfo.sampleProfile.policy⟩],
      [some ⟨⟨1⟩, .shared, 0, .whole⟩, none, none, none, none]⟩ }

theorem resize_error_preserves_earlier_mutations (mode : CloseMode) :
    commonCloseCore mode resizeConflict closeSampleArgs =
      some (.returned (.error .accountBorrowFailed) afterResizeFailure) := by
  cases mode <;> rfl

theorem resize_error_is_not_rollback : afterResizeFailure ≠ resizeConflict := by decide

theorem self_alias_closes_once (mode : CloseMode) :
    commonCloseCore mode AccountInfoSdk.sample closeSampleArgs =
      some (.returned (.ok ()) closeSampleAfterSdk) := closeSample_core mode

theorem self_alias_neither_doubles_final_balance_nor_loses_backing :
    (closeSampleAfterSdk.borrow.lookupCell AccountInfo.sampleInfo.lamports).map Borrow.Cell.value =
      some (.lamports 0) ∧
    closeSampleAfterSdk.buffers[1]? = some (some ⟨3, 0, [10, 20, 30, 40, 50, 60]⟩) :=
  ⟨rfl, rfl⟩

end SolanalibTest.Specs.Core.AnchorLifecycleClose
