/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorSpl.Token

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorSpl.OwnedAmount

open Solanalib.Contracts.Model Solanalib.Specs.Core

def held := (AccountInfo.tryBorrowMutData AccountInfo.sampleState AccountInfo.sampleArgs).2
def boxed := AnchorErrorOwned.Reference.fromProgramResult AnchorOwnedSamples.auxiliary
  .accountBorrowFailed

theorem boxed_borrow_failure : AnchorSplAmountOwned.program AnchorOwnedSamples.amount
  .accountBorrowFailed
    (held, AnchorOwnedSamples.auxiliary) () (.returned boxed.1 (held, boxed.2)) := by
  refine ⟨.returned boxed.1 (held, boxed.2), ?_, rfl⟩
  exact AnchorErrorOwned.fromProgram_focus_returned AnchorErrorOwned.Reference.ops Owned.Focus.snd
    (held, AnchorOwnedSamples.auxiliary) .accountBorrowFailed boxed.1 boxed.2
    (AnchorErrorOwned.Reference.fromProgram_returns AnchorOwnedSamples.auxiliary
      .accountBorrowFailed
      (by decide))

/-- Checked borrow failure builds an owned Anchor ProgramError. It neither
reads the amount bytes nor releases the exclusive guard of another caller. -/
theorem checked_error_preserves_existing_guard :
    (Solanalib.Specs.AnchorSpl.token.accessor.amount_contract.contract
      AnchorOwnedSamples.amount).post
      (held, AnchorOwnedSamples.auxiliary) AccountInfo.sampleArgs
      (.returned (.error boxed.1) (held, boxed.2)) :=
  AnchorSplAmountOwned.run_borrow_error (types := AnchorOwnedSamples.amount)
    (before := (held, AnchorOwnedSamples.auxiliary)) (args := AccountInfo.sampleArgs)
    (during := held) (failure := .accountBorrowFailed)
    (produced := .returned boxed.1 (held, boxed.2)) (by rfl) boxed_borrow_failure

theorem error_payload_and_held_data :
    AnchorErrorOwned.current AnchorOwnedSamples.amount.errors (held, boxed.2) boxed.1 =
      some (AnchorAccount.programError .accountBorrowFailed) ∧
    Borrow.current held ⟨0, 0⟩ = .ok (.whole, .data [10, 20, 30]) := ⟨rfl, rfl⟩

/-- Box allocation failure after a checked borrow error remains terminal; it
is not converted into the distinct short-slice panic of the accessor. -/
theorem checked_error_box_terminal : AnchorSplAmountOwned.run AnchorOwnedSamples.amount
    (held, AnchorErrorOwned.Reference.initial 0) AccountInfo.sampleArgs
    (.terminated (.inr (.allocation .box))) := by
  refine ⟨.terminated (.inr (.allocation .box)), ?_, rfl⟩
  refine ⟨.terminated (.allocation .box), ?_, rfl⟩
  refine ⟨.terminated (.allocation .box), ?_, rfl⟩
  exact ⟨.terminated (.allocation .box), rfl, rfl⟩

def wrongDataArgs : AccountInfo.Args :=
  { AccountInfo.sampleArgs with info :=
    { AccountInfo.sampleInfo with data := AccountInfo.sampleInfo.lamports } }

/-- The primary owned family excludes the same reached wrong-content read as
its observation facet; it invents neither an owned error nor a cleanup result. -/
theorem wrong_content_not_admitted :
    ¬ (Solanalib.Specs.AnchorSpl.token.accessor.amount_contract.contract
      AnchorOwnedSamples.amount).requires
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) wrongDataArgs :=
  fun impossible => impossible

theorem wrong_content_has_no_outcome
    (outcome : Outcome (AnchorAccount.World AnchorErrorOwned.Reference.State)
      (Except (AnchorSplAmountOwned.Error AnchorOwnedSamples.amount) Nat)
      AnchorSpl.AmountPanic (AnchorSplAmountOwned.Terminal AnchorOwnedSamples.amount)) :
    ¬ AnchorSplAmountOwned.run AnchorOwnedSamples.amount
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) wrongDataArgs outcome :=
  fun impossible => impossible

def wrongContentHeld : AccountInfo.State :=
  (AccountInfo.tryBorrowMutData AccountInfo.sampleState wrongDataArgs).2

/-- The new domain does not suppress an earlier borrow error when the selected
cell would have the wrong type on a successful acquisition. Boxing and the existing guard of the
caller are both retained. -/
theorem wrong_content_conflict_retains_error :
    (Solanalib.Specs.AnchorSpl.token.accessor.amount_contract.contract
      AnchorOwnedSamples.amount).requires
      (wrongContentHeld, AnchorOwnedSamples.auxiliary) wrongDataArgs ∧
    AnchorSplAmountOwned.run AnchorOwnedSamples.amount
      (wrongContentHeld, AnchorOwnedSamples.auxiliary) wrongDataArgs
      (.returned (.error boxed.1) (wrongContentHeld, boxed.2)) ∧
    Borrow.current wrongContentHeld ⟨0, 0⟩ = .ok (.whole, .lamports 40) := by
  refine ⟨trivial, ?_, rfl⟩
  apply AnchorSplAmountOwned.run_borrow_error (types := AnchorOwnedSamples.amount)
    (before := (wrongContentHeld, AnchorOwnedSamples.auxiliary)) (args := wrongDataArgs)
    (during := wrongContentHeld) (failure := .accountBorrowFailed)
    (produced := .returned boxed.1 (wrongContentHeld, boxed.2)) (by rfl)
  refine ⟨.returned boxed.1 (wrongContentHeld, boxed.2), ?_, rfl⟩
  exact AnchorErrorOwned.fromProgram_focus_returned AnchorErrorOwned.Reference.ops Owned.Focus.snd
    (wrongContentHeld, AnchorOwnedSamples.auxiliary) .accountBorrowFailed boxed.1 boxed.2
    (AnchorErrorOwned.Reference.fromProgram_returns AnchorOwnedSamples.auxiliary
      .accountBorrowFailed
      (by decide))

def shortReleased : AccountInfo.State :=
  (Borrow.release (AccountInfo.tryBorrowData AccountInfo.sampleState AccountInfo.sampleArgs).2 ⟨0,
    0⟩).2

/-- Short data is an admitted byte slice. Unwind releases the temporary guard
without boxing a checked error or changing the auxiliary resources. -/
theorem short_slice_unwinds_with_cleanup :
    (Solanalib.Specs.AnchorSpl.token.accessor.amount_contract.contract
      AnchorOwnedSamples.amount).requires
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) AccountInfo.sampleArgs ∧
    AnchorSplAmountOwned.run AnchorOwnedSamples.amount
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary) AccountInfo.sampleArgs
      (.unwound .sliceBounds (shortReleased, AnchorOwnedSamples.auxiliary)) ∧
    Borrow.current shortReleased ⟨0, 0⟩ = .error .invalidGuard := by
  refine ⟨trivial, ?_, rfl⟩
  exact AnchorSplAmountOwned.run_read (types := AnchorOwnedSamples.amount)
    (before := (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary))
    (args := AccountInfo.sampleArgs)
    (during := (AccountInfo.tryBorrowData AccountInfo.sampleState AccountInfo.sampleArgs).2)
    (guard := ⟨0, 0⟩) (bytes := [10, 20, 30]) (by rfl) (by rfl)

/-- Abort remains terminal rather than acquiring an invented post-state. -/
theorem short_slice_aborts :
    AnchorSplAmountOwned.run AnchorOwnedSamples.amount
      (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary)
      { AccountInfo.sampleArgs with profile := { AccountInfo.sampleProfile with aborts := true } }
      (.terminated (.inl .sliceBounds)) :=
  AnchorSplAmountOwned.run_read (types := AnchorOwnedSamples.amount)
    (before := (AccountInfo.sampleState, AnchorOwnedSamples.auxiliary))
    (args := { AccountInfo.sampleArgs with profile := { AccountInfo.sampleProfile with aborts :=
      true } })
    (during := (AccountInfo.tryBorrowData AccountInfo.sampleState AccountInfo.sampleArgs).2)
    (guard := ⟨0, 0⟩) (bytes := [10, 20, 30]) (by rfl) (by rfl)

def abstractArgs : AccountInfo.Args :=
  { AccountInfo.sampleArgs with profile := { AccountInfo.sampleProfile with wordBits := 0 } }
def amountReleased :=
  (Borrow.release (AccountInfo.tryBorrowData AnchorSpl.amountSampleState abstractArgs).2 ⟨0, 0⟩).2

/-- Source width is a separate binding obligation. Even outside that domain,
the mathematical accessor preserves its actual data read and guard cleanup. -/
theorem abstract_width_retains_amount_and_cleanup :
    ¬ AccountInfo.Valid abstractArgs.profile AnchorSpl.amountSampleState abstractArgs.info ∧
    (Solanalib.Specs.AnchorSpl.token.accessor.amount_contract.contract
      AnchorOwnedSamples.amount).requires
      (AnchorSpl.amountSampleState, AnchorOwnedSamples.auxiliary) abstractArgs ∧
    Solanalib.Specs.AnchorSpl.token.accessor.amount_run AnchorOwnedSamples.amount
      (AnchorSpl.amountSampleState, AnchorOwnedSamples.auxiliary) abstractArgs
      (.returned (.ok 42) (amountReleased, AnchorOwnedSamples.auxiliary)) ∧
    Borrow.current amountReleased ⟨0, 0⟩ = .error .invalidGuard := by
  refine ⟨?_, trivial, rfl, rfl⟩
  intro valid
  exact (by decide : ¬ 2 ≤ 0) valid.1

end SolanalibTest.Specs.AnchorSpl.OwnedAmount
