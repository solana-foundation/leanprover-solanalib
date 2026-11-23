/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Pinocchio.RentAccount

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.Pinocchio.RentAccount

open Solanalib.Contracts.Model Solanalib.Specs.Core

theorem copies_rate_without_shared_guard :
    Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate.from_account_view_run
      (Sysvar.Witness.singleAccount Sysvar.Witness.rentAccount)
      Sysvar.Witness.handle =
      (.ok ⟨6960⟩, Sysvar.Witness.singleAccount Sysvar.Witness.rentAccount) := rfl

theorem existing_shared_guard_is_unchanged :
    Sysvar.rent111FromAccount (Sysvar.Witness.singleGuard Sysvar.Witness.rentAccount .shared)
      Sysvar.Witness.handle =
      (.ok ⟨6960⟩, Sysvar.Witness.singleGuard Sysvar.Witness.rentAccount .shared) := rfl

theorem exclusive_failure_precedes_wrong_address :
    Sysvar.rent111FromAccount (Sysvar.Witness.singleGuard AccountView.Account.empty .exclusive)
      Sysvar.Witness.handle =
      (.error .accountBorrowFailed,
        Sysvar.Witness.singleGuard AccountView.Account.empty .exclusive) := rfl

theorem exclusive_error_admitted_without_data :
    Sysvar.Rent111ReadReady
      (Sysvar.Witness.singleGuard AccountView.Account.empty .exclusive) Sysvar.Witness.handle := by
  refine ⟨⟨⟨AccountView.Account.empty, Borrow.Policy.accountView⟩, rfl⟩, ?_⟩
  intro borrowed
  contradiction

theorem wrong_address_needs_no_data_extent :
    Sysvar.rent111FromAccount (Sysvar.Witness.singleAccount AccountView.Account.empty)
      Sysvar.Witness.handle =
      (.error .invalidArgument, Sysvar.Witness.singleAccount AccountView.Account.empty) := rfl

theorem wrong_address_admitted_without_data :
    Sysvar.Rent111ReadReady
      (Sysvar.Witness.singleAccount AccountView.Account.empty) Sysvar.Witness.handle := by
  refine ⟨⟨⟨AccountView.Account.empty, Borrow.Policy.accountView⟩, rfl⟩, ?_⟩
  intro _ address
  have distinct : AccountView.Account.empty.metadata.address ≠ Solanalib.Runtime.Ids.sysvarRent :=
    by decide
  exact False.elim (distinct address)

def shortRent : AccountView.Account :=
  { AccountView.Account.empty with metadata := ⟨Solanalib.Runtime.Ids.sysvarRent, false, false,
    false⟩ }

/-- The raw short-data fallback is excluded by the source-facing contract. -/
theorem short_rate_rejected :
    ¬ 8 ≤ shortRent.bytes.length ∧
      ¬ Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate.from_account_view_contract.requires
        (Sysvar.Witness.singleAccount shortRent) Sysvar.Witness.handle ∧
      Solanalib.Specs.Pinocchio.sysvars.rent.Rent.fixed_rate.from_account_view_run
        (Sysvar.Witness.singleAccount shortRent) Sysvar.Witness.handle =
        (.ok ⟨0⟩, Sysvar.Witness.singleAccount shortRent) :=
  ⟨by decide, by
    intro ready
    have extent := ready.2 (by decide) rfl
    contradiction, rfl⟩

theorem seven_bytes_rejected :
    ¬ Sysvar.Rent111ReadReady
      (Sysvar.Witness.singleAccount
        { shortRent with dataLen := 7, backing := List.replicate 7 0 }) Sysvar.Witness.handle := by
  intro ready
  have extent := ready.2 (by decide) rfl
  contradiction

theorem missing_account_rejected :
    ¬ Sysvar.Rent111ReadReady (⟨[], []⟩ : AccountView.State) Sysvar.Witness.handle := by
  rintro ⟨⟨cell, present⟩, _⟩
  contradiction

end SolanalibTest.Specs.Pinocchio.RentAccount
