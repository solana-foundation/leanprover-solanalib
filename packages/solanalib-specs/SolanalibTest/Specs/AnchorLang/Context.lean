/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorLang.context

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorLang.Context

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.AnchorContext
open Solanalib.Specs.AnchorLang.context.CpiContext

/-- A constructor client can recover every stored field from the contract alone. -/
theorem fields_from_contract (index : ObservationIndex) (before after : index.State)
    (args : AnchorContext.NewWithSignerArgs index.Accounts)
    (context : AnchorContext.Value index.Accounts index.AccountInfo)
    (post : (new_with_signer_observation_contract index).post before args (.returned context
      after)) :
    after = before ∧ context.accounts = args.accounts ∧
      context.programId = args.programId ∧ context.signerSeeds = args.signerSeeds ∧
      context.remainingAccounts = [] := by
  obtain ⟨stateEq, resultEq⟩ := post
  exact ⟨stateEq, by rw [resultEq]; rfl, by rw [resultEq]; rfl,
    by rw [resultEq]; rfl, by rw [resultEq]; rfl⟩

/-- Any later account projection sees the same arbitrary payload that was passed
to the constructor. This does not assume or invoke a `ToAccountInfos` callback. -/
theorem constructor_then_projection (index : ObservationIndex) {Projected : Type}
    (project : index.Accounts → Projected)
    (operation : index.State → AnchorContext.NewWithSignerArgs index.Accounts →
      AnchorContext.Value index.Accounts index.AccountInfo × index.State)
    (contract : (new_with_signer_observation_contract index).RealizedBy operation)
    (before : index.State) (args : AnchorContext.NewWithSignerArgs index.Accounts) :
    project (operation before args).1.accounts = project args.accounts ∧
      (operation before args).2 = before := by
  have fields := fields_from_contract index before _ args _ (contract before args trivial)
  exact ⟨congrArg project fields.2.1, fields.1⟩

def accountArgs : AnchorContext.NewWithSignerArgs (List _root_.Solanalib.Runtime.Pubkey) :=
  ⟨.ofNat 9, [.ofNat 1, .ofNat 2], [[[1, 2], [255]], [[3]]]⟩

/-- An empty remaining-account vector does not empty the independent `T` payload. -/
theorem empty_remaining_preserves_nonempty_payload :
    (newWithSigner (AccountInfo := Nat) accountArgs).accounts = [.ofNat 1, .ofNat 2] ∧
      (newWithSigner (AccountInfo := Nat) accountArgs).remainingAccounts = [] :=
  ⟨rfl, rfl⟩

/-- The constructor preserves PDA grouping, per-PDA seed order, and bytes. -/
theorem nested_seed_groups_are_preserved :
    (newWithSigner (AccountInfo := Nat) accountArgs).signerSeeds =
      [[[1, 2], [255]], [[3]]] ∧
    ((newWithSigner (AccountInfo := Nat) accountArgs).signerSeeds.map List.length) = [2, 1] :=
  ⟨rfl, rfl⟩

/-- In Anchor 1.0.2 the stored program is the supplied Pubkey, independent of T. -/
theorem stores_program_id :
    (newWithSigner (AccountInfo := Nat) accountArgs).programId = .ofNat 9 := rfl

def longSeedArgs : AnchorContext.NewWithSignerArgs Unit :=
  ⟨.zero, (), [[List.replicate 33 7]]⟩

/-- Seed-length checks are not performed by this constructor. Invocation and
address derivation have their own conditions and are not modeled by this call. -/
theorem constructor_does_not_validate_seed_length :
    (new_with_signer_observation_contract ⟨Unit, Unit, Nat⟩).post () longSeedArgs
      (.returned ⟨(), [], .zero, [[List.replicate 33 7]]⟩ ()) :=
  ⟨rfl, rfl⟩

/-- The universal family witness specializes independently of its registered sample. -/
theorem non_sample_state_reference :
    (new_with_signer_observation_contract ⟨List String, List _root_.Solanalib.Runtime.Pubkey,
      Nat⟩).post
      ["before"] accountArgs
      (.returned (newWithSigner accountArgs) ["before"]) :=
  new_with_signer_observation_reference.at ⟨List String, List _root_.Solanalib.Runtime.Pubkey, Nat⟩
    _ _ _ trivial rfl

end SolanalibTest.Specs.AnchorLang.Context
