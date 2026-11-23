/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.PinocchioToken2022.State

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.PinocchioToken2022.State

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.Token

/-- Structural equality for kernel-checked finite model controls. -/
def exceptEq {E A : Type} [DecidableEq E] [DecidableEq A] :
    DecidableEq (Except E A)
  | .ok x, .ok y => if same : x = y then isTrue (same ▸ rfl)
      else isFalse (fun equal => same (Except.ok.inj equal))
  | .error x, .error y => if same : x = y then isTrue (same ▸ rfl)
      else isFalse (fun equal => same (Except.error.inj equal))
  | .ok _, .error _ => isFalse (by intro equal; cases equal)
  | .error _, .ok _ => isFalse (by intro equal; cases equal)

local instance {E A : Type} [DecidableEq E] [DecidableEq A] :
    DecidableEq (Except E A) := exceptEq

/-- A complete base account requires no extension-type marker. -/
theorem exact_base_admitted :
    (fromAccountView .token2022 .account
      (viewWitnessState token2022ProgramId accountWitness.bytes) ⟨0⟩).1 =
        .ok accountWitnessRef := by
  decide +kernel

/-- A minimal extended account has its type byte at offset 165. -/
def extendedAccount : Bytes := accountWitness.bytes ++ [2]

/-- The returned account view excludes the type byte and retains its lease. -/
theorem extended_account_success :
    let after := (fromAccountView .token2022 .account
      (viewWitnessState token2022ProgramId extendedAccount) ⟨0⟩).2
    (fromAccountView .token2022 .account
      (viewWitnessState token2022ProgramId extendedAccount) ⟨0⟩).1 =
        .ok accountWitnessRef ∧
    currentAccount after accountWitnessRef = .ok accountWitness ∧
    after.resolve accountWitnessRef.guard = some ⟨⟨0⟩, .shared, 1, ⟨0, 165⟩⟩ := by
  decide +kernel

/-- A nonzero complete base prefix used beneath token-2022 extension bytes. -/
def observedAccountRaw : AccountRaw :=
  ⟨legacyProgramId.bytes ++ token2022ProgramId.bytes ++ Solanalib.Runtime.u64le 37 ++
    List.replicate 36 0 ++ [2] ++ List.replicate 56 0, by
      simp [Solanalib.Runtime.u64le, legacyProgramId.length_eq,
        token2022ProgramId.length_eq, accountLength]⟩

/-- The actual parser post-state of the extended fixture. -/
def observedExtendedState : ViewState :=
  (Solanalib.Specs.PinocchioToken2022.state.account.Account.from_account_view_reference
    (viewWitnessState token2022ProgramId (observedAccountRaw.bytes ++ [2, 255])) ⟨0⟩).2

/-- One extended-account parse supplies all four source-facing getters with the
same live base view; extension bytes cannot replace the balance or key fields. -/
theorem extended_account_getters :
    let before := viewWitnessState token2022ProgramId (observedAccountRaw.bytes ++ [2, 255])
    let after := observedExtendedState
    (Solanalib.Specs.PinocchioToken2022.state.account.Account.from_account_view_reference
      before ⟨0⟩).1 = .ok accountWitnessRef ∧
    Solanalib.Specs.PinocchioToken2022.state.account.Account.amount_reference
      after accountWitnessRef = (37, after) ∧
    currentKey after (Solanalib.Specs.PinocchioToken2022.state.account.Account.mint_reference
      after accountWitnessRef).1 = .ok legacyProgramId ∧
    currentKey after (Solanalib.Specs.PinocchioToken2022.state.account.Account.owner_reference
      after accountWitnessRef).1 = .ok token2022ProgramId ∧
    stateRun stateAbortPolicy.panic after accountWitnessRef
      (.returned .frozen after) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  have current : currentAccount observedExtendedState accountWitnessRef =
      .ok observedAccountRaw := by decide +kernel
  have frozen : decodeAccountState observedAccountRaw.stateByte = some .frozen := by
    decide +kernel
  simp only [stateRun, current, frozen]

/-- An initialized mint with a distinct decimal byte for prefix-read controls. -/
def mintBase : Bytes := List.replicate 44 0 ++ [6, 1] ++ List.replicate 36 0

/-- Nonzero mint padding is deliberately accepted by this Pinocchio version. -/
def paddedMint : Bytes := mintBase ++ List.replicate 83 9 ++ [1]

/-- Pinocchio uses the common marker offset 165, not the end of its 82-byte Mint. -/
theorem padded_mint_success :
    let before := viewWitnessState token2022ProgramId paddedMint
    let after := (fromAccountView .token2022 .mint before ⟨0⟩).2
    (fromAccountView .token2022 .mint before ⟨0⟩).1 = .ok mintWitnessRef ∧
    (decimalsReference after mintWitnessRef).1 = 6 := by
  decide +kernel

/-- A marker placed immediately after the mint base does not satisfy extended admission. -/
theorem marker_at_82_rejected :
    (fromAccountView .token2022 .mint
      (viewWitnessState token2022ProgramId (mintBase ++ [1])) ⟨0⟩).1 =
        .error .InvalidAccountData := by
  decide +kernel

/-- 355 bytes are excluded even with the correct account marker. -/
theorem multisig_length_rejected :
    (fromAccountView .token2022 .account
      (viewWitnessState token2022ProgramId
        (extendedAccount ++ List.replicate 189 0)) ⟨0⟩).1 =
        .error .InvalidAccountData := by
  decide +kernel

/-- The marker is a type check, not merely a nonzero flag. -/
theorem wrong_type_rejected :
    (fromAccountView .token2022 .account
      (viewWitnessState token2022ProgramId (accountWitness.bytes ++ [1])) ⟨0⟩).1 =
        .error .InvalidAccountData := by
  decide +kernel

/-- An exclusive borrow makes malformed data fail at acquisition first. -/
def blocked : ViewState :=
  { viewWitnessState token2022ProgramId [] with
    slots := [some ⟨⟨0⟩, .exclusive, 0, ⟨0, 0⟩⟩] }

/-- The borrow conflict in Token-2022 precedes its data-layout error. -/
theorem borrow_before_layout :
    fromAccountView .token2022 .account blocked ⟨0⟩ =
      (.error .AccountBorrowFailed, blocked) := by
  decide +kernel

/-- Owner validation still precedes both borrowing and data validation. -/
theorem owner_before_borrow :
    fromAccountView .token2022 .mint
      { blocked with cells := (viewWitnessState .zero []).cells } ⟨0⟩ =
      (.error .InvalidAccountOwner,
        { blocked with cells := (viewWitnessState .zero []).cells }) := by
  decide +kernel

/-- The actual post-error state records retirement of the temporary guard. -/
theorem layout_error_releases :
    fromAccountView .token2022 .account (viewWitnessState token2022ProgramId []) ⟨0⟩ =
      (.error .InvalidAccountData,
        { viewWitnessState token2022ProgramId [] with slots := [none] }) ∧
    (fromAccountView .token2022 .account (viewWitnessState token2022ProgramId []) ⟨0⟩).2.lease
      ⟨0⟩ = .free := by
  decide +kernel

/-- A prior independent shared guard remains live during failed parser cleanup. -/
def sharedBeforeError : ViewState :=
  { viewWitnessState token2022ProgramId [0] with
    slots := [some ⟨⟨0⟩, .shared, 4, ⟨0, 1⟩⟩] }

/-- Cleanup consumes just the newly acquired identity, preserving the older one. -/
theorem failed_parse_preserves_prior_guard :
    fromAccountView .token2022 .account sharedBeforeError ⟨0⟩ =
      (.error .InvalidAccountData,
        { sharedBeforeError with slots := sharedBeforeError.slots ++ [none] }) ∧
    (fromAccountView .token2022 .account sharedBeforeError ⟨0⟩).2.resolve ⟨0, 4⟩ =
      some ⟨⟨0⟩, .shared, 4, ⟨0, 1⟩⟩ := by
  decide +kernel

/-- the actual saturation limit of AccountView is 254 distinct shared leases. -/
def saturated : ViewState :=
  { viewWitnessState token2022ProgramId accountWitness.bytes with
    slots := List.replicate 254 (some ⟨⟨0⟩, .shared, 0, ⟨0, accountLength⟩⟩) }

/-- The parser cannot acquire guard number 255. -/
theorem saturation_rejected :
    saturated.sharedCount ⟨0⟩ = 254 ∧
    fromAccountView .token2022 .account saturated ⟨0⟩ =
      (.error .AccountBorrowFailed, saturated) := by
  decide +kernel

/-- Raw option tags and initialized bytes are not checked by the mint parser of Pinocchio. -/
theorem raw_mint_flags_admitted :
    (fromAccountView .token2022 .mint
      (viewWitnessState token2022ProgramId (List.replicate 82 255)) ⟨0⟩).1 =
        .ok mintWitnessRef ∧
    unpackMint (List.replicate 82 255) = .error .InvalidAccountData := by
  decide +kernel

/-- The short-data integer accessor never pads missing bytes. -/
theorem amount_read_requires_all_bytes :
    readNat (List.replicate 71 0) 64 8 = none ∧
      readNat (List.replicate 64 0 ++ Solanalib.Runtime.u64le 37) 64 8 = some 37 := by
  decide +kernel

/-- Pod sizing and Pack validation intentionally interpret the initialization byte differently. -/
theorem pod_nonzero_differs_from_pack :
    (unpackPodMint (List.replicate 45 0 ++ [2] ++ List.replicate 36 0)).isOk = true ∧
    unpackMint (List.replicate 45 0 ++ [2] ++ List.replicate 36 0) =
      .error .InvalidAccountData := by
  decide +kernel

/-- Both token-2022 parser policies keep their existing missing-cell error
outside the Rust handle interpretation; unconditional admission invents no cell. -/
theorem missing_cell_parser_errors :
    let before : ViewState := ⟨[], []⟩
    Solanalib.Specs.PinocchioToken2022.state.account.Account.from_account_view_contract.requires
      before ⟨0⟩ ∧
    Solanalib.Specs.PinocchioToken2022.state.mint.Mint.from_account_view_contract.requires
      before ⟨0⟩ ∧
    Solanalib.Specs.PinocchioToken2022.state.account.Account.from_account_view_reference
      before ⟨0⟩ = (.error .InvalidAccountData, before) ∧
    Solanalib.Specs.PinocchioToken2022.state.mint.Mint.from_account_view_reference
      before ⟨0⟩ = (.error .InvalidAccountData, before) :=
  ⟨True.intro, True.intro, rfl, rfl⟩

end SolanalibTest.Specs.PinocchioToken2022.State
