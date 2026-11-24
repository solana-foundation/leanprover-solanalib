/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.SplToken2022.Instructions
public import Solanalib.Specs.SplToken2022.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.SplToken2022.Instructions

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.Core.Token
open Solanalib.Specs.Core.Token.Onchain

/-- A world holding an exclusive mint-data guard before preparation. -/
def lockedMint : State :=
  (Borrow.acquire witnessState witnessInfo.data .exclusive AccountInfo.View.whole).2

/-- A bad program ID fails before the already-conflicting mint borrow is attempted. -/
theorem program_admission_precedes_borrow :
    prepare lockedMint { witnessArgs with tokenProgramId := .zero } =
      (.error .IncorrectProgramId, lockedMint) := by
  rfl

/-- The value model also accepts mathematical scalars outside the Rust
domain; a rejected program exits before their instruction encoding. -/
def outsideScalarCall : Call sampleTypes :=
  { witnessCall with args :=
    { witnessArgs with tokenProgramId := .zero, amount := Solanalib.Runtime.U64_LIMIT } }

/-- The former value-family precondition rejected this finite error case. -/
theorem outside_scalar_domain : ¬ outsideScalarCall.args.Valid lockedMint := by
  intro valid
  exact Nat.lt_irrefl Solanalib.Runtime.U64_LIMIT valid.2.1

/-- The same value-family/reference index admits this mathematical input. -/
theorem outside_scalar_admitted :
    (invokeTransferCheckedFamily.contract sampleTypes).requires (lockedMint, (0 : Nat))
      outsideScalarCall := True.intro

/-- The actual early error preserves the preexisting exclusive guard and
does not execute the supplied CPI callback or invent local borrow cleanup. -/
theorem outside_scalar_error_executes :
    invokeTransferCheckedRun sampleTypes (lockedMint, (0 : Nat)) outsideScalarCall
      (.returned (.error .IncorrectProgramId) (lockedMint, (0 : Nat))) := by
  rfl

theorem mint_conflict_is_checked_error :
    prepare lockedMint witnessArgs = (.error .AccountBorrowFailed, lockedMint) := by
  rfl

/-- A correctly sized but uninitialized mint-data sample. -/
def uninitializedState : State :=
  { witnessState with cells := [⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data (List.replicate 82 0), AccountInfo.sampleProfile.policy⟩] }

/-- A parsing error drops the temporary mint guard instead of leaking a lease. -/
theorem mint_error_releases_guard :
    prepare uninitializedState witnessArgs =
      (.error .UninitializedAccount, { uninitializedState with slots := [none] }) := by
  rfl

/-- The transfer source sharing the empty-data test cell. -/
def sourceInfo : AccountInfo.Value := { witnessInfo with key := .ofNat 1, data := ⟨3⟩ }
/-- The initialized mint account used by preparation controls. -/
def mintInfo : AccountInfo.Value := { witnessInfo with key := .ofNat 2 }
/-- The transfer destination sharing the empty-data test cell. -/
def destinationInfo : AccountInfo.Value := { witnessInfo with key := .ofNat 3, data := ⟨3⟩ }
/-- A Token-owned authority whose data cell contains a POD multisig. -/
def authorityInfo : AccountInfo.Value :=
  { witnessInfo with key := .ofNat 4, owner := legacyProgramId, data := ⟨2⟩ }
/-- An additional multisig key with its AccountInfo signer flag unset. -/
def signerA : AccountInfo.Value := { witnessInfo with key := .ofNat 5, data := ⟨3⟩, isSigner :=
  false }
/-- A second additional multisig key used twice to check duplicate preservation. -/
def signerB : AccountInfo.Value := { witnessInfo with key := .ofNat 6, data := ⟨3⟩, isSigner :=
  false }
/-- An additional key absent from the multisig signer list. -/
def otherInfo : AccountInfo.Value := { witnessInfo with key := .ofNat 7, data := ⟨3⟩ }

/-- Threshold and initialization bytes are intentionally unusual: this helper
uses only n and the first n signer keys after owner/size admission. -/
def multisigBytes : Bytes :=
  [250, 2, 0] ++ signerA.key.bytes ++ signerB.key.bytes ++ List.replicate (9 * 32) 0

/-- A shared world with initialized mint, POD multisig and empty additional data. -/
def multisigState : State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data witnessMintBytes, AccountInfo.sampleProfile.policy⟩,
    ⟨.data multisigBytes, AccountInfo.sampleProfile.policy⟩,
    ⟨.data [], AccountInfo.sampleProfile.policy⟩], []⟩

/-- An ordered additional-account list containing two keys, a nonmember and a duplicate. -/
def multisigArgs : Args := {
  witnessArgs with
  source := sourceInfo
  mint := mintInfo
  destination := destinationInfo
  authority := authorityInfo
  additional := [signerB, otherInfo, signerA, signerB] }

/-- Observe the ordered account keys of a successful value-level preparation. -/
def selectedKeys (result : Step Prepared) : List Solanalib.Runtime.Pubkey :=
  match result with
  | .success prepared => prepared.accounts.map AccountInfo.Value.key
  | _ => []

/-- Observe exact signer and writable bytes of prepared metadata. -/
def selectedFlags (result : Step Prepared) : List (Nat × Nat) :=
  match result with
  | .success prepared => prepared.instruction.metas.map fun item => (item.signerByte,
    item.writableByte)
  | _ => []

/-- Selection follows additional-account order, keeps duplicates and does not
require the selected AccountInfo.isSigner flags to be set. -/
theorem multisig_order_duplicates_and_unsigned_inputs :
    selectedKeys (prepare multisigState multisigArgs).1 =
      [.ofNat 1, .ofNat 2, .ofNat 3, .ofNat 4, .ofNat 6, .ofNat 5, .ofNat 6] := by
  decide +kernel

theorem multisig_authority_flag_is_corrected :
    selectedFlags (prepare multisigState multisigArgs).1 =
      [(0, 1), (0, 0), (0, 1), (0, 0), (1, 0), (1, 0), (1, 0)] := by
  decide +kernel

/-- Data-length observation, multisig parsing and mint parsing each retire their guard. -/
theorem multisig_all_guards_released :
    (prepare multisigState multisigArgs).2.slots = [none, none, none] := by
  decide +kernel

/-- A POD multisig declaring more than its eleven stored signer slots. -/
def excessiveSignersState : State :=
  { multisigState with cells := (multisigState.cells.set 2
      ⟨.data (multisigBytes.set 1 12), AccountInfo.sampleProfile.policy⟩) }

/-- The POD n byte is not sanitized into a returned ProgramError. Slicing with
n > 11 panics, and unwinding releases the authority borrow. -/
theorem excessive_multisig_n_panics :
    prepare excessiveSignersState multisigArgs =
      (.panic .multisigSignerRange, { excessiveSignersState with slots := [none, none] }) := by
  decide +kernel

/-- A world with an exclusive authority-data guard before recognition. -/
def lockedAuthority : State :=
  (Borrow.acquire multisigState authorityInfo.data .exclusive AccountInfo.View.whole).2

theorem authority_borrow_panic_precedes_mint_work :
    prepare lockedAuthority multisigArgs = (.panic .borrowFailed, lockedAuthority) := by
  decide +kernel

/-- A Token-owned authority whose data length is not the multisig length. -/
def wrongSizeState : State :=
  { multisigState with cells := (multisigState.cells.set 2
      ⟨.data (multisigBytes.take 354), AccountInfo.sampleProfile.policy⟩) }

/-- A token-owned account with the wrong byte length is treated as a single authority. -/
theorem wrong_multisig_size_keeps_single_authority :
    selectedFlags (prepare wrongSizeState multisigArgs).1 =
      [(0, 1), (0, 0), (0, 1), (1, 0)] := by
  decide +kernel

/-- The test transfer-hook program identity. -/
def hookId : Solanalib.Runtime.Pubkey := .ofNat 99
/-- The additional account selected by the static hook metadata. -/
def extraInfo : AccountInfo.Value := { witnessInfo with key := .ofNat 88, data := ⟨3⟩ }
/-- The validation PDA account with its separate data cell. -/
def validationInfo : AccountInfo.Value := { witnessInfo with key := .zero, data := ⟨2⟩ }
/-- The additional account matching the hook program identity. -/
def hookInfo : AccountInfo.Value := { witnessInfo with key := hookId, data := ⟨3⟩ }
/-- A non-multisig authority for the transfer-hook controls. -/
def singleAuthority : AccountInfo.Value := { authorityInfo with owner := .zero }

/-- Base mint, required zero padding, account type, then TransferHook TLV. -/
def hookMintBytes : Bytes :=
  witnessMintBytes ++ List.replicate 83 0 ++ [1, 14, 0, 64, 0] ++
    List.replicate 32 0 ++ hookId.bytes

/-- A 35-byte POD extra-account record with noncanonical nonzero Boolean bytes. -/
def rawExtra (key : Solanalib.Runtime.Pubkey) : Bytes := [0] ++ key.bytes ++ [7, 255]

/-- A complete Execute TLV entry containing one active extra-account record. -/
def validationBytes : Bytes :=
  Hook.executeDiscriminator ++ Solanalib.Runtime.u32le 74 ++ Solanalib.Runtime.u32le 2 ++
    rawExtra sourceInfo.key ++ rawExtra extraInfo.key

/-- An extended mint and validation TLV in a shared, initially unborrowed world. -/
def hookState : State :=
  ⟨[⟨.lamports 40, AccountInfo.sampleProfile.policy⟩,
    ⟨.data hookMintBytes, AccountInfo.sampleProfile.policy⟩,
    ⟨.data validationBytes, AccountInfo.sampleProfile.policy⟩,
    ⟨.data [], AccountInfo.sampleProfile.policy⟩], []⟩

/-- The ordered additional account list of the transfer-hook control. -/
def hookArgs : Args := {
  multisigArgs with
  authority := singleAuthority
  additional := [sourceInfo, extraInfo, validationInfo, hookInfo] }

/-- Extras precede the validation account, which precedes the hook program.
The static source alias is retained instead of deduplicated. -/
theorem hook_extra_account_order :
    selectedKeys (prepare hookState hookArgs).1 =
      [.ofNat 1, .ofNat 2, .ofNat 3, .ofNat 4, .ofNat 1, .ofNat 88, .zero, .ofNat 99] := by
  decide +kernel

/-- Extra signers are always cleared. A source alias is de-escalated against
the readonly Execute request, even though the transfer itself writes source. -/
theorem hook_extra_privileges :
    selectedFlags (prepare hookState hookArgs).1 =
      [(0, 1), (0, 0), (0, 1), (1, 0), (0, 0), (0, 1), (0, 0), (0, 0)] := by
  decide +kernel

/-- Mint+validation scopes and both ordered account-data collection passes retire. -/
theorem hook_all_guards_released :
    (prepare hookState hookArgs).2.slots = List.replicate 13 none := by
  decide +kernel

theorem hook_program_is_required :
    prepare hookState { hookArgs with additional := [] } =
      (.error Hook.incorrectHookAccount, { hookState with slots := [none] }) := by
  decide +kernel

/-- Absence of the validation account is admitted, with just the hook program appended. -/
theorem hook_validation_is_optional :
    selectedKeys (prepare hookState { hookArgs with additional := [hookInfo] }).1 =
      [.ofNat 1, .ofNat 2, .ofNat 3, .ofNat 4, .ofNat 99] := by
  decide +kernel

/-- A validation buffer with a malformed nonzero trailing TLV discriminator. -/
def badValidationState : State :=
  { hookState with cells := (hookState.cells.set 2
      ⟨.data [], AccountInfo.sampleProfile.policy⟩) }

theorem hook_bad_validation_releases_both_scopes :
    prepare badValidationState hookArgs =
      (.error .InvalidAccountData, { badValidationState with slots := [none, none] }) := by
  decide +kernel

/-- The two missing-account cases have distinct custom errors. -/
theorem hook_missing_extra_is_distinct :
    (prepare hookState { hookArgs with additional := [sourceInfo, validationInfo, hookInfo] }).1 =
      .error Hook.incorrectExtraAccount := by
  decide +kernel

/-- A source account with an exclusive data borrow during hook preparation. -/
def lockedSource : State :=
  (Borrow.acquire hookState sourceInfo.data .exclusive AccountInfo.View.whole).2

theorem extra_resolution_borrow_failure_drops_scopes :
    prepare lockedSource hookArgs =
      (.error .AccountBorrowFailed, { lockedSource with slots := lockedSource.slots ++ [none, none]
        }) := by
  decide +kernel

/-- A zero seed tag stops decoding without inspecting following bytes. -/
theorem seed_zero_stops_before_invalid_tag :
    Hook.decodeSeeds (.ofBytes [0, 255]) = .ok [] := by
  rfl

theorem seed_literal_truncation_rejected :
    Hook.decodeSeeds (.ofBytes ([1, 31] ++ List.replicate 30 9)) =
      .error Hook.invalidSeedBytes := by
  rfl

theorem external_program_lookup_precedes_seed_decode :
    Hook.resolve Address.witnessCrypto [] .zero [] ⟨128, .ofBytes [255], false, false⟩ =
      .error (.program Hook.accountNotFound) := by
  rfl

theorem missing_seed_data_is_distinct_from_missing_account :
    Hook.resolveSeed [] [(.zero, none)] (.accountData 0 200 32) =
      .error Hook.accountDataNotFound ∧
    Hook.resolveSeed [] [] (.accountData 0 200 32) = .error Hook.accountNotFound := by
  constructor <;> rfl

/-- Whole-TLV validation rejects a malformed later entry before reading an earlier Execute entry. -/
theorem tlv_validation_precedes_selected_lookup :
    Hook.decodeValidation (Hook.executeDiscriminator ++ Solanalib.Runtime.u32le 4 ++
      Solanalib.Runtime.u32le 0 ++ [1]) =
      .error .InvalidAccountData := by
  rfl

theorem short_zero_tlv_is_not_type_not_found :
    Hook.decodeValidation (List.replicate 8 0) = .error .InvalidAccountData ∧
    Hook.decodeValidation (List.replicate 12 0) = .error Hook.tlvTypeNotFound := by
  constructor <;> rfl

theorem meta_capacity_bytes_must_have_exact_element_size :
    Hook.decodeMetaList [0, 0, 0, 0, 99] = .error .InvalidArgument := by
  rfl

theorem inactive_meta_capacity_is_not_interpreted :
    Hook.decodeMetaList (Solanalib.Runtime.u32le 0 ++ List.replicate 35 255) = .ok [] := by
  rfl

/-- An empty provider relation used to prove local errors require no CPI execution. -/
def unreachableProvider :
    CpiRequest.Invocation (State × Nat) AccountInfo.Value Error Nat Nat :=
  fun _ _ _ => False

/-- A local returned error has an execution even when the invocation provider
has no outcomes: CPI is never reached on that path. -/
theorem local_error_never_needs_invocation :
    run sampleTypes (lockedMint, (5 : Nat))
      ⟨{ witnessArgs with tokenProgramId := .zero }, unreachableProvider⟩
      (.returned (.error .IncorrectProgramId) (lockedMint, (5 : Nat))) := by
  rfl

/-- A RefCell panic follows the chosen abort profile and cannot become Ok. -/
theorem local_panic_aborts_without_invocation :
    run sampleTypes (lockedAuthority, (5 : Nat))
      ⟨{ multisigArgs with profile := ⟨64, true⟩ }, unreachableProvider⟩
      (.terminated (.inl .borrowFailed)) := by
  rfl

theorem local_panic_unwinds_with_borrow_state :
    run sampleTypes (lockedAuthority, (5 : Nat))
      ⟨multisigArgs, unreachableProvider⟩
      (.unwound (.inl .borrowFailed) (lockedAuthority, (5 : Nat))) := by
  rfl

/-- A concrete changed balance used to test opaque-call state preservation. -/
def changedProviderState : State :=
  { witnessAfter with cells := (witnessAfter.cells.set 0
      ⟨.lamports 77, AccountInfo.sampleProfile.policy⟩) }

/-- A successful CPI interpretation that changes account and ambient state. -/
def successfulProvider :
    CpiRequest.Invocation (State × Nat) AccountInfo.Value Error Nat Nat :=
  fun before request outcome =>
    before.1 = witnessAfter ∧ request.signers = witnessArgs.signers ∧
      outcome = .returned (.ok ()) (changedProviderState, before.2 + request.accounts.length)

/-- The provider sees the released mint guard and exact nested seeds, and its
account and ambient effects survive the successful wrapper return. -/
theorem invocation_success_preserves_actual_effects :
    run sampleTypes (witnessState, (5 : Nat)) ⟨witnessArgs, successfulProvider⟩
      (.returned (.ok ()) (changedProviderState, (9 : Nat))) := by
  unfold run
  rw [witness_prepares]
  exact ⟨.returned (.ok ()) (changedProviderState, (9 : Nat)), ⟨rfl, rfl, rfl⟩, rfl⟩

/-- An unwinding CPI interpretation retaining its changed account world. -/
def unwindingProvider :
    CpiRequest.Invocation (State × Nat) AccountInfo.Value Error Nat Nat :=
  fun _ _ outcome => outcome = .unwound 17 (changedProviderState, 23)

theorem invocation_unwind_preserves_actual_effects :
    run sampleTypes (witnessState, (5 : Nat)) ⟨witnessArgs, unwindingProvider⟩
      (.unwound (.inr (17 : Nat)) (changedProviderState, (23 : Nat))) := by
  unfold run
  rw [witness_prepares]
  exact ⟨.unwound (17 : Nat) (changedProviderState, (23 : Nat)), rfl, rfl⟩

/-- A terminal CPI interpretation with its exact terminal reason. -/
def terminatingProvider :
    CpiRequest.Invocation (State × Nat) AccountInfo.Value Error Nat Nat :=
  fun _ _ outcome => outcome = .terminated 29

theorem invocation_terminal_preserves_reason :
    run sampleTypes (witnessState, (5 : Nat)) ⟨witnessArgs, terminatingProvider⟩
      (.terminated (.inr (29 : Nat))) := by
  unfold run
  rw [witness_prepares]
  exact ⟨.terminated (29 : Nat), rfl, rfl⟩

end SolanalibTest.Specs.SplToken2022.Instructions

namespace SolanalibTest.Specs.SplToken2022.Instructions.Pr575Compatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_burn_checkedBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_burn_checkedCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_burn_checkedBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ instruction_burn_checkedBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (instruction_burn_checkedBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_burn_checkedBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_burn_checkedBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_burn_checkedBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_burn_checkedBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_burn_checkedBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_burn_checkedBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "lit\
    tle"⟩]
    }, false),
  -- wrong-target-os; unsupported
  ({ instruction_burn_checkedBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_burn_checkedBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_burn_checkedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "lin\
    ux"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_burn_checkedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩] },
    false),
  -- wrong-target-endian; unsupported
  ({ instruction_burn_checkedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_burn_checkedBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_burn_checkedBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_burn_checkedBuild with dependencies := (instruction_burn_checkedBuild.dependencies
    ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_burn_checkedBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_burn_checkedBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_burn_checkedBuild with dependencies := (instruction_burn_checkedBuild.dependencies
    ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_burn_checkedBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_burn_checkedBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_burn_checkedBuild with dependencies := (instruction_burn_checkedBuild.dependencies
    ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_burn_checkedBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_burn_checkedBuild with dependencies :=
    (instruction_burn_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_burn_checked_profile_controls :
    instruction_burn_checkedCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .instruction_burn_checked).any
        (fun profile => ["spl-token-2022-8.0.1-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_burn_checked_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { instruction_burn_checkedBuild with version := version }).identities
          .instruction_burn_checked).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::instruction::burn_checked",
          "spl_token_2022::instruction::burn_checked"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_close_accountBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_close_accountCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_close_accountBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ instruction_close_accountBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (instruction_close_accountBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_close_accountBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_close_accountBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_close_accountBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_close_accountBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_close_accountBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_close_accountBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "li\
    ttle"⟩]
    }, false),
  -- wrong-target-os; unsupported
  ({ instruction_close_accountBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_close_accountBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_close_accountBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "li\
    nux"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_close_accountBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩] },
    false),
  -- wrong-target-endian; unsupported
  ({ instruction_close_accountBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_close_accountBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_close_accountBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_close_accountBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_close_accountBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_close_accountBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_close_accountBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_close_accountBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_close_accountBuild with dependencies :=
    (instruction_close_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_close_account_profile_controls :
    instruction_close_accountCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .instruction_close_account).any
        (fun profile => ["spl-token-2022-8.0.1-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_close_account_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { instruction_close_accountBuild with version := version }).identities
          .instruction_close_account).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::instruction::close_account",
          "spl_token_2022::instruction::close_account"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_freeze_accountBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_freeze_accountCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_freeze_accountBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ instruction_freeze_accountBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (instruction_freeze_accountBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_freeze_accountBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_freeze_accountBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_freeze_accountBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_freeze_accountBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_freeze_accountBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_freeze_accountBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "l\
    ittle"⟩]
    }, false),
  -- wrong-target-os; unsupported
  ({ instruction_freeze_accountBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_freeze_accountBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_freeze_accountBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "l\
    inux"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_freeze_accountBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "6\
    4"⟩] },
    false),
  -- wrong-target-endian; unsupported
  ({ instruction_freeze_accountBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "6\
    4"⟩,
    ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_freeze_accountBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_freeze_accountBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_freeze_accountBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_freeze_accountBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_freeze_accountBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_freeze_accountBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_freeze_accountBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_freeze_accountBuild with dependencies :=
    (instruction_freeze_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_freeze_account_profile_controls :
    instruction_freeze_accountCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .instruction_freeze_account).any
        (fun profile => ["spl-token-2022-8.0.1-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_freeze_account_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { instruction_freeze_accountBuild with version := version }).identities
          .instruction_freeze_account).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::instruction::freeze_account",
          "spl_token_2022::instruction::freeze_account"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_initialize_account3Build : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_initialize_account3Cases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_initialize_account3Build, true),
  -- inspected-reference-8.0.1; eligible
  ({ instruction_initialize_account3Build with version := "8.0.1" }, true),
  -- lower; eligible
  (instruction_initialize_account3Build, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_initialize_account3Build with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_initialize_account3Build with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_initialize_account3Build with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_initialize_account3Build with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_initialize_account3Build with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_initialize_account3Build with target := [⟨"pointer_width", "64"⟩, ⟨"endian",
    "little"⟩] }, false),
  -- wrong-target-os; unsupported
  ({ instruction_initialize_account3Build with target := [⟨"os", "linux"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_initialize_account3Build with target := [⟨"os", "solana"⟩, ⟨"endian", "lit\
    tle"⟩]
    }, false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_initialize_account3Build with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "linux"⟩, ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_initialize_account3Build with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩] }, false),
  -- wrong-target-endian; unsupported
  ({ instruction_initialize_account3Build with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩, ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_initialize_account3Build, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-pubkey" then { dependency with version := "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-pubkey" then { dependency with version := "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_initialize_account3Build, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-pubkey" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-pubkey" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.filter (fun dependency => dependency.package
    != "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_initialize_account3Build, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-instruction" then { dependency with version := "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_initialize_account3Build, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-instruction" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-instruction" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-instruction" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.filter (fun dependency => dependency.package
    != "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_initialize_account3Build, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) },
    true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_initialize_account3Build, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) },
    true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) },
    false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.filter (fun dependency => dependency.package
    != "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_initialize_account3Build with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-pubkey" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-instruction" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_initialize_account3Build with dependencies :=
    (instruction_initialize_account3Build.dependencies.map (fun dependency => if dependency.package
    == "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) },
    false)
]

set_option maxRecDepth 8192 in
theorem instruction_initialize_account3_profile_controls :
    instruction_initialize_account3Cases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .instruction_initialize_account3).any
        (fun profile => ["spl-token-2022-8.0.1-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_initialize_account3_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { instruction_initialize_account3Build with version := version }).identities
          .instruction_initialize_account3).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::instruction::initialize_account3",
          "spl_token_2022::instruction::initialize_account3"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_initialize_immutable_ownerBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_initialize_immutable_ownerCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_initialize_immutable_ownerBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ instruction_initialize_immutable_ownerBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (instruction_initialize_immutable_ownerBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_initialize_immutable_ownerBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_initialize_immutable_ownerBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_initialize_immutable_ownerBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_initialize_immutable_ownerBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_initialize_immutable_ownerBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_initialize_immutable_ownerBuild with target := [⟨"pointer_width", "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- wrong-target-os; unsupported
  ({ instruction_initialize_immutable_ownerBuild with target := [⟨"os", "linux"⟩, ⟨"pointer\
    _width",
    "64"⟩, ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_initialize_immutable_ownerBuild with target := [⟨"os", "solana"⟩, ⟨"endian",
    "little"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_initialize_immutable_ownerBuild with target := [⟨"os", "solana"⟩,
    ⟨"pointer_width", "linux"⟩, ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_initialize_immutable_ownerBuild with target := [⟨"os", "solana"⟩,
    ⟨"pointer_width", "64"⟩] }, false),
  -- wrong-target-endian; unsupported
  ({ instruction_initialize_immutable_ownerBuild with target := [⟨"os", "solana"⟩,
    ⟨"pointer_width", "64"⟩, ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_initialize_immutable_ownerBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.3.0" } else
    dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.4.0" } else
    dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_initialize_immutable_ownerBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.2.98" } else
    dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else
    dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.filter (fun dependency =>
    dependency.package != "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_initialize_immutable_ownerBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "2.3.3" } else
    dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_initialize_immutable_ownerBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "2.2.98" } else
    dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "2.2.1-rc.\
      1" }
    else dependency)) }, false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.filter (fun dependency =>
    dependency.package != "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_initialize_immutable_ownerBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.2.2" } else
    dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_initialize_immutable_ownerBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.2.98" } else
    dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.2.1-r\
      c.1" }
    else dependency)) }, false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.filter (fun dependency =>
    dependency.package != "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_initialize_immutable_ownerBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.2.0" } else
    dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "2.2.0" } else
    dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_initialize_immutable_ownerBuild with dependencies :=
    (instruction_initialize_immutable_ownerBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.2.0" } else
    dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_initialize_immutable_owner_profile_controls :
    instruction_initialize_immutable_ownerCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .instruction_initialize_immutable_owner).any
        (fun profile => ["spl-token-2022-8.0.1-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_initialize_immutable_owner_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { instruction_initialize_immutable_ownerBuild with version := version }).identities
          .instruction_initialize_immutable_owner).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::instruction::initialize_immutable_own\
          er",
          "spl_token_2022::instruction::initialize_immutable_owner"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_initialize_mint2Build : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_initialize_mint2Cases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_initialize_mint2Build, true),
  -- inspected-reference-8.0.1; eligible
  ({ instruction_initialize_mint2Build with version := "8.0.1" }, true),
  -- lower; eligible
  (instruction_initialize_mint2Build, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_initialize_mint2Build with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_initialize_mint2Build with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_initialize_mint2Build with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_initialize_mint2Build with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_initialize_mint2Build with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_initialize_mint2Build with target := [⟨"pointer_width", "64"⟩, ⟨"endian",
    "little"⟩] }, false),
  -- wrong-target-os; unsupported
  ({ instruction_initialize_mint2Build with target := [⟨"os", "linux"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_initialize_mint2Build with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_initialize_mint2Build with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "linux"⟩, ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_initialize_mint2Build with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩]
    }, false),
  -- wrong-target-endian; unsupported
  ({ instruction_initialize_mint2Build with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_initialize_mint2Build, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_initialize_mint2Build, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.filter (fun dependency => dependency.package !=
    "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_initialize_mint2Build, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_initialize_mint2Build, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.filter (fun dependency => dependency.package !=
    "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_initialize_mint2Build, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_initialize_mint2Build, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_initialize_mint2Build with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_initialize_mint2Build with dependencies :=
    (instruction_initialize_mint2Build.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_initialize_mint2_profile_controls :
    instruction_initialize_mint2Cases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .instruction_initialize_mint2).any
        (fun profile => ["spl-token-2022-8.0.1-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_initialize_mint2_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { instruction_initialize_mint2Build with version := version }).identities
          .instruction_initialize_mint2).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::instruction::initialize_mint2",
          "spl_token_2022::instruction::initialize_mint2"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_initialize_non_transferable_mintBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_initialize_non_transferable_mintCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_initialize_non_transferable_mintBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ instruction_initialize_non_transferable_mintBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (instruction_initialize_non_transferable_mintBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_initialize_non_transferable_mintBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_initialize_non_transferable_mintBuild with target := [⟨"pointer_width", "6\
    4"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- wrong-target-os; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with target := [⟨"os", "linux"⟩,
    ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_initialize_non_transferable_mintBuild with target := [⟨"os", "solana"⟩, ⟨
    "endian",
    "little"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with target := [⟨"os", "solana"⟩,
    ⟨"pointer_width", "linux"⟩, ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_initialize_non_transferable_mintBuild with target := [⟨"os", "solana"⟩,
    ⟨"pointer_width", "64"⟩] }, false),
  -- wrong-target-endian; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with target := [⟨"os", "solana"⟩,
    ⟨"pointer_width", "64"⟩, ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_initialize_non_transferable_mintBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.3.0" } else
    dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.4.0" } else
    dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_initialize_non_transferable_mintBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.2.98" } else
    dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else
    dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.filter (fun dependency =>
    dependency.package != "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_initialize_non_transferable_mintBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "2.3.3" } else
    dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_initialize_non_transferable_mintBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "2.2.98" } else
    dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "2.2.1-rc.\
      1" }
    else dependency)) }, false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.filter (fun dependency =>
    dependency.package != "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_initialize_non_transferable_mintBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.2.2" } else
    dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_initialize_non_transferable_mintBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.2.98" } else
    dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "3.0.0" } else
    dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.2.1-r\
      c.1" }
    else dependency)) }, false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.filter (fun dependency =>
    dependency.package != "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-pubkey" then { dependency with version := "2.2.0" } else
    dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-instruction" then { dependency with version := "2.2.0" } else
    dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_initialize_non_transferable_mintBuild with dependencies :=
    (instruction_initialize_non_transferable_mintBuild.dependencies.map (fun dependency => if
    dependency.package == "solana-program-error" then { dependency with version := "2.2.0" } else
    dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_initialize_non_transferable_mint_profile_controls :
    instruction_initialize_non_transferable_mintCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .instruction_initialize_non_transferable_mint).any
        (fun profile => ["spl-token-2022-8.0.1-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_initialize_non_transferable_mint_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { instruction_initialize_non_transferable_mintBuild with version := version }).identities
          .instruction_initialize_non_transferable_mint).eraseDups ==
        [⟨"spl-token-2022", version,
          "spl_token_2022::instruction::initialize_non_transferable_mint",
          "spl_token_2022::instruction::initialize_non_transferable_mint"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_mint_toBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_mint_toCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_mint_toBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ instruction_mint_toBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (instruction_mint_toBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_mint_toBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_mint_toBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_mint_toBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_mint_toBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_mint_toBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_mint_toBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-os; unsupported
  ({ instruction_mint_toBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩, ⟨"e\
    ndian",
    "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_mint_toBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_mint_toBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "linux"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_mint_toBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩] }, false),
  -- wrong-target-endian; unsupported
  ({ instruction_mint_toBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨
    "endian",
    "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_mint_toBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_mint_toBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.filter
    (fun dependency => dependency.package != "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_mint_toBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-instruction" then { dependency with version :=
    "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_mint_toBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-instruction" then { dependency with version :=
    "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-instruction" then { dependency with version :=
    "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-instruction" then { dependency with version :=
    "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.filter
    (fun dependency => dependency.package != "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_mint_toBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-program-error" then { dependency with version :=
    "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_mint_toBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-program-error" then { dependency with version :=
    "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-program-error" then { dependency with version :=
    "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-program-error" then { dependency with version :=
    "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.filter
    (fun dependency => dependency.package != "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_mint_toBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-instruction" then { dependency with version :=
    "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_mint_toBuild with dependencies := (instruction_mint_toBuild.dependencies.map (fun
    dependency => if dependency.package == "solana-program-error" then { dependency with version :=
    "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_mint_to_profile_controls :
    instruction_mint_toCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability .instruction_mint_to).any
        (fun profile => ["spl-token-2022-8.0.1-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_mint_to_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { instruction_mint_toBuild with version := version }).identities
          .instruction_mint_to).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::instruction::mint_to",
          "spl_token_2022::instruction::mint_to"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_set_authorityBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_set_authorityCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_set_authorityBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ instruction_set_authorityBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (instruction_set_authorityBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_set_authorityBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_set_authorityBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_set_authorityBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_set_authorityBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_set_authorityBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_set_authorityBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "li\
    ttle"⟩]
    }, false),
  -- wrong-target-os; unsupported
  ({ instruction_set_authorityBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_set_authorityBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_set_authorityBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "li\
    nux"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_set_authorityBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩] },
    false),
  -- wrong-target-endian; unsupported
  ({ instruction_set_authorityBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_set_authorityBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_set_authorityBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_set_authorityBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_set_authorityBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_set_authorityBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_set_authorityBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_set_authorityBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_set_authorityBuild with dependencies :=
    (instruction_set_authorityBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_set_authority_profile_controls :
    instruction_set_authorityCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .instruction_set_authority).any
        (fun profile => ["spl-token-2022-8.0.1-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_set_authority_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { instruction_set_authorityBuild with version := version }).identities
          .instruction_set_authority).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::instruction::set_authority",
          "spl_token_2022::instruction::set_authority"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_thaw_accountBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_thaw_accountCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_thaw_accountBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ instruction_thaw_accountBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (instruction_thaw_accountBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_thaw_accountBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_thaw_accountBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_thaw_accountBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_thaw_accountBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_thaw_accountBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_thaw_accountBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "lit\
    tle"⟩]
    }, false),
  -- wrong-target-os; unsupported
  ({ instruction_thaw_accountBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_thaw_accountBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_thaw_accountBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "lin\
    ux"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_thaw_accountBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩] },
    false),
  -- wrong-target-endian; unsupported
  ({ instruction_thaw_accountBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_thaw_accountBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_thaw_accountBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_thaw_accountBuild with dependencies := (instruction_thaw_accountBuild.dependencies
    ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_thaw_accountBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_thaw_accountBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_thaw_accountBuild with dependencies := (instruction_thaw_accountBuild.dependencies
    ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_thaw_accountBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_thaw_accountBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_thaw_accountBuild with dependencies := (instruction_thaw_accountBuild.dependencies
    ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_thaw_accountBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_thaw_accountBuild with dependencies :=
    (instruction_thaw_accountBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_thaw_account_profile_controls :
    instruction_thaw_accountCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .instruction_thaw_account).any
        (fun profile => ["spl-token-2022-8.0.1-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_thaw_account_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { instruction_thaw_accountBuild with version := version }).identities
          .instruction_thaw_account).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::instruction::thaw_account",
          "spl_token_2022::instruction::thaw_account"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def instruction_transfer_checkedBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def instruction_transfer_checkedCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (instruction_transfer_checkedBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ instruction_transfer_checkedBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (instruction_transfer_checkedBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ instruction_transfer_checkedBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ instruction_transfer_checkedBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ instruction_transfer_checkedBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ instruction_transfer_checkedBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ instruction_transfer_checkedBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ instruction_transfer_checkedBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian",
    "little"⟩] }, false),
  -- wrong-target-os; unsupported
  ({ instruction_transfer_checkedBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ instruction_transfer_checkedBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-pointer_width; unsupported
  ({ instruction_transfer_checkedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "linux"⟩, ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ instruction_transfer_checkedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩]
    }, false),
  -- wrong-target-endian; unsupported
  ({ instruction_transfer_checkedBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width",
    "64"⟩,
    ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (instruction_transfer_checkedBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (instruction_transfer_checkedBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-instruction-2.2.1; eligible
  (instruction_transfer_checkedBuild, true),
  -- dependency-reference-solana-instruction-2.3.3; eligible
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.3.3" } else dependency)) }, true),
  -- dependency-solana-instruction-lower; eligible
  (instruction_transfer_checkedBuild, true),
  -- dependency-solana-instruction-hypothetical-declaration-probe; eligible
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-instruction-exclusive-upper; unsupported
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-instruction-unlisted-prerelease; unsupported
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-instruction; unresolved
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-instruction")) }, false),
  -- wrong-dependency-origin-solana-instruction; unsupported
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-instruction; ValueError containing Ambiguous dependency
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies ++ [⟨
    "solana-instruction", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- dependency-reference-solana-program-error-2.2.1; eligible
  (instruction_transfer_checkedBuild, true),
  -- dependency-reference-solana-program-error-2.2.2; eligible
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.2" } else dependency)) }, true),
  -- dependency-solana-program-error-lower; eligible
  (instruction_transfer_checkedBuild, true),
  -- dependency-solana-program-error-hypothetical-declaration-probe; eligible
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.98" } else dependency)) }, true),
  -- dependency-solana-program-error-exclusive-upper; unsupported
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "3.0.0" } else dependency)) }, false),
  -- dependency-solana-program-error-unlisted-prerelease; unsupported
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.1-rc.1" } else dependency)) },
    false),
  -- missing-dependency-solana-program-error; unresolved
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.filter (fun dependency => dependency.package !=
    "solana-program-error")) }, false),
  -- wrong-dependency-origin-solana-program-error; unsupported
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-program-error; ValueError containing Ambiguous dependency
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies ++ [⟨
    "solana-program-error", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ instruction_transfer_checkedBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-instruction-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-instruction" then { dependency with version := "2.2.0" } else dependency)) }, false),
  -- dependency-solana-program-error-below-lower-bound-fixture-2.2.0; unsupported
  ({ instruction_transfer_checkedBuild with dependencies :=
    (instruction_transfer_checkedBuild.dependencies.map (fun dependency => if dependency.package ==
    "solana-program-error" then { dependency with version := "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem instruction_transfer_checked_profile_controls :
    instruction_transfer_checkedCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability
        .instruction_transfer_checked).any
        (fun profile => ["spl-token-2022-8.0.1-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem instruction_transfer_checked_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { instruction_transfer_checkedBuild with version := version }).identities
          .instruction_transfer_checked).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::instruction::transfer_checked",
          "spl_token_2022::instruction::transfer_checked"⟩])) = true := by
  decide +kernel

/-- Inspected references and labelled hypothetical builds are matcher fixtures.
They supply no source binding, body proof or additional native observation. -/
def native_mint_check_idBuild : Versioning.Build where
  package := "spl-token-2022"
  version := "8.0.0"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩]
  features := some []
  targetFeatures := some []
  dependencies := [⟨"solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

def native_mint_check_idCases : List (Versioning.Build × Bool) := [
  -- inspected-reference-8.0.0; eligible
  (native_mint_check_idBuild, true),
  -- inspected-reference-8.0.1; eligible
  ({ native_mint_check_idBuild with version := "8.0.1" }, true),
  -- lower; eligible
  (native_mint_check_idBuild, true),
  -- hypothetical-declaration-probe; eligible
  ({ native_mint_check_idBuild with version := "8.0.97" }, true),
  -- exclusive-upper; unsupported
  ({ native_mint_check_idBuild with version := "9.0.0" }, false),
  -- unlisted-prerelease; unsupported
  ({ native_mint_check_idBuild with version := "8.0.0-rc.1" }, false),
  -- wrong-package; unsupported
  ({ native_mint_check_idBuild with package := "unrelated-source" }, false),
  -- wrong-origin; unsupported
  ({ native_mint_check_idBuild with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ }, false),
  -- missing-target-os; unresolved
  ({ native_mint_check_idBuild with target := [⟨"pointer_width", "64"⟩, ⟨"endian", "little"⟩] },
    false),
  -- wrong-target-os; unsupported
  ({ native_mint_check_idBuild with target := [⟨"os", "linux"⟩, ⟨"pointer_width", "64"⟩, ⟨
    "endian",
    "little"⟩] }, false),
  -- missing-target-pointer_width; unresolved
  ({ native_mint_check_idBuild with target := [⟨"os", "solana"⟩, ⟨"endian", "little"⟩] }, false),
  -- wrong-target-pointer_width; unsupported
  ({ native_mint_check_idBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "linux"⟩,
    ⟨"endian", "little"⟩] }, false),
  -- missing-target-endian; unresolved
  ({ native_mint_check_idBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩] }, false),
  -- wrong-target-endian; unsupported
  ({ native_mint_check_idBuild with target := [⟨"os", "solana"⟩, ⟨"pointer_width", "64"⟩,
    ⟨"endian", "linux"⟩] }, false),
  -- dependency-reference-solana-pubkey-2.2.1; eligible
  (native_mint_check_idBuild, true),
  -- dependency-reference-solana-pubkey-2.3.0; eligible
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.3.0" } else dependency)) }, true),
  -- dependency-reference-solana-pubkey-2.4.0; eligible
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.4.0" } else dependency)) }, true),
  -- dependency-solana-pubkey-lower; eligible
  (native_mint_check_idBuild, true),
  -- dependency-solana-pubkey-hypothetical-declaration-probe; eligible
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.2.98" } else dependency)) }, true),
  -- dependency-solana-pubkey-exclusive-upper; unsupported
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "3.0.0" } else dependency)) }, false),
  -- dependency-solana-pubkey-unlisted-prerelease; unsupported
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.2.1-rc.1" } else dependency)) }, false),
  -- missing-dependency-solana-pubkey; unresolved
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.filter
    (fun dependency => dependency.package != "solana-pubkey")) }, false),
  -- wrong-dependency-origin-solana-pubkey; unsupported
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package ==
    "solana-pubkey" then { dependency with source := ⟨"git", "https://example.invalid/review-fork",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"⟩ } else dependency)) }, false),
  -- ambiguous-dependency-solana-pubkey; ValueError containing Ambiguous dependency
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies ++ [⟨
    "solana-pubkey", "2.2.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]) }, false),
  -- below-lower-bound-fixture-7.999.999; unsupported
  ({ native_mint_check_idBuild with version := "7.999.999" }, false),
  -- dependency-solana-pubkey-below-lower-bound-fixture-2.2.0; unsupported
  ({ native_mint_check_idBuild with dependencies := (native_mint_check_idBuild.dependencies.map
    (fun dependency => if dependency.package == "solana-pubkey" then { dependency with version :=
    "2.2.0" } else dependency)) }, false)
]

set_option maxRecDepth 8192 in
theorem native_mint_check_id_profile_controls :
    native_mint_check_idCases.all (fun test =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.applicability .native_mint_check_id).any
        (fun profile => ["spl-token-2022-8.0.1-pubkey-2-2-solana"].contains profile.id &&
          profile.matches test.1)) == test.2)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- Expected callable identities are literal source-registry identities;
they are not computed from catalog identities or profile fields. -/
theorem native_mint_check_id_callable_identities :
    ["8.0.0", "8.0.1", "8.0.97"].all (fun version =>
      (((Solanalib.Specs.SplToken2022.Capabilities.catalog.forBuild
        { native_mint_check_idBuild with version := version }).identities
          .native_mint_check_id).eraseDups ==
        [⟨"spl-token-2022", version, "spl_token_2022::native_mint::check_id",
          "spl_token_2022::native_mint::check_id"⟩])) = true := by
  decide +kernel

end SolanalibTest.Specs.SplToken2022.Instructions.Pr575Compatibility
