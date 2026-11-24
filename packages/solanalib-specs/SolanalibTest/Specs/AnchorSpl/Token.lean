/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.AnchorSpl
public import Solanalib.Specs.AnchorLang.accounts
public import Solanalib.Specs.AnchorSpl.Capabilities

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace SolanalibTest.Specs.AnchorSpl.Token

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSpl

/-- Two selected dereferences compose to the decoded mint payload. No
relationship between that payload and account bytes is assumed by dereference. -/
theorem account_then_mint_deref :
    mintDeref (AnchorAccount.accountDeref
      (AnchorAccount.Account.mk (Mint.mk sampleMint) AccountInfo.sampleInfo)) = sampleMint := rfl

theorem interface_then_mint_deref :
    interfaceMintDeref (AnchorAccount.interfaceAccountDeref
      (AnchorAccount.InterfaceAccount.mk
        ⟨InterfaceMint.mk sampleMint, AccountInfo.sampleInfo⟩ .zero)) = sampleMint := rfl

def shortReleased : AccountInfo.State :=
  (Borrow.release (AccountInfo.tryBorrowData AccountInfo.sampleState AccountInfo.sampleArgs).2 ⟨0,
    0⟩).2

/-- Short account data produces a slice panic and releases the temporary guard;
it is not reported as InvalidAccountData or AccountBorrowFailed. -/
theorem short_amount_panics :
    amount AccountInfo.sampleState AccountInfo.sampleArgs =
      some (.unwound .sliceBounds shortReleased) ∧
    shortReleased.sharedCount AccountInfo.sampleInfo.data = 0 := ⟨rfl, rfl⟩

theorem short_amount_aborts :
    amount AccountInfo.sampleState
      { AccountInfo.sampleArgs with profile := { AccountInfo.sampleProfile with aborts := true } } =
      some (.terminated .sliceBounds) := rfl

def borrowed : AccountInfo.State :=
  (AccountInfo.tryBorrowMutData amountSampleState AccountInfo.sampleArgs).2

/-- Borrow failure occurs before the byte accessor and retains the exact SDK
error inside the ProgramError wrapper of Anchor. -/
theorem amount_borrow_error : amount borrowed AccountInfo.sampleArgs =
    some (.returned (.error (AnchorAccount.programError .accountBorrowFailed)) borrowed) := rfl

/-- The amount accessor accepts a 72-byte account with an arbitrary owner;
the full 165-byte token state is not validated by this function. -/
theorem amount_reads_without_owner_or_full_state_check :
    amountSampleBytes.length = 72 ∧
    amount amountSampleState AccountInfo.sampleArgs =
      some (.returned (.ok 42)
        (Borrow.release (AccountInfo.tryBorrowData amountSampleState AccountInfo.sampleArgs).2 ⟨0,
          0⟩).2) :=
  ⟨rfl, rfl⟩

def wrongDataArgs : AccountInfo.Args :=
  { AccountInfo.sampleArgs with info :=
    { AccountInfo.sampleInfo with data := AccountInfo.sampleInfo.lamports } }

/-- A successful guard acquisition does not make a lamports cell a byte slice.
The reached wrong-content path has no fabricated result and is not admitted. -/
theorem wrong_content_rejected :
    (AccountInfo.tryBorrowData AccountInfo.sampleState wrongDataArgs).1 = .ok ⟨0, 0⟩ ∧
    Borrow.current (AccountInfo.tryBorrowData AccountInfo.sampleState wrongDataArgs).2 ⟨0, 0⟩ =
      .ok (.whole, .lamports 40) ∧
    amount AccountInfo.sampleState wrongDataArgs = none ∧
    ¬ amountContract.requires AccountInfo.sampleState wrongDataArgs := by
  exact ⟨rfl, rfl, rfl, fun impossible => impossible⟩

def wrongContentHeld : AccountInfo.State :=
  (AccountInfo.tryBorrowMutData AccountInfo.sampleState wrongDataArgs).2

/-- The typed read is not reached when borrowing fails. Even a wrong-content
cell preserves that earlier checked error and the live guard of another caller. -/
theorem wrong_content_conflict_is_admitted :
    amountContract.requires wrongContentHeld wrongDataArgs ∧
    amount wrongContentHeld wrongDataArgs =
      some (.returned (.error (AnchorAccount.programError .accountBorrowFailed)) wrongContentHeld) ∧
    Borrow.current wrongContentHeld ⟨0, 0⟩ = .ok (.whole, .lamports 40) :=
  ⟨trivial, rfl, rfl⟩

def absentDataArgs : AccountInfo.Args :=
  { AccountInfo.sampleArgs with info := { AccountInfo.sampleInfo with data := ⟨99⟩ } }

/-- No new presence premise hides the existing checked missing-handle branch. -/
theorem missing_handle_is_admitted :
    amountContract.requires AccountInfo.sampleState absentDataArgs ∧
    amount AccountInfo.sampleState absentDataArgs =
      some (.returned (.error (AnchorAccount.programError .accountBorrowFailed))
        AccountInfo.sampleState) :=
  ⟨trivial, rfl⟩

def sharedBefore : AccountInfo.State :=
  (AccountInfo.tryBorrowData amountSampleState AccountInfo.sampleArgs).2

def sharedAfter : AccountInfo.State :=
  (Borrow.release (AccountInfo.tryBorrowData sharedBefore AccountInfo.sampleArgs).2 ⟨1, 0⟩).2

/-- A successful local read releases its own new guard, retaining an older
shared guard and the current byte contents it observes. -/
theorem read_preserves_previous_shared_guard :
    amountContract.requires sharedBefore AccountInfo.sampleArgs ∧
    amount sharedBefore AccountInfo.sampleArgs = some (.returned (.ok 42) sharedAfter) ∧
    Borrow.current sharedAfter ⟨0, 0⟩ = .ok (.whole, .data amountSampleBytes) ∧
    Borrow.current sharedAfter ⟨1, 0⟩ = .error .invalidGuard := by
  refine ⟨trivial, ?_, rfl, rfl⟩
  exact amount_read (before := sharedBefore) (args := AccountInfo.sampleArgs)
    (during := (AccountInfo.tryBorrowData sharedBefore AccountInfo.sampleArgs).2)
    (guard := ⟨1, 0⟩) (bytes := amountSampleBytes) (by rfl) (by rfl)

def sourceInfo : AccountInfo.Value := { AccountInfo.sampleInfo with key := .ofNat 1 }
def destinationInfo : AccountInfo.Value := { AccountInfo.sampleInfo with key := .ofNat 2 }
def authorityInfo : AccountInfo.Value := { AccountInfo.sampleInfo with key := .ofNat 3 }

def constructedContext : TransferContext :=
  AnchorContext.newWithSigner ⟨.ofNat 99, ⟨sourceInfo, destinationInfo, authorityInfo⟩,
    [[], [[1, 2], []], [[3]]]⟩

def transferArgs : TransferArgs := ⟨constructedContext, 42⟩

/-- Context construction followed by transfer retains the account order and
each nested signer-seed group; the helper uses its fixed token program. -/
theorem context_then_transfer_request :
    (transferRequest transferArgs).accounts = [sourceInfo, destinationInfo, authorityInfo] ∧
    (transferRequest transferArgs).signers = [[], [[1, 2], []], [[3]]] ∧
    (transferRequest transferArgs).instruction.programId = Token.legacyProgramId := ⟨rfl, rfl, rfl⟩

/-- The fixed builder marks source/destination writable and authority signer,
without consulting the input AccountInfo flags or the context program ID. -/
theorem ordered_transfer_metas :
    (transferInstruction transferArgs).metas.map _root_.Solanalib.Runtime.CpiMeta.key =
      [sourceInfo.key, destinationInfo.key, authorityInfo.key] ∧
    (transferInstruction transferArgs).metas.map _root_.Solanalib.Runtime.CpiMeta.signerByte = [0,
      0, 1] ∧
    (transferInstruction transferArgs).metas.map _root_.Solanalib.Runtime.CpiMeta.writableByte =
      [1, 1, 0] ∧
    (transferInstruction transferArgs).data = [3, 42, 0, 0, 0, 0, 0, 0, 0] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem context_unused_fields (programId : _root_.Solanalib.Runtime.Pubkey)
    (remaining : List AccountInfo.Value) :
    transferRequest { transferArgs with context :=
      { constructedContext with programId := programId, remainingAccounts := remaining } } =
      transferRequest transferArgs := rfl

/-- The error of the opaque invocation preserves its actual changed state. -/
theorem invocation_error_keeps_state :
    transferRun transferSample (9 : Nat) transferArgs
      (.returned (.error (AnchorAccount.programError .insufficientFunds)) (14 : Nat)) :=
  ⟨.returned (.error .insufficientFunds) (14 : Nat), rfl, rfl⟩

def panicInvocation : TransferIndex :=
  ⟨Nat, String, String,
    fun before _ outcome => outcome = .unwound "invoke" (before + 1)⟩

theorem invocation_unwind_keeps_state :
    transferRun panicInvocation (9 : Nat) transferArgs (.unwound "invoke" (10 : Nat)) :=
  ⟨.unwound "invoke" (10 : Nat), rfl, rfl⟩

def stopInvocation : TransferIndex :=
  ⟨Nat, String, String, fun _ _ outcome => outcome = .terminated "stop"⟩

theorem invocation_terminal :
    transferRun stopInvocation (9 : Nat) transferArgs (.terminated "stop") :=
  ⟨.terminated "stop", rfl, rfl⟩

end SolanalibTest.Specs.AnchorSpl.Token

namespace SolanalibTest.Specs.AnchorSpl.Token.ExtendedProfiles

open Solanalib.Contracts.Model Solanalib.Specs.Core

set_option maxRecDepth 8192

abbrev Key := Solanalib.Specs.AnchorSpl.Capabilities.Key

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal callable identities and resolved facts. These fixtures neither
prove source bodies nor discharge the remaining profile conditions. -/
def fixtures : List (Key × Versioning.Build × List (String × String)) :=
  [(.associated_token_create,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        target := [⟨"os", "solana"⟩],
        features := some ["associated_token"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-associated-token-accoun\
          t",
          "7.0.0", registry⟩, ⟨"spl-associated-token-account-client", "2.0.0", registry⟩,
          ⟨"solana-pubkey", "2.2.1", registry⟩] },
      [("anchor_spl::associated_token::create", "anchor_spl::associated_token::create")]),
    (.associated_token_create,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        target := [⟨"os", "solana"⟩],
        features := some ["associated_token"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-associated-token-accoun\
          t",
          "7.0.0", registry⟩, ⟨"spl-associated-token-account-client", "2.0.0", registry⟩,
          ⟨"solana-pubkey", "2.4.0", registry⟩] },
      [("anchor_spl::associated_token::create", "anchor_spl::associated_token::create")]),
    (.metadata_create_metadata_accounts_v3,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        target := [⟨"os", "solana"⟩],
        features := some ["metadata"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"mpl-token-metadata", "5.1.1",
          registry⟩] },
      [("anchor_spl::metadata::create_metadata_accounts_v3",
        "anchor_spl::metadata::create_metadata_accounts_v3")]),
    (.token_Token_id,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token"],
        dependencies := [⟨"spl-token", "8.0.0", registry⟩] },
      [("anchor_lang::Id::id", "<anchor_spl::token::Token as anchor_lang::Id>::id")]),
    (.token_TokenAccount_deref,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token"],
        dependencies := [⟨"spl-token", "8.0.0", registry⟩] },
      [("core::ops::deref::Deref::deref",
        "<anchor_spl::token::TokenAccount as core::ops::deref::Deref>::deref")]),
    (.token_transfer_with_program_owner,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token", "8.0.0", registry⟩,
          ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error", "2.2.0", registry⟩]
          },
      [("anchor_spl::token::transfer", "anchor_spl::token::transfer")]),
    (.token_2022_burn,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022::burn", "anchor_spl::token_2022::burn")]),
    (.token_2022_close_account,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022::close_account", "anchor_spl::token_2022::close_account")]),
    (.token_2022_get_account_data_size,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022::get_account_data_size",
        "anchor_spl::token_2022::get_account_data_size")]),
    (.token_2022_initialize_account3,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022::initialize_account3",
        "anchor_spl::token_2022::initialize_account3")]),
    (.token_2022_initialize_immutable_owner,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022::initialize_immutable_owner",
        "anchor_spl::token_2022::initialize_immutable_owner")]),
    (.token_2022_initialize_mint2,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022::initialize_mint2", "anchor_spl::token_2022::initialize_min\
        t2")]),
    (.token_2022_mint_to,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022::mint_to", "anchor_spl::token_2022::mint_to")]),
    (.token_2022_set_authority,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022::set_authority", "anchor_spl::token_2022::set_authority")]),
    (.token_2022_extensions_group_member_pointer_group_member_pointer_initialize,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022_extensions"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022_extensions::group_member_pointer::group_member_pointer_init\
        ialize",
        "anchor_spl::token_2022_extensions::group_member_pointer::group_member_pointer_init\
          ialize")]),
    (.token_2022_extensions_group_pointer_group_pointer_initialize,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022_extensions"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022_extensions::group_pointer::group_pointer_initialize",
        "anchor_spl::token_2022_extensions::group_pointer::group_pointer_initialize")]),
    (.token_2022_extensions_metadata_pointer_metadata_pointer_initialize,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022_extensions"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022_extensions::metadata_pointer::metadata_pointer_initialize",
        "anchor_spl::token_2022_extensions::metadata_pointer::metadata_pointer_initialize")]),
    (.token_2022_extensions_mint_close_authority_mint_close_authority_initialize,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022_extensions"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022_extensions::mint_close_authority::mint_close_authority_init\
        ialize",
        "anchor_spl::token_2022_extensions::mint_close_authority::mint_close_authority_init\
          ialize")]),
    (.token_2022_extensions_non_transferable_non_transferable_mint_initialize,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022_extensions"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022_extensions::non_transferable::non_transferable_mint_initial\
        ize",
        "anchor_spl::token_2022_extensions::non_transferable::non_transferable_mint_initial\
          ize")]),
    (.token_2022_extensions_permanent_delegate_permanent_delegate_initialize,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022_extensions"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022_extensions::permanent_delegate::permanent_delegate_initiali\
        ze",
        "anchor_spl::token_2022_extensions::permanent_delegate::permanent_delegate_initiali\
          ze")]),
    (.token_2022_extensions_transfer_hook_transfer_hook_initialize,
      {
        package := "anchor-spl",
        version := "0.32.0",
        source := registry,
        features := some ["token_2022_extensions"],
        dependencies := [⟨"anchor-lang", "0.32.0", registry⟩, ⟨"spl-token-2022", "8.0.0",
          registry⟩, ⟨"solana-account-info", "2.3.0", registry⟩, ⟨"solana-program-error",
            "2.2.0",
          registry⟩] },
      [("anchor_spl::token_2022_extensions::transfer_hook::transfer_hook_initialize",
        "anchor_spl::token_2022_extensions::transfer_hook::transfer_hook_initialize")])]

def identitiesMatch (key : Key) (build : Versioning.Build)
    (expected : List (String × String)) : Bool :=
  decide ((Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild build).identities key =
    expected.map (fun (item, implementation) =>
      ⟨"anchor-spl", build.version, item, implementation⟩))

def members : List Key := [.associated_token_create, .metadata_create_metadata_accounts_v3,
  .token_Token_id, .token_TokenAccount_deref, .token_transfer_with_program_owner, .token_2022_burn,
  .token_2022_close_account, .token_2022_get_account_data_size, .token_2022_initialize_account3,
  .token_2022_initialize_immutable_owner, .token_2022_initialize_mint2, .token_2022_mint_to,
  .token_2022_set_authority,
  .token_2022_extensions_group_member_pointer_group_member_pointer_initialize,
  .token_2022_extensions_group_pointer_group_pointer_initialize,
  .token_2022_extensions_metadata_pointer_metadata_pointer_initialize,
  .token_2022_extensions_mint_close_authority_mint_close_authority_initialize,
  .token_2022_extensions_non_transferable_non_transferable_mint_initialize,
  .token_2022_extensions_permanent_delegate_permanent_delegate_initialize,
  .token_2022_extensions_transfer_hook_transfer_hook_initialize]

theorem every_member_has_a_literal_case :
    members.length = 20 ∧ members.all (fun key =>
      fixtures.any (fun (selected, _, _) => decide (key = selected))) = true := by
  decide +kernel

/-- The exact references were inspected; the other releases below are only
inputs exercising the explicitly assumed compatible interval. -/
theorem reference_identities_keep_actual_versions :
    ["0.32.0", "0.32.1", "0.32.2", "0.32.3"].all (fun version => fixtures.all (fun (key, build,
      expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem compatible_identities_keep_actual_versions :
    ["0.32.4", "0.32.99+fixture"].all (fun version => fixtures.all (fun (key, build, expected) =>
      identitiesMatch key { build with version := version } expected)) = true := by
  decide +kernel

theorem lower_upper_and_prerelease_bounds :
    ["0.31.99", "0.33.0", "1.0.2", "0.32.4-rc.1"].all (fun version => fixtures.all (fun (key,
      build, _) =>
      identitiesMatch key { build with version := version } [])) = true := by
  decide +kernel

/-- The two shared keys retain their named 0.32 profiles beside the 1.0 profiles. -/
theorem reference_sets_and_ranges_remain_separate :
    members.all (fun key =>
      let profiles := (Solanalib.Specs.AnchorSpl.Capabilities.catalog.applicability key).filter
        (fun profile => match key with
          | .token_Token_id => profile.id == "anchor-spl-support-0.32.1-token-Token-id"
          | .token_TokenAccount_deref =>
            profile.id == "anchor-spl-support-0.32.1-token-TokenAccount-deref"
          | _ => true)
      decide (profiles.length = 1) && profiles.all (fun profile =>
        decide (profile.releases = ["0.32.0", "0.32.1", "0.32.2", "0.32.3"] ∧
          profile.compatibleRanges = [⟨"0.32.0", "0.33.0"⟩]))) = true := by
  decide +kernel

theorem a_version_cannot_replace_the_defining_source :
    fixtures.all (fun (key, build, _) =>
      identitiesMatch key { build with package := "wrong-defining-package" } [] &&
      identitiesMatch key { build with source :=
        ⟨"git", "https://example.invalid/library", "012345678901234567890123456789012345678\
          9"⟩ } [] &&
      identitiesMatch key { build with source :=
        ⟨"registry", "https://example.invalid/registry", ""⟩ } []) = true := by
  decide +kernel

/-- Each required edge is checked independently. Duplicate compatible
candidates remain ambiguous actual dependency facts. -/
theorem dependency_facts_cannot_be_missing_wrong_or_ambiguous :
    fixtures.all (fun (key, build, _) => build.dependencies.all (fun required =>
      identitiesMatch key { build with dependencies := (build.dependencies.filter
        (fun dependency => dependency.package != required.package)) } [] &&
      identitiesMatch key { build with dependencies := (build.dependencies.map
        (fun dependency => if dependency.package == required.package then
          { dependency with version := "99.0.0" } else dependency)) } [] &&
      identitiesMatch key { build with dependencies := (build.dependencies.map
        (fun dependency => if dependency.package == required.package then
          { dependency with source :=
            ⟨"git", "https://example.invalid/dependency", "01234567890123456789012345678901\
              23456789"⟩ }
          else dependency)) } [] &&
      identitiesMatch key { build with dependencies := build.dependencies ++ [required] } [])) =
        true := by
  decide +kernel

/-- Provider references and compatible fixtures preserve the actual
identity of the caller; the provider version is not substituted for the defining crate. -/
theorem dependency_references_and_compatible_versions :
    ([("anchor-lang", ["0.32.0", "0.32.3", "0.32.99", "0.32.99+fixture"]),
      ("spl-token-2022", ["8.0.0", "8.0.1", "8.9.99", "8.9.99+fixture"]),
      ("solana-account-info", ["2.3.0", "2.9.99", "2.9.99+fixture"]),
      ("solana-program-error", ["2.2.0", "2.2.1", "2.2.2", "2.9.99", "2.9.99+fixture"])] : List
        (String × List String)).all (fun (package, versions) =>
      fixtures.all (fun (key, build, expected) => versions.all (fun version =>
        identitiesMatch key { build with dependencies := (build.dependencies.map
          (fun dependency => if dependency.package == package then
            { dependency with version := version } else dependency)) } expected))) = true := by
  decide +kernel

/-- In particular, the unit BorshIoError of ProgramError 3 cannot replace the
selected owned String carrier. Other rows enforce their declared bounds. -/
theorem dependency_bounds_retain_the_selected_domains :
    ([("anchor-lang", ["0.31.99", "0.33.0", "1.0.2", "0.32.4-rc.1"]),
      ("spl-token-2022", ["7.0.0", "9.0.0", "8.0.1-rc.1"]),
      ("solana-account-info", ["2.2.1", "3.0.0", "2.3.0-rc.1"]),
      ("solana-program-error", ["2.1.0", "3.0.0", "2.2.2-rc.1"])] : List (String × List
        String)).all (fun (package, versions) =>
      fixtures.all (fun (key, build, _) => if (build.dependency package).isSome then
        versions.all (fun version => identitiesMatch key
          { build with dependencies := (build.dependencies.map (fun dependency =>
            if dependency.package == package then { dependency with version := version }
            else dependency)) } []) else true)) = true := by
  decide +kernel

/-- A missing fact is unknown. Wrong and duplicated facts cannot be supplied
by the host machine or hidden by another valid field. -/
theorem target_facts_are_operation_specific :
    fixtures.all (fun (key, build, _) => build.target.all (fun required =>
      let changed : Versioning.TargetFact :=
        ⟨required.field, if required.field == "pointer_width" then "32"
          else if required.field == "os" then "linux"
          else if required.field == "endian" then "big" else "unwind"⟩
      identitiesMatch key { build with target := (build.target.filter
        (fun fact => fact.field != required.field)) } [] &&
      identitiesMatch key { build with target := (build.target.map
        (fun fact => if fact.field == required.field then changed else fact)) } [] &&
      identitiesMatch key { build with target := build.target ++ [required] } [])) = true := by
  decide +kernel

theorem required_module_features_are_known_and_enabled :
    fixtures.all (fun (key, build, _) => if build.features.isSome then
      identitiesMatch key { build with features := none } [] &&
      identitiesMatch key { build with features := some [] } [] &&
      identitiesMatch key { build with features := some ["unrelated-module"] } []
      else true) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorSpl.Token.ExtendedProfiles

namespace SolanalibTest.Specs.AnchorSpl.UpdatedProfiles

open Solanalib.Contracts.Model.Versioning

set_option autoImplicit false

/-- These fixtures exercise the actual catalog. Isolating each newly added
profile keeps a rejected profile distinct from admission by an inherited
alternative; no model family or interpretation condition is replaced. -/
def onlyProfile (id : String) : Solanalib.Contracts.Model.Capabilities.Catalog :=
  { Solanalib.Specs.AnchorSpl.Capabilities.catalog with
    applicability := fun key =>
      (Solanalib.Specs.AnchorSpl.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

abbrev Row := Solanalib.Specs.AnchorSpl.Capabilities.Key × String × String × String

def identifies (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 =
    [⟨build.package, build.version, row.2.2.1, row.2.2.2⟩])

def rejects (build : Build) (row : Row) : Bool :=
  decide (((onlyProfile row.2.1).forBuild build).identities row.1 = [])

def registry : Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

def dependencyVersion (build : Build) (package version : String) : Build :=
  { build with dependencies := (build.dependencies.map (fun dep =>
      if dep.package == package then { dep with version := version } else dep)) }

def build0 : Build where
  package := "anchor-spl"
  version := "1.1.2"
  source := registry
  features := some ["token_2022"]
  dependencies := [
    ⟨"spl-token-2022-interface", "2.1.0", registry⟩]

def rows0 : List Row := [
    (.token_interface_TokenAccount_deref,
      "anchor-spl-support-1.1.2-token_interface-TokenAccount-deref",
      "core::ops::deref::Deref::deref",
        "<anchor_spl::token_interface::TokenAccount as core::ops::deref::Deref>::deref")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_0 :
    rows0.length = 1 ∧
    ["1.1.2", "1.1.3", "1.2.0"].all (fun version =>
      rows0.all (identifies { build0 with version := version })) = true := by
  decide +kernel

def accepted0 : List Build := [
  dependencyVersion build0 "spl-token-2022-interface" "2.1.1"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_0 :
    accepted0.length = 1 ∧
    accepted0.all (fun build => rows0.all (identifies build)) = true := by
  decide +kernel

def rejected0 : List Build := [
  { build0 with version := "1.1.1" },
  { build0 with version := "1.2.1" },
  { build0 with version := "1.1.3-rc.1" },
  { build0 with package := "unrelated-library" },
  { build0 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build0 "spl-token-2022-interface" "3.0.0",
  { build0 with dependencies := (build0.dependencies.filter (fun dep => dep.package !=
    "spl-token-2022-interface")) },
  { build0 with dependencies := (build0.dependencies ++ [⟨"spl-token-2022-interface", "2.1.\
    0",
    registry⟩]) },
  { build0 with dependencies := (build0.dependencies.map (fun dep =>
        if dep.package == "spl-token-2022-interface" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) },
  { build0 with features := none },
  { build0 with features := some [] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_0 :
    rejected0.length = 11 ∧
    rejected0.all (fun build => rows0.all (rejects build)) = true := by
  decide +kernel

def build1 : Build where
  package := "anchor-spl"
  version := "1.1.2"
  source := registry
  features := some ["token_2022"]
  dependencies := [
    ⟨"anchor-lang", "1.1.2", registry⟩,
    ⟨"spl-token-2022-interface", "2.1.0", registry⟩,
    ⟨"solana-account-info", "3.1.1", registry⟩,
    ⟨"solana-program-error", "3.0.1", registry⟩]

def rows1 : List Row := [
    (.token_2022_set_authority_program_id, "anchor-spl-token-1-1-2-token2022SetAuthority112",
      "anchor_spl::token_2022::set_authority", "anchor_spl::token_2022::set_authority"),
    (.token_2022_mint_to_checked, "anchor-spl-token-1-1-2-token2022MintToChecked112",
      "anchor_spl::token_2022::mint_to_checked", "anchor_spl::token_2022::mint_to_checked"),
    (.token_2022_burn_checked, "anchor-spl-token-1-1-2-token2022BurnChecked112",
      "anchor_spl::token_2022::burn_checked", "anchor_spl::token_2022::burn_checked"),
    (.token_2022_transfer_checked_program_id, "anchor-spl-token-1-1-2-token2022TransferChec\
      ked112",
      "anchor_spl::token_2022::transfer_checked", "anchor_spl::token_2022::transfer_checked")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_1 :
    rows1.length = 4 ∧
    ["1.1.2", "1.1.3", "1.2.0"].all (fun version =>
      rows1.all (identifies { build1 with version := version })) = true := by
  decide +kernel

def accepted1 : List Build := [
  dependencyVersion build1 "anchor-lang" "1.1.3",
  dependencyVersion build1 "spl-token-2022-interface" "2.1.1",
  dependencyVersion build1 "solana-account-info" "3.1.2",
  dependencyVersion build1 "solana-program-error" "3.0.2"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_1 :
    accepted1.length = 4 ∧
    accepted1.all (fun build => rows1.all (identifies build)) = true := by
  decide +kernel

def rejected1 : List Build := [
  { build1 with version := "1.1.1" },
  { build1 with version := "1.2.1" },
  { build1 with version := "1.1.3-rc.1" },
  { build1 with package := "unrelated-library" },
  { build1 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build1 "anchor-lang" "1.2.1",
  dependencyVersion build1 "spl-token-2022-interface" "3.0.0",
  dependencyVersion build1 "solana-account-info" "4.0.0",
  dependencyVersion build1 "solana-program-error" "4.0.0",
  { build1 with dependencies := (build1.dependencies.filter (fun dep => dep.package !=
    "anchor-lang")) },
  { build1 with dependencies := (build1.dependencies ++ [⟨"anchor-lang", "1.1.2", registry⟩]) },
  { build1 with dependencies := (build1.dependencies.map (fun dep =>
        if dep.package == "anchor-lang" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) },
  { build1 with features := none },
  { build1 with features := some [] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_1 :
    rejected1.length = 14 ∧
    rejected1.all (fun build => rows1.all (rejects build)) = true := by
  decide +kernel

def build2 : Build where
  package := "anchor-spl"
  version := "1.1.2"
  source := registry
  target := [⟨"os", "solana"⟩]
  features := some ["associated_token"]
  dependencies := [
    ⟨"anchor-lang", "1.1.2", registry⟩,
    ⟨"spl-associated-token-account-interface", "2.0.0", registry⟩,
    ⟨"solana-pubkey", "3.0.0", registry⟩,
    ⟨"solana-address", "2.6.1", registry⟩]

def rows2 : List Row := [
    (.associated_token_create_idempotent,
      "anchor-spl-support-1.1.2-associated_token-create_idempotent",
      "anchor_spl::associated_token::create_idempotent",
        "anchor_spl::associated_token::create_idempotent"),
    (.associated_token_create_program_id, "anchor-spl-support-1.1.2-associated_token-create",
      "anchor_spl::associated_token::create", "anchor_spl::associated_token::create")]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Exact reference and compatible fixture versions retain the actual
defining version and the complete registered item/implementation identity. -/
theorem actual_identities_2 :
    rows2.length = 2 ∧
    ["1.1.2", "1.1.3", "1.2.0"].all (fun version =>
      rows2.all (identifies { build2 with version := version })) = true := by
  decide +kernel

def accepted2 : List Build := [
  dependencyVersion build2 "anchor-lang" "1.1.3",
  dependencyVersion build2 "spl-associated-token-account-interface" "2.0.1",
  dependencyVersion build2 "solana-pubkey" "3.0.1",
  dependencyVersion build2 "solana-address" "2.6.2"]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem compatible_dependencies_2 :
    accepted2.length = 4 ∧
    accepted2.all (fun build => rows2.all (identifies build)) = true := by
  decide +kernel

def rejected2 : List Build := [
  { build2 with version := "1.1.1" },
  { build2 with version := "1.2.1" },
  { build2 with version := "1.1.3-rc.1" },
  { build2 with package := "unrelated-library" },
  { build2 with source := ⟨"git", "https://example.invalid/library", "pinned"⟩ },
  dependencyVersion build2 "anchor-lang" "1.2.1",
  dependencyVersion build2 "spl-associated-token-account-interface" "3.0.0",
  dependencyVersion build2 "solana-pubkey" "4.0.0",
  dependencyVersion build2 "solana-address" "3.0.0",
  { build2 with dependencies := (build2.dependencies.filter (fun dep => dep.package !=
    "anchor-lang")) },
  { build2 with dependencies := (build2.dependencies ++ [⟨"anchor-lang", "1.1.2", registry⟩]) },
  { build2 with dependencies := (build2.dependencies.map (fun dep =>
        if dep.package == "anchor-lang" then
          { dep with source := ⟨"git", "https://example.invalid/dependency", "pinned"⟩ } else dep)) },
  { build2 with target := (build2.target.filter (fun fact => fact.field != "os")) },
  { build2 with target := (build2.target.map (fun fact =>
        if fact.field == "os" then { fact with value := "linux" } else fact)) },
  { build2 with target := (build2.target ++ [⟨"os", "linux"⟩]) },
  { build2 with features := none },
  { build2 with features := some [] }]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem range_and_gate_rejections_2 :
    rejected2.length = 17 ∧
    rejected2.all (fun build => rows2.all (rejects build)) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorSpl.UpdatedProfiles

@[expose] public section

namespace SolanalibTest.Specs.AnchorSpl.V1_0_2Token

open Solanalib.Contracts.Model Solanalib.Specs.Core

/-- Restrict a test to one new profile so later parent alternatives remain intact. -/
def selectedProfile (id : String) :=
  { Solanalib.Specs.AnchorSpl.Capabilities.catalog with applicability := fun key =>
      (Solanalib.Specs.AnchorSpl.Capabilities.catalog.applicability key).filter (fun profile =>
        profile.id == id) }

def build0 : Versioning.Build where
  package := "anchor-spl"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some ["token_2022"]
  targetFeatures := none
  dependencies := [⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile0_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-spl-support-1.0.2-token_2022-Token2022-id").forBuild
        { build0 with version := version }).identities .token_2022_Token2022_id =
          [⟨"anchor-spl", version, "anchor_lang::Id::id",
            "<anchor_spl::token_2022::Token2022 as anchor_lang::Id>::id"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile0_present_in_full_catalog :
    ([⟨"anchor-spl", "1.0.2", "anchor_lang::Id::id",
            "<anchor_spl::token_2022::Token2022 as anchor_lang::Id>::id"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild
        build0).identities .token_2022_Token2022_id)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile0_range_rejections :
    ((selectedProfile "anchor-spl-support-1.0.2-token_2022-Token2022-id").applicability
      .token_2022_Token2022_id).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-spl-support-1.0.2-token_2022-Token2022-id").forBuild { build0 with
        version := version }).identities
        .token_2022_Token2022_id).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile0_build_rejections :
    ([{ build0 with package := "anchor-spl-other" },
      { build0 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build0 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build0 with dependencies := [] },
      { build0 with dependencies := [⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"spl-token-2022-interface", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"spl-token-2022-interface", "2.1.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build0 with dependencies := [⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩] },
      { build0 with features := none },
      { build0 with features := some [] } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild build).identities
        .token_2022_Token2022_id).isEmpty) = true := by
  decide +kernel

def build1 : Versioning.Build where
  package := "anchor-spl"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some ["token_2022"]
  targetFeatures := none
  dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile1_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-spl-token-1-0-2-token2022InitializeAccount3102").forBuild
        { build1 with version := version }).identities .token_2022_initialize_account3_program_id =
          [⟨"anchor-spl", version, "anchor_spl::token_2022::initialize_account3",
            "anchor_spl::token_2022::initialize_account3"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile1_present_in_full_catalog :
    ([⟨"anchor-spl", "1.0.2", "anchor_spl::token_2022::initialize_account3",
            "anchor_spl::token_2022::initialize_account3"⟩] : List Capabilities.RustIdentity).all
              (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild
        build1).identities .token_2022_initialize_account3_program_id)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile1_range_rejections :
    ((selectedProfile "anchor-spl-token-1-0-2-token2022InitializeAccount3102").applicability
      .token_2022_initialize_account3_program_id).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-spl-token-1-0-2-token2022InitializeAccount3102").forBuild { build1
        with version := version }).identities
        .token_2022_initialize_account3_program_id).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile1_build_rejections :
    ([{ build1 with package := "anchor-spl-other" },
      { build1 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build1 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build1 with dependencies := [⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build1 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩] },
      { build1 with features := none },
      { build1 with features := some [] } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild build).identities
        .token_2022_initialize_account3_program_id).isEmpty) = true := by
  decide +kernel

def build2 : Versioning.Build where
  package := "anchor-spl"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some ["token_2022"]
  targetFeatures := none
  dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile2_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-spl-token-1-0-2-token2022TransferChecked102").forBuild
        { build2 with version := version }).identities
          .token_2022_transfer_checked_program_id_interface =
          [⟨"anchor-spl", version, "anchor_spl::token_2022::transfer_checked",
            "anchor_spl::token_2022::transfer_checked"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile2_present_in_full_catalog :
    ([⟨"anchor-spl", "1.0.2", "anchor_spl::token_2022::transfer_checked",
            "anchor_spl::token_2022::transfer_checked"⟩] : List Capabilities.RustIdentity).all (fun
              identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild
        build2).identities .token_2022_transfer_checked_program_id_interface)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile2_range_rejections :
    ((selectedProfile "anchor-spl-token-1-0-2-token2022TransferChecked102").applicability
      .token_2022_transfer_checked_program_id_interface).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-spl-token-1-0-2-token2022TransferChecked102").forBuild { build2
        with version := version }).identities
        .token_2022_transfer_checked_program_id_interface).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile2_build_rejections :
    ([{ build2 with package := "anchor-spl-other" },
      { build2 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build2 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build2 with dependencies := [⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build2 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-account-info", "3.1.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-program-error", "3.0.1", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩] },
      { build2 with features := none },
      { build2 with features := some [] } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild build).identities
        .token_2022_transfer_checked_program_id_interface).isEmpty) = true := by
  decide +kernel

def build3 : Versioning.Build where
  package := "anchor-spl"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := [⟨"os", "solana"⟩]
  features := some ["associated_token"]
  targetFeatures := none
  dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile3_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile
        "anchor-spl-support-1.0.2-associated_token-create_idempotent").forBuild
        { build3 with version := version }).identities .associated_token_create_idempotent =
          [⟨"anchor-spl", version, "anchor_spl::associated_token::create_idempotent",
            "anchor_spl::associated_token::create_idempotent"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile3_present_in_full_catalog :
    ([⟨"anchor-spl", "1.0.2", "anchor_spl::associated_token::create_idempotent",
            "anchor_spl::associated_token::create_idempotent"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild
        build3).identities .associated_token_create_idempotent)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile3_range_rejections :
    ((selectedProfile "anchor-spl-support-1.0.2-associated_token-create_idempotent").applicability
      .associated_token_create_idempotent).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-spl-support-1.0.2-associated_token-create_idempotent").forBuild {
        build3 with version := version }).identities
        .associated_token_create_idempotent).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile3_build_rejections :
    ([{ build3 with package := "anchor-spl-other" },
      { build3 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build3 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build3 with dependencies := [⟨"spl-associated-token-account-interface", "2.0.0", ⟨
        "registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩, ⟨"solana-pubkey",
        "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩⟩, ⟨
        "solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://example.invalid/registry", ""⟩⟩, ⟨
        "solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build3 with dependencies := [⟨"anchor-lang", "1.0.2", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-associated-token-account-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-pubkey", "3.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"solana-address", "2.6.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩] },
      { build3 with target := [] },
      { build3 with target := [⟨"os", "solana"⟩, ⟨"os", "solana"⟩] },
      { build3 with target := [⟨"os", "unsupported-target-value"⟩] },
      { build3 with features := none },
      { build3 with features := some [] } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild build).identities
        .associated_token_create_idempotent).isEmpty) = true := by
  decide +kernel

def build4 : Versioning.Build where
  package := "anchor-spl"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some ["token"]
  targetFeatures := none
  dependencies := [⟨"spl-token-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile4_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-spl-support-1.0.2-token-Token-id").forBuild
        { build4 with version := version }).identities .token_Token_id =
          [⟨"anchor-spl", version, "anchor_lang::Id::id",
            "<anchor_spl::token::Token as anchor_lang::Id>::id"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile4_present_in_full_catalog :
    ([⟨"anchor-spl", "1.0.2", "anchor_lang::Id::id",
            "<anchor_spl::token::Token as anchor_lang::Id>::id"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild
        build4).identities .token_Token_id)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile4_range_rejections :
    ((selectedProfile "anchor-spl-support-1.0.2-token-Token-id").applicability
      .token_Token_id).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-spl-support-1.0.2-token-Token-id").forBuild { build4 with version
        := version }).identities
        .token_Token_id).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile4_build_rejections :
    ([{ build4 with package := "anchor-spl-other" },
      { build4 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build4 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build4 with dependencies := [] },
      { build4 with dependencies := [⟨"spl-token-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build4 with dependencies := [⟨"spl-token-interface", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build4 with dependencies := [⟨"spl-token-interface", "2.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build4 with dependencies := [⟨"spl-token-interface", "2.0.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩] },
      { build4 with features := none },
      { build4 with features := some [] } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild build).identities
        .token_Token_id).isEmpty) = true := by
  decide +kernel

def build5 : Versioning.Build where
  package := "anchor-spl"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some ["token"]
  targetFeatures := none
  dependencies := [⟨"spl-token-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile5_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile "anchor-spl-support-1.0.2-token-TokenAccount-deref").forBuild
        { build5 with version := version }).identities .token_TokenAccount_deref =
          [⟨"anchor-spl", version, "core::ops::deref::Deref::deref",
            "<anchor_spl::token::TokenAccount as core::ops::deref::Deref>::deref"⟩])) = true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile5_present_in_full_catalog :
    ([⟨"anchor-spl", "1.0.2", "core::ops::deref::Deref::deref",
            "<anchor_spl::token::TokenAccount as core::ops::deref::Deref>::deref"⟩] : List
              Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild
        build5).identities .token_TokenAccount_deref)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile5_range_rejections :
    ((selectedProfile "anchor-spl-support-1.0.2-token-TokenAccount-deref").applicability
      .token_TokenAccount_deref).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-spl-support-1.0.2-token-TokenAccount-deref").forBuild { build5
        with version := version }).identities
        .token_TokenAccount_deref).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile5_build_rejections :
    ([{ build5 with package := "anchor-spl-other" },
      { build5 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build5 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build5 with dependencies := [] },
      { build5 with dependencies := [⟨"spl-token-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-interface", "2.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build5 with dependencies := [⟨"spl-token-interface", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build5 with dependencies := [⟨"spl-token-interface", "2.0.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build5 with dependencies := [⟨"spl-token-interface", "2.0.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩] },
      { build5 with features := none },
      { build5 with features := some [] } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild build).identities
        .token_TokenAccount_deref).isEmpty) = true := by
  decide +kernel

def build6 : Versioning.Build where
  package := "anchor-spl"
  version := "1.0.2"
  source := ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩
  target := []
  features := some ["token_2022"]
  targetFeatures := none
  dependencies := [⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
    ""⟩⟩]

/-- Literal item and implementation identities retain the queried release.
The final version is a compatibility fixture, not another native recording. -/
theorem profile6_literal_identities :
    ["1.0.0", "1.0.1", "1.0.2", "1.0.3", "1.0.4"].all (fun version =>
      decide (((selectedProfile
        "anchor-spl-support-1.0.2-token_interface-TokenAccount-deref").forBuild
        { build6 with version := version }).identities .token_interface_TokenAccount_deref =
          [⟨"anchor-spl", version, "core::ops::deref::Deref::deref",
            "<anchor_spl::token_interface::TokenAccount as core::ops::deref::Deref>::deref"⟩])) =
              true := by
  decide +kernel

/-- The original reference release with its required facts selects these identities.
This selector fixture does not reconstruct an assessed Cargo build. -/
theorem profile6_present_in_full_catalog :
    ([⟨"anchor-spl", "1.0.2", "core::ops::deref::Deref::deref",
            "<anchor_spl::token_interface::TokenAccount as core::ops::deref::Deref>::deref"⟩] :
              List Capabilities.RustIdentity).all (fun identity =>
      decide (identity ∈ (Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild
        build6).identities .token_interface_TokenAccount_deref)) = true := by
  decide +kernel

/-- Scope bounds and prereleases cannot select this profile. The length check
prevents an absent profile from satisfying the negative control vacuously. -/
theorem profile6_range_rejections :
    ((selectedProfile "anchor-spl-support-1.0.2-token_interface-TokenAccount-deref").applicability
      .token_interface_TokenAccount_deref).length = 1 ∧
    ["0.999.999", "1.1.0", "1.0.4-rc.1"].all (fun version =>
      (((selectedProfile "anchor-spl-support-1.0.2-token_interface-TokenAccount-deref").forBuild {
        build6 with version := version }).identities
        .token_interface_TokenAccount_deref).isEmpty) = true := by
  decide +kernel

/-- Each case changes one required source/build fact; provider obligations stay separate. -/
theorem profile6_build_rejections :
    ([{ build6 with package := "anchor-spl-other" },
      { build6 with source := ⟨"git", "https://example.invalid/repository", "0123456789abcd\
        ef0123456789abcdef01234567"⟩ },
      { build6 with source := ⟨"registry", "https://example.invalid/registry", ""⟩ },
      { build6 with dependencies := [] },
      { build6 with dependencies := [⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩, ⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build6 with dependencies := [⟨"spl-token-2022-interface", "99.0.0", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build6 with dependencies := [⟨"spl-token-2022-interface", "2.1.0-rc.1", ⟨"registry", "https://github.com/rust-lang/crates.io-index",
        ""⟩⟩] },
      { build6 with dependencies := [⟨"spl-token-2022-interface", "2.1.0", ⟨"registry", "https://example.invalid/registry",
        ""⟩⟩] },
      { build6 with features := none },
      { build6 with features := some [] } ] : List Versioning.Build).all
      (fun build => ((Solanalib.Specs.AnchorSpl.Capabilities.catalog.forBuild build).identities
        .token_interface_TokenAccount_deref).isEmpty) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorSpl.V1_0_2Token

namespace SolanalibTest.Specs.AnchorSpl.LegacyTokenCompatibility

open Solanalib.Contracts.Model Solanalib.Specs.Core
open Solanalib.Specs.AnchorSpl.Capabilities (Key catalog)

def registry : Versioning.Source :=
  ⟨"registry", "https://github.com/rust-lang/crates.io-index", ""⟩

/-- Literal Rust identities are independent of generated profile selection. -/
def referenceRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.token_2022_transfer_checked_legacy_interface, {
    package := "anchor-spl", version := "0\
    .29.0",
    source := registry, dependencies := [⟨"anchor-lang", "0.29.0", registry⟩, ⟨"spl-token-2\
      022",
    "0.9.0", registry⟩, ⟨"solana-program", "1.18.26", registry⟩], features := some ["token_\
      2022"] },
      [("anchor_spl::token_2022::transfer_checked", "anchor_spl::token_2022::transfer_check\
        ed")]),
    (.token_interface_TokenInterface_ids, {
      package := "anchor-spl", version := "0.29.0", source :=
      registry, dependencies := [⟨"spl-token", "4.0.0", registry⟩, ⟨"spl-token-2022", "0.9.\
        0",
      registry⟩], features := some ["token_2022"] },
      [("anchor_lang::Ids::ids",
        "<anchor_spl::token_interface::TokenInterface as anchor_lang::Ids>::ids")]),
    (.token_interface_TokenAccount_deref, {
      package := "anchor-spl", version := "0.29.0", source :=
      registry, dependencies := [⟨"spl-token-2022", "0.9.0", registry⟩], features := some
        ["token_2022"] },
      [("core::ops::deref::Deref::deref",
        "<anchor_spl::token_interface::TokenAccount as core::ops::deref::Deref>::deref")])]

/-- These uninspected patch versions exercise compatibility assumptions only. -/
def compatibleRows : List (Key × Versioning.Build × List (String × String)) :=
  [(.token_2022_transfer_checked_legacy_interface, {
    package := "anchor-spl", version := "0\
    .29.1",
    source := registry, dependencies := [⟨"anchor-lang", "0.29.0", registry⟩, ⟨"spl-token-2\
      022",
    "0.9.0", registry⟩, ⟨"solana-program", "1.18.26", registry⟩], features := some ["token_\
      2022"] },
      [("anchor_spl::token_2022::transfer_checked", "anchor_spl::token_2022::transfer_check\
        ed")]),
    (.token_interface_TokenInterface_ids, {
      package := "anchor-spl", version := "0.29.1", source :=
      registry, dependencies := [⟨"spl-token", "4.0.0", registry⟩, ⟨"spl-token-2022", "0.9.\
        0",
      registry⟩], features := some ["token_2022"] },
      [("anchor_lang::Ids::ids",
        "<anchor_spl::token_interface::TokenInterface as anchor_lang::Ids>::ids")]),
    (.token_interface_TokenAccount_deref, {
      package := "anchor-spl", version := "0.29.1", source :=
      registry, dependencies := [⟨"spl-token-2022", "0.9.0", registry⟩], features := some
        ["token_2022"] },
      [("core::ops::deref::Deref::deref",
        "<anchor_spl::token_interface::TokenAccount as core::ops::deref::Deref>::deref")])]

theorem exact_reference_identities :
    referenceRows.length = 3 ∧ referenceRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem compatible_actual_version_identities :
    compatibleRows.length = 3 ∧ compatibleRows.all (fun row => decide
      ((catalog.forBuild row.2.1).identities row.1 =
        row.2.2.map (fun names => ⟨row.2.1.package, row.2.1.version, names.1, names.2⟩))) = true :=
          by
  decide +kernel

theorem build_metadata_keeps_actual_version :
    compatibleRows.all (fun row =>
      let build := { row.2.1 with version := row.2.1.version ++ "+review" }
      decide ((catalog.forBuild build).identities row.1 =
        row.2.2.map (fun names => ⟨build.package, build.version, names.1, names.2⟩))) = true := by
  decide +kernel

def rejectedVersions : List (Key × Versioning.Build × List String) :=
  [(.token_2022_transfer_checked_legacy_interface, {
    package := "anchor-spl", version := "0\
    .29.0",
    source := registry, dependencies := [⟨"anchor-lang", "0.29.0", registry⟩, ⟨"spl-token-2\
      022",
    "0.9.0", registry⟩, ⟨"solana-program", "1.18.26", registry⟩], features := some ["token_\
      2022"]
    }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.token_interface_TokenInterface_ids, {
      package := "anchor-spl", version := "0.29.0", source :=
      registry, dependencies := [⟨"spl-token", "4.0.0", registry⟩, ⟨"spl-token-2022", "0.9.\
        0",
      registry⟩], features := some ["token_2022"] }, ["0.28.999", "0.30.0", "0.29.0-rc.1"]),
    (.token_interface_TokenAccount_deref, {
      package := "anchor-spl", version := "0.29.0", source :=
      registry, dependencies := [⟨"spl-token-2022", "0.9.0", registry⟩], features := some
        ["token_2022"] }, ["0.28.999", "0.30.0", "0.29.0-rc.1"])]

theorem bounds_and_prereleases_rejected :
    rejectedVersions.all (fun row => row.2.2.all (fun version =>
      ((catalog.forBuild { row.2.1 with version := version }).identities row.1).isEmpty)) = true :=
        by
  decide +kernel

theorem defining_package_and_fork_rejected :
    (referenceRows ++ compatibleRows).all (fun row =>
      ((catalog.forBuild { row.2.1 with package := "wrong-defining-package" }).identities
        row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with source :=
        ⟨"git", "https://example.invalid/source-fork", "01234567890123456789012345678901234\
          56789"⟩
        }).identities row.1).isEmpty) = true := by
  decide +kernel

/-- Literal provider intervals test selection, without claiming native coverage. -/
def dependencyVersions : List (String × String × List String) :=
  [("anchor-lang", "0.29.1", ["0.28.999", "0.30.0", "0.29.1-rc.1"]),
    ("solana-program", "1.18.27", ["1.18.25", "2.0.0", "1.18.27-rc.1"]),
    ("spl-token", "4.0.1", ["3.999.999", "5.0.0", "4.0.1-rc.1"]),
    ("spl-token-2022", "0.9.1", ["0.8.999", "0.10.0", "0.9.1-rc.1"])]

theorem compatible_dependencies_keep_literal_identities :
    dependencyVersions.length = 4 ∧
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      match dependencyVersions.find? (fun item => item.1 == dep.package) with
      | none => false
      | some item =>
        let build := { row.2.1 with dependencies := row.2.1.dependencies.map (fun d =>
          if d.package = dep.package then { d with version := item.2.1 } else d) }
        decide ((catalog.forBuild build).identities row.1 =
          row.2.2.map (fun names => ⟨build.package, build.version, names.1, names.2⟩)))) = true :=
            by
  decide +kernel

theorem dependency_bounds_prereleases_and_two_compatible_candidates_rejected :
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      match dependencyVersions.find? (fun item => item.1 == dep.package) with
      | none => false
      | some item =>
        item.2.2.all (fun version =>
          ((catalog.forBuild { row.2.1 with dependencies := row.2.1.dependencies.map (fun d =>
            if d.package = dep.package then { d with version } else d) }).identities
              row.1).isEmpty) &&
        ((catalog.forBuild { row.2.1 with dependencies :=
          row.2.1.dependencies ++ [{ dep with version := item.2.1 }] }).identities row.1).isEmpty))
            = true := by
  decide +kernel

theorem required_dependency_cannot_be_omitted :
    referenceRows.any (fun row => !row.2.1.dependencies.isEmpty) = true ∧
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      ((catalog.forBuild { row.2.1 with dependencies :=
        (row.2.1.dependencies.filter (fun d => d.package != dep.package)) }).identities
          row.1).isEmpty)) = true := by
  decide +kernel

theorem dependency_generation_fork_and_ambiguity_rejected :
    (referenceRows ++ compatibleRows).all (fun row => row.2.1.dependencies.all (fun dep =>
      ((catalog.forBuild { row.2.1 with dependencies :=
        (row.2.1.dependencies.map (fun d => if d.package = dep.package then
          { d with version := "99.0.0" } else d)) }).identities row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with dependencies :=
        (row.2.1.dependencies.map (fun d => if d.package = dep.package then
          { d with source := ⟨"git", "https://example.invalid/provider-fork",
            "0123456789012345678901234567890123456789"⟩ } else d)) }).identities row.1).isEmpty &&
      ((catalog.forBuild { row.2.1 with dependencies := row.2.1.dependencies ++ [dep] }).identities
        row.1).isEmpty)) = true := by
  decide +kernel

theorem required_features_must_be_known_and_enabled :
    referenceRows.any (fun row => row.2.1.features.isSome) = true ∧
    (referenceRows ++ compatibleRows).all (fun row =>
      if row.2.1.features.isSome then
        ((catalog.forBuild { row.2.1 with features := none }).identities row.1).isEmpty &&
        ((catalog.forBuild { row.2.1 with features := some [] }).identities row.1).isEmpty
      else true) = true := by
  decide +kernel

end SolanalibTest.Specs.AnchorSpl.LegacyTokenCompatibility
