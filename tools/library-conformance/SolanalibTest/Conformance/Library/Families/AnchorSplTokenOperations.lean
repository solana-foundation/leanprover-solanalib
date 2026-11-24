/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.AnchorSpl.Token
import Solanalib.Specs.AnchorSpl.token_2022
import SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations.Checker

/-!
# Projected Anchor SPL token wrappers

Exact immutable public wrapper spans use real Anchor context/account types and
real instruction constructors. Only complete invocation/getter signatures are
scripted. No SDK invocation implementation or token processor is executed.
-/

set_option autoImplicit false

open Solanalib.Specs.AnchorSpl

namespace SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations

def corpora : List (String × List Checker) := [
  ("anchor_spl_token_0_32_1", [
    checker .tokenTransfer0321 "anchor_spl::token::transfer"
      "Solanalib.Specs.AnchorSpl.token.transfer_with_program_owner_run"
        token.transfer_with_program_owner_run rfl
      token.transfer_with_program_owner_contract.contract rfl,
    checker .token2022Burn0321 "anchor_spl::token_2022::burn"
      "Solanalib.Specs.AnchorSpl.token_2022.burn_run" token_2022.burn_run
        rfl
      token_2022.burn_contract.contract rfl,
    checker .token2022CloseAccount0321 "anchor_spl::token_2022::close_account"
      "Solanalib.Specs.AnchorSpl.token_2022.close_account_run"
        token_2022.close_account_run rfl
      token_2022.close_account_contract.contract rfl,
    checker .token2022GetAccountDataSize0321 "anchor_spl::token_2022::get_account_data_size"
      "Solanalib.Specs.AnchorSpl.token_2022.get_account_data_size_run"
        token_2022.get_account_data_size_run rfl
      token_2022.get_account_data_size_contract.contract rfl,
    checker .token2022InitializeAccount30321 "anchor_spl::token_2022::initialize_account3"
      "Solanalib.Specs.AnchorSpl.token_2022.initialize_account3_run"
        token_2022.initialize_account3_run rfl
      token_2022.initialize_account3_contract.contract rfl,
    checker .token2022InitializeImmutableOwner0321
      "anchor_spl::token_2022::initialize_immutable_owner"
      "Solanalib.Specs.AnchorSpl.token_2022.initialize_immutable_owner_run"
        token_2022.initialize_immutable_owner_run rfl
      token_2022.initialize_immutable_owner_contract.contract rfl,
    checker .token2022InitializeMint20321 "anchor_spl::token_2022::initialize_mint2"
      "Solanalib.Specs.AnchorSpl.token_2022.initialize_mint2_run"
        token_2022.initialize_mint2_run rfl
      token_2022.initialize_mint2_contract.contract rfl,
    checker .token2022MintTo0321 "anchor_spl::token_2022::mint_to"
      "Solanalib.Specs.AnchorSpl.token_2022.mint_to_run"
        token_2022.mint_to_run rfl
      token_2022.mint_to_contract.contract rfl,
    checker .token2022SetAuthority0321 "anchor_spl::token_2022::set_authority"
      "Solanalib.Specs.AnchorSpl.token_2022.set_authority_run"
        token_2022.set_authority_run rfl
      token_2022.set_authority_contract.contract rfl,
    checker .token2022TransferChecked0321 "anchor_spl::token_2022::transfer_checked"
      "Solanalib.Specs.AnchorSpl.token_2022.transfer_checked_run"
        token_2022.transfer_checked_run rfl
      token_2022.transfer_checked_contract.contract rfl,
    checker .groupMemberPointer0321
      "anchor_spl::token_2022_extensions::group_member_pointer::group_member_pointer_initia\
        lize"
      "Solanalib.Specs.AnchorSpl.token_2022_extensions.group_member_pointer.group_member_po\
        inter_initialize_run"
          token_2022_extensions.group_member_pointer.group_member_pointer_initialize_run
          rfl
      token_2022_extensions.group_member_pointer.group_member_pointer_initialize_contract.contract
        rfl,
    checker .groupPointer0321
      "anchor_spl::token_2022_extensions::group_pointer::group_pointer_initialize"
      "Solanalib.Specs.AnchorSpl.token_2022_extensions.group_pointer.group_pointer_initiali\
        ze_run"
        token_2022_extensions.group_pointer.group_pointer_initialize_run
        rfl
      token_2022_extensions.group_pointer.group_pointer_initialize_contract.contract
        rfl,
    checker .metadataPointer0321
      "anchor_spl::token_2022_extensions::metadata_pointer::metadata_pointer_initialize"
      "Solanalib.Specs.AnchorSpl.token_2022_extensions.metadata_pointer.metadata_pointer_in\
        itialize_run"
          token_2022_extensions.metadata_pointer.metadata_pointer_initialize_run
          rfl
      token_2022_extensions.metadata_pointer.metadata_pointer_initialize_contract.contract
        rfl,
    checker .mintCloseAuthority0321
      "anchor_spl::token_2022_extensions::mint_close_authority::mint_close_authority_initia\
        lize"
      "Solanalib.Specs.AnchorSpl.token_2022_extensions.mint_close_authority.mint_close_auth\
        ority_initialize_run"
          token_2022_extensions.mint_close_authority.mint_close_authority_initialize_run
          rfl
      token_2022_extensions.mint_close_authority.mint_close_authority_initialize_contract.contract
        rfl,
    checker .nonTransferableMint0321
      "anchor_spl::token_2022_extensions::non_transferable::non_transferable_mint_initializ\
        e"
      "Solanalib.Specs.AnchorSpl.token_2022_extensions.non_transferable.non_transferable_mi\
        nt_initialize_run"
          token_2022_extensions.non_transferable.non_transferable_mint_initialize_run
          rfl
      token_2022_extensions.non_transferable.non_transferable_mint_initialize_contract.contract
        rfl,
    checker .permanentDelegate0321
      "anchor_spl::token_2022_extensions::permanent_delegate::permanent_delegate_initialize"
      "Solanalib.Specs.AnchorSpl.token_2022_extensions.permanent_delegate.permanent_delegat\
        e_initialize_run"
          token_2022_extensions.permanent_delegate.permanent_delegate_initialize_run
          rfl
      token_2022_extensions.permanent_delegate.permanent_delegate_initialize_contract.contract
        rfl,
    checker .transferHook0321
      "anchor_spl::token_2022_extensions::transfer_hook::transfer_hook_initialize"
      "Solanalib.Specs.AnchorSpl.token_2022_extensions.transfer_hook.transfer_hook_initiali\
        ze_run"
        token_2022_extensions.transfer_hook.transfer_hook_initialize_run
        rfl
      token_2022_extensions.transfer_hook.transfer_hook_initialize_contract.contract
        rfl]),
  ("anchor_spl_token_1_1_2", [
    checker .token2022BurnChecked112 "anchor_spl::token_2022::burn_checked"
      "Solanalib.Specs.AnchorSpl.token_2022.burn_checked_run"
        token_2022.burn_checked_run rfl
      token_2022.burn_checked_contract.contract rfl,
    checker .token2022MintToChecked112 "anchor_spl::token_2022::mint_to_checked"
      "Solanalib.Specs.AnchorSpl.token_2022.mint_to_checked_run"
        token_2022.mint_to_checked_run rfl
      token_2022.mint_to_checked_contract.contract rfl,
    checker .token2022SetAuthority112 "anchor_spl::token_2022::set_authority"
      "Solanalib.Specs.AnchorSpl.token_2022.set_authority_program_id_run"
        token_2022.set_authority_program_id_run rfl
      token_2022.set_authority_program_id_contract.contract rfl,
    checker .token2022TransferChecked112 "anchor_spl::token_2022::transfer_checked"
      "Solanalib.Specs.AnchorSpl.token_2022.transfer_checked_program_id_run"
        token_2022.transfer_checked_program_id_run rfl
      token_2022.transfer_checked_program_id_contract.contract rfl]),
  ("anchor_spl_token_1_0_2", [
    checker .token2022InitializeAccount3102 "anchor_spl::token_2022::initialize_account3"
      "Solanalib.Specs.AnchorSpl.token_2022.initialize_account3_program_id_run"
        token_2022.initialize_account3_program_id_run rfl
      token_2022.initialize_account3_program_id_contract.contract rfl,
    checker .token2022TransferChecked102 "anchor_spl::token_2022::transfer_checked"
      "Solanalib.Specs.AnchorSpl.token_2022.transfer_checked_program_id_interface_run"
        token_2022.transfer_checked_program_id_interface_run rfl
      token_2022.transfer_checked_program_id_interface_contract.contract
        rfl]),
  ("anchor_spl_token_0_29_0", [
    checker .token2022TransferChecked029 "anchor_spl::token_2022::transfer_checked"
      "Solanalib.Specs.AnchorSpl.token_2022.transfer_checked_legacy_interface_run"
        token_2022.transfer_checked_legacy_interface_run rfl
      token_2022.transfer_checked_legacy_interface_contract.contract
        rfl]),
  ("anchor_spl_token_0_27_0", [
    checker .tokenBurn027 "anchor_spl::token::burn"
      "Solanalib.Specs.AnchorSpl.token.burn_run" token.burn_run rfl
      token.burn_contract.contract rfl,
    checker .tokenMintTo027 "anchor_spl::token::mint_to"
      "Solanalib.Specs.AnchorSpl.token.mint_to_run" token.mint_to_run rfl
      token.mint_to_contract.contract rfl,
    checker .tokenTransfer027 "anchor_spl::token::transfer"
      "Solanalib.Specs.AnchorSpl.token.transfer_inline_error_run"
        token.transfer_inline_error_run rfl
      token.transfer_inline_error_contract.contract rfl])]

end SolanalibTest.Conformance.Library.Families.AnchorSplTokenOperations
