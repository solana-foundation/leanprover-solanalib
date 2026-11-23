/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.AnchorSpl.Support
import SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires

/-! Exact release/build profiles for actual value calls and projected wrappers.
Each entry supplies the full contract and reference of the selected version, with
checked definitional equalities to the evaluated shared mathematical family. -/

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplSupport

def check_0_32_1_tokenDeref : Checker :=
  derefChecker .tokenAccount "<anchor_spl::token::TokenAccount as \
    core::ops::deref::Deref>::deref"
    "Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_contract"
    "Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_run"
    (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_contract.contract
      (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_sample)) rfl
    (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_run
      (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_sample)) rfl

def check_0_32_1_interfaceDeref : Checker :=
  derefChecker .interfaceTokenAccount
    "<anchor_spl::token_interface::TokenAccount as core::ops::deref::Deref>::deref"
    "Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_contract"
    "Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_run"
    (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_contract.contract
      (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_sample)) rfl
    (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_run
      (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_sample)) rfl

def check_0_32_1_tokenId : Checker :=
  idChecker .token "<anchor_spl::token::Token as anchor_lang::Id>::id"
    "Solanalib.Specs.AnchorSpl.token.Token.id_contract"
    "Solanalib.Specs.AnchorSpl.token.Token.id_run"
    (Solanalib.Specs.AnchorSpl.token.Token.id_contract.contract Unit) rfl
      (Solanalib.Specs.AnchorSpl.token.Token.id_run Unit) rfl

def check_0_32_1_create : Checker :=
  wrapperChecker (.associated .legacyBoxed .create) "anchor_spl::associated_token::create"
    "Solanalib.Specs.AnchorSpl.associated_token.create_contract"
    "Solanalib.Specs.AnchorSpl.associated_token.create_run"
    (Solanalib.Specs.AnchorSpl.associated_token.create_contract.contract Reference.types) rfl
      (Solanalib.Specs.AnchorSpl.associated_token.create_run Reference.types) rfl

def check_0_32_1_memo : Checker :=
  wrapperChecker .memo "anchor_spl::memo::build_memo"
    "Solanalib.Specs.AnchorSpl.memo.build_memo_contract"
    "Solanalib.Specs.AnchorSpl.memo.build_memo_run"
    (Solanalib.Specs.AnchorSpl.memo.build_memo_contract.contract Reference.types) rfl
      (Solanalib.Specs.AnchorSpl.memo.build_memo_run Reference.types) rfl

def check_0_32_1_metadata : Checker :=
  wrapperChecker .metadata "anchor_spl::metadata::create_metadata_accounts_v3"
    "Solanalib.Specs.AnchorSpl.metadata.create_metadata_accounts_v3_contract"
    "Solanalib.Specs.AnchorSpl.metadata.create_metadata_accounts_v3_run"
    (Solanalib.Specs.AnchorSpl.metadata.create_metadata_accounts_v3_contract.contract
      Reference.types) rfl (Solanalib.Specs.AnchorSpl.metadata.create_metadata_accounts_v3_run
      Reference.types) rfl

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplSupport

def check_1_1_2_interfaceDeref : Checker :=
  derefChecker .interfaceTokenAccount
    "<anchor_spl::token_interface::TokenAccount as core::ops::deref::Deref>::deref"
    "Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_contract"
    "Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_run"
    (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_contract.contract
      (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_sample)) rfl
    (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_run
      (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_sample)) rfl

def check_1_1_2_create : Checker :=
  wrapperChecker (.associated .modern .create) "anchor_spl::associated_token::create"
    "Solanalib.Specs.AnchorSpl.associated_token.create_program_id_contract"
    "Solanalib.Specs.AnchorSpl.associated_token.create_program_id_run"
    (Solanalib.Specs.AnchorSpl.associated_token.create_program_id_contract.contract
      Reference.types) rfl (Solanalib.Specs.AnchorSpl.associated_token.create_program_id_run
      Reference.types) rfl

def check_1_1_2_idempotent : Checker :=
  wrapperChecker (.associated .modern .idempotent)
    "anchor_spl::associated_token::create_idempotent"
    "Solanalib.Specs.AnchorSpl.associated_token.create_idempotent_contract"
    "Solanalib.Specs.AnchorSpl.associated_token.create_idempotent_run"
    (Solanalib.Specs.AnchorSpl.associated_token.create_idempotent_contract.contract
      Reference.types) rfl (Solanalib.Specs.AnchorSpl.associated_token.create_idempotent_run
      Reference.types) rfl

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplSupport

def check_1_0_2_tokenDeref : Checker :=
  derefChecker .tokenAccount "<anchor_spl::token::TokenAccount as \
    core::ops::deref::Deref>::deref"
    "Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_contract"
    "Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_run"
    (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_contract.contract
      (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_sample)) rfl
    (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_run
      (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_sample)) rfl

def check_1_0_2_interfaceDeref : Checker :=
  derefChecker .interfaceTokenAccount
    "<anchor_spl::token_interface::TokenAccount as core::ops::deref::Deref>::deref"
    "Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_contract"
    "Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_run"
    (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_contract.contract
      (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_sample)) rfl
    (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_run
      (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_sample)) rfl

def check_1_0_2_tokenId : Checker :=
  idChecker .token "<anchor_spl::token::Token as anchor_lang::Id>::id"
    "Solanalib.Specs.AnchorSpl.token.Token.id_contract"
    "Solanalib.Specs.AnchorSpl.token.Token.id_run"
    (Solanalib.Specs.AnchorSpl.token.Token.id_contract.contract Unit) rfl
      (Solanalib.Specs.AnchorSpl.token.Token.id_run Unit) rfl

def check_1_0_2_token2022Id : Checker :=
  idChecker .token2022 "<anchor_spl::token_2022::Token2022 as anchor_lang::Id>::id"
    "Solanalib.Specs.AnchorSpl.token_2022.Token2022.id_contract"
    "Solanalib.Specs.AnchorSpl.token_2022.Token2022.id_run"
    (Solanalib.Specs.AnchorSpl.token_2022.Token2022.id_contract.contract Unit) rfl
      (Solanalib.Specs.AnchorSpl.token_2022.Token2022.id_run Unit) rfl

def check_1_0_2_idempotent : Checker :=
  wrapperChecker (.associated .modern .idempotent)
    "anchor_spl::associated_token::create_idempotent"
    "Solanalib.Specs.AnchorSpl.associated_token.create_idempotent_contract"
    "Solanalib.Specs.AnchorSpl.associated_token.create_idempotent_run"
    (Solanalib.Specs.AnchorSpl.associated_token.create_idempotent_contract.contract
      Reference.types) rfl (Solanalib.Specs.AnchorSpl.associated_token.create_idempotent_run
      Reference.types) rfl

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplSupport

def check_0_29_0_interfaceDeref : Checker :=
  derefChecker .interfaceTokenAccount
    "<anchor_spl::token_interface::TokenAccount as core::ops::deref::Deref>::deref"
    "Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_contract"
    "Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_run"
    (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_contract.contract
      (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_sample)) rfl
    (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_run
      (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_sample)) rfl

def check_0_29_0_ids : Checker :=
  idsChecker "Solanalib.Specs.AnchorSpl.token_interface.TokenInterface.ids_contract"
    "Solanalib.Specs.AnchorSpl.token_interface.TokenInterface.ids_run"
    (Solanalib.Specs.AnchorSpl.token_interface.TokenInterface.ids_contract.contract Unit) rfl
      (Solanalib.Specs.AnchorSpl.token_interface.TokenInterface.ids_run Unit) rfl

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplSupport

def check_0_27_0_stakeDeref : Checker :=
  derefChecker .stakeAccount "<anchor_spl::stake::StakeAccount as \
    core::ops::deref::Deref>::deref"
    "Solanalib.Specs.AnchorSpl.stake.StakeAccount.deref_contract"
    "Solanalib.Specs.AnchorSpl.stake.StakeAccount.deref_run"
    (Solanalib.Specs.AnchorSpl.stake.StakeAccount.deref_contract.contract
      (Solanalib.Specs.AnchorSpl.stake.StakeAccount.deref_sample)) rfl
    (Solanalib.Specs.AnchorSpl.stake.StakeAccount.deref_run
      (Solanalib.Specs.AnchorSpl.stake.StakeAccount.deref_sample)) rfl

def check_0_27_0_tokenDeref : Checker :=
  derefChecker .tokenAccount "<anchor_spl::token::TokenAccount as \
    core::ops::deref::Deref>::deref"
    "Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_contract"
    "Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_run"
    (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_contract.contract
      (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_sample)) rfl
    (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_run
      (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_sample)) rfl

def check_0_27_0_deactivate : Checker :=
  wrapperChecker .deactivate "anchor_spl::stake::deactivate_stake"
    "Solanalib.Specs.AnchorSpl.stake.deactivate_stake_contract"
    "Solanalib.Specs.AnchorSpl.stake.deactivate_stake_run"
    (Solanalib.Specs.AnchorSpl.stake.deactivate_stake_contract.contract Reference.types) rfl
      (Solanalib.Specs.AnchorSpl.stake.deactivate_stake_run Reference.types) rfl

def check_0_27_0_withdraw : Checker :=
  wrapperChecker .withdraw "anchor_spl::stake::withdraw"
    "Solanalib.Specs.AnchorSpl.stake.withdraw_contract"
    "Solanalib.Specs.AnchorSpl.stake.withdraw_run"
    (Solanalib.Specs.AnchorSpl.stake.withdraw_contract.contract Reference.types) rfl
      (Solanalib.Specs.AnchorSpl.stake.withdraw_run Reference.types) rfl

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport

def corpora : List (String × List Checker) := [
  ("anchor_spl_support_v0321_pubkey221", [check_0_32_1_tokenDeref, check_0_32_1_interfaceDeref,
    check_0_32_1_tokenId, check_0_32_1_create, check_0_32_1_memo, check_0_32_1_metadata]),
  ("anchor_spl_support_v0321_pubkey240", [check_0_32_1_tokenDeref, check_0_32_1_interfaceDeref,
    check_0_32_1_tokenId, check_0_32_1_create, check_0_32_1_metadata]),
  ("anchor_spl_support_v0321_interface", [check_0_32_1_interfaceDeref]),
  ("anchor_spl_support_v112", [check_1_1_2_interfaceDeref, check_1_1_2_create,
    check_1_1_2_idempotent]),
  ("anchor_spl_support_v102", [check_1_0_2_tokenDeref, check_1_0_2_interfaceDeref,
    check_1_0_2_tokenId, check_1_0_2_token2022Id, check_1_0_2_idempotent]),
  ("anchor_spl_support_v029", [check_0_29_0_interfaceDeref, check_0_29_0_ids]),
  ("anchor_spl_support_v027", [check_0_27_0_stakeDeref, check_0_27_0_tokenDeref,
    check_0_27_0_deactivate, check_0_27_0_withdraw])]

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport
