/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Specs.AnchorSpl.Support
import SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Wrappers

set_option autoImplicit false

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplSupport
open Solanalib.Specs.Core.AnchorSplSupport.Conformance

/-- The exact checker parses an existing live wrapper; all pointee values remain admitted. -/
theorem v0_32_1_token_interface_TokenAccount_deref_ready (input : Wrapper.Pointee
  .interfaceTokenAccount) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_contract.contract
      Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_sample)
      (some input) () :=
  deref_requires .interfaceTokenAccount _ rfl input

/-- The exact native fixture is admitted for each scripted invocation reply and custodian choice. -/
theorem v0_32_1_memo_build_memo_ready (reply : Script) (custodian : Bool) :
    Solanalib.Contracts.Model.requires (Solanalib.Specs.AnchorSpl.memo.build_memo_contract.contract
      Reference.types)
      (Sample.initial reply.reply) (nativeArgs .memo custodian) :=
  wrapper_requires .memo _ rfl reply custodian

/-- The exact native fixture is admitted for each scripted invocation reply and custodian choice. -/
theorem v0_32_1_metadata_create_metadata_accounts_v3_ready (reply : Script) (custodian : Bool) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.metadata.create_metadata_accounts_v3_contract.contract
      Reference.types)
      (Sample.initial reply.reply) (nativeArgs .metadata custodian) :=
  wrapper_requires .metadata _ rfl reply custodian

/-- The exact native fixture is admitted for each scripted invocation reply and custodian choice. -/
theorem v0_32_1_associated_token_create_ready (reply : Script) (custodian : Bool) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.associated_token.create_contract.contract Reference.types)
      (Sample.initial reply.reply) (nativeArgs (.associated .legacyBoxed .create) custodian) :=
  wrapper_requires (.associated .legacyBoxed .create) _ rfl reply custodian

/-- The exact checker parses an existing live wrapper; all pointee values remain admitted. -/
theorem v0_32_1_token_TokenAccount_deref_ready (input : Wrapper.Pointee .tokenAccount) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_contract.contract
      Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_sample)
      (some input) () :=
  deref_requires .tokenAccount _ rfl input

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplSupport
open Solanalib.Specs.Core.AnchorSplSupport.Conformance

/-- The exact native fixture is admitted for each scripted invocation reply and custodian choice. -/
theorem v1_1_2_associated_token_create_ready (reply : Script) (custodian : Bool) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.associated_token.create_program_id_contract.contract
      Reference.types)
      (Sample.initial reply.reply) (nativeArgs (.associated .modern .create) custodian) :=
  wrapper_requires (.associated .modern .create) _ rfl reply custodian

/-- The exact checker parses an existing live wrapper; all pointee values remain admitted. -/
theorem v1_1_2_token_interface_TokenAccount_deref_ready (input : Wrapper.Pointee
  .interfaceTokenAccount) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_contract.contract
      Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_sample)
      (some input) () :=
  deref_requires .interfaceTokenAccount _ rfl input

/-- The exact native fixture is admitted for each scripted invocation reply and custodian choice. -/
theorem v1_1_2_associated_token_create_idempotent_ready (reply : Script) (custodian : Bool) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.associated_token.create_idempotent_contract.contract
      Reference.types)
      (Sample.initial reply.reply) (nativeArgs (.associated .modern .idempotent) custodian) :=
  wrapper_requires (.associated .modern .idempotent) _ rfl reply custodian

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplSupport
open Solanalib.Specs.Core.AnchorSplSupport.Conformance

/-- The exact checker parses an existing live wrapper; all pointee values remain admitted. -/
theorem v1_0_2_token_interface_TokenAccount_deref_ready (input : Wrapper.Pointee
  .interfaceTokenAccount) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_contract.contract
      Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_sample)
      (some input) () :=
  deref_requires .interfaceTokenAccount _ rfl input

/-- The exact native fixture is admitted for each scripted invocation reply and custodian choice. -/
theorem v1_0_2_associated_token_create_idempotent_ready (reply : Script) (custodian : Bool) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.associated_token.create_idempotent_contract.contract
      Reference.types)
      (Sample.initial reply.reply) (nativeArgs (.associated .modern .idempotent) custodian) :=
  wrapper_requires (.associated .modern .idempotent) _ rfl reply custodian

/-- The exact checker parses an existing live wrapper; all pointee values remain admitted. -/
theorem v1_0_2_token_TokenAccount_deref_ready (input : Wrapper.Pointee .tokenAccount) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_contract.contract
      Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_sample)
      (some input) () :=
  deref_requires .tokenAccount _ rfl input

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplSupport
open Solanalib.Specs.Core.AnchorSplSupport.Conformance

/-- The exact checker parses an existing live wrapper; all pointee values remain admitted. -/
theorem v0_29_0_token_interface_TokenAccount_deref_ready (input : Wrapper.Pointee
  .interfaceTokenAccount) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_contract.contract
      Solanalib.Specs.AnchorSpl.token_interface.TokenAccount.deref_sample)
      (some input) () :=
  deref_requires .interfaceTokenAccount _ rfl input

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires

namespace SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplSupport
open Solanalib.Specs.Core.AnchorSplSupport.Conformance

/-- The exact native fixture is admitted for each scripted invocation reply and custodian choice. -/
theorem v0_27_0_stake_withdraw_ready (reply : Script) (custodian : Bool) :
    Solanalib.Contracts.Model.requires (Solanalib.Specs.AnchorSpl.stake.withdraw_contract.contract
      Reference.types)
      (Sample.initial reply.reply) (nativeArgs .withdraw custodian) :=
  wrapper_requires .withdraw _ rfl reply custodian

/-- The exact checker parses an existing live wrapper; all pointee values remain admitted. -/
theorem v0_27_0_stake_StakeAccount_deref_ready (input : Wrapper.Pointee .stakeAccount) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.stake.StakeAccount.deref_contract.contract
      Solanalib.Specs.AnchorSpl.stake.StakeAccount.deref_sample)
      (some input) () :=
  deref_requires .stakeAccount _ rfl input

/-- The exact checker parses an existing live wrapper; all pointee values remain admitted. -/
theorem v0_27_0_token_TokenAccount_deref_ready (input : Wrapper.Pointee .tokenAccount) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_contract.contract
      Solanalib.Specs.AnchorSpl.token.TokenAccount.deref_sample)
      (some input) () :=
  deref_requires .tokenAccount _ rfl input

/-- The exact native fixture is admitted for each scripted invocation reply and custodian choice. -/
theorem v0_27_0_stake_deactivate_stake_ready (reply : Script) (custodian : Bool) :
    Solanalib.Contracts.Model.requires
      (Solanalib.Specs.AnchorSpl.stake.deactivate_stake_contract.contract Reference.types)
      (Sample.initial reply.reply) (nativeArgs .deactivate custodian) :=
  wrapper_requires .deactivate _ rfl reply custodian

end SolanalibTest.Conformance.Library.Families.AnchorSplSupport.Requires
