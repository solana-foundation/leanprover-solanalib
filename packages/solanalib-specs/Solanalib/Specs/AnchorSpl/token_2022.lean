/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
module

public import Solanalib.Specs.Core.AnchorSplTokenOperations.Sample
public import Solanalib.Specs.Core.AnchorSplTokenOperations.Continuation
public import Solanalib.Specs.Core.AnchorSplTokenOperations.BuilderErrors

@[expose] public section

open Solanalib.Contracts.Model

set_option autoImplicit false

namespace Solanalib.Specs.AnchorSpl

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplTokenOperations

namespace token_2022

/-- The 0.32.1 reference binding; per-function applicability selects compatible sources.
CPI providers remain opaque and ownership stays source-ordered. -/
def transfer_checked_contract := family .token2022TransferChecked0321
def transfer_checked_run := reference .token2022TransferChecked0321
def transfer_checked_sample := Sample.types .token2022TransferChecked0321
theorem transfer_checked_reference : FamilyReference transfer_checked_contract transfer_checked_run
  :=
  reference_holds .token2022TransferChecked0321
theorem transfer_checked_has_execution :
    FamilyHasExecution transfer_checked_contract transfer_checked_run transfer_checked_sample :=
  Sample.execution .token2022TransferChecked0321
theorem transfer_checked_satisfiable : FamilySatisfiable transfer_checked_contract
  transfer_checked_sample :=
  transfer_checked_has_execution.satisfiable

end token_2022

end Solanalib.Specs.AnchorSpl

namespace Solanalib.Specs.AnchorSpl

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplTokenOperations

namespace token

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def transfer_with_program_owner_contract := family .tokenTransfer0321
def transfer_with_program_owner_run := reference .tokenTransfer0321
def transfer_with_program_owner_sample := Sample.types .tokenTransfer0321
theorem transfer_with_program_owner_reference : FamilyReference
  transfer_with_program_owner_contract transfer_with_program_owner_run :=
  reference_holds .tokenTransfer0321
theorem transfer_with_program_owner_has_execution :
    FamilyHasExecution transfer_with_program_owner_contract transfer_with_program_owner_run
      transfer_with_program_owner_sample :=
  Sample.execution .tokenTransfer0321
theorem transfer_with_program_owner_satisfiable : FamilySatisfiable
  transfer_with_program_owner_contract transfer_with_program_owner_sample :=
  transfer_with_program_owner_has_execution.satisfiable

end token

namespace token_2022

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def burn_contract := family .token2022Burn0321
def burn_run := reference .token2022Burn0321
def burn_sample := Sample.types .token2022Burn0321
theorem burn_reference : FamilyReference burn_contract burn_run :=
  reference_holds .token2022Burn0321
theorem burn_has_execution :
    FamilyHasExecution burn_contract burn_run burn_sample :=
  Sample.execution .token2022Burn0321
theorem burn_satisfiable : FamilySatisfiable burn_contract burn_sample :=
  burn_has_execution.satisfiable

end token_2022

namespace token_2022

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def close_account_contract := family .token2022CloseAccount0321
def close_account_run := reference .token2022CloseAccount0321
def close_account_sample := Sample.types .token2022CloseAccount0321
theorem close_account_reference : FamilyReference close_account_contract close_account_run :=
  reference_holds .token2022CloseAccount0321
theorem close_account_has_execution :
    FamilyHasExecution close_account_contract close_account_run close_account_sample :=
  Sample.execution .token2022CloseAccount0321
theorem close_account_satisfiable : FamilySatisfiable close_account_contract close_account_sample :=
  close_account_has_execution.satisfiable

end token_2022

namespace token_2022

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def get_account_data_size_contract := family .token2022GetAccountDataSize0321
def get_account_data_size_run := reference .token2022GetAccountDataSize0321
def get_account_data_size_sample := Sample.types .token2022GetAccountDataSize0321
theorem get_account_data_size_reference : FamilyReference get_account_data_size_contract
  get_account_data_size_run :=
  reference_holds .token2022GetAccountDataSize0321
theorem get_account_data_size_has_execution :
    FamilyHasExecution get_account_data_size_contract get_account_data_size_run
      get_account_data_size_sample :=
  Sample.execution .token2022GetAccountDataSize0321
theorem get_account_data_size_satisfiable : FamilySatisfiable get_account_data_size_contract
  get_account_data_size_sample :=
  get_account_data_size_has_execution.satisfiable

end token_2022

namespace token_2022

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def initialize_account3_contract := family .token2022InitializeAccount30321
def initialize_account3_run := reference .token2022InitializeAccount30321
def initialize_account3_sample := Sample.types .token2022InitializeAccount30321
theorem initialize_account3_reference : FamilyReference initialize_account3_contract
  initialize_account3_run :=
  reference_holds .token2022InitializeAccount30321
theorem initialize_account3_has_execution :
    FamilyHasExecution initialize_account3_contract initialize_account3_run
      initialize_account3_sample :=
  Sample.execution .token2022InitializeAccount30321
theorem initialize_account3_satisfiable : FamilySatisfiable initialize_account3_contract
  initialize_account3_sample :=
  initialize_account3_has_execution.satisfiable

end token_2022

namespace token_2022

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def initialize_immutable_owner_contract := family .token2022InitializeImmutableOwner0321
def initialize_immutable_owner_run := reference .token2022InitializeImmutableOwner0321
def initialize_immutable_owner_sample := Sample.types .token2022InitializeImmutableOwner0321
theorem initialize_immutable_owner_reference : FamilyReference initialize_immutable_owner_contract
  initialize_immutable_owner_run :=
  reference_holds .token2022InitializeImmutableOwner0321
theorem initialize_immutable_owner_has_execution :
    FamilyHasExecution initialize_immutable_owner_contract initialize_immutable_owner_run
      initialize_immutable_owner_sample :=
  Sample.execution .token2022InitializeImmutableOwner0321
theorem initialize_immutable_owner_satisfiable : FamilySatisfiable
  initialize_immutable_owner_contract initialize_immutable_owner_sample :=
  initialize_immutable_owner_has_execution.satisfiable

end token_2022

namespace token_2022

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def initialize_mint2_contract := family .token2022InitializeMint20321
def initialize_mint2_run := reference .token2022InitializeMint20321
def initialize_mint2_sample := Sample.types .token2022InitializeMint20321
theorem initialize_mint2_reference : FamilyReference initialize_mint2_contract initialize_mint2_run
  :=
  reference_holds .token2022InitializeMint20321
theorem initialize_mint2_has_execution :
    FamilyHasExecution initialize_mint2_contract initialize_mint2_run initialize_mint2_sample :=
  Sample.execution .token2022InitializeMint20321
theorem initialize_mint2_satisfiable : FamilySatisfiable initialize_mint2_contract
  initialize_mint2_sample :=
  initialize_mint2_has_execution.satisfiable

end token_2022

namespace token_2022

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def mint_to_contract := family .token2022MintTo0321
def mint_to_run := reference .token2022MintTo0321
def mint_to_sample := Sample.types .token2022MintTo0321
theorem mint_to_reference : FamilyReference mint_to_contract mint_to_run :=
  reference_holds .token2022MintTo0321
theorem mint_to_has_execution :
    FamilyHasExecution mint_to_contract mint_to_run mint_to_sample :=
  Sample.execution .token2022MintTo0321
theorem mint_to_satisfiable : FamilySatisfiable mint_to_contract mint_to_sample :=
  mint_to_has_execution.satisfiable

end token_2022

namespace token_2022

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def set_authority_contract := family .token2022SetAuthority0321
def set_authority_run := reference .token2022SetAuthority0321
def set_authority_sample := Sample.types .token2022SetAuthority0321
theorem set_authority_reference : FamilyReference set_authority_contract set_authority_run :=
  reference_holds .token2022SetAuthority0321
theorem set_authority_has_execution :
    FamilyHasExecution set_authority_contract set_authority_run set_authority_sample :=
  Sample.execution .token2022SetAuthority0321
theorem set_authority_satisfiable : FamilySatisfiable set_authority_contract set_authority_sample :=
  set_authority_has_execution.satisfiable

end token_2022

namespace token_2022_extensions.group_member_pointer

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def group_member_pointer_initialize_contract := family .groupMemberPointer0321
def group_member_pointer_initialize_run := reference .groupMemberPointer0321
def group_member_pointer_initialize_sample := Sample.types .groupMemberPointer0321
theorem group_member_pointer_initialize_reference : FamilyReference
  group_member_pointer_initialize_contract group_member_pointer_initialize_run :=
  reference_holds .groupMemberPointer0321
theorem group_member_pointer_initialize_has_execution :
    FamilyHasExecution group_member_pointer_initialize_contract group_member_pointer_initialize_run
      group_member_pointer_initialize_sample :=
  Sample.execution .groupMemberPointer0321
theorem group_member_pointer_initialize_satisfiable : FamilySatisfiable
  group_member_pointer_initialize_contract group_member_pointer_initialize_sample :=
  group_member_pointer_initialize_has_execution.satisfiable

end token_2022_extensions.group_member_pointer

namespace token_2022_extensions.group_pointer

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def group_pointer_initialize_contract := family .groupPointer0321
def group_pointer_initialize_run := reference .groupPointer0321
def group_pointer_initialize_sample := Sample.types .groupPointer0321
theorem group_pointer_initialize_reference : FamilyReference group_pointer_initialize_contract
  group_pointer_initialize_run :=
  reference_holds .groupPointer0321
theorem group_pointer_initialize_has_execution :
    FamilyHasExecution group_pointer_initialize_contract group_pointer_initialize_run
      group_pointer_initialize_sample :=
  Sample.execution .groupPointer0321
theorem group_pointer_initialize_satisfiable : FamilySatisfiable group_pointer_initialize_contract
  group_pointer_initialize_sample :=
  group_pointer_initialize_has_execution.satisfiable

end token_2022_extensions.group_pointer

namespace token_2022_extensions.metadata_pointer

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def metadata_pointer_initialize_contract := family .metadataPointer0321
def metadata_pointer_initialize_run := reference .metadataPointer0321
def metadata_pointer_initialize_sample := Sample.types .metadataPointer0321
theorem metadata_pointer_initialize_reference : FamilyReference
  metadata_pointer_initialize_contract metadata_pointer_initialize_run :=
  reference_holds .metadataPointer0321
theorem metadata_pointer_initialize_has_execution :
    FamilyHasExecution metadata_pointer_initialize_contract metadata_pointer_initialize_run
      metadata_pointer_initialize_sample :=
  Sample.execution .metadataPointer0321
theorem metadata_pointer_initialize_satisfiable : FamilySatisfiable
  metadata_pointer_initialize_contract metadata_pointer_initialize_sample :=
  metadata_pointer_initialize_has_execution.satisfiable

end token_2022_extensions.metadata_pointer

namespace token_2022_extensions.mint_close_authority

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def mint_close_authority_initialize_contract := family .mintCloseAuthority0321
def mint_close_authority_initialize_run := reference .mintCloseAuthority0321
def mint_close_authority_initialize_sample := Sample.types .mintCloseAuthority0321
theorem mint_close_authority_initialize_reference : FamilyReference
  mint_close_authority_initialize_contract mint_close_authority_initialize_run :=
  reference_holds .mintCloseAuthority0321
theorem mint_close_authority_initialize_has_execution :
    FamilyHasExecution mint_close_authority_initialize_contract mint_close_authority_initialize_run
      mint_close_authority_initialize_sample :=
  Sample.execution .mintCloseAuthority0321
theorem mint_close_authority_initialize_satisfiable : FamilySatisfiable
  mint_close_authority_initialize_contract mint_close_authority_initialize_sample :=
  mint_close_authority_initialize_has_execution.satisfiable

end token_2022_extensions.mint_close_authority

namespace token_2022_extensions.non_transferable

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def non_transferable_mint_initialize_contract := family .nonTransferableMint0321
def non_transferable_mint_initialize_run := reference .nonTransferableMint0321
def non_transferable_mint_initialize_sample := Sample.types .nonTransferableMint0321
theorem non_transferable_mint_initialize_reference : FamilyReference
  non_transferable_mint_initialize_contract non_transferable_mint_initialize_run :=
  reference_holds .nonTransferableMint0321
theorem non_transferable_mint_initialize_has_execution :
    FamilyHasExecution non_transferable_mint_initialize_contract
      non_transferable_mint_initialize_run non_transferable_mint_initialize_sample :=
  Sample.execution .nonTransferableMint0321
theorem non_transferable_mint_initialize_satisfiable : FamilySatisfiable
  non_transferable_mint_initialize_contract non_transferable_mint_initialize_sample :=
  non_transferable_mint_initialize_has_execution.satisfiable

end token_2022_extensions.non_transferable

namespace token_2022_extensions.permanent_delegate

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def permanent_delegate_initialize_contract := family .permanentDelegate0321
def permanent_delegate_initialize_run := reference .permanentDelegate0321
def permanent_delegate_initialize_sample := Sample.types .permanentDelegate0321
theorem permanent_delegate_initialize_reference : FamilyReference
  permanent_delegate_initialize_contract permanent_delegate_initialize_run :=
  reference_holds .permanentDelegate0321
theorem permanent_delegate_initialize_has_execution :
    FamilyHasExecution permanent_delegate_initialize_contract permanent_delegate_initialize_run
      permanent_delegate_initialize_sample :=
  Sample.execution .permanentDelegate0321
theorem permanent_delegate_initialize_satisfiable : FamilySatisfiable
  permanent_delegate_initialize_contract permanent_delegate_initialize_sample :=
  permanent_delegate_initialize_has_execution.satisfiable

end token_2022_extensions.permanent_delegate

namespace token_2022_extensions.transfer_hook

/-- Exact reviewed 0.32.1 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def transfer_hook_initialize_contract := family .transferHook0321
def transfer_hook_initialize_run := reference .transferHook0321
def transfer_hook_initialize_sample := Sample.types .transferHook0321
theorem transfer_hook_initialize_reference : FamilyReference transfer_hook_initialize_contract
  transfer_hook_initialize_run :=
  reference_holds .transferHook0321
theorem transfer_hook_initialize_has_execution :
    FamilyHasExecution transfer_hook_initialize_contract transfer_hook_initialize_run
      transfer_hook_initialize_sample :=
  Sample.execution .transferHook0321
theorem transfer_hook_initialize_satisfiable : FamilySatisfiable transfer_hook_initialize_contract
  transfer_hook_initialize_sample :=
  transfer_hook_initialize_has_execution.satisfiable

end token_2022_extensions.transfer_hook

end Solanalib.Specs.AnchorSpl

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorSpl

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplTokenOperations

namespace token_2022

/-- Exact reviewed 1.1.2 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def burn_checked_contract := family .token2022BurnChecked112
def burn_checked_run := reference .token2022BurnChecked112
def burn_checked_sample := Sample.types .token2022BurnChecked112
theorem burn_checked_reference : FamilyReference burn_checked_contract burn_checked_run :=
  reference_holds .token2022BurnChecked112
theorem burn_checked_has_execution :
    FamilyHasExecution burn_checked_contract burn_checked_run burn_checked_sample :=
  Sample.execution .token2022BurnChecked112
theorem burn_checked_satisfiable : FamilySatisfiable burn_checked_contract burn_checked_sample :=
  burn_checked_has_execution.satisfiable

end token_2022

namespace token_2022

/-- Exact reviewed 1.1.2 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def mint_to_checked_contract := family .token2022MintToChecked112
def mint_to_checked_run := reference .token2022MintToChecked112
def mint_to_checked_sample := Sample.types .token2022MintToChecked112
theorem mint_to_checked_reference : FamilyReference mint_to_checked_contract mint_to_checked_run :=
  reference_holds .token2022MintToChecked112
theorem mint_to_checked_has_execution :
    FamilyHasExecution mint_to_checked_contract mint_to_checked_run mint_to_checked_sample :=
  Sample.execution .token2022MintToChecked112
theorem mint_to_checked_satisfiable : FamilySatisfiable mint_to_checked_contract
  mint_to_checked_sample :=
  mint_to_checked_has_execution.satisfiable

end token_2022

namespace token_2022

/-- Exact reviewed 1.1.2 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def set_authority_program_id_contract := family .token2022SetAuthority112
def set_authority_program_id_run := reference .token2022SetAuthority112
def set_authority_program_id_sample := Sample.types .token2022SetAuthority112
theorem set_authority_program_id_reference : FamilyReference set_authority_program_id_contract
  set_authority_program_id_run :=
  reference_holds .token2022SetAuthority112
theorem set_authority_program_id_has_execution :
    FamilyHasExecution set_authority_program_id_contract set_authority_program_id_run
      set_authority_program_id_sample :=
  Sample.execution .token2022SetAuthority112
theorem set_authority_program_id_satisfiable : FamilySatisfiable set_authority_program_id_contract
  set_authority_program_id_sample :=
  set_authority_program_id_has_execution.satisfiable

end token_2022

namespace token_2022

/-- Exact reviewed 1.1.2 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def transfer_checked_program_id_contract := family .token2022TransferChecked112
def transfer_checked_program_id_run := reference .token2022TransferChecked112
def transfer_checked_program_id_sample := Sample.types .token2022TransferChecked112
theorem transfer_checked_program_id_reference : FamilyReference
  transfer_checked_program_id_contract transfer_checked_program_id_run :=
  reference_holds .token2022TransferChecked112
theorem transfer_checked_program_id_has_execution :
    FamilyHasExecution transfer_checked_program_id_contract transfer_checked_program_id_run
      transfer_checked_program_id_sample :=
  Sample.execution .token2022TransferChecked112
theorem transfer_checked_program_id_satisfiable : FamilySatisfiable
  transfer_checked_program_id_contract transfer_checked_program_id_sample :=
  transfer_checked_program_id_has_execution.satisfiable

end token_2022

end Solanalib.Specs.AnchorSpl

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorSpl

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplTokenOperations

namespace token_2022

/-- Exact reviewed 1.0.2 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def initialize_account3_program_id_contract := family .token2022InitializeAccount3102
def initialize_account3_program_id_run := reference .token2022InitializeAccount3102
def initialize_account3_program_id_sample := Sample.types .token2022InitializeAccount3102
theorem initialize_account3_program_id_reference : FamilyReference
  initialize_account3_program_id_contract initialize_account3_program_id_run :=
  reference_holds .token2022InitializeAccount3102
theorem initialize_account3_program_id_has_execution :
    FamilyHasExecution initialize_account3_program_id_contract initialize_account3_program_id_run
      initialize_account3_program_id_sample :=
  Sample.execution .token2022InitializeAccount3102
theorem initialize_account3_program_id_satisfiable : FamilySatisfiable
  initialize_account3_program_id_contract initialize_account3_program_id_sample :=
  initialize_account3_program_id_has_execution.satisfiable

end token_2022

end Solanalib.Specs.AnchorSpl

namespace Solanalib.Specs.AnchorSpl.token_2022

open Solanalib.Contracts.Model Solanalib.Specs.Core Solanalib.Specs.Core.AnchorSplTokenOperations

/-- Copied-program-ID interface with its original `Types` and `Args` binding
index. Its source body and projected behavior agree with the other copied-ID
wrapper; their complete typed families are kept distinct. -/
def transfer_checked_program_id_interface_contract := family .token2022TransferChecked102
def transfer_checked_program_id_interface_run := reference .token2022TransferChecked102
def transfer_checked_program_id_interface_sample := Sample.types .token2022TransferChecked102
theorem transfer_checked_program_id_interface_reference : FamilyReference
  transfer_checked_program_id_interface_contract transfer_checked_program_id_interface_run :=
  reference_holds .token2022TransferChecked102
theorem transfer_checked_program_id_interface_has_execution :
    FamilyHasExecution transfer_checked_program_id_interface_contract
      transfer_checked_program_id_interface_run transfer_checked_program_id_interface_sample :=
  Sample.execution .token2022TransferChecked102
theorem transfer_checked_program_id_interface_satisfiable : FamilySatisfiable
  transfer_checked_program_id_interface_contract transfer_checked_program_id_interface_sample :=
  transfer_checked_program_id_interface_has_execution.satisfiable


end Solanalib.Specs.AnchorSpl.token_2022

@[expose] public section

set_option autoImplicit false

namespace Solanalib.Specs.AnchorSpl

open Solanalib.Contracts.Model Solanalib.Specs.Core
open AnchorSplTokenOperations

namespace token_2022

/-- Exact reviewed 0.29.0 wrapper, with signature-level CPI providers and source-ordered ownership.
-/
def transfer_checked_legacy_interface_contract := family .token2022TransferChecked029
def transfer_checked_legacy_interface_run := reference .token2022TransferChecked029
def transfer_checked_legacy_interface_sample := Sample.types .token2022TransferChecked029
theorem transfer_checked_legacy_interface_reference : FamilyReference
  transfer_checked_legacy_interface_contract transfer_checked_legacy_interface_run :=
  reference_holds .token2022TransferChecked029
theorem transfer_checked_legacy_interface_has_execution :
    FamilyHasExecution transfer_checked_legacy_interface_contract
      transfer_checked_legacy_interface_run transfer_checked_legacy_interface_sample :=
  Sample.execution .token2022TransferChecked029
theorem transfer_checked_legacy_interface_satisfiable : FamilySatisfiable
  transfer_checked_legacy_interface_contract transfer_checked_legacy_interface_sample :=
  transfer_checked_legacy_interface_has_execution.satisfiable

end token_2022

end Solanalib.Specs.AnchorSpl
